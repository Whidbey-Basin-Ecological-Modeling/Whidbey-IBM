#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include <memory>
#include <cmath>

#include "fish.h"
#include "model.h"
#include "predation.h"
#include "test_utilities.h"

// Helper function to calculate expected mortality matching Fish::getMortality()
static double calculateExpectedMortalityLegacyEqn(
    const Model &model,
    const MapNode &loc,
    double forkLength
) {
    const double mort_min_c = model.getFloat(ModelParamKey::MortMin);
    const double mort_max_d = model.getFloat(ModelParamKey::MortMax);
    const double habTypeMortConst = 0.6; // Z in the new equation
    const double a = 1.849;
    const double b_m = -0.8;
    const double b_s = -2.395;
    const double e = model.getFloat(ModelParamKey::MortalityInflectionPoint);
    const double L = forkLength;
    const double X = loc.popDensity;
    const double S = 250;
    const double result = (((mort_min_c + (mort_max_d - mort_min_c) * std::exp(-std::exp(-b_m * (std::log(X) - std::log(e))))) * (S / (std::exp(b_s + a * std::log(L)))))) * habTypeMortConst;
    return result;
}

TEST_CASE("Fish::getMortality baseline calculation", "[fish][mortality]") {
    using Catch::Approx;

    auto hydroModel = std::make_unique<MockHydroModel>();
    Model model(hydroModel.get());

    auto node = createMapNode(0.0f, 0.0f, HabitatType::Distributary);
    CHECK(node->habitat.structure() == HabitatStructure::Neutral);
    node->popDensity = 0.05f;

    SECTION("Calculates mortality matching equation for standard values") {
        Fish fish(1UL, 0L, 25.0f, node.get());
        CHECK(fish.forkLength == 25.0f);

        float mortality = fish.getMortality(model, *node);
        double expected = calculateExpectedMortalityLegacyEqn(model, *node, 25.0);

        REQUIRE(mortality == Approx(expected).epsilon(1e-5));
    }

    SECTION("Mortality scales with different fork lengths") {
        Fish smallFish(1UL, 0L, 20.0f, node.get());
        Fish largeFish(2UL, 0L, 29.0f, node.get());

        float smallMort = smallFish.getMortality(model, *node);
        float largeMort = largeFish.getMortality(model, *node);

        double expectedSmall = calculateExpectedMortalityLegacyEqn(model, *node, 20.0);
        double expectedLarge = calculateExpectedMortalityLegacyEqn(model, *node, 29.0);

        REQUIRE(smallMort == Approx(expectedSmall).epsilon(1e-5));
        REQUIRE(largeMort == Approx(expectedLarge).epsilon(1e-5));
        REQUIRE(smallMort > largeMort);
    }

    SECTION("Mortality responds to population density") {
        Fish fish(1UL, 0L, 25.0f, node.get());

        node->popDensity = 0.001f;
        float lowDensityMort = fish.getMortality(model, *node);
        double expectedLow = calculateExpectedMortalityLegacyEqn(model, *node, 25.0);
        REQUIRE(lowDensityMort == Approx(expectedLow).epsilon(1e-4));

        node->popDensity = 0.5f;
        float highDensityMort = fish.getMortality(model, *node);
        double expectedHigh = calculateExpectedMortalityLegacyEqn(model, *node, 25.0);
        REQUIRE(highDensityMort == Approx(expectedHigh).epsilon(1e-4));

        REQUIRE(lowDensityMort > highDensityMort);
    }
}

TEST_CASE("Fish::getMortality with dynamic predation mortality", "[fish][mortality][predation]") {
    using Catch::Approx;

    auto hydroModel = std::make_unique<MockHydroModel>();
    Model model(hydroModel.get());

    auto calcExpectedDynamicMortality = [](const Model &m, const MapNode &node, double forkLength) -> double {
        const double mort_min_c = m.getFloat(ModelParamKey::MortMin);
        const double mort_max_d = m.getFloat(ModelParamKey::MortMax);
        const double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(node.habitat, m.time, forkLength, m.getConfigMap());
        const double a = 1.849;
        const double b_m = -0.8;
        const double b_s = -2.395;
        const double e = m.getFloat(ModelParamKey::MortalityInflectionPoint);
        const double L = forkLength;
        const double X = node.popDensity;
        const double S = 250;
        return (((mort_min_c + (mort_max_d - mort_min_c) * std::exp(-std::exp(-b_m * (std::log(X) - std::log(e))))) * (S / (std::exp(b_s + a * std::log(L)))))) * habitatTypeConst;
    };

    SECTION("Calculates mortality across habitat structures (Complex, Neutral, Simplified)") {
        auto complexNode = createMapNode(0.0f, 0.0f, HabitatType::BlindChannel);
        auto neutralNode = createMapNode(1.0f, 0.0f, HabitatType::Distributary);
        auto simplifiedNode = createMapNode(2.0f, 0.0f, HabitatType::Harbor);
        simplifiedNode->habitat = Habitat(HabitatType::Harbor, LargeHabitatType::Delta);

        CHECK(complexNode->habitat.structure() == HabitatStructure::Complex);
        CHECK(neutralNode->habitat.structure() == HabitatStructure::Neutral);
        CHECK(simplifiedNode->habitat.structure() == HabitatStructure::Simplified);

        complexNode->popDensity = 0.05f;
        neutralNode->popDensity = 0.05f;
        simplifiedNode->popDensity = 0.05f;

        model.time = 1000;
        Fish fish(1UL, 0L, 50.0f, complexNode.get());

        float complexMort = fish.getMortality(model, *complexNode);
        float neutralMort = fish.getMortality(model, *neutralNode);
        float simplifiedMort = fish.getMortality(model, *simplifiedNode);

        REQUIRE(complexMort == Approx(calcExpectedDynamicMortality(model, *complexNode, 50.0)).epsilon(1e-5));
        REQUIRE(neutralMort == Approx(calcExpectedDynamicMortality(model, *neutralNode, 50.0)).epsilon(1e-5));
        REQUIRE(simplifiedMort == Approx(calcExpectedDynamicMortality(model, *simplifiedNode, 50.0)).epsilon(1e-5));

        // Baseline constants: Complex (0.5) < Neutral (1.0) < Simplified (1.5)
        REQUIRE(complexMort < neutralMort);
        REQUIRE(neutralMort < simplifiedMort);
        REQUIRE(neutralMort == Approx(complexMort * 2.0).epsilon(1e-5));
        REQUIRE(simplifiedMort == Approx(complexMort * 3.0).epsilon(1e-5));
    }

    SECTION("Mortality varies by time window cutoff") {
        auto node = createMapNode(0.0f, 0.0f, HabitatType::Distributary);
        CHECK(node->habitat.largeType() == LargeHabitatType::Delta);
        node->popDensity = 0.05f;

        Fish fish(1UL, 0L, 50.0f, node.get());

        model.time = 1000; // Early time window (t1: hour < 2500)
        float earlyMort = fish.getMortality(model, *node);
        REQUIRE(earlyMort == Approx(calcExpectedDynamicMortality(model, *node, 50.0)).epsilon(1e-5));

        model.time = 2500; // Late time window (t2: hour >= 2500)
        float lateMort = fish.getMortality(model, *node);
        REQUIRE(lateMort == Approx(calcExpectedDynamicMortality(model, *node, 50.0)).epsilon(1e-5));

        // Delta active predator relative density increases in late window (0.64 -> 0.74)
        REQUIRE(lateMort > earlyMort);
    }

    SECTION("Mortality incorporates active predator groups for large fish vs small fish") {
        auto intertidalNode = createMapNode(0.0f, 0.0f, HabitatType::Eelgrass);
        CHECK(intertidalNode->habitat.largeType() == LargeHabitatType::Intertidal);
        intertidalNode->popDensity = 0.02f;

        model.time = 3000;

        Fish fish150(1UL, 0L, 150.0f, intertidalNode.get());
        float mort150 = fish150.getMortality(model, *intertidalNode);
        REQUIRE(mort150 == Approx(calcExpectedDynamicMortality(model, *intertidalNode, 150.0)).epsilon(1e-5));

        Fish fish50(2UL, 0L, 50.0f, intertidalNode.get());
        float mort50 = fish50.getMortality(model, *intertidalNode);
        REQUIRE(mort50 == Approx(calcExpectedDynamicMortality(model, *intertidalNode, 50.0)).epsilon(1e-5));
    }
}
