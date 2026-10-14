#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include <memory>
#include <cmath>

#include "fish.h"
#include "model.h"
#include "test_utilities.h"

// Helper function to calculate expected mortality matching Fish::getMortality()
static double calculateExpectedMortality(
    const Model &model,
    const MapNode &loc,
    double forkLength
) {
    const double mort_min_c = model.getFloat(ModelParamKey::MortMin);
    const double mort_max_d = model.getFloat(ModelParamKey::MortMax);
    const float habitat_mortality_multiplier = model.getFloat(ModelParamKey::HabitatMortalityMultiplier);
    const double habTypeMortConst = loc.habitat.getMortalityConst(habitat_mortality_multiplier);
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
    node->popDensity = 0.05f;

    SECTION("Calculates mortality matching equation for standard values") {
        Fish fish(1UL, 0L, 50.0f, node.get());
        CHECK(fish.forkLength == 50.0f);

        float mortality = fish.getMortality(model, *node);
        double expected = calculateExpectedMortality(model, *node, 50.0);

        REQUIRE(mortality == Approx(expected).epsilon(1e-5));
    }

    SECTION("Mortality scales with different fork lengths") {
        Fish smallFish(1UL, 0L, 35.0f, node.get());
        Fish largeFish(2UL, 0L, 100.0f, node.get());

        float smallMort = smallFish.getMortality(model, *node);
        float largeMort = largeFish.getMortality(model, *node);

        double expectedSmall = calculateExpectedMortality(model, *node, 35.0);
        double expectedLarge = calculateExpectedMortality(model, *node, 100.0);

        REQUIRE(smallMort == Approx(expectedSmall).epsilon(1e-5));
        REQUIRE(largeMort == Approx(expectedLarge).epsilon(1e-5));
        REQUIRE(smallMort > largeMort);
    }

    SECTION("Mortality responds to population density") {
        Fish fish(1UL, 0L, 50.0f, node.get());

        node->popDensity = 0.001f;
        float lowDensityMort = fish.getMortality(model, *node);
        double expectedLow = calculateExpectedMortality(model, *node, 50.0);
        REQUIRE(lowDensityMort == Approx(expectedLow).epsilon(1e-4));

        node->popDensity = 0.5f;
        float highDensityMort = fish.getMortality(model, *node);
        double expectedHigh = calculateExpectedMortality(model, *node, 50.0);
        REQUIRE(highDensityMort == Approx(expectedHigh).epsilon(1e-4));

        REQUIRE(lowDensityMort > highDensityMort);
    }
}

TEST_CASE("Fish::getMortality habitat multiplier effect", "[fish][mortality]") {
    using Catch::Approx;

    auto hydroModel = std::make_unique<MockHydroModel>();
    Model model(hydroModel.get());

    auto distNode = createMapNode(0.0f, 0.0f, HabitatType::Distributary);
    auto nearshoreNode = createMapNode(1.0f, 0.0f, HabitatType::Nearshore);
    auto openWaterNode = createMapNode(2.0f, 0.0f, HabitatType::OpenWater);
    auto distEdgeNode = createMapNode(3.0f, 0.0f, HabitatType::DistributaryEdge);

    distNode->popDensity = 0.02f;
    nearshoreNode->popDensity = 0.02f;
    openWaterNode->popDensity = 0.02f;
    distEdgeNode->popDensity = 0.02f;

    Fish fish(1UL, 0L, 60.0f, distNode.get());

    float distMort = fish.getMortality(model, *distNode);
    float nearshoreMort = fish.getMortality(model, *nearshoreNode);
    float openWaterMort = fish.getMortality(model, *openWaterNode);
    float distEdgeMort = fish.getMortality(model, *distEdgeNode);

    REQUIRE(distMort == Approx(calculateExpectedMortality(model, *distNode, 60.0)).epsilon(1e-5));
    REQUIRE(nearshoreMort == Approx(calculateExpectedMortality(model, *nearshoreNode, 60.0)).epsilon(1e-5));
    REQUIRE(openWaterMort == Approx(calculateExpectedMortality(model, *openWaterNode, 60.0)).epsilon(1e-5));
    REQUIRE(distEdgeMort == Approx(calculateExpectedMortality(model, *distEdgeNode, 60.0)).epsilon(1e-5));

    // Distributary and Nearshore use HabitatMortalityMultiplier (default 2.0)
    // OpenWater and DistributaryEdge have const 1.0
    const float multiplier = model.getFloat(ModelParamKey::HabitatMortalityMultiplier);
    CHECK(multiplier == Approx(2.0f));
    REQUIRE(distMort == Approx(openWaterMort * multiplier).epsilon(1e-5));
    REQUIRE(nearshoreMort == Approx(openWaterMort * multiplier).epsilon(1e-5));
    REQUIRE(distEdgeMort == Approx(openWaterMort).epsilon(1e-5));
}
