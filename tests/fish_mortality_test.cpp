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

static void setHabitatMortalityMultiplier(Model &model, float multiplier) {
    const ModelConfigMap &config = model.getConfigMap();
    auto &mutableConfig = const_cast<ModelConfigMap &>(config);
    mutableConfig.set(ModelParamKey::HabitatMortalityMultiplier, multiplier);
}

TEST_CASE("Fish::getMortality baseline calculation", "[fish][mortality]") {
    using Catch::Approx;

    auto hydroModel = std::make_unique<MockHydroModel>();
    Model model(hydroModel.get());
    setHabitatMortalityMultiplier(model, 0.6f);

    auto node = createMapNode(0.0f, 0.0f, HabitatType::Distributary);
    CHECK(node->habitat.structure() == HabitatStructure::Neutral);
    node->popDensity = 0.05f;

    SECTION("Calculates mortality matching equation for standard values") {
        Fish fish(1UL, 0L, 25.0f, node.get());
        CHECK(fish.forkLength == 25.0f);

        float mortality = fish.getMortality(model, *node);
        double expected = calculateExpectedMortality(model, *node, 25.0);

        REQUIRE(mortality == Approx(expected).epsilon(1e-5));
    }

    SECTION("Mortality scales with different fork lengths") {
        Fish smallFish(1UL, 0L, 20.0f, node.get());
        Fish largeFish(2UL, 0L, 29.0f, node.get());

        float smallMort = smallFish.getMortality(model, *node);
        float largeMort = largeFish.getMortality(model, *node);

        double expectedSmall = calculateExpectedMortality(model, *node, 20.0);
        double expectedLarge = calculateExpectedMortality(model, *node, 29.0);

        REQUIRE(smallMort == Approx(expectedSmall).epsilon(1e-5));
        REQUIRE(largeMort == Approx(expectedLarge).epsilon(1e-5));
        REQUIRE(smallMort > largeMort);
    }

    SECTION("Mortality responds to population density") {
        Fish fish(1UL, 0L, 25.0f, node.get());

        node->popDensity = 0.001f;
        float lowDensityMort = fish.getMortality(model, *node);
        double expectedLow = calculateExpectedMortality(model, *node, 25.0);
        REQUIRE(lowDensityMort == Approx(expectedLow).epsilon(1e-4));

        node->popDensity = 0.5f;
        float highDensityMort = fish.getMortality(model, *node);
        double expectedHigh = calculateExpectedMortality(model, *node, 25.0);
        REQUIRE(highDensityMort == Approx(expectedHigh).epsilon(1e-4));

        REQUIRE(lowDensityMort > highDensityMort);
    }
}
