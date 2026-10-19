#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include <stdexcept>
#include "predation.h"

TEST_CASE("PredationMortality size range active status", "[predation]") {
    SECTION("Surface fish active in [30, 100]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::SurfaceFish, 29.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SurfaceFish, 30.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SurfaceFish, 60.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SurfaceFish, 100.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::SurfaceFish, 100.1));
    }

    SECTION("Demersal fish active in [30, 100]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::DemersalFish, 29.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::DemersalFish, 30.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::DemersalFish, 100.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::DemersalFish, 100.001));
    }

    SECTION("Otter active in [80, 300]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::Otter, 79.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::Otter, 80.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::Otter, 300.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::Otter, 300.1));
    }

    SECTION("Seal active in [100, 500]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::Seal, 99.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::Seal, 100.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::Seal, 500.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::Seal, 500.1));
    }

    SECTION("Porpoise active in [100, 400]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::Porpoise, 99.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::Porpoise, 100.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::Porpoise, 400.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::Porpoise, 400.1));
    }

    SECTION("Sea lion active in [100, 1000]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::SeaLion, 99.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SeaLion, 100.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SeaLion, 1000.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::SeaLion, 1000.1));
    }

    SECTION("Diving bird active in [30, 300]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::DivingBird, 29.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::DivingBird, 30.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::DivingBird, 300.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::DivingBird, 300.1));
    }

    SECTION("Wading bird lg active in [30, 200]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdLg, 29.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdLg, 30.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdLg, 200.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdLg, 200.1));
    }

    SECTION("Wading bird sm active in [30, 60]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdSm, 29.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdSm, 30.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdSm, 60.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::WadingBirdSm, 60.1));
    }

    SECTION("Carnivore bird active in [150, 500]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::CarnivoreBird, 149.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::CarnivoreBird, 150.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::CarnivoreBird, 500.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::CarnivoreBird, 500.1));
    }

    SECTION("Surface pecking bird active in [30, 200]") {
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::SurfacePeckingBird, 29.9));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SurfacePeckingBird, 30.0));
        REQUIRE(PredationMortality::isPredatorActive(PredatorGroup::SurfacePeckingBird, 200.0));
        REQUIRE_FALSE(PredationMortality::isPredatorActive(PredatorGroup::SurfacePeckingBird, 200.1));
    }

    SECTION("Invalid PredatorGroup throws exception") {
        REQUIRE_THROWS_AS(
            PredationMortality::isPredatorActive(PredatorGroup::PredatorGroupCountSentinel, 50.0),
            std::invalid_argument
        );
    }
}

TEST_CASE("PredationMortality habitat baseline constants", "[predation]") {
    SECTION("Structure baseline constants match default ModelConfigMap") {
        ModelConfigMap config;
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Complex, config) == 0.5);
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Neutral, config) == 1.0);
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Simplified, config) == 1.5);
    }

    SECTION("Structure baseline constants read custom values from ModelConfigMap") {
        ModelConfigMap config;
        config.set(ModelParamKey::HabitatMortConstComplex, 0.25f);
        config.set(ModelParamKey::HabitatMortConstNeutral, 0.75f);
        config.set(ModelParamKey::HabitatMortConstSimplified, 2.25f);

        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Complex, config) == 0.25);
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Neutral, config) == 0.75);
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Simplified, config) == 2.25);
    }

    SECTION("Structure baseline constants loaded from JSON Document") {
        rapidjson::Document doc;
        doc.Parse(R"({
            "habitatMortConstComplex": 0.4,
            "habitatMortConstNeutral": 0.8,
            "habitatMortConstSimplified": 1.2
        })");
        ModelConfigMap config;
        config.loadFromJson(doc);

        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Complex, config) == 0.4f);
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Neutral, config) == 0.8f);
        REQUIRE(PredationMortality::getHabitatBaselineConst(HabitatStructure::Simplified, config) == 1.2f);
    }

    SECTION("Invalid HabitatStructure throws exception") {
        ModelConfigMap config;
        REQUIRE_THROWS_AS(
            PredationMortality::getHabitatBaselineConst(HabitatStructure::HabitatStructureCountSentinel, config),
            std::invalid_argument
        );
    }
}

TEST_CASE("PredationMortality predator relative density matrix lookup", "[predation]") {
    SECTION("Surface fish relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Delta, 0) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Delta, 2500) == 0.3);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Freshwater, 100) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Freshwater, 3000) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Intertidal, 500) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Intertidal, 2500) == 0.15);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Offshore, 500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::Offshore, 2500) == 0.2);
    }

    SECTION("Demersal fish relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Delta, 1000) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Delta, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Freshwater, 1000) == 0.02);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Freshwater, 2500) == 0.03);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Intertidal, 1000) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Intertidal, 2500) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Offshore, 1000) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DemersalFish, LargeHabitatType::Offshore, 2500) == 0.3);
    }

    SECTION("Otter relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Delta, 1000) == 0.15);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Delta, 2500) == 0.15);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Freshwater, 1000) == 0.25);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Freshwater, 2500) == 0.25);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Intertidal, 1000) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Intertidal, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Offshore, 1000) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Otter, LargeHabitatType::Offshore, 2600) == 0.0);
    }

    SECTION("Seal relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Delta, 1000) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Delta, 2500) == 0.15);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Freshwater, 1000) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Freshwater, 2500) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Intertidal, 1000) == 0.3);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Intertidal, 2500) == 0.3);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Offshore, 1000) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Seal, LargeHabitatType::Offshore, 2500) == 0.1);
    }

    SECTION("Porpoise relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Delta, 1000) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Delta, 2500) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Freshwater, 1000) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Freshwater, 2500) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Intertidal, 1000) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Intertidal, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Offshore, 1000) == 0.4);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::Porpoise, LargeHabitatType::Offshore, 3000) == 0.4);
    }

    SECTION("Sea lion relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Delta, 1000) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Delta, 2500) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Freshwater, 1000) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Freshwater, 2500) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Intertidal, 1000) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Intertidal, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Offshore, 1000) == 0.25);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SeaLion, LargeHabitatType::Offshore, 3000) == 0.6);
    }

    SECTION("Diving bird relative density (time window transition at hour 2500)") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Delta, 2499) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Delta, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Freshwater, 100) == 0.05);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Freshwater, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Intertidal, 100) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Intertidal, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Offshore, 100) == 0.25);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::DivingBird, LargeHabitatType::Offshore, 2500) == 0.25);
    }

    SECTION("Wading bird lg relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Delta, 100) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Delta, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Freshwater, 100) == 0.07);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Freshwater, 2500) == 0.03);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Intertidal, 100) == 0.4);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Intertidal, 2500) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Offshore, 100) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdLg, LargeHabitatType::Offshore, 2500) == 0.0);
    }

    SECTION("Wading bird sm relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Delta, 100) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Delta, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Freshwater, 100) == 0.07);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Freshwater, 2500) == 0.03);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Intertidal, 100) == 0.4);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Intertidal, 2500) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Offshore, 100) == 0.0);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::WadingBirdSm, LargeHabitatType::Offshore, 2500) == 0.0);
    }

    SECTION("Carnivore bird relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Delta, 100) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Delta, 2500) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Freshwater, 100) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Freshwater, 2500) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Intertidal, 100) == 0.1);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Intertidal, 2500) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Offshore, 100) == 0.07);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::CarnivoreBird, LargeHabitatType::Offshore, 2500) == 0.13);
    }

    SECTION("Surface pecking bird relative density") {
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Delta, 100) == 0.04);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Delta, 2500) == 0.04);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Freshwater, 100) == 0.01);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Freshwater, 2500) == 0.01);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Intertidal, 100) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Intertidal, 2500) == 0.2);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Offshore, 100) == 0.25);
        REQUIRE(PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfacePeckingBird, LargeHabitatType::Offshore, 2500) == 0.25);
    }

    SECTION("Invalid arguments throw exceptions") {
        REQUIRE_THROWS_AS(
            PredationMortality::getPredatorRelativeDensity(PredatorGroup::PredatorGroupCountSentinel, LargeHabitatType::Delta, 100),
            std::invalid_argument
        );
        REQUIRE_THROWS_AS(
            PredationMortality::getPredatorRelativeDensity(PredatorGroup::SurfaceFish, LargeHabitatType::LargeHabitatTypeCountSentinel, 100),
            std::invalid_argument
        );
    }
}

TEST_CASE("PredationMortality active predator relative density sum calculations", "[predation]") {
    using Catch::Approx;

    SECTION("Delta habitat, hour < 2500, fork length 50mm") {
        double sum = PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType::Delta, 1000, 50.0);
        // Active at 50mm: SurfaceFish(0.1), DemersalFish(0.05), DivingBird(0.05), WadingBirdLg(0.2), WadingBirdSm(0.2), SurfacePeckingBird(0.04)
        // Sum = 0.1 + 0.05 + 0.05 + 0.2 + 0.2 + 0.04 = 0.64
        REQUIRE(sum == Approx(0.64));
    }

    SECTION("Delta habitat, hour >= 2500, fork length 50mm") {
        double sum = PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType::Delta, 2500, 50.0);
        // Active at 50mm: SurfaceFish(0.3), DemersalFish(0.1), DivingBird(0.1), WadingBirdLg(0.1), WadingBirdSm(0.1), SurfacePeckingBird(0.04)
        // Sum = 0.3 + 0.1 + 0.1 + 0.1 + 0.1 + 0.04 = 0.74
        REQUIRE(sum == Approx(0.74));
    }

    SECTION("Freshwater habitat, hour < 2500, fork length 65mm") {
        double sum = PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType::Freshwater, 1000, 65.0);
        // Active at 65mm: SurfaceFish(0.05), DemersalFish(0.02), DivingBird(0.05), WadingBirdLg(0.07), SurfacePeckingBird(0.01)
        // (WadingBirdSm is inactive because 65 > 60)
        // Sum = 0.05 + 0.02 + 0.05 + 0.07 + 0.01 = 0.20
        REQUIRE(sum == Approx(0.20));
    }

    SECTION("Offshore habitat, hour < 2500, fork length 200mm") {
        double sum = PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType::Offshore, 1000, 200.0);
        // Active at 200mm: Otter(0.0), Seal(0.1), Porpoise(0.4), SeaLion(0.25), DivingBird(0.25), WadingBirdLg(0.0), CarnivoreBird(0.07), SurfacePeckingBird(0.25)
        // Sum = 0.0 + 0.1 + 0.4 + 0.25 + 0.25 + 0.0 + 0.07 + 0.25 = 1.32
        REQUIRE(sum == Approx(1.32));
    }

    SECTION("Fork length out of range (no predators active)") {
        double sumLow = PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType::Delta, 1000, 20.0);
        double sumHigh = PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType::Offshore, 1000, 1100.0);
        REQUIRE(sumLow == Approx(0.0));
        REQUIRE(sumHigh == Approx(0.0));
    }
}

TEST_CASE("PredationMortality calculateHabitatTypeConst", "[predation]") {
    using Catch::Approx;
    ModelConfigMap config;

    SECTION("Delta complex habitat, hour < 2500, fork length 50mm") {
        Habitat habitat(HabitatType::BlindChannel);
        CHECK(habitat.structure() == HabitatStructure::Complex);
        CHECK(habitat.largeType() == LargeHabitatType::Delta);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 50.0, config);
        // Z (0.6) * mort.const (0.5) * (1 + active_pred_sum (0.64)) = 0.3 * 1.64 = 0.492
        REQUIRE(habitatTypeConst == Approx(0.492));
    }

    SECTION("Delta neutral habitat, hour >= 2500, fork length 50mm") {
        Habitat habitat(HabitatType::Distributary);
        CHECK(habitat.structure() == HabitatStructure::Neutral);
        CHECK(habitat.largeType() == LargeHabitatType::Delta);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 2500, 50.0, config);
        // Z (0.6) * mort.const (1.0) * (1 + active_pred_sum (0.74)) = 0.6 * 1.74 = 1.044
        REQUIRE(habitatTypeConst == Approx(1.044));
    }

    SECTION("Delta simplified habitat, hour < 2500, fork length 50mm") {
        Habitat habitat(HabitatType::Harbor, LargeHabitatType::Delta);
        CHECK(habitat.structure() == HabitatStructure::Simplified);
        CHECK(habitat.largeType() == LargeHabitatType::Delta);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 50.0, config);
        // Z (0.6) * mort.const (1.5) * (1 + active_pred_sum (0.64)) = 0.9 * 1.64 = 1.476
        REQUIRE(habitatTypeConst == Approx(1.476));
    }

    SECTION("Freshwater complex habitat, hour < 2500, fork length 65mm") {
        Habitat habitat(HabitatType::Creek);
        CHECK(habitat.structure() == HabitatStructure::Complex);
        CHECK(habitat.largeType() == LargeHabitatType::Freshwater);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 65.0, config);
        // Z (0.6) * mort.const (0.5) * (1 + active_pred_sum (0.20)) = 0.3 * 1.20 = 0.36
        REQUIRE(habitatTypeConst == Approx(0.36));
    }

    SECTION("Offshore neutral habitat, hour < 2500, fork length 200mm") {
        Habitat habitat(HabitatType::OpenWater);
        CHECK(habitat.structure() == HabitatStructure::Neutral);
        CHECK(habitat.largeType() == LargeHabitatType::Offshore);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 200.0, config);
        // Z (0.6) * mort.const (1.0) * (1 + active_pred_sum (1.32)) = 0.6 * 2.32 = 1.392
        REQUIRE(habitatTypeConst == Approx(1.392));
    }

    SECTION("Intertidal complex habitat, hour >= 2500, fork length 150mm") {
        Habitat habitat(HabitatType::Eelgrass);
        CHECK(habitat.structure() == HabitatStructure::Complex);
        CHECK(habitat.largeType() == LargeHabitatType::Intertidal);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 3000, 150.0, config);
        // Z (0.6) * mort.const (0.5) * (1 + active_pred_sum (1.30)) = 0.3 * 2.30 = 0.69
        REQUIRE(habitatTypeConst == Approx(0.69));
    }

    SECTION("Intertidal simplified habitat, hour < 2500, fork length 50mm") {
        Habitat habitat(HabitatType::Harbor, LargeHabitatType::Intertidal);
        CHECK(habitat.structure() == HabitatStructure::Simplified);
        CHECK(habitat.largeType() == LargeHabitatType::Intertidal);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 50.0, config);
        // Z (0.6) * mort.const (1.5) * (1 + active_pred_sum (1.25)) = 0.9 * 2.25 = 2.025
        REQUIRE(habitatTypeConst == Approx(2.025));
    }

    SECTION("Custom config changes calculateHabitatTypeConst output") {
        Habitat habitat(HabitatType::BlindChannel);
        CHECK(habitat.structure() == HabitatStructure::Complex);
        CHECK(habitat.largeType() == LargeHabitatType::Delta);

        ModelConfigMap customConfig;
        customConfig.set(ModelParamKey::HabitatMortConstComplex, 1.0f);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 50.0, customConfig);
        // Z (0.6) * mort.const (1.0) * (1 + active_pred_sum (0.64)) = 0.6 * 1.64 = 0.984
        REQUIRE(habitatTypeConst == Approx(0.984));
    }

    SECTION("No active predators outside fork length bounds") {
        Habitat habitat(HabitatType::Distributary);
        CHECK(habitat.structure() == HabitatStructure::Neutral);
        CHECK(habitat.largeType() == LargeHabitatType::Delta);

        double habitatTypeConst = PredationMortality::calculateHabitatTypeConst(habitat, 1000, 20.0, config);
        // Z (0.6) * mort.const (1.0) * (1 + active_pred_sum (0.0)) = 0.6 * 1.0 = 0.6
        REQUIRE(habitatTypeConst == Approx(0.6));
    }
}
