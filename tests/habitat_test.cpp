#include <catch2/catch_test_macros.hpp>
#include <stdexcept>
#include "habitat.h"

TEST_CASE("Habitat struct constructors and equality operators", "[habitat]") {
    SECTION("Default constructor initializes to Distributary") {
        Habitat h;
        REQUIRE(h.fine == HabitatType::Distributary);
        REQUIRE(h == HabitatType::Distributary);
        REQUIRE(h == Habitat(HabitatType::Distributary));
    }

    SECTION("Explicit constructor initializes with specified HabitatType") {
        Habitat h(HabitatType::Nearshore);
        REQUIRE(h.fine == HabitatType::Nearshore);
        REQUIRE(h == HabitatType::Nearshore);
        REQUIRE(h != HabitatType::Distributary);
        REQUIRE(h == Habitat(HabitatType::Nearshore));
        REQUIRE(h != Habitat(HabitatType::Distributary));
    }
}

TEST_CASE("Habitat helper methods", "[habitat]") {
    SECTION("isDistributary") {
        REQUIRE(Habitat(HabitatType::Distributary).isDistributary() == true);
        REQUIRE(Habitat(HabitatType::DistributaryEdge).isDistributary(true) == true);
        REQUIRE(Habitat(HabitatType::DistributaryEdge).isDistributary(false) == false);
        REQUIRE(Habitat(HabitatType::Nearshore).isDistributary() == false);
    }

    SECTION("isHarbor") {
        REQUIRE(Habitat(HabitatType::Harbor).isHarbor() == true);
        REQUIRE(Habitat(HabitatType::Distributary).isHarbor() == false);
    }

    SECTION("isNearshore") {
        REQUIRE(Habitat(HabitatType::Nearshore).isNearshore() == true);
        REQUIRE(Habitat(HabitatType::OpenWater).isNearshore() == false);
    }

    SECTION("isBlindChannel") {
        REQUIRE(Habitat(HabitatType::BlindChannel).isBlindChannel() == true);
        REQUIRE(Habitat(HabitatType::Distributary).isBlindChannel() == false);
    }

    SECTION("isImpoundment") {
        REQUIRE(Habitat(HabitatType::Impoundment).isImpoundment() == true);
        REQUIRE(Habitat(HabitatType::BlindChannel).isImpoundment() == false);
    }

    SECTION("Composite helpers") {
        REQUIRE(Habitat(HabitatType::Distributary).isDistributaryOrHarbor() == true);
        REQUIRE(Habitat(HabitatType::Harbor).isDistributaryOrHarbor() == true);
        REQUIRE(Habitat(HabitatType::Nearshore).isDistributaryOrHarbor() == false);

        REQUIRE(Habitat(HabitatType::Distributary).isDistributaryOrNearshore() == true);
        REQUIRE(Habitat(HabitatType::DistributaryEdge).isDistributaryOrNearshore() == true);
        REQUIRE(Habitat(HabitatType::Nearshore).isDistributaryOrNearshore() == true);
        REQUIRE(Habitat(HabitatType::Harbor).isDistributaryOrNearshore() == false);

        REQUIRE(Habitat(HabitatType::Distributary).isDistributaryWithoutEdgeOrIsNearshore() == true);
        REQUIRE(Habitat(HabitatType::DistributaryEdge).isDistributaryWithoutEdgeOrIsNearshore() == false);
        REQUIRE(Habitat(HabitatType::Nearshore).isDistributaryWithoutEdgeOrIsNearshore() == true);
    }

    SECTION("getMortalityConst") {
        float multiplier = 2.5f;
        REQUIRE(Habitat(HabitatType::Distributary).getMortalityConst(multiplier) == multiplier);
        REQUIRE(Habitat(HabitatType::Nearshore).getMortalityConst(multiplier) == multiplier);
        REQUIRE(Habitat(HabitatType::DistributaryEdge).getMortalityConst(multiplier) == 1.0f);
        REQUIRE(Habitat(HabitatType::Harbor).getMortalityConst(multiplier) == 1.0f);
        REQUIRE(Habitat(HabitatType::OpenWater).getMortalityConst(multiplier) == 1.0f);
    }
}

TEST_CASE("Habitat::toString conversions", "[habitat]") {
    REQUIRE(Habitat::toString(HabitatType::BlindChannel) == "Blind channel");
    REQUIRE(Habitat::toString(HabitatType::Impoundment) == "Impoundment");
    REQUIRE(Habitat::toString(HabitatType::LowTideTerrace) == "Low tide terrace");
    REQUIRE(Habitat::toString(HabitatType::Distributary) == "Distributary");
    REQUIRE(Habitat::toString(HabitatType::DistributaryEdge) == "Distributary edge");
    REQUIRE(Habitat::toString(HabitatType::Harbor) == "Boat harbor");
    REQUIRE(Habitat::toString(HabitatType::Nearshore) == "Nearshore");
    REQUIRE(Habitat::toString(HabitatType::OpenWater) == "Open water");
    REQUIRE(Habitat::toString(HabitatType::IntertidalMudFlat) == "Intertidal mud flat");
    REQUIRE(Habitat::toString(HabitatType::Rock) == "Rock");
    REQUIRE(Habitat::toString(HabitatType::SubtidalFlat) == "Sub-tidal flat");
    REQUIRE(Habitat::toString(HabitatType::Exit) == "Exit");
    REQUIRE(Habitat::toString(HabitatType::HabitatTypeCountSentinel) == "Unknown");

    // Member toString() method
    REQUIRE(Habitat(HabitatType::BlindChannel).toString() == "Blind channel");
    REQUIRE(Habitat(HabitatType::Exit).toString() == "Exit");
}

TEST_CASE("Habitat string parsing and aliases", "[habitat]") {
    SECTION("Standard names and case insensitivity") {
        REQUIRE(Habitat::fromString("blind channel") == HabitatType::BlindChannel);
        REQUIRE(Habitat::fromString("Blind Channel") == HabitatType::BlindChannel);
        REQUIRE(Habitat::fromString("BLIND CHANNEL") == HabitatType::BlindChannel);
        REQUIRE(Habitat::fromString("impoundment") == HabitatType::Impoundment);
        REQUIRE(Habitat::fromString("low tide terrace") == HabitatType::LowTideTerrace);
        REQUIRE(Habitat::fromString("distributary") == HabitatType::Distributary);
        REQUIRE(Habitat::fromString("distributary edge") == HabitatType::DistributaryEdge);
        REQUIRE(Habitat::fromString("nearshore") == HabitatType::Nearshore);
        REQUIRE(Habitat::fromString("open water") == HabitatType::OpenWater);
        REQUIRE(Habitat::fromString("rock") == HabitatType::Rock);
        REQUIRE(Habitat::fromString("exit") == HabitatType::Exit);
    }

    SECTION("Aliases and alternate spellings") {
        REQUIRE(Habitat::fromString("distributary channel") == HabitatType::Distributary);
        REQUIRE(Habitat::fromString("boat harbor") == HabitatType::Harbor);
        REQUIRE(Habitat::fromString("harbor") == HabitatType::Harbor);
        REQUIRE(Habitat::fromString("shoreline") == HabitatType::Nearshore);
        REQUIRE(Habitat::fromString("intertidal mud flat") == HabitatType::IntertidalMudFlat);
        REQUIRE(Habitat::fromString("intertidal mudflat") == HabitatType::IntertidalMudFlat);
        REQUIRE(Habitat::fromString("sub-tidal flat") == HabitatType::SubtidalFlat);
        REQUIRE(Habitat::fromString("subtidal flat") == HabitatType::SubtidalFlat);
    }

    SECTION("Whitespace and carriage return trimming") {
        REQUIRE(Habitat::fromString("  distributary\r\n") == HabitatType::Distributary);
        REQUIRE(Habitat::fromString("\tboat harbor\n") == HabitatType::Harbor);
        REQUIRE(Habitat::fromString("  exit  ") == HabitatType::Exit);
    }

    SECTION("Round-trip toString -> fromString for all valid types") {
        HabitatType allTypes[] = {
            HabitatType::BlindChannel,
            HabitatType::Impoundment,
            HabitatType::LowTideTerrace,
            HabitatType::Distributary,
            HabitatType::DistributaryEdge,
            HabitatType::Harbor,
            HabitatType::Nearshore,
            HabitatType::IntertidalMudFlat,
            HabitatType::OpenWater,
            HabitatType::Rock,
            HabitatType::SubtidalFlat,
            HabitatType::Exit
        };

        for (HabitatType type : allTypes) {
            std::string str = Habitat::toString(type);
            REQUIRE(Habitat::fromString(str) == type);
        }
    }

    SECTION("tryParse success and failure") {
        HabitatType outType;
        REQUIRE(Habitat::tryParse("distributary", outType) == true);
        REQUIRE(outType == HabitatType::Distributary);

        Habitat outHabitat;
        REQUIRE(Habitat::tryParse("boat harbor", outHabitat) == true);
        REQUIRE(outHabitat.fine == HabitatType::Harbor);

        REQUIRE(Habitat::tryParse("unknown_fake_habitat", outType) == false);
        REQUIRE(Habitat::tryParse("", outType) == false);
    }

    SECTION("fromString throws on invalid input") {
        REQUIRE_THROWS_AS(Habitat::fromString("nonexistent"), std::invalid_argument);
        REQUIRE_THROWS_AS(Habitat::fromString(""), std::invalid_argument);
    }
}
