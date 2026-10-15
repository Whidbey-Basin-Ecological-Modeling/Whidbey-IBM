#include <catch2/catch_test_macros.hpp>
#include <stdexcept>
#include "habitat.h"

TEST_CASE("Habitat class constructors and equality operators", "[habitat]") {
    SECTION("Default constructor initializes to Distributary and Delta and Neutral structure") {
        Habitat h;
        REQUIRE(h.fineType() == HabitatType::Distributary);
        REQUIRE(h.largeType() == LargeHabitatType::Delta);
        REQUIRE(h.structure() == HabitatStructure::Neutral);
        REQUIRE(h == HabitatType::Distributary);
        REQUIRE(h == LargeHabitatType::Delta);
        REQUIRE(h == HabitatStructure::Neutral);
        REQUIRE(h == Habitat(HabitatType::Distributary, LargeHabitatType::Delta));
    }

    SECTION("Explicit single-argument constructor initializes with specified HabitatType, default LargeHabitatType, and default HabitatStructure") {
        Habitat h(HabitatType::Nearshore);
        REQUIRE(h.fineType() == HabitatType::Nearshore);
        REQUIRE(h.largeType() == LargeHabitatType::Intertidal);
        REQUIRE(h.structure() == HabitatStructure::Neutral);
        REQUIRE(h == HabitatType::Nearshore);
        REQUIRE(h == LargeHabitatType::Intertidal);
        REQUIRE(h == HabitatStructure::Neutral);
        REQUIRE(h != HabitatType::Distributary);
        REQUIRE(h != LargeHabitatType::Delta);
        REQUIRE(h == Habitat(HabitatType::Nearshore));
        REQUIRE(h != Habitat(HabitatType::Distributary));
    }

    SECTION("Explicit two-argument constructor initializes fine and large independently and structure according to fine/large") {
        Habitat h(HabitatType::Harbor, LargeHabitatType::Delta);
        REQUIRE(h.fineType() == HabitatType::Harbor);
        REQUIRE(h.largeType() == LargeHabitatType::Delta);
        REQUIRE(h.structure() == HabitatStructure::Simplified);
        REQUIRE(h == HabitatType::Harbor);
        REQUIRE(h == LargeHabitatType::Delta);
        REQUIRE(h == HabitatStructure::Simplified);
        REQUIRE(h != Habitat(HabitatType::Harbor)); // default large for Harbor is Intertidal
        REQUIRE(h == Habitat(HabitatType::Harbor, LargeHabitatType::Delta));
    }
}

TEST_CASE("Habitat fine-to-large default mappings and disambiguations", "[habitat]") {
    SECTION("Delta defaults") {
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::BlindChannel) == LargeHabitatType::Delta);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Impoundment) == LargeHabitatType::Delta);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::LowTideTerrace) == LargeHabitatType::Delta);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Distributary) == LargeHabitatType::Delta);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::DistributaryEdge) == LargeHabitatType::Delta);

        REQUIRE(Habitat(HabitatType::BlindChannel).largeType() == LargeHabitatType::Delta);
        REQUIRE(Habitat(HabitatType::Impoundment).largeType() == LargeHabitatType::Delta);
        REQUIRE(Habitat(HabitatType::LowTideTerrace).largeType() == LargeHabitatType::Delta);
        REQUIRE(Habitat(HabitatType::Distributary).largeType() == LargeHabitatType::Delta);
        REQUIRE(Habitat(HabitatType::DistributaryEdge).largeType() == LargeHabitatType::Delta);
    }

    SECTION("Intertidal defaults (including Harbor and Mudflat disambiguation)") {
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Harbor) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Mudflat) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Nearshore) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::SubtidalFlat) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Rock) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Beach) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Riprap) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Eelgrass) == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Lagoon) == LargeHabitatType::Intertidal);

        REQUIRE(Habitat(HabitatType::Harbor).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Mudflat).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Nearshore).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::SubtidalFlat).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Rock).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Beach).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Riprap).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Eelgrass).largeType() == LargeHabitatType::Intertidal);
        REQUIRE(Habitat(HabitatType::Lagoon).largeType() == LargeHabitatType::Intertidal);
    }

    SECTION("Freshwater defaults") {
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Creek) == LargeHabitatType::Freshwater);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Mainstem) == LargeHabitatType::Freshwater);

        REQUIRE(Habitat(HabitatType::Creek).largeType() == LargeHabitatType::Freshwater);
        REQUIRE(Habitat(HabitatType::Mainstem).largeType() == LargeHabitatType::Freshwater);
    }

    SECTION("Offshore defaults") {
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Kelp) == LargeHabitatType::Offshore);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::OpenWater) == LargeHabitatType::Offshore);
        REQUIRE(Habitat::getDefaultLargeHabitat(HabitatType::Exit) == LargeHabitatType::Offshore);

        REQUIRE(Habitat(HabitatType::Kelp).largeType() == LargeHabitatType::Offshore);
        REQUIRE(Habitat(HabitatType::OpenWater).largeType() == LargeHabitatType::Offshore);
        REQUIRE(Habitat(HabitatType::Exit).largeType() == LargeHabitatType::Offshore);
    }
}

TEST_CASE("Habitat structure default mappings from Section 2.3", "[habitat]") {
    SECTION("Delta structures") {
        REQUIRE(Habitat::getDefaultStructure(HabitatType::BlindChannel, LargeHabitatType::Delta) == HabitatStructure::Complex);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Impoundment, LargeHabitatType::Delta) == HabitatStructure::Complex);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::LowTideTerrace, LargeHabitatType::Delta) == HabitatStructure::Complex);

        REQUIRE(Habitat::getDefaultStructure(HabitatType::Distributary, LargeHabitatType::Delta) == HabitatStructure::Neutral);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::DistributaryEdge, LargeHabitatType::Delta) == HabitatStructure::Neutral);

        REQUIRE(Habitat::getDefaultStructure(HabitatType::Harbor, LargeHabitatType::Delta) == HabitatStructure::Simplified);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Mudflat, LargeHabitatType::Delta) == HabitatStructure::Simplified);
    }

    SECTION("Freshwater structures") {
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Creek, LargeHabitatType::Freshwater) == HabitatStructure::Complex);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Mainstem, LargeHabitatType::Freshwater) == HabitatStructure::Neutral);
    }

    SECTION("Intertidal structures") {
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Eelgrass, LargeHabitatType::Intertidal) == HabitatStructure::Complex);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Lagoon, LargeHabitatType::Intertidal) == HabitatStructure::Complex);

        REQUIRE(Habitat::getDefaultStructure(HabitatType::Beach, LargeHabitatType::Intertidal) == HabitatStructure::Neutral);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Mudflat, LargeHabitatType::Intertidal) == HabitatStructure::Neutral);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Rock, LargeHabitatType::Intertidal) == HabitatStructure::Neutral);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Nearshore, LargeHabitatType::Intertidal) == HabitatStructure::Neutral);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::SubtidalFlat, LargeHabitatType::Intertidal) == HabitatStructure::Neutral);

        REQUIRE(Habitat::getDefaultStructure(HabitatType::Harbor, LargeHabitatType::Intertidal) == HabitatStructure::Simplified);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Riprap, LargeHabitatType::Intertidal) == HabitatStructure::Simplified);
    }

    SECTION("Offshore structures") {
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Kelp, LargeHabitatType::Offshore) == HabitatStructure::Complex);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::OpenWater, LargeHabitatType::Offshore) == HabitatStructure::Neutral);
        REQUIRE(Habitat::getDefaultStructure(HabitatType::Exit, LargeHabitatType::Offshore) == HabitatStructure::Neutral);
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
    REQUIRE(Habitat::toString(HabitatType::Mudflat) == "Mudflat");
    REQUIRE(Habitat::toString(HabitatType::Rock) == "Rock");
    REQUIRE(Habitat::toString(HabitatType::SubtidalFlat) == "Sub-tidal flat");
    REQUIRE(Habitat::toString(HabitatType::Creek) == "Creek");
    REQUIRE(Habitat::toString(HabitatType::Mainstem) == "Mainstem");
    REQUIRE(Habitat::toString(HabitatType::Beach) == "Beach");
    REQUIRE(Habitat::toString(HabitatType::Riprap) == "Riprap");
    REQUIRE(Habitat::toString(HabitatType::Eelgrass) == "Eelgrass");
    REQUIRE(Habitat::toString(HabitatType::Lagoon) == "Lagoon");
    REQUIRE(Habitat::toString(HabitatType::Kelp) == "Kelp");
    REQUIRE(Habitat::toString(HabitatType::Exit) == "Exit");
    REQUIRE(Habitat::toString(HabitatType::HabitatTypeCountSentinel) == "Unknown");

    // Large habitat toString
    REQUIRE(Habitat::toString(LargeHabitatType::Delta) == "Delta");
    REQUIRE(Habitat::toString(LargeHabitatType::Freshwater) == "Freshwater");
    REQUIRE(Habitat::toString(LargeHabitatType::Intertidal) == "Intertidal");
    REQUIRE(Habitat::toString(LargeHabitatType::Offshore) == "Offshore");
    REQUIRE(Habitat::toString(LargeHabitatType::LargeHabitatTypeCountSentinel) == "Unknown");

    // HabitatStructure toString
    REQUIRE(Habitat::toString(HabitatStructure::Simplified) == "Simplified");
    REQUIRE(Habitat::toString(HabitatStructure::Neutral) == "Neutral");
    REQUIRE(Habitat::toString(HabitatStructure::Complex) == "Complex");
    REQUIRE(Habitat::toString(HabitatStructure::HabitatStructureCountSentinel) == "Unknown");

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
        REQUIRE(Habitat::fromString("creek") == HabitatType::Creek);
        REQUIRE(Habitat::fromString("mainstem") == HabitatType::Mainstem);
        REQUIRE(Habitat::fromString("beach") == HabitatType::Beach);
        REQUIRE(Habitat::fromString("riprap") == HabitatType::Riprap);
        REQUIRE(Habitat::fromString("eelgrass") == HabitatType::Eelgrass);
        REQUIRE(Habitat::fromString("lagoon") == HabitatType::Lagoon);
        REQUIRE(Habitat::fromString("kelp") == HabitatType::Kelp);
    }

    SECTION("Large habitat parsing") {
        REQUIRE(Habitat::largeFromString("delta") == LargeHabitatType::Delta);
        REQUIRE(Habitat::largeFromString("Delta") == LargeHabitatType::Delta);
        REQUIRE(Habitat::largeFromString("freshwater") == LargeHabitatType::Freshwater);
        REQUIRE(Habitat::largeFromString("Freshwater") == LargeHabitatType::Freshwater);
        REQUIRE(Habitat::largeFromString("intertidal") == LargeHabitatType::Intertidal);
        REQUIRE(Habitat::largeFromString("offshore") == LargeHabitatType::Offshore);
        REQUIRE_THROWS_AS(Habitat::largeFromString("unknown"), std::invalid_argument);

        LargeHabitatType outLarge;
        REQUIRE(Habitat::tryParse("Delta", outLarge) == true);
        REQUIRE(outLarge == LargeHabitatType::Delta);
        REQUIRE(Habitat::tryParse("invalid", outLarge) == false);
    }

    SECTION("Habitat structure parsing") {
        REQUIRE(Habitat::structureFromString("simplified") == HabitatStructure::Simplified);
        REQUIRE(Habitat::structureFromString("Simplified") == HabitatStructure::Simplified);
        REQUIRE(Habitat::structureFromString("neutral") == HabitatStructure::Neutral);
        REQUIRE(Habitat::structureFromString("Neutral") == HabitatStructure::Neutral);
        REQUIRE(Habitat::structureFromString("complex") == HabitatStructure::Complex);
        REQUIRE(Habitat::structureFromString("Complex") == HabitatStructure::Complex);
        REQUIRE_THROWS_AS(Habitat::structureFromString("unknown"), std::invalid_argument);

        HabitatStructure outStructure;
        REQUIRE(Habitat::tryParse("Complex", outStructure) == true);
        REQUIRE(outStructure == HabitatStructure::Complex);
        REQUIRE(Habitat::tryParse("invalid", outStructure) == false);
    }

    SECTION("Aliases and alternate spellings") {
        REQUIRE(Habitat::fromString("distributary channel") == HabitatType::Distributary);
        REQUIRE(Habitat::fromString("boat harbor") == HabitatType::Harbor);
        REQUIRE(Habitat::fromString("harbor") == HabitatType::Harbor);
        REQUIRE(Habitat::fromString("shoreline") == HabitatType::Nearshore);
        REQUIRE(Habitat::fromString("intertidal mud flat") == HabitatType::Mudflat);
        REQUIRE(Habitat::fromString("intertidal mudflat") == HabitatType::Mudflat);
        REQUIRE(Habitat::fromString("mudflat") == HabitatType::Mudflat);
        REQUIRE(Habitat::fromString("sub-tidal flat") == HabitatType::SubtidalFlat);
        REQUIRE(Habitat::fromString("subtidal flat") == HabitatType::SubtidalFlat);
        REQUIRE(Habitat::fromString("rip-rap") == HabitatType::Riprap);
        REQUIRE(Habitat::fromString("rip rap") == HabitatType::Riprap);
        REQUIRE(Habitat::fromString("eel grass") == HabitatType::Eelgrass);
        REQUIRE(Habitat::fromString("kelp") == HabitatType::Kelp);
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
            HabitatType::Mudflat,
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
        REQUIRE(outHabitat.fineType() == HabitatType::Harbor);

        REQUIRE(Habitat::tryParse("unknown_fake_habitat", outType) == false);
        REQUIRE(Habitat::tryParse("", outType) == false);
    }

    SECTION("fromString throws on invalid input") {
        REQUIRE_THROWS_AS(Habitat::fromString("nonexistent"), std::invalid_argument);
        REQUIRE_THROWS_AS(Habitat::fromString(""), std::invalid_argument);
    }
}
