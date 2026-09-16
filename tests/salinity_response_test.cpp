#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include "salinity_response.h"

TEST_CASE("SalinityResponse::calculateSalinityBias response behavior", "[salinity][response]") {
    const float L_50 = 65.0f;
    const float K_STEEP = 0.1f;
    const float BIAS_WEIGHT = 0.2f;
    const float SALINITY_MAX = 32.0f;

    SECTION("Fish smaller than L_50 are attracted to low salinity (< SALINITY_MAX/2) and avoid high salinity (> SALINITY_MAX/2)") {
        float smallFish = 35.0f;

        // Attracted to low salinity values (bias > 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 5.0f, L_50, K_STEEP, BIAS_WEIGHT) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 10.0f, L_50, K_STEEP, BIAS_WEIGHT) > 1.0f);

        // Avoids high salinity values (bias < 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 20.0f, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 25.0f, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);

        // Preference decreases as salinity increases
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(smallFish, 10.0f, L_50, K_STEEP, BIAS_WEIGHT));
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 10.0f, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(smallFish, 20.0f, L_50, K_STEEP, BIAS_WEIGHT));
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 20.0f, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT));
    }

    SECTION("Fish larger than L_50 are attracted to high salinity (> SALINITY_MAX/2) and avoid low salinity (< SALINITY_MAX/2)") {
        float largeFish = 95.0f;

        // Avoids low salinity values (bias < 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 5.0f, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 10.0f, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);

        // Attracted to high salinity values (bias > 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 20.0f, L_50, K_STEEP, BIAS_WEIGHT) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 25.0f, L_50, K_STEEP, BIAS_WEIGHT) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT) > 1.0f);

        // Preference increases as salinity increases
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(largeFish, 20.0f, L_50, K_STEEP, BIAS_WEIGHT));
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 20.0f, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(largeFish, 10.0f, L_50, K_STEEP, BIAS_WEIGHT));
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 10.0f, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(largeFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT));
    }

    SECTION("Fish length equal to L_50 exhibits neutral bias at boundary salinities") {
        float neutralFish = L_50;

        REQUIRE(SalinityResponse::calculateSalinityBias(neutralFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT) == Catch::Approx(1.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(neutralFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT) == Catch::Approx(1.0f));
    }

    SECTION("Salinity values exceeding SALINITY_MAX are capped") {
        float smallFish = 35.0f;
        float largeFish = 95.0f;

        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX + 10.0f, L_50, K_STEEP, BIAS_WEIGHT) ==
                Catch::Approx(SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT)));
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX + 10.0f, L_50, K_STEEP, BIAS_WEIGHT) ==
                Catch::Approx(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT)));
    }

    SECTION("Relative preference comparison across fish sizes") {
        float smallFish = 35.0f;
        float largeFish = 95.0f;

        // Small fish prefers fresh water more than large fish does
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(largeFish, 0.0f, L_50, K_STEEP, BIAS_WEIGHT));

        // Large fish prefers salt water more than small fish does
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT) >
                SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX, L_50, K_STEEP, BIAS_WEIGHT));
    }

    SECTION("Fish larger than L_50 in sub-midpoint salinity has bias < 1.0") {
        float forkLength = 71.1116f;
        float nodeSalinity = 13.4691f;

        REQUIRE(SalinityResponse::calculateSalinityBias(forkLength, nodeSalinity, L_50, K_STEEP, BIAS_WEIGHT) < 1.0f);
    }

    SECTION("Custom configuration parameters modify bias calculation accordingly") {
        float fish = 65.0f;
        float nodeSalinity = 0.0f; // fresh water

        // With default attractionLength (65.0), 65mm fish is neutral (bias == 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(fish, nodeSalinity, 65.0f, 0.1f, 0.2f) == Catch::Approx(1.0f));

        // If attractionLength is increased to 80.0, 65mm fish prefers fresh water (bias > 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(fish, nodeSalinity, 80.0f, 0.1f, 0.2f) > 1.0f);

        // If attractionLength is decreased to 50.0, 65mm fish avoids fresh water (bias < 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(fish, nodeSalinity, 50.0f, 0.1f, 0.2f) < 1.0f);

        // If biasWeight is 0, bias is exactly 1.0 regardless of fish size or salinity
        REQUIRE(SalinityResponse::calculateSalinityBias(35.0f, nodeSalinity, 65.0f, 0.1f, 0.0f) == Catch::Approx(1.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(95.0f, nodeSalinity, 65.0f, 0.1f, 0.0f) == Catch::Approx(1.0f));

        // Steeper sigmoid increases preference magnitude for off-center fish
        float biasLowSteep = SalinityResponse::calculateSalinityBias(70.0f, 32.0f, 65.0f, 0.01f, 0.2f);
        float biasHighSteep = SalinityResponse::calculateSalinityBias(70.0f, 32.0f, 65.0f, 0.5f, 0.2f);
        REQUIRE(biasHighSteep > biasLowSteep);
    }
}
