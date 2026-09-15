#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include "salinity_response.h"

TEST_CASE("SalinityResponse::calculateSalinityBias response behavior", "[salinity][response]") {
    const float L_50 = 65.0f;
    const float SALINITY_MAX = 32.0f;

    SECTION("Fish smaller than L_50 are attracted to low salinity (< SALINITY_MAX/2) and avoid high salinity (> SALINITY_MAX/2)") {
        float smallFish = 35.0f;

        // Attracted to low salinity values (bias > 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 0.0f) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 5.0f) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 10.0f) > 1.0f);

        // Avoids high salinity values (bias < 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 20.0f) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 25.0f) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX) < 1.0f);

        // Preference decreases as salinity increases
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 0.0f) >
                SalinityResponse::calculateSalinityBias(smallFish, 10.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 10.0f) >
                SalinityResponse::calculateSalinityBias(smallFish, 20.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 20.0f) >
                SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX));
    }

    SECTION("Fish larger than L_50 are attracted to high salinity (> SALINITY_MAX/2) and avoid low salinity (< SALINITY_MAX/2)") {
        float largeFish = 95.0f;

        // Avoids low salinity values (bias < 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 0.0f) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 5.0f) < 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 10.0f) < 1.0f);

        // Attracted to high salinity values (bias > 1.0)
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 20.0f) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 25.0f) > 1.0f);
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX) > 1.0f);

        // Preference increases as salinity increases
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX) >
                SalinityResponse::calculateSalinityBias(largeFish, 20.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 20.0f) >
                SalinityResponse::calculateSalinityBias(largeFish, 10.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, 10.0f) >
                SalinityResponse::calculateSalinityBias(largeFish, 0.0f));
    }

    SECTION("Fish length equal to L_50 exhibits neutral bias at boundary salinities") {
        float neutralFish = L_50;

        REQUIRE(SalinityResponse::calculateSalinityBias(neutralFish, 0.0f) == Catch::Approx(1.0f));
        REQUIRE(SalinityResponse::calculateSalinityBias(neutralFish, SALINITY_MAX) == Catch::Approx(1.0f));
    }

    SECTION("Salinity values exceeding SALINITY_MAX are capped") {
        float smallFish = 35.0f;
        float largeFish = 95.0f;

        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX + 10.0f) ==
                Catch::Approx(SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX)));
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX + 10.0f) ==
                Catch::Approx(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX)));
    }

    SECTION("Relative preference comparison across fish sizes") {
        float smallFish = 35.0f;
        float largeFish = 95.0f;

        // Small fish prefers fresh water more than large fish does
        REQUIRE(SalinityResponse::calculateSalinityBias(smallFish, 0.0f) >
                SalinityResponse::calculateSalinityBias(largeFish, 0.0f));

        // Large fish prefers salt water more than small fish does
        REQUIRE(SalinityResponse::calculateSalinityBias(largeFish, SALINITY_MAX) >
                SalinityResponse::calculateSalinityBias(smallFish, SALINITY_MAX));
    }
}
