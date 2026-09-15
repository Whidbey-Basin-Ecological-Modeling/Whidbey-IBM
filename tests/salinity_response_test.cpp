#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>
#include "salinity_response.h"

TEST_CASE("SalinityResponse::calculateSalinityBias computes correct exponential weight", "[salinity][response]") {
    SECTION("fork length equal to L_50 (75mm)") {
        float forkLength = 75.0f;
        float salinity = 1.0f;
        float bias = SalinityResponse::calculateSalinityBias(forkLength, salinity);
        // drive = 0.5, BETA = 2.0, salinity = 1.0 -> BETA * drive * salinity = 1.0 -> exp(1.0)
        REQUIRE(bias == Catch::Approx(std::exp(1.0f)));
    }

    SECTION("fork length smaller than L_50") {
        float forkLength = 25.0f;
        float salinity = 2.0f;
        float bias = SalinityResponse::calculateSalinityBias(forkLength, salinity);
        float drive = 1.0f / (1.0f + std::exp(-0.2f * (25.0f - 75.0f)));
        float expected = std::exp(2.0f * drive * 2.0f);
        REQUIRE(bias == Catch::Approx(expected));
    }

    SECTION("zero or negative salinity") {
        float forkLength = 75.0f;
        float salinity = 0.0f;
        float bias = SalinityResponse::calculateSalinityBias(forkLength, salinity);
        REQUIRE(bias == Catch::Approx(1.0f));
    }
}
