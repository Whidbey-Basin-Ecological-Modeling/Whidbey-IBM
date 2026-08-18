#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>

#include "fish_post_movement.h"

TEST_CASE("FishPostMovement::calculateExitProbability returns 0.0 for fork length <= 25mm", "[fish][exit][post_movement]") {
    SECTION("fork length well below minimum threshold (fry)") {
        const float forkLength = 10.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == 0.0f);
    }

    SECTION("fork length just below 25mm threshold") {
        const float forkLength = 24.9f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == 0.0f);
    }

    SECTION("fork length exactly at 25mm boundary") {
        const float forkLength = 25.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == 0.0f);
    }

    SECTION("negative or zero fork length clamped to 0.0") {
        REQUIRE(FishPostMovement::calculateExitProbability(0.0f) == 0.0f);
        REQUIRE(FishPostMovement::calculateExitProbability(-5.0f) == 0.0f);
    }
}

TEST_CASE("FishPostMovement::calculateExitProbability linearly scales between 25mm and 125mm", "[fish][exit][post_movement]") {
    SECTION("fork length at 50mm has 25% exit probability") {
        const float forkLength = 50.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == Catch::Approx(0.25f));
    }

    SECTION("fork length at 75mm has 50% exit probability") {
        const float forkLength = 75.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == Catch::Approx(0.50f));
    }

    SECTION("fork length at 100mm has 75% exit probability") {
        const float forkLength = 100.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == Catch::Approx(0.75f));
    }
}

TEST_CASE("FishPostMovement::calculateExitProbability returns 1.0 for fork length >= 125mm", "[fish][exit][post_movement]") {
    SECTION("fork length exactly at 125mm boundary") {
        const float forkLength = 125.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == 1.0f);
    }

    SECTION("fork length just above 125mm threshold") {
        const float forkLength = 125.1f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == 1.0f);
    }

    SECTION("fork length well above maximum threshold (large smolt)") {
        const float forkLength = 150.0f;
        const float prob = FishPostMovement::calculateExitProbability(forkLength);
        REQUIRE(prob == 1.0f);
    }
}
