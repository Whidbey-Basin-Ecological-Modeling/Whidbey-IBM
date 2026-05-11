//
// Created by Troy Frever on 4/7/26.
//

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <numeric>
#include <vector>

#include "model.h"
#include "test_utilities.h"
#include "util.h"
#include "catch2/catch_approx.hpp"

class ModelRecruitmentFixture {
public:
    ModelRecruitmentFixture()
        : hydroModel(std::make_unique<MockHydroModel>()),
          model(hydroModel.get()) {
        model.initialPopulations.emplace_back();
        model.initialPopulations[0].recDayPlan.resize(24, 0UL);
        model.time = 0;
        model.recTimeIntercept = 0;
    }

protected:
    std::unique_ptr<MockHydroModel> hydroModel;
    Model model;

    void setRecCounts(const std::vector<int> &counts) {
        model.initialPopulations[0].recCounts = counts;
    }

    void setTime(long t) {
        model.time = t;
    }

    void setIntercept(int intercept) {
        model.recTimeIntercept = intercept;
    }

    void seedPlan(const std::vector<size_t> &plan) {
        model.initialPopulations[0].recDayPlan = plan;
    }
};

namespace {
    size_t sumPlan(const std::vector<size_t> &plan) {
        return std::accumulate(plan.begin(), plan.end(), static_cast<size_t>(0));
    }

    std::vector<size_t> expectedPlanForSeed(int seed, size_t recruitCount) {
        GlobalRand::reseed(seed);

        std::vector<size_t> expected(24, 0UL);
        for (size_t i = 0; i < recruitCount; ++i) {
            ++expected[GlobalRand::int_rand(0, 23)];
        }
        return expected;
    }

    float expectedForkLengthForSeed(int seed, unsigned bucketIndex) {
        GlobalRand::reseed(seed);
        return 35.0f + 5.0f * static_cast<float>(bucketIndex) + unit_rand() * 5.0f;
    }

    size_t expectedRecruitPointForSeed(int seed, size_t pointCount) {
        GlobalRand::reseed(seed);

        // recruitSingle() calls unit_rand() once (for fork length) before selecting the recruit point, so we
        // simulate that here. this test is obviously brittle for this reason.
        // sample() is overridden in this test, so it does not consume RNG.
        (void) unit_rand();

        return static_cast<size_t>(GlobalRand::int_rand(0, static_cast<int>(pointCount) - 1));
    }
}

TEST_CASE_METHOD(ModelRecruitmentFixture, "Model::planRecruitment", "[model][recruitment]") {
    SECTION("clears any existing daily plan before generating a new one") {
        const auto oldRecCount = 9UL;
        const auto expectedRecCount = 3UL;

        model.initialPopulations[0].recDayPlan.assign(24, oldRecCount);
        setRecCounts({expectedRecCount});
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(model.initialPopulations[0].recDayPlan.size() == 24);
        REQUIRE(sumPlan(model.initialPopulations[0].recDayPlan) == expectedRecCount);
        for (size_t slot: model.initialPopulations[0].recDayPlan) {
            REQUIRE(slot <= expectedRecCount);
        }
    }

    SECTION("uses the recruit-count day indexed by time and intercept") {
        setRecCounts({2, 5, 7});
        setTime(24);
        setIntercept(24);
        const auto expectedDailyTotal = static_cast<size_t>(model.initialPopulations[0].recCounts[2]);
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(sumPlan(model.initialPopulations[0].recDayPlan) == expectedDailyTotal);
    }

    SECTION("produces the same plan for a fixed seed") {
        setRecCounts({6});
        const int seed = 42;
        const auto expected = expectedPlanForSeed(seed, 6);
        GlobalRand::reseed(seed);

        model.planRecruitment();

        REQUIRE(model.initialPopulations[0].recDayPlan == expected);
    }

    SECTION("handles a zero recruit count") {
        model.initialPopulations[0].recDayPlan.assign(24, 4UL);
        setRecCounts({0});
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(sumPlan(model.initialPopulations[0].recDayPlan) == 0UL);
        for (size_t slot: model.initialPopulations[0].recDayPlan) {
            REQUIRE(slot == 0UL);
        }
    }

    SECTION("supports a larger recruit count without exceeding the 24 hourly slots") {
        setRecCounts({48});
        GlobalRand::reseed(11);

        model.planRecruitment();

        REQUIRE(model.initialPopulations[0].recDayPlan.size() == 24);
        REQUIRE(sumPlan(model.initialPopulations[0].recDayPlan) == 48UL);
        for (size_t slot: model.initialPopulations[0].recDayPlan) {
            REQUIRE(slot <= 48UL);
        }
    }

    SECTION("uses the shifted recruit day when the intercept changes the day index") {
        setRecCounts({1, 9, 4});
        setTime(23);
        setIntercept(1);
        const auto expectedDailyTotal = static_cast<size_t>(model.initialPopulations[0].recCounts[1]);
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(sumPlan(model.initialPopulations[0].recDayPlan) == expectedDailyTotal);
    }

    SECTION("sets recDayPlan for every initial population") {
        model.initialPopulations.emplace_back();

        model.initialPopulations[0].recCounts = {2};
        model.initialPopulations[1].recCounts = {5};

        model.initialPopulations[0].recDayPlan.assign(24, 111UL);
        model.initialPopulations[1].recDayPlan.assign(24, 222UL);

        const int seed = 42;
        GlobalRand::reseed(seed);

        std::vector<size_t> expected0(24, 0UL);
        for (size_t i = 0; i < 2UL; ++i) {
            ++expected0[GlobalRand::int_rand(0, 23)];
        }

        std::vector<size_t> expected1(24, 0UL);
        for (size_t i = 0; i < 5UL; ++i) {
            ++expected1[GlobalRand::int_rand(0, 23)];
        }

        GlobalRand::reseed(seed);
        model.planRecruitment();

        CHECK(model.initialPopulations.size() == 2UL);
        REQUIRE(model.initialPopulations[0].recDayPlan == expected0);
        REQUIRE(model.initialPopulations[1].recDayPlan == expected1);
    }
}

TEST_CASE_METHOD(ModelRecruitmentFixture, "Model::recruitSingle", "[model][recruitment]") {
    SECTION("adds one fish, increments next ID, uses the seeded recruit point, and tags the recruit") {
        auto pointA = createMapNode(10.0f, 20.0f);
        auto pointB = createMapNode(30.0f, 40.0f);
        pointA->id = 101;
        pointB->id = 202;

        model.initialPopulations[0].recPoints = {pointA.get(), pointB.get()};
        model.initialPopulations[0].recSizeDists = {
            std::vector<float>{0.1f, 0.2f, 0.7f}
        };
        model.time = 17;
        model.recTimeIntercept = 0;
        model.nextFishID = 0UL;
        model.individuals.clear();
        model.livingIndividuals.clear();

        constexpr int seed = 42;
        constexpr unsigned bucketIndex = 2U;
        const size_t expectedPointIndex = expectedRecruitPointForSeed(seed, model.initialPopulations[0].recPoints.size());
        const float expectedForkLength = expectedForkLengthForSeed(seed, bucketIndex);

        GlobalRand::reseed(seed);
        SampleOverrideHelper sampleOverride([](const float *, unsigned) -> unsigned {
            return bucketIndex;
        });

        model.recruitSingle(model.initialPopulations[0]);

        REQUIRE(model.individuals.size() == 1UL);
        REQUIRE(model.livingIndividuals.size() == 1UL);
        REQUIRE(model.livingIndividuals.front() == 0UL);
        REQUIRE(model.nextFishID == 1UL);

        const Fish &fish = model.individuals.front();
        REQUIRE(fish.id == 0UL);
        REQUIRE(fish.spawnTime == model.time);
        REQUIRE(fish.location == model.initialPopulations[0].recPoints[expectedPointIndex]);
        REQUIRE(fish.taggedTime == model.time);
        REQUIRE(fish.locationHistory != nullptr);
        REQUIRE(fish.growthHistory != nullptr);
        REQUIRE(fish.pmaxHistory != nullptr);
        REQUIRE(fish.mortalityHistory != nullptr);
        REQUIRE(fish.tempHistory != nullptr);
        REQUIRE(fish.depthHistory != nullptr);
        REQUIRE(fish.flowSpeedHistory_old != nullptr);
        REQUIRE(fish.flowVelocityHistory != nullptr);
        REQUIRE(fish.locationHistory->size() == 1UL);
        REQUIRE((*fish.locationHistory)[0] == fish.location->id);
        REQUIRE(fish.forkLength == Catch::Approx(expectedForkLength).margin(0.0001f));
        REQUIRE(fish.forkLength >= 45.0f);
        REQUIRE(fish.forkLength < 50.0f);
    }

    SECTION("uses the requested initial population when recruiting a single fish") {
        model.initialPopulations.emplace_back();

        auto firstPoint = createMapNode(10.0f, 10.0f);
        auto firstPointB = createMapNode(20.0f, 20.0f);
        auto secondPoint = createMapNode(30.0f, 30.0f);

        firstPoint->id = 101;
        firstPointB->id = 202;
        secondPoint->id = 303;

        model.initialPopulations[0].recPoints = {firstPoint.get(), firstPointB.get()};
        model.initialPopulations[0].recSizeDists = {
            std::vector<float>{1.0f, 0.0f, 0.0f}
        };

        model.initialPopulations[1].recPoints = {secondPoint.get()};
        model.initialPopulations[1].recSizeDists = {
            std::vector<float>{0.0f, 0.0f, 1.0f}
        };

        model.time = 0L;
        model.recTimeIntercept = 0;
        model.nextFishID = 0UL;
        model.individuals.clear();
        model.livingIndividuals.clear();

        constexpr int seed = 42;
        GlobalRand::reseed(seed);
        SampleOverrideHelper sampleOverride([](const float *, unsigned) -> unsigned {
            return 2U;
        });

        model.recruitSingle(model.initialPopulations[1]);

        REQUIRE(model.individuals.size() == 1UL);
        REQUIRE(model.livingIndividuals.size() == 1UL);
        REQUIRE(model.nextFishID == 1UL);

        const Fish &fish = model.individuals.front();
        REQUIRE(fish.location == secondPoint.get());
        REQUIRE(fish.forkLength >= 45.0f);
        REQUIRE(fish.forkLength < 50.0f);
    }

    SECTION("clamps to the last size bucket when the recruit week exceeds available distributions") {
        auto point = createMapNode(0.0f, 0.0f);
        point->id = 7;

        model.initialPopulations[0].recPoints = {point.get()};

        // Create 2 weekly distributions with distinct patterns
        // Week 0: heavily weighted toward bucket 0 (35-40mm)
        // Week 1 (last): heavily weighted toward bucket 2 (45-50mm)
        model.initialPopulations[0].recSizeDists = {
            std::vector<float>{10.0f, 0.0f, 0.0f},  // Week 0: bucket 0 dominant
            std::vector<float>{0.0f, 0.0f, 10.0f},  // Week 1: bucket 2 dominant
        };

        // Set time to week 3 (exceeds the 2 available weeks)
        model.time = 24L * 7L * 3L;  // 3 weeks = 504 hours
        model.recTimeIntercept = 0;

        // Recruit multiple fish to verify statistical pattern
        constexpr int seed = 42;
        GlobalRand::reseed(seed);

        constexpr int numRecruits = 100;
        int inLastBucketRange = 0;  // Count fish in 45-50mm range

        for (int i = 0; i < numRecruits; ++i) {
            model.recruitSingle(model.initialPopulations[0]);
            const Fish& fish = model.individuals.back();
            if (fish.forkLength >= 45.0f && fish.forkLength < 50.0f) {
                ++inLastBucketRange;
            }
        }

        const Fish& fish = model.individuals.front();
        REQUIRE(fish.forkLength >= 45.0f);
        REQUIRE(fish.forkLength < 50.0f);

        // If the last week's distribution is used, nearly all fish should be
        // in the 45-50mm range (bucket 2). If week 0 were used instead,
        // nearly all would be in 35-40mm range.
        CHECK(model.individuals.size() == numRecruits);
        REQUIRE(inLastBucketRange > numRecruits * 0.9f);  // >90% should be in bucket 2 range
    }

    SECTION("does not tag recruits whose ID is not a multiple of 2500") {
        auto point = createMapNode(0.0f, 0.0f);
        point->id = 7;
        model.initialPopulations[0].recPoints = {point.get()};
        model.initialPopulations[0].recSizeDists = {
            std::vector<float>{1.0f}
        };

        model.time = 0L;
        model.nextFishID = 1UL;

        model.recruitSingle(model.initialPopulations[0]);

        REQUIRE(model.individuals.size() == 1UL);
        REQUIRE(model.individuals.front().taggedTime == -1L);
        REQUIRE(model.individuals.front().locationHistory == nullptr);
    }
}

TEST_CASE_METHOD(ModelRecruitmentFixture, "Model::recruit", "[model][recruitment]") {
    SECTION("recruits the correct total number across all populations") {
        // Set up two populations with different recruitment plans
        model.initialPopulations.emplace_back();
        model.initialPopulations[1].recDayPlan.resize(24, 0UL);

        auto point0 = createMapNode(10.0f, 10.0f);
        auto point1 = createMapNode(20.0f, 20.0f);
        point0->id = 101;
        point1->id = 202;

        model.initialPopulations[0].recPoints = {point0.get()};
        model.initialPopulations[0].recSizeDists = {std::vector<float>{1.0f}};
        model.initialPopulations[0].recDayPlan[0] = 3;  // 3 recruits from population 0

        model.initialPopulations[1].recPoints = {point1.get()};
        model.initialPopulations[1].recSizeDists = {std::vector<float>{1.0f}};
        model.initialPopulations[1].recDayPlan[0] = 2;  // 2 recruits from population 1

        model.time = 0;
        model.nextFishID = 0UL;
        model.individuals.clear();
        model.livingIndividuals.clear();

        model.recruit();

        REQUIRE(model.individuals.size() == 5UL);
        REQUIRE(model.livingIndividuals.size() == 5UL);
    }

    SECTION("uses the correct timestep index into recDayPlan for all populations") {
        // Set up two populations with data in multiple timesteps
        model.initialPopulations.emplace_back();
        model.initialPopulations[1].recDayPlan.resize(24, 0UL);

        auto point0 = createMapNode(10.0f, 10.0f);
        auto point1 = createMapNode(20.0f, 20.0f);
        point0->id = 101;
        point1->id = 202;

        model.initialPopulations[0].recPoints = {point0.get()};
        model.initialPopulations[0].recSizeDists = {std::vector<float>{1.0f}};
        // Populate multiple timesteps: timestep 7 has the recruits we expect
        model.initialPopulations[0].recDayPlan[0] = 10;
        model.initialPopulations[0].recDayPlan[7] = 3;
        model.initialPopulations[0].recDayPlan[15] = 5;

        model.initialPopulations[1].recPoints = {point1.get()};
        model.initialPopulations[1].recSizeDists = {std::vector<float>{1.0f}};
        model.initialPopulations[1].recDayPlan[0] = 8;
        model.initialPopulations[1].recDayPlan[7] = 2;
        model.initialPopulations[1].recDayPlan[15] = 4;

        // Set time to timestep 7 (mod 24)
        model.time = 7;
        model.nextFishID = 0UL;
        model.individuals.clear();
        model.livingIndividuals.clear();

        model.recruit();

        // Should recruit only from timestep 7: 3 from population 0 and 2 from population 1
        REQUIRE(model.individuals.size() == 5UL);
        REQUIRE(model.livingIndividuals.size() == 5UL);
    }
}
