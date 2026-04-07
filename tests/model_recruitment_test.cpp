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

class ModelRecruitmentFixture {
public:
    ModelRecruitmentFixture()
        : hydroModel(std::make_unique<MockHydroModel>()),
          model(hydroModel.get()) {
        model.recDayPlan.resize(24, 0UL);
        model.time = 0;
        model.recTimeIntercept = 0;
    }

protected:
    std::unique_ptr<MockHydroModel> hydroModel;
    Model model;

    void setRecCounts(const std::vector<int> &counts) {
        model.recCounts = counts;
    }

    void setTime(long t) {
        model.time = t;
    }

    void setIntercept(int intercept) {
        model.recTimeIntercept = intercept;
    }

    void seedPlan(const std::vector<size_t> &plan) {
        model.recDayPlan = plan;
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
}

TEST_CASE_METHOD(ModelRecruitmentFixture, "Model::planRecruitment", "[model][recruitment]") {
    SECTION("clears any existing daily plan before generating a new one") {
        model.recDayPlan.assign(24, 9UL);
        setRecCounts({3});
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(model.recDayPlan.size() == 24);
        REQUIRE(sumPlan(model.recDayPlan) == 3UL);
        for (size_t slot: model.recDayPlan) {
            REQUIRE(slot <= 3UL);
        }
    }

    SECTION("uses the recruit-count day indexed by time and intercept") {
        setRecCounts({2, 5, 7});
        setTime(24);
        setIntercept(24);
        const auto expectedDailyTotal = static_cast<size_t>(model.recCounts[2]);
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(sumPlan(model.recDayPlan) == expectedDailyTotal);
    }

    SECTION("produces the same plan for a fixed seed") {
        setRecCounts({6});
        const int seed = 42;
        const auto expected = expectedPlanForSeed(seed, 6);
        GlobalRand::reseed(seed);

        model.planRecruitment();

        REQUIRE(model.recDayPlan == expected);
    }

    SECTION("handles a zero recruit count") {
        model.recDayPlan.assign(24, 4UL);
        setRecCounts({0});
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(sumPlan(model.recDayPlan) == 0UL);
        for (size_t slot: model.recDayPlan) {
            REQUIRE(slot == 0UL);
        }
    }

    SECTION("supports a larger recruit count without exceeding the 24 hourly slots") {
        setRecCounts({48});
        GlobalRand::reseed(11);

        model.planRecruitment();

        REQUIRE(model.recDayPlan.size() == 24);
        REQUIRE(sumPlan(model.recDayPlan) == 48UL);
        for (size_t slot: model.recDayPlan) {
            REQUIRE(slot <= 48UL);
        }
    }

    SECTION("uses the shifted recruit day when the intercept changes the day index") {
        setRecCounts({1, 9, 4});
        setTime(23);
        setIntercept(1);
        const auto expectedDailyTotal = static_cast<size_t>(model.recCounts[1]);
        GlobalRand::reseed(42);

        model.planRecruitment();

        REQUIRE(sumPlan(model.recDayPlan) == expectedDailyTotal);
    }
}
