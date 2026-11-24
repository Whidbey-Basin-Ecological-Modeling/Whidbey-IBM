#include <catch2/catch_test_macros.hpp>
#include <stdexcept>
#include "model.h"
#include "test_utilities.h"

TEST_CASE("Model::countAll ignores dummy node", "[model]") {
    auto hydroModel = std::make_unique<MockHydroModel>();
    Model model(hydroModel.get());

    auto dummyNode = new MapNode(-1, -1.0f, -1.0f);
    dummyNode->area = 0.0f;

    auto regularNode = new MapNode(1, 10.0f, 10.0f);
    regularNode->area = 100.0f;

    model.map.push_back(dummyNode);
    model.map.push_back(regularNode);

    model.individuals.emplace_back(
        0,
        0,
        50.0f,
        dummyNode
    );

    model.countAll(false);

    REQUIRE(regularNode->popDensity == 0.0f);
    REQUIRE(regularNode->residentIds.empty());

    REQUIRE(dummyNode->residentIds.empty());
    REQUIRE(dummyNode->popDensity == 0.0f);
}

TEST_CASE("Model::countAll calculates density for regular nodes while ignoring dummy node", "[model]") {
    auto hydroModel = std::make_unique<MockHydroModel>();
    Model model(hydroModel.get());

    auto dummyNode = new MapNode(-1, -1.0f, -1.0f);
    dummyNode->area = 0.0f;

    float regularNodeArea = 100.0f;
    auto regularNode = new MapNode(1, 10.0f, 10.0f);
    regularNode->area = regularNodeArea;

    model.map.push_back(dummyNode);
    model.map.push_back(regularNode);

    model.individuals.emplace_back(0, 0, 50.0f, dummyNode);

    size_t regularNodeFishCount = 2;
    model.individuals.emplace_back(1, 0, 50.0f, regularNode);
    model.livingIndividuals.push_back(1);
    model.individuals.emplace_back(2, 0, 50.0f, regularNode);
    model.livingIndividuals.push_back(2);

    model.countAll(false);

    float expectedDensity = (float)regularNodeFishCount / regularNodeArea;
    REQUIRE(regularNode->residentIds.size() == regularNodeFishCount);
    REQUIRE(regularNode->popDensity == expectedDensity);

    REQUIRE(dummyNode->residentIds.empty());
    REQUIRE(dummyNode->popDensity == 0.0f);
}

TEST_CASE("Model stops when its clock advances beyond available hydro records", "[model]") {
    auto hydroModel = std::make_unique<MockHydroModel>();
    hydroModel->hydroNodes.emplace_back(0);
    hydroModel->hydroNodes[0].us = {1.0f, 2.0f};
    Model model(hydroModel.get());

    model.masterUpdate();
    REQUIRE(model.time == 1);
    REQUIRE(hydroModel->getTime() == 1);

    REQUIRE_THROWS_AS(model.masterUpdate(), std::runtime_error);
    REQUIRE(model.time == 2);
    REQUIRE(hydroModel->getTime() == 2);

    model.setHistoryTimestep(1);
    REQUIRE(model.time == 1);
    REQUIRE(hydroModel->getTime() == 1);

    REQUIRE_THROWS_AS(model.setHistoryTimestep(2), std::runtime_error);
    REQUIRE(model.time == 2);
    REQUIRE(hydroModel->getTime() == 2);
}
