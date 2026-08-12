#include <catch2/catch_test_macros.hpp>
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
    model.livingIndividuals.push_back(0);

    model.countAll(false);

    REQUIRE(regularNode->popDensity == 0.0f);
    REQUIRE(regularNode->residentIds.empty());

    REQUIRE(dummyNode->residentIds.size() == 1);
    REQUIRE(dummyNode->popDensity == 0.0f);
}
