//
// Created by Troy Frever on 6/30/25.
//

#include <catch2/catch_test_macros.hpp>
#include <memory>
#include "load.h"
#include "map.h"

// Helper function to create a MapNode for testing
auto createTestNode(int id = 0, HabitatType type = HabitatType::Distributary) {
    auto node = std::make_unique<MapNode>(type, 0.0f, 0.0f, 0.0f);
    node->id = id;
    return node;
}

TEST_CASE("checkAndAddEdge functionality", "[edges]") {
    auto source = createTestNode(1);
    auto target = createTestNode(2);

    SECTION("Adding new non-redundant edge") {
        Edge edge(source.get(), target.get(), 1.0f);

        checkAndAddEdge(edge);

        REQUIRE(source->edgesOut.size() == 1);
        REQUIRE(target->edgesIn.size() == 1);
        REQUIRE(source->edgesOut[0].source == source.get());
        REQUIRE(source->edgesOut[0].target == target.get());
        REQUIRE(target->edgesIn[0].source == source.get());
        REQUIRE(target->edgesIn[0].target == target.get());
    }

    SECTION("Redundant edge (reverse direction exists)") {
        // Add edge from target to source first
        Edge reverseEdge(target.get(), source.get(), 1.0f);
        source->edgesIn.push_back(reverseEdge);
        target->edgesOut.push_back(reverseEdge);

        Edge edge(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge);

        REQUIRE(source->edgesOut.empty());
        REQUIRE(target->edgesIn.empty());

        REQUIRE(target->edges.empty());
    }

    SECTION("Duplicate edge (same direction)") {
        Edge edge1(source.get(), target.get(), 1.0f);
        source->edgesOut.push_back(edge1);
        target->edgesIn.push_back(edge1);

        Edge edge2(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge2);

        REQUIRE(source->edgesOut.size() == 1);
        REQUIRE(target->edgesIn.size() == 1);
    }

    SECTION("Multiple non-redundant edges") {
        auto node1 = createTestNode(1);
        auto node2 = createTestNode(2);
        auto node3 = createTestNode(3);

        Edge edge1(node1.get(), node2.get(), 1.0f);
        Edge edge2(node2.get(), node3.get(), 1.0f);

        checkAndAddEdge(edge1);
        checkAndAddEdge(edge2);

        REQUIRE(node1->edgesOut.size() == 1);
        REQUIRE(node2->edgesIn.size() == 1);
        REQUIRE(node2->edgesOut.size() == 1);
        REQUIRE(node3->edgesIn.size() == 1);
    }

    SECTION("Edge with same source and target") {
        Edge selfEdge(source.get(), source.get(), 1.0f);

        checkAndAddEdge(selfEdge);

        REQUIRE(source->edgesIn.empty());
        REQUIRE(source->edgesOut.empty());
    }

    SECTION("Edge exists in source->edgesOut but not target->edgesIn") {
        Edge edge1(source.get(), target.get(), 1.0f);
        source->edgesOut.push_back(edge1);

        CHECK(source->edgesOut.size() == 1);
        CHECK(target->edgesIn.empty());

        Edge edge2(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge2);

        INFO("Edge should get added to edgesIn but not duplicated in EdgesOut");
        CHECK(source->edgesOut.size() == 1);
        REQUIRE(target->edgesIn.size() == 1);
        REQUIRE(source->edgesOut[0].source == source.get());
        REQUIRE(source->edgesOut[0].target == target.get());
        REQUIRE(target->edgesIn[0].source == source.get());
        REQUIRE(target->edgesIn[0].target == target.get());
    }

    SECTION("Edge exists in target->edgesIn but not source->edgesOut") {
        Edge edge1(source.get(), target.get(), 1.0f);
        target->edgesIn.push_back(edge1);

        CHECK(source->edgesOut.empty());
        CHECK(target->edgesIn.size() == 1);

        Edge edge2(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge2);

        INFO("Edge should get added to edgesOut but not duplicated in EdgesIn");
        CHECK(target->edgesIn.size() == 1);
        REQUIRE(source->edgesOut[0].source == source.get());
        REQUIRE(source->edgesOut[0].target == target.get());
        REQUIRE(target->edgesIn[0].source == source.get());
        REQUIRE(target->edgesIn[0].target == target.get());
    }
}

// TODO: delete all tests above this line after edgesIn and edgesOut are removed
TEST_CASE("checkAndAddEdge functionality (unified edges)", "[edges]") {
    auto source = createTestNode(1);
    auto target = createTestNode(2);

    SECTION("Adding new non-redundant edge") {
        Edge edge(source.get(), target.get(), 1.0f);

        checkAndAddEdge(edge);

        REQUIRE(source->edges.size() == 1);
        REQUIRE(target->edges.size() == 1);

        REQUIRE(source->edges[0].source == source.get());
        REQUIRE(source->edges[0].target == target.get());
        REQUIRE(target->edges[0].source == source.get());
        REQUIRE(target->edges[0].target == target.get());

        REQUIRE(source->edges[0].otherEnd(source.get()) == target.get());
        REQUIRE(target->edges[0].otherEnd(target.get()) == source.get());
    }

    SECTION("Redundant edge (reverse direction exists)") {
        // Add reverse first via the public API so the graph is in a valid state
        Edge reverseEdge(target.get(), source.get(), 1.0f);
        checkAndAddEdge(reverseEdge);

        // Now attempt to add the reverse of that (should be rejected)
        Edge edge(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge);

        REQUIRE(source->edges.size() == 1);
        REQUIRE(target->edges.size() == 1);

        REQUIRE(source->edges[0].source == target.get());
        REQUIRE(source->edges[0].target == source.get());
        REQUIRE(target->edges[0].source == target.get());
        REQUIRE(target->edges[0].target == source.get());
    }

    SECTION("Duplicate edge (same direction)") {
        Edge edge1(source.get(), target.get(), 1.0f);
        source->edges.push_back(edge1);
        target->edges.push_back(edge1);

        Edge edge2(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge2);

        REQUIRE(source->edges.size() == 1);
        REQUIRE(target->edges.size() == 1);
    }

    SECTION("Multiple non-redundant edges") {
        auto node1 = createTestNode(1);
        auto node2 = createTestNode(2);
        auto node3 = createTestNode(3);

        Edge edge1(node1.get(), node2.get(), 1.0f);
        Edge edge2(node2.get(), node3.get(), 1.0f);

        checkAndAddEdge(edge1);
        checkAndAddEdge(edge2);

        REQUIRE(node1->edges.size() == 1);
        REQUIRE(node2->edges.size() == 2);
        REQUIRE(node3->edges.size() == 1);

        // Spot-check adjacency via otherEnd
        REQUIRE(node1->edges[0].otherEnd(node1.get()) == node2.get());
        REQUIRE(node3->edges[0].otherEnd(node3.get()) == node2.get());
    }

    SECTION("Edge with same source and target") {
        Edge selfEdge(source.get(), source.get(), 1.0f);

        checkAndAddEdge(selfEdge);

        REQUIRE(source->edges.empty());
    }

    SECTION("Edge exists in source->edges but not target->edges") {
        Edge edge1(source.get(), target.get(), 1.0f);
        source->edges.push_back(edge1);

        CHECK(source->edges.size() == 1);
        CHECK(target->edges.empty());

        Edge edge2(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge2);

        INFO("Edge should get added to target->edges but not duplicated in source->edges");
        CHECK(source->edges.size() == 1);
        REQUIRE(target->edges.size() == 1);

        REQUIRE(source->edges[0].source == source.get());
        REQUIRE(source->edges[0].target == target.get());
        REQUIRE(target->edges[0].source == source.get());
        REQUIRE(target->edges[0].target == target.get());
    }

    SECTION("Edge exists in target->edges but not source->edges") {
        Edge edge1(source.get(), target.get(), 1.0f);
        target->edges.push_back(edge1);

        CHECK(source->edges.empty());
        CHECK(target->edges.size() == 1);

        Edge edge2(source.get(), target.get(), 1.0f);
        checkAndAddEdge(edge2);

        INFO("Edge should get added to source->edges but not duplicated in target->edges");
        CHECK(target->edges.size() == 1);
        REQUIRE(source->edges.size() == 1);

        REQUIRE(source->edges[0].source == source.get());
        REQUIRE(source->edges[0].target == target.get());
        REQUIRE(target->edges[0].source == source.get());
        REQUIRE(target->edges[0].target == target.get());
    }
}