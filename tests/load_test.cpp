//
// Created by Troy Frever on 6/30/25.
//

#include <catch2/catch_test_macros.hpp>
#include <memory>
#include "load.h"
#include "map.h"
#include "catch2/catch_approx.hpp"

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

    // SECTION("Redundant edge (reverse direction exists)") {
    //     // Add edge from target to source first
    //     Edge reverseEdge(target.get(), source.get(), 1.0f);
    //     source->edgesIn.push_back(reverseEdge);
    //     target->edgesOut.push_back(reverseEdge);
    //
    //     Edge edge(source.get(), target.get(), 1.0f);
    //     checkAndAddEdge(edge);
    //
    //     REQUIRE(source->edgesOut.empty());
    //     REQUIRE(target->edgesIn.empty());
    //
    //     REQUIRE(target->edges.empty());
    // }

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

TEST_CASE("mergeNodes functionality (unified edges)", "[merge]") {
    auto nodeA = createTestNode(1, HabitatType::Distributary);
    auto nodeB = createTestNode(2, HabitatType::Distributary);
    auto neighbor1 = createTestNode(3, HabitatType::Distributary);
    auto neighbor2 = createTestNode(4, HabitatType::Nearshore);

    nodeA->x = 0.0f;
    nodeA->y = 0.0f;
    nodeA->area = 100.0f;
    nodeA->elev = 1.0f;
    nodeA->pathDist = 50.0f;

    nodeB->x = 10.0f;
    nodeB->y = 0.0f;
    nodeB->area = 200.0f;
    nodeB->elev = 3.0f;
    nodeB->pathDist = 70.0f;

    neighbor1->x = 20.0f;
    neighbor1->y = 0.0f;

    neighbor2->x = 5.0f;
    neighbor2->y = 10.0f;

    SECTION("Basic merge creates new node with combined properties") {
        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);
        REQUIRE(newNode->area == 300.0f);
        REQUIRE(newNode->elev == 2.0f);
        REQUIRE(newNode->pathDist == 60.0f);
        REQUIRE(newNode->x == 5.0f);
        REQUIRE(newNode->y == 0.0f);
        REQUIRE(newNode->id == nodeA->id);
        REQUIRE(newNode->type == HabitatType::Distributary);

        delete newNode;
    }

    SECTION("Merge with single edge from nodeA to neighbor") {
        // Create edge: nodeA <-> neighbor1
        Edge edge1(nodeA.get(), neighbor1.get(), 10.0f);
        nodeA->edges.push_back(edge1);
        neighbor1->edges.push_back(edge1);

        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);
        REQUIRE(newNode->edges.size() == 1);

        // Edge should connect newNode to neighbor1
        const Edge &edgeToNeighbor = newNode->edges[0];
        REQUIRE((edgeToNeighbor.source == newNode || edgeToNeighbor.target == newNode));
        REQUIRE((edgeToNeighbor.source == neighbor1.get() || edgeToNeighbor.target == neighbor1.get()));

        // Check that neighbor has the reciprocal edge
        REQUIRE(neighbor1->edges.size() == 1);
        REQUIRE((neighbor1->edges[0].source == newNode || neighbor1->edges[0].target == newNode));

        float expectedExtraLength = 5.0f;
        REQUIRE(edgeToNeighbor.length == Catch::Approx(10.0f + expectedExtraLength));

        delete newNode;
    }

    SECTION("Merge with edges from both nodeA and nodeB to different neighbors") {
        // Edge: nodeA <-> neighbor1
        Edge edge1(nodeA.get(), neighbor1.get(), 10.0f);
        nodeA->edges.push_back(edge1);
        neighbor1->edges.push_back(edge1);

        // Edge: nodeB <-> neighbor2
        Edge edge2(nodeB.get(), neighbor2.get(), 20.0f);
        nodeB->edges.push_back(edge2);
        neighbor2->edges.push_back(edge2);

        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);
        REQUIRE(newNode->edges.size() == 2);

        // Verify both neighbors are connected to newNode
        bool hasNeighbor1 = false;
        bool hasNeighbor2 = false;
        for (const auto &edge : newNode->edges) {
            MapNode *other = edge.otherEnd(newNode);
            if (other == neighbor1.get()) {
                hasNeighbor1 = true;
            } else if (other == neighbor2.get()) {
                hasNeighbor2 = true;
            }
        }
        REQUIRE(hasNeighbor1);
        REQUIRE(hasNeighbor2);

        // Verify neighbors' reciprocal edges
        REQUIRE(neighbor1->edges.size() == 1);
        REQUIRE(neighbor1->edges[0].otherEnd(neighbor1.get()) == newNode);

        REQUIRE(neighbor2->edges.size() == 1);
        REQUIRE(neighbor2->edges[0].otherEnd(neighbor2.get()) == newNode);

        delete newNode;
    }

    SECTION("Merge excludes edges between the two merged nodes") {
        // Edge between nodeA and nodeB
        Edge edgeAB(nodeA.get(), nodeB.get(), 5.0f);
        nodeA->edges.push_back(edgeAB);
        nodeB->edges.push_back(edgeAB);

        // Edge from nodeA to neighbor1
        Edge edgeAN(nodeA.get(), neighbor1.get(), 10.0f);
        nodeA->edges.push_back(edgeAN);
        neighbor1->edges.push_back(edgeAN);

        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);
        // Should only have one edge (to neighbor1), not to nodeB
        REQUIRE(newNode->edges.size() == 1);

        MapNode *other = newNode->edges[0].otherEnd(newNode);
        REQUIRE(other == neighbor1.get());
        REQUIRE(other != nodeB.get());

        delete newNode;
    }

    SECTION("Merge updates edge lengths for extra distance") {
        // Edge from nodeA to neighbor1
        Edge edge1(nodeA.get(), neighbor1.get(), 10.0f);
        nodeA->edges.push_back(edge1);
        neighbor1->edges.push_back(edge1);

        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);

        const Edge &mergedEdge = newNode->edges[0];
        float expectedExtraLength = 5.0f; // distance between nodeA and nodeB, divided by 2
        float expectedNewLength = 10.0f + expectedExtraLength;
        REQUIRE(mergedEdge.length == Catch::Approx(expectedNewLength));

        delete newNode;
    }

    SECTION("Merge with complex network removes old edges from all neighbors") {
        // Create a small network:
        // neighbor1 <-> nodeA <-> neighbor2
        //               <-> nodeB
        // neighbor3 <-> nodeB
        auto neighbor3 = createTestNode(5);

        Edge edge1(neighbor1.get(), nodeA.get(), 10.0f);
        neighbor1->edges.push_back(edge1);
        nodeA->edges.push_back(edge1);

        Edge edge2(nodeA.get(), neighbor2.get(), 15.0f);
        nodeA->edges.push_back(edge2);
        neighbor2->edges.push_back(edge2);

        Edge edge3(nodeA.get(), nodeB.get(), 5.0f);
        nodeA->edges.push_back(edge3);
        nodeB->edges.push_back(edge3);

        Edge edge4(neighbor3.get(), nodeB.get(), 20.0f);
        neighbor3->edges.push_back(edge4);
        nodeB->edges.push_back(edge4);

        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);

        // newNode should have edges to neighbor1, neighbor2, and neighbor3
        REQUIRE(newNode->edges.size() == 3);

        // Verify no edges point to old nodes
        for (const auto &edge : newNode->edges) {
            MapNode *other = edge.otherEnd(newNode);
            REQUIRE(other != nodeA.get());
            REQUIRE(other != nodeB.get());
        }

        // Verify all neighbors have correct reciprocal edges
        REQUIRE(neighbor1->edges.size() == 1);
        REQUIRE(neighbor1->edges[0].otherEnd(neighbor1.get()) == newNode);

        REQUIRE(neighbor2->edges.size() == 1);
        REQUIRE(neighbor2->edges[0].otherEnd(neighbor2.get()) == newNode);

        REQUIRE(neighbor3->edges.size() == 1);
        REQUIRE(neighbor3->edges[0].otherEnd(neighbor3.get()) == newNode);

        delete newNode;
        neighbor3.reset();
    }

    SECTION("Merge maintains graph consistency - all edges bidirectional") {
        // Create edges from nodeA and nodeB to neighbors
        Edge edge1(nodeA.get(), neighbor1.get(), 10.0f);
        nodeA->edges.push_back(edge1);
        neighbor1->edges.push_back(edge1);

        Edge edge2(nodeB.get(), neighbor2.get(), 20.0f);
        nodeB->edges.push_back(edge2);
        neighbor2->edges.push_back(edge2);

        MapNode *newNode = mergeNodes(nodeA.get(), nodeB.get());

        REQUIRE(newNode != nullptr);

        // Every edge in newNode should have a reciprocal in the other endpoint
        for (const auto &edge : newNode->edges) {
            MapNode *other = edge.otherEnd(newNode);
            bool foundReciprocal = false;
            for (const auto &otherEdge : other->edges) {
                if (otherEdge.source == edge.source && otherEdge.target == edge.target) {
                    foundReciprocal = true;
                    break;
                }
            }
            REQUIRE(foundReciprocal);
        }

        delete newNode;
    }
}
