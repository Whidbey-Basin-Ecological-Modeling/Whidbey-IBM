//
// Created by Troy Frever on 6/30/25.
//

#include <catch2/catch_test_macros.hpp>
#include <memory>
#include <sstream>
#include "load.h"
#include "map.h"
#include "catch2/catch_approx.hpp"

// Helper function to create a MapNode for testing
auto createTestNode(int id = 0, HabitatType type = HabitatType::Distributary) {
    auto node = std::make_unique<MapNode>(type, 0.0f, 0.0f, 0.0f);
    node->id = id;
    return node;
}

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

TEST_CASE("readNodes functionality", "[load]") {
    SECTION("Valid sequential nodes") {
        std::string csvData = "node,xcoord,ycoord\n"
                              "1,524938.0,5361074.0\n"
                              "2,524942.7,5361856.0\n"
                              "3,524952.8,5362025.5\n";
        std::stringstream ss(csvData);
        std::vector<MapNode*> dest;

        bool success = readNodes(dest, ss);

        REQUIRE(success == true);
        REQUIRE(dest.size() == 4);
        CHECK(dest[0]->id == -1);
        CHECK(dest[1]->id == 1);
        CHECK(dest[1]->x == Catch::Approx(524938.0));
        CHECK(dest[1]->y == Catch::Approx(5361074.0));
        CHECK(dest[2]->id == 2);
        CHECK(dest[2]->x == Catch::Approx(524942.7));
        CHECK(dest[2]->y == Catch::Approx(5361856.0));
        CHECK(dest[3]->id == 3);
        CHECK(dest[3]->x == Catch::Approx(524952.8));
        CHECK(dest[3]->y == Catch::Approx(5362025.5));

        for (auto node : dest) delete node;
    }

    SECTION("Non-sequential IDs error check") {
        std::string csvData = "node,xcoord,ycoord\n"
                              "1,10.0,20.0\n"
                              "3,30.0,40.0\n";
        std::stringstream ss(csvData);
        std::vector<MapNode*> dest;

        bool success = readNodes(dest, ss);

        REQUIRE(success == false);

        for (auto node : dest) delete node;
    }

    SECTION("IDs not starting with 1 error check") {
        std::string csvData = "node,xcoord,ycoord\n"
                              "2,10.0,20.0\n";
        std::stringstream ss(csvData);
        std::vector<MapNode*> dest;

        bool success = readNodes(dest, ss);

        REQUIRE(success == false);

        for (auto node : dest) delete node;
    }

    SECTION("Empty file error check") {
        std::string csvData = "";
        std::stringstream ss(csvData);
        std::vector<MapNode*> dest;

        bool success = readNodes(dest, ss);

        REQUIRE(success == false);
        REQUIRE(dest.empty());
    }

    SECTION("Dummy node and index matching") {
        std::string csvData = "node,xcoord,ycoord\n"
                              "1,10.0,20.0\n"
                              "2,30.0,40.0\n"
                              "3,50.0,60.0\n";
        std::stringstream ss(csvData);
        std::vector<MapNode*> dest;

        bool success = readNodes(dest, ss);

        REQUIRE(success == true);
        REQUIRE(dest.size() == 4);
        CHECK(dest[0]->id == -1);

        // Verify that node ids match the node index after the dummy
        for (size_t i = 1; i < dest.size(); ++i) {
            CHECK(dest[i]->id == static_cast<int>(i));
        }

        for (auto node : dest) delete node;
    }
}

TEST_CASE("readGeometry functionality", "[load]") {
    SECTION("Valid geometry updates areas") {
        std::vector<MapNode*> dest;
        dest.push_back(new MapNode(-1, 0, 0)); // Dummy
        dest.push_back(new MapNode(1, 100.0f, 200.0f));
        dest.push_back(new MapNode(2, 300.0f, 400.0f));
        
        dest[1]->area = 0.0f;
        dest[2]->area = 0.0f;

        std::string csvData = "node,x,y,area\n"
                              "1,100.0,200.0,50.5\n"
                              "2,300.0,400.0,75.2\n";
        std::stringstream ss(csvData);

        bool success = readGeometry(dest, ss);

        REQUIRE(success == true);
        CHECK(dest[1]->area == Catch::Approx(50.5f));
        CHECK(dest[2]->area == Catch::Approx(75.2f));

        for (auto node : dest) delete node;
    }

    SECTION("Empty geometry file error check") {
        std::vector<MapNode*> dest;
        dest.push_back(new MapNode(-1, 0, 0));
        
        std::string csvData = "";
        std::stringstream ss(csvData);

        bool success = readGeometry(dest, ss);

        REQUIRE(success == false);

        for (auto node : dest) delete node;
    }

    SECTION("Bad geometry data (too few columns)") {
        std::vector<MapNode*> dest;
        dest.push_back(new MapNode(-1, 0, 0));
        dest.push_back(new MapNode(1, 100.0, 200.0));
        
        std::string csvData = "node,x,y,area\n"
                              "1,100.0,200.0\n"; // Missing area
        std::stringstream ss(csvData);

        bool success = readGeometry(dest, ss);

        REQUIRE(success == false);

        for (auto node : dest) delete node;
    }

    SECTION("Node ID out of range") {
        std::vector<MapNode*> dest;
        dest.push_back(new MapNode(-1, 0, 0));
        dest.push_back(new MapNode(1, 100.0, 200.0));
        
        std::string csvData = "node,x,y,area\n"
                              "2,200.0,300.0,50.0\n"; // ID 2 is out of range (max 1)
        std::stringstream ss(csvData);

        bool success = readGeometry(dest, ss);

        REQUIRE(success == false);

        for (auto node : dest) delete node;
    }

    SECTION("Coordinate mismatch error check") {
        std::vector<MapNode*> dest;
        dest.push_back(new MapNode(-1, 0, 0));
        dest.push_back(new MapNode(1, 100.0, 200.0));
        
        std::string csvData = "node,x,y,area\n"
                              "1,101.0,200.0,50.0\n"; // x is 101, but node 1 has x=100
        std::stringstream ss(csvData);

        bool success = readGeometry(dest, ss);

        REQUIRE(success == false);

        for (auto node : dest) delete node;
    }
}

TEST_CASE("readEdges functionality", "[load][edges]") {
    std::vector<MapNode*> nodes;
    // dummy at 0
    nodes.push_back(new MapNode(-1, 0.0f, 0.0f));
    nodes.push_back(new MapNode(1, 10.0f, 20.0f));
    nodes.push_back(new MapNode(2, 30.0f, 40.0f));
    nodes.push_back(new MapNode(3, 50.0f, 60.0f));

    SECTION("Valid edges file") {
        std::stringstream ss;
        ss << "node_a,node_b,distance" << std::endl;
        ss << "1,2,100.0" << std::endl;
        ss << "2,3,200.0" << std::endl;

        bool result = readEdges(nodes, ss);
        REQUIRE(result == true);
        REQUIRE(nodes[1]->edges.size() == 1);
        REQUIRE(nodes[2]->edges.size() == 2);
        REQUIRE(nodes[3]->edges.size() == 1);

        CHECK(nodes[1]->edges[0].length == Catch::Approx(100.0f));
        CHECK(nodes[3]->edges[0].length == Catch::Approx(200.0f));
        CHECK(nodes[1]->edges[0].otherEnd(nodes[1]) == nodes[2]);
        CHECK(nodes[3]->edges[0].otherEnd(nodes[3]) == nodes[2]);
    }

    SECTION("Duplicate edges") {
        std::stringstream ss;
        ss << "node_a,node_b,distance" << std::endl;
        ss << "1,2,100.0" << std::endl;
        ss << "1,2,100.0" << std::endl; // Duplicate

        bool result = readEdges(nodes, ss);
        REQUIRE(result == true);
        REQUIRE(nodes[1]->edges.size() == 1);
        REQUIRE(nodes[2]->edges.size() == 1);
    }

    SECTION("Effective duplicate edges") {
        std::stringstream ss;
        ss << "node_a,node_b,distance" << std::endl;
        ss << "1,2,100.0" << std::endl;
        ss << "2,1,100.0" << std::endl; // Effective Duplicate

        bool result = readEdges(nodes, ss);
        REQUIRE(result == true);
        REQUIRE(nodes[1]->edges.size() == 1);
        REQUIRE(nodes[2]->edges.size() == 1);
    }

    SECTION("Inconsistent edge state (Manual simulation)") {
        // Manually inject an edge into node 2 only
        MapNode* node1 = nodes[1];
        MapNode* node2 = nodes[2];
        Edge e(node1, node2, 100.0f);
        node2->edges.push_back(e);

        std::stringstream ss;
        ss << "node_a,node_b,distance" << std::endl;
        ss << "1,2,100.0" << std::endl; // Should be rejected because node 2 already has it

        bool result = readEdges(nodes, ss);
        REQUIRE(result == true);
        // node 1 should still be empty if validation worked for both nodes
        CHECK(node1->edges.empty());
        // node 2 should still have only the manual one
        REQUIRE(node2->edges.size() == 1);
    }

    SECTION("Self-loop edge") {
        std::stringstream ss;
        ss << "node_a,node_b,distance" << std::endl;
        ss << "1,1,100.0" << std::endl;

        bool result = readEdges(nodes, ss);
        REQUIRE(result == true);
        REQUIRE(nodes[1]->edges.empty());
    }

    SECTION("Out of range node IDs") {
        std::stringstream ss;
        ss << "node_a,node_b,distance" << std::endl;
        ss << "1,4,100.0" << std::endl;

        bool result = readEdges(nodes, ss);
        REQUIRE(result == true);
        REQUIRE(nodes[1]->edges.empty());
    }

    // Cleanup
    for (auto node : nodes) {
        delete node;
    }
}
