//
// Created by Troy Frever on 2/18/26.
//

//
// Edge consistency tests for the existing edgesIn/edgesOut structure.
// These tests validate the graph invariants that must hold after edge insertion,
// providing a safety net before any structural refactoring.
//

#include <catch2/catch_test_macros.hpp>
#include <memory>
#include <algorithm>
#include <unordered_set>
#include <vector>
#include <iostream>
#include <set>

#include "map.h"
#include "load.h"
#include "test_utilities.h"

// ── Validation routine for edgesIn/edgesOut consistency ──

struct EdgeValidationResult {
    bool passed = true;
    size_t totalNodes = 0;
    size_t totalUniqueEdges = 0;
    std::vector<std::string> errors;

    void fail(const std::string &msg) {
        passed = false;
        errors.push_back(msg);
    }
};

// ── Validation routine for unified edges consistency ──

EdgeValidationResult validateEdgeConsistency(const std::vector<MapNode *> &map) {
    EdgeValidationResult result;
    result.totalNodes = map.size();

    std::unordered_set<MapNode *> mapSet(map.begin(), map.end());

    // We'll count unique directed edges by collecting (source, target) pairs
    std::set<std::pair<MapNode *, MapNode *>> uniqueDirectedEdges;

    for (MapNode *node : map) {

        // 1. Every edge in node->edges must have this node as source or target
        for (size_t i = 0; i < node->edges.size(); i++) {
            const Edge &e = node->edges[i];
            if (e.source != node && e.target != node) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edges[" + std::to_string(i) + "] has neither source nor target == this node");
            }
        }

        // 2. No self-loops
        for (const Edge &e : node->edges) {
            if (e.source == e.target) {
                result.fail("Node " + std::to_string(node->id) + ": self-loop in edges");
            }
        }

        // 3. All edge endpoints must be nodes that exist in the map
        for (const Edge &e : node->edges) {
            MapNode *other = e.otherEnd(node);
            if (mapSet.count(other) == 0) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edges references neighbor not in map");
            }
        }

        // 4. No duplicate edges (same source-target pair appearing twice)
        for (size_t i = 0; i < node->edges.size(); i++) {
            for (size_t j = i + 1; j < node->edges.size(); j++) {
                if (node->edges[i].source == node->edges[j].source
                    && node->edges[i].target == node->edges[j].target) {
                    result.fail("Node " + std::to_string(node->id)
                        + ": duplicate edge ("
                        + std::to_string(node->edges[i].source->id) + " -> "
                        + std::to_string(node->edges[i].target->id) + ")");
                }
            }
        }

        // 5. Symmetry: for every edge in this node's list, the other endpoint
        //    must also have this same edge (same source-target pair) in its edges list
        for (const Edge &e : node->edges) {
            MapNode *other = e.otherEnd(node);
            bool found = std::any_of(
                other->edges.begin(), other->edges.end(),
                [&e](const Edge &oe) {
                    return oe.source == e.source && oe.target == e.target;
                }
            );
            if (!found) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edge (" + std::to_string(e.source->id) + " -> "
                    + std::to_string(e.target->id)
                    + ") but neighbor " + std::to_string(other->id)
                    + " has no matching entry in edges");
            }
        }

        // 6. Edge lengths must be positive
        for (const Edge &e : node->edges) {
            if (e.length <= 0.0f) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edges has non-positive length " + std::to_string(e.length));
            }
        }

        // Collect unique directed edges for the count
        for (const Edge &e : node->edges) {
            uniqueDirectedEdges.insert({e.source, e.target});
        }
    }

    result.totalUniqueEdges = uniqueDirectedEdges.size();

    return result;
}

EdgeValidationResult validateEdgeConsistencyOld(const std::vector<MapNode *> &map) {
    EdgeValidationResult result;
    result.totalNodes = map.size();

    std::unordered_set<MapNode *> mapSet(map.begin(), map.end());
    size_t totalEdgeSlots = 0;

    for (MapNode *node : map) {

        // 1. Every edgesIn entry must have target == this node
        for (size_t i = 0; i < node->edgesIn.size(); i++) {
            const Edge &e = node->edgesIn[i];
            if (e.target != node) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesIn[" + std::to_string(i) + "].target != this node");
            }
        }

        // 2. Every edgesOut entry must have source == this node
        for (size_t i = 0; i < node->edgesOut.size(); i++) {
            const Edge &e = node->edgesOut[i];
            if (e.source != node) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesOut[" + std::to_string(i) + "].source != this node");
            }
        }

        // 3. No self-loops
        for (const Edge &e : node->edgesIn) {
            if (e.source == node) {
                result.fail("Node " + std::to_string(node->id) + ": self-loop in edgesIn");
            }
        }
        for (const Edge &e : node->edgesOut) {
            if (e.target == node) {
                result.fail("Node " + std::to_string(node->id) + ": self-loop in edgesOut");
            }
        }

        // 4. All edge endpoints must be nodes that exist in the map
        for (const Edge &e : node->edgesIn) {
            if (mapSet.count(e.source) == 0) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesIn references source not in map");
            }
        }
        for (const Edge &e : node->edgesOut) {
            if (mapSet.count(e.target) == 0) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesOut references target not in map");
            }
        }

        // 5. No duplicate edges within edgesIn
        for (size_t i = 0; i < node->edgesIn.size(); i++) {
            for (size_t j = i + 1; j < node->edgesIn.size(); j++) {
                if (node->edgesIn[i].source == node->edgesIn[j].source) {
                    result.fail("Node " + std::to_string(node->id)
                        + ": duplicate edgesIn from source "
                        + std::to_string(node->edgesIn[i].source->id));
                }
            }
        }

        // 6. No duplicate edges within edgesOut
        for (size_t i = 0; i < node->edgesOut.size(); i++) {
            for (size_t j = i + 1; j < node->edgesOut.size(); j++) {
                if (node->edgesOut[i].target == node->edgesOut[j].target) {
                    result.fail("Node " + std::to_string(node->id)
                        + ": duplicate edgesOut to target "
                        + std::to_string(node->edgesOut[i].target->id));
                }
            }
        }

        // 7. Symmetry: for every edgesOut entry (this -> X),
        //    X must have a matching edgesIn entry (this -> X)
        for (const Edge &e : node->edgesOut) {
            bool found = std::any_of(
                e.target->edgesIn.begin(), e.target->edgesIn.end(),
                [node](const Edge &ie) { return ie.source == node; }
            );
            if (!found) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesOut to " + std::to_string(e.target->id)
                    + " but target has no matching edgesIn");
            }
        }

        // 8. Symmetry: for every edgesIn entry (X -> this),
        //    X must have a matching edgesOut entry (X -> this)
        for (const Edge &e : node->edgesIn) {
            bool found = std::any_of(
                e.source->edgesOut.begin(), e.source->edgesOut.end(),
                [node](const Edge &oe) { return oe.target == node; }
            );
            if (!found) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesIn from " + std::to_string(e.source->id)
                    + " but source has no matching edgesOut");
            }
        }

        // 9. Edge lengths must be positive
        for (const Edge &e : node->edgesIn) {
            if (e.length <= 0.0f) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesIn has non-positive length " + std::to_string(e.length));
            }
        }
        for (const Edge &e : node->edgesOut) {
            if (e.length <= 0.0f) {
                result.fail("Node " + std::to_string(node->id)
                    + ": edgesOut has non-positive length " + std::to_string(e.length));
            }
        }

        totalEdgeSlots += node->edgesOut.size();
    }

    // edgesOut is canonical: each directed edge A->B appears once in A.edgesOut
    result.totalUniqueEdges = totalEdgeSlots;

    return result;
}

// ── Helper to print validation results (useful for debugging failures) ──

void requireValidation(const EdgeValidationResult &result) {
    if (!result.passed) {
        for (const auto &err : result.errors) {
            FAIL(err);
        }
    }
    REQUIRE(result.passed);
}

// ── Unit tests using synthetic graphs ──

TEST_CASE("Edge consistency: simple two-node graph via checkAndAddEdge", "[edges][consistency]") {
    auto nodeA = std::make_unique<MapNode>(HabitatType::Distributary, 1.0f, 0.0f, 0.0f);
    auto nodeB = std::make_unique<MapNode>(HabitatType::BlindChannel, 1.0f, 0.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    Edge e(nodeA.get(), nodeB.get(), 5.0f);
    checkAndAddEdge(e);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);

    REQUIRE(nodeA->edgesOut.size() == 1);
    REQUIRE(nodeB->edgesIn.size() == 1);
    REQUIRE(nodeA->edgesIn.empty());
    REQUIRE(nodeB->edgesOut.empty());
    REQUIRE(result.totalUniqueEdges == 1);
}

TEST_CASE("Edge consistency: connectNodes helper", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    auto nodeC = createMapNode(2.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;
    nodeC->id = 2;

    connectNodes(nodeA.get(), nodeB.get(), 3.0f);
    connectNodes(nodeB.get(), nodeC.get(), 4.0f);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get(), nodeC.get()};
    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);

    // nodeB should have 1 edgesIn (from A) and 1 edgesOut (to C)
    REQUIRE(nodeB->edgesIn.size() == 1);
    REQUIRE(nodeB->edgesOut.size() == 1);
    REQUIRE(result.totalUniqueEdges == 2);
}

TEST_CASE("Edge consistency: checkAndAddEdge rejects self-loops", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    nodeA->id = 0;

    Edge e(nodeA.get(), nodeA.get(), 1.0f);
    checkAndAddEdge(e);

    REQUIRE(nodeA->edgesIn.empty());
    REQUIRE(nodeA->edgesOut.empty());
}

TEST_CASE("Edge consistency: checkAndAddEdge rejects reverse duplicate", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    Edge e1(nodeA.get(), nodeB.get(), 5.0f);
    checkAndAddEdge(e1);

    // Try adding reverse
    Edge e2(nodeB.get(), nodeA.get(), 5.0f);
    checkAndAddEdge(e2);

    // Should still have exactly 1 directed edge: A -> B
    REQUIRE(nodeA->edgesOut.size() == 1);
    REQUIRE(nodeB->edgesIn.size() == 1);
    REQUIRE(nodeA->edgesIn.empty());
    REQUIRE(nodeB->edgesOut.empty());

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);
}

TEST_CASE("Edge consistency: star topology", "[edges][consistency]") {
    auto center = createMapNode(0.0f, 0.0f);
    center->id = 0;

    std::vector<std::unique_ptr<MapNode>> spokes;
    for (int i = 1; i <= 5; i++) {
        auto spoke = createMapNode(static_cast<float>(i), 0.0f);
        spoke->id = i;
        connectNodes(center.get(), spoke.get(), static_cast<float>(i));
        spokes.push_back(std::move(spoke));
    }

    std::vector<MapNode *> map;
    map.push_back(center.get());
    for (auto &s : spokes) map.push_back(s.get());

    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);

    REQUIRE(center->edgesOut.size() == 5);
    REQUIRE(center->edgesIn.empty());
    REQUIRE(result.totalUniqueEdges == 5);

    for (auto &s : spokes) {
        REQUIRE(s->edgesIn.size() == 1);
        REQUIRE(s->edgesOut.empty());
    }
}

TEST_CASE("Edge consistency: bidirectional edges via connectNodes", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    // Two directed edges: A->B and B->A
    connectNodes(nodeA.get(), nodeB.get(), 3.0f);
    connectNodes(nodeB.get(), nodeA.get(), 3.0f);

    REQUIRE(nodeA->edgesOut.size() == 1);
    REQUIRE(nodeA->edgesIn.size() == 1);
    REQUIRE(nodeB->edgesOut.size() == 1);
    REQUIRE(nodeB->edgesIn.size() == 1);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);
    REQUIRE(result.totalUniqueEdges == 2);
}

TEST_CASE("Edge consistency: linear chain", "[edges][consistency]") {
    const int chainLength = 6;
    std::vector<std::unique_ptr<MapNode>> nodes;
    for (int i = 0; i < chainLength; i++) {
        auto node = createMapNode(static_cast<float>(i), 0.0f);
        node->id = i;
        nodes.push_back(std::move(node));
    }

    for (int i = 0; i < chainLength - 1; i++) {
        connectNodes(nodes[i].get(), nodes[i + 1].get(), 1.0f);
    }

    std::vector<MapNode *> map;
    for (auto &n : nodes) map.push_back(n.get());

    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);
    REQUIRE(result.totalUniqueEdges == chainLength - 1);

    // Interior nodes have 1 in + 1 out; endpoints have only 1
    REQUIRE(nodes[0]->edgesOut.size() == 1);
    REQUIRE(nodes[0]->edgesIn.empty());
    REQUIRE(nodes[chainLength - 1]->edgesIn.size() == 1);
    REQUIRE(nodes[chainLength - 1]->edgesOut.empty());

    for (int i = 1; i < chainLength - 1; i++) {
        REQUIRE(nodes[i]->edgesIn.size() == 1);
        REQUIRE(nodes[i]->edgesOut.size() == 1);
    }
}

TEST_CASE("Edge consistency: checkAndAddEdge with multiple nodes via checkAndAddEdge",
          "[edges][consistency]") {
    // Build a small graph entirely through checkAndAddEdge (as loadMap does)
    auto n0 = createMapNode(0.0f, 0.0f);
    auto n1 = createMapNode(1.0f, 0.0f);
    auto n2 = createMapNode(2.0f, 0.0f);
    auto n3 = createMapNode(0.0f, 1.0f);
    n0->id = 0; n1->id = 1; n2->id = 2; n3->id = 3;

    checkAndAddEdge(Edge(n0.get(), n1.get(), 1.0f));
    checkAndAddEdge(Edge(n1.get(), n2.get(), 1.0f));
    checkAndAddEdge(Edge(n0.get(), n3.get(), 1.5f));
    checkAndAddEdge(Edge(n3.get(), n2.get(), 1.5f));

    // Try some duplicates and reverses that should be rejected
    checkAndAddEdge(Edge(n0.get(), n1.get(), 1.0f)); // exact dup
    checkAndAddEdge(Edge(n1.get(), n0.get(), 1.0f)); // reverse
    checkAndAddEdge(Edge(n2.get(), n1.get(), 1.0f)); // reverse

    std::vector<MapNode *> map = {n0.get(), n1.get(), n2.get(), n3.get()};
    auto result = validateEdgeConsistencyOld(map);
    requireValidation(result);
    REQUIRE(result.totalUniqueEdges == 4);

    // n0: out to n1 and n3
    REQUIRE(n0->edgesOut.size() == 2);
    REQUIRE(n0->edgesIn.empty());

    // n2: in from n1 and n3
    REQUIRE(n2->edgesIn.size() == 2);
    REQUIRE(n2->edgesOut.empty());
}

TEST_CASE("Validation detects broken symmetry", "[edges][consistency][negative]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    // Manually create broken state: A has edgesOut to B, but B has no edgesIn from A
    Edge e(nodeA.get(), nodeB.get(), 2.0f);
    nodeA->edgesOut.push_back(e);
    // Deliberately NOT adding to nodeB->edgesIn

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistencyOld(map);

    REQUIRE_FALSE(result.passed);
    REQUIRE(result.errors.size() >= 1);
    // Should mention the missing matching edgesIn
    bool foundSymmetryError = std::any_of(result.errors.begin(), result.errors.end(),
        [](const std::string &err) { return err.find("no matching edgesIn") != std::string::npos; });
    REQUIRE(foundSymmetryError);
}

TEST_CASE("Validation detects dangling edge reference", "[edges][consistency][negative]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    connectNodes(nodeA.get(), nodeB.get(), 2.0f);

    // Only include nodeA in the map — nodeB is "not in map" but referenced by edge
    std::vector<MapNode *> map = {nodeA.get()};
    auto result = validateEdgeConsistencyOld(map);

    REQUIRE_FALSE(result.passed);
    bool foundDanglingError = std::any_of(result.errors.begin(), result.errors.end(),
        [](const std::string &err) { return err.find("not in map") != std::string::npos; });
    REQUIRE(foundDanglingError);
}

// TODO: delete the "old" tests above once they are no longer necessary

// ══════════════════════════════════════════════════════════════════════════════
// Tests exercising the unified `edges` vector
// ══════════════════════════════════════════════════════════════════════════════

TEST_CASE("Edge consistency: simple two-node graph via checkAndAddEdge (edges)", "[edges][consistency]") {
    auto nodeA = std::make_unique<MapNode>(HabitatType::Distributary, 1.0f, 0.0f, 0.0f);
    auto nodeB = std::make_unique<MapNode>(HabitatType::BlindChannel, 1.0f, 0.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    Edge e(nodeA.get(), nodeB.get(), 5.0f);
    checkAndAddEdge(e);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistency(map);
    requireValidation(result);

    // Both endpoints carry the single directed edge A->B
    REQUIRE(nodeA->edges.size() == 1);
    REQUIRE(nodeB->edges.size() == 1);
    REQUIRE(nodeA->edges[0].otherEnd(nodeA.get()) == nodeB.get());
    REQUIRE(nodeB->edges[0].otherEnd(nodeB.get()) == nodeA.get());
    REQUIRE(result.totalUniqueEdges == 1);
}

TEST_CASE("Edge consistency: connectNodes helper (edges)", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    auto nodeC = createMapNode(2.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;
    nodeC->id = 2;

    connectNodes(nodeA.get(), nodeB.get(), 3.0f);
    connectNodes(nodeB.get(), nodeC.get(), 4.0f);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get(), nodeC.get()};
    auto result = validateEdgeConsistency(map);
    requireValidation(result);

    // A participates in 1 edge (A->B), B in 2 (A->B and B->C), C in 1 (B->C)
    REQUIRE(nodeA->edges.size() == 1);
    REQUIRE(nodeB->edges.size() == 2);
    REQUIRE(nodeC->edges.size() == 1);
    REQUIRE(result.totalUniqueEdges == 2);
}

TEST_CASE("Edge consistency: checkAndAddEdge rejects self-loops (edges)", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    nodeA->id = 0;

    Edge e(nodeA.get(), nodeA.get(), 1.0f);
    checkAndAddEdge(e);

    REQUIRE(nodeA->edges.empty());
}

TEST_CASE("Edge consistency: checkAndAddEdge rejects reverse duplicate (edges)", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    Edge e1(nodeA.get(), nodeB.get(), 5.0f);
    checkAndAddEdge(e1);

    // Try adding reverse — should be rejected
    Edge e2(nodeB.get(), nodeA.get(), 5.0f);
    checkAndAddEdge(e2);

    // Should still have exactly 1 directed edge: A -> B, present on both nodes
    REQUIRE(nodeA->edges.size() == 1);
    REQUIRE(nodeB->edges.size() == 1);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistency(map);
    requireValidation(result);
}

TEST_CASE("Edge consistency: star topology (edges)", "[edges][consistency]") {
    auto center = createMapNode(0.0f, 0.0f);
    center->id = 0;

    std::vector<std::unique_ptr<MapNode>> spokes;
    for (int i = 1; i <= 5; i++) {
        auto spoke = createMapNode(static_cast<float>(i), 0.0f);
        spoke->id = i;
        connectNodes(center.get(), spoke.get(), static_cast<float>(i));
        spokes.push_back(std::move(spoke));
    }

    std::vector<MapNode *> map;
    map.push_back(center.get());
    for (auto &s : spokes) map.push_back(s.get());

    auto result = validateEdgeConsistency(map);
    requireValidation(result);

    // Center participates in all 5 edges; each spoke in 1
    REQUIRE(center->edges.size() == 5);
    REQUIRE(result.totalUniqueEdges == 5);

    for (auto &s : spokes) {
        REQUIRE(s->edges.size() == 1);
        REQUIRE(s->edges[0].otherEnd(s.get()) == center.get());
    }
}

TEST_CASE("Edge consistency: bidirectional edges via connectNodes (edges)", "[edges][consistency]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    // Two directed edges: A->B and B->A
    connectNodes(nodeA.get(), nodeB.get(), 3.0f);
    connectNodes(nodeB.get(), nodeA.get(), 3.0f);

    // Each node carries both directed edges
    REQUIRE(nodeA->edges.size() == 2);
    REQUIRE(nodeB->edges.size() == 2);

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistency(map);
    requireValidation(result);
    REQUIRE(result.totalUniqueEdges == 2);
}

TEST_CASE("Edge consistency: linear chain (edges)", "[edges][consistency]") {
    const int chainLength = 6;
    std::vector<std::unique_ptr<MapNode>> nodes;
    for (int i = 0; i < chainLength; i++) {
        auto node = createMapNode(static_cast<float>(i), 0.0f);
        node->id = i;
        nodes.push_back(std::move(node));
    }

    for (int i = 0; i < chainLength - 1; i++) {
        connectNodes(nodes[i].get(), nodes[i + 1].get(), 1.0f);
    }

    std::vector<MapNode *> map;
    for (auto &n : nodes) map.push_back(n.get());

    auto result = validateEdgeConsistency(map);
    requireValidation(result);
    REQUIRE(result.totalUniqueEdges == static_cast<size_t>(chainLength - 1));

    // Endpoints participate in 1 edge; interior nodes in 2
    REQUIRE(nodes[0]->edges.size() == 1);
    REQUIRE(nodes[chainLength - 1]->edges.size() == 1);

    for (int i = 1; i < chainLength - 1; i++) {
        REQUIRE(nodes[i]->edges.size() == 2);
    }
}

TEST_CASE("Edge consistency: multiple nodes via checkAndAddEdge (edges)",
          "[edges][consistency]") {
    auto n0 = createMapNode(0.0f, 0.0f);
    auto n1 = createMapNode(1.0f, 0.0f);
    auto n2 = createMapNode(2.0f, 0.0f);
    auto n3 = createMapNode(0.0f, 1.0f);
    n0->id = 0; n1->id = 1; n2->id = 2; n3->id = 3;

    checkAndAddEdge(Edge(n0.get(), n1.get(), 1.0f));
    checkAndAddEdge(Edge(n1.get(), n2.get(), 1.0f));
    checkAndAddEdge(Edge(n0.get(), n3.get(), 1.5f));
    checkAndAddEdge(Edge(n3.get(), n2.get(), 1.5f));

    // Try some duplicates and reverses that should be rejected
    checkAndAddEdge(Edge(n0.get(), n1.get(), 1.0f)); // exact dup
    checkAndAddEdge(Edge(n1.get(), n0.get(), 1.0f)); // reverse
    checkAndAddEdge(Edge(n2.get(), n1.get(), 1.0f)); // reverse

    std::vector<MapNode *> map = {n0.get(), n1.get(), n2.get(), n3.get()};
    auto result = validateEdgeConsistency(map);
    requireValidation(result);
    REQUIRE(result.totalUniqueEdges == 4);

    // Each node participates in exactly 2 edges
    REQUIRE(n0->edges.size() == 2);
    REQUIRE(n1->edges.size() == 2);
    REQUIRE(n2->edges.size() == 2);
    REQUIRE(n3->edges.size() == 2);
}

TEST_CASE("Validation detects broken symmetry (edges)", "[edges][consistency][negative]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    // Manually create broken state: A has edge to B in its edges list,
    // but B does NOT have the same edge in its edges list
    Edge e(nodeA.get(), nodeB.get(), 2.0f);
    nodeA->edges.push_back(e);
    // Deliberately NOT adding to nodeB->edges

    std::vector<MapNode *> map = {nodeA.get(), nodeB.get()};
    auto result = validateEdgeConsistency(map);

    REQUIRE_FALSE(result.passed);
    REQUIRE(result.errors.size() >= 1);
    bool foundSymmetryError = std::any_of(result.errors.begin(), result.errors.end(),
        [](const std::string &err) { return err.find("no matching entry in edges") != std::string::npos; });
    REQUIRE(foundSymmetryError);
}

TEST_CASE("Validation detects dangling edge reference (edges)", "[edges][consistency][negative]") {
    auto nodeA = createMapNode(0.0f, 0.0f);
    auto nodeB = createMapNode(1.0f, 0.0f);
    nodeA->id = 0;
    nodeB->id = 1;

    connectNodes(nodeA.get(), nodeB.get(), 2.0f);

    // Only include nodeA in the map — nodeB is "not in map" but referenced by edge
    std::vector<MapNode *> map = {nodeA.get()};
    auto result = validateEdgeConsistency(map);

    REQUIRE_FALSE(result.passed);
    bool foundDanglingError = std::any_of(result.errors.begin(), result.errors.end(),
        [](const std::string &err) { return err.find("not in map") != std::string::npos; });
    REQUIRE(foundDanglingError);
}