#include <complex>
#include <catch2/catch_test_macros.hpp>
#include "hydro.h"
#include "catch2/matchers/catch_matchers.hpp"
#include "catch2/matchers/catch_matchers_floating_point.hpp"

TEST_CASE("hydro updates timestep", "") {
    HydroModel hydroModel;
    hydroModel.updateTime(4);
    REQUIRE(hydroModel.getTime() == 4);
    hydroModel.updateTime(7);
    REQUIRE(hydroModel.getTime() == 7);
}

TEST_CASE("HydroModel::getScaledFlowVelocityAt tests", "[hydro]") {
    HydroModel hydro_model;
    constexpr float DEFAULT_U = 2.0f;
    constexpr float DEFAULT_V = 3.0f;
    hydro_model.hydroNodes.emplace_back(0);
    hydro_model.hydroNodes[0].us = {DEFAULT_U};
    hydro_model.hydroNodes[0].vs = {DEFAULT_V};

    SECTION("Normal node (non-blind, non-impoundment)") {
        MapNode node(HabitatType::Distributary, 100.0f, 0.0f, 0.0f);
        node.nearestHydroNode = &hydro_model.hydroNodes[0];

        FlowVelocity result = hydro_model.getScaledFlowVelocityAt(node);

        REQUIRE_THAT(result.u, Catch::Matchers::WithinRel(DEFAULT_U, 0.001f));
        REQUIRE_THAT(result.v, Catch::Matchers::WithinRel(DEFAULT_V, 0.001f));
    }

    SECTION("Blind channel node") {
        float node_area = 25.0f;
        MapNode node(HabitatType::BlindChannel, node_area, 0.0f, 0.0f);
        node.area = node_area;
        node.nearestHydroNode = &hydro_model.hydroNodes[0];

        FlowVelocity result_blind_channel = hydro_model.getScaledFlowVelocityAt(node);

        CHECK(result_blind_channel.u < DEFAULT_U);
        CHECK(result_blind_channel.v < DEFAULT_V);
        CHECK(result_blind_channel.u > 0.0f);
        CHECK(result_blind_channel.v > 0.0f);
        SECTION("Impoundment node") {
            node.type = HabitatType::Impoundment;

            FlowVelocity result_impoundment = hydro_model.getScaledFlowVelocityAt(node);

            CHECK(result_impoundment.u < result_blind_channel.u);
            CHECK(result_impoundment.v < result_blind_channel.v);
            CHECK(result_impoundment.u > 0.0f);
            CHECK(result_impoundment.v > 0.0f);
            REQUIRE_THAT(result_impoundment.u, Catch::Matchers::WithinRel(result_blind_channel.u * 0.1, 0.001));
            REQUIRE_THAT(result_impoundment.v, Catch::Matchers::WithinRel(result_blind_channel.v * 0.1, 0.001));
        }
    }
}

TEST_CASE("HydroModel::calculateFlowSpeedScalar tests", "[hydro]") {
    HydroModel hydro_model;
    constexpr float DEFAULT_U = 2.0f;
    constexpr float DEFAULT_V = 3.0f;
    hydro_model.hydroNodes.emplace_back(0);
    hydro_model.hydroNodes[0].us = {DEFAULT_U};
    hydro_model.hydroNodes[0].vs = {DEFAULT_V};

    SECTION("Normal node returns 1.0") {
        MapNode node(HabitatType::Distributary, 100.0f, 0.0f, 0.0f);
        node.nearestHydroNode = &hydro_model.hydroNodes[0];

        double scalar = hydro_model.calculateFlowSpeedScalar(node);
        REQUIRE_THAT(scalar, Catch::Matchers::WithinRel(1.0, 0.001));
    }

    SECTION("Blind channel scalar calculation") {
        MapNode node(HabitatType::BlindChannel, 25.0f, 0.0f, 0.0f);
        node.area = 25.0f;
        node.nearestHydroNode = &hydro_model.hydroNodes[0];

        double scalar = hydro_model.calculateFlowSpeedScalar(node);
        REQUIRE(scalar <= 1.0);
        REQUIRE(scalar > 0.0);
    }

    SECTION("Impoundment applies additional scalar") {
        MapNode node(HabitatType::BlindChannel, 100.0f, 0.0f, 0.0f);
        node.area = 100.0f;
        node.nearestHydroNode = &hydro_model.hydroNodes[0];

        double bc_scalar = hydro_model.calculateFlowSpeedScalar(node);
        REQUIRE(bc_scalar <= 1.0);
        REQUIRE(bc_scalar > 0.0);

        node.type = HabitatType::Impoundment;
        double impoundment_scalar = hydro_model.calculateFlowSpeedScalar(node);

        REQUIRE_THAT(impoundment_scalar, Catch::Matchers::WithinRel(bc_scalar * 0.1f, 0.001));
        REQUIRE(impoundment_scalar > 0.0);
    }

    SECTION("Large blind channel area is capped at 1.0") {
        MapNode node(HabitatType::BlindChannel, 10000.0f, 0.0f, 0.0f);
        node.nearestHydroNode = &hydro_model.hydroNodes[0];
        node.area = std::pow(1000000.0f, 2.0f);

        double scalar = hydro_model.calculateFlowSpeedScalar(node);
        REQUIRE_THAT(scalar, Catch::Matchers::WithinRel(1.0, 0.0001));
    }
}

TEST_CASE("HydroModel::isDry tests", "[hydro]") {
    HydroModel hydro_model;
    hydro_model.hydroNodes.emplace_back(0);
    // At timestep 0: dry (is_wet = 0.0f); at timestep 1: wet (is_wet = 1.0f)
    hydro_model.hydroNodes[0].is_wet = {0.0f, 1.0f};

    SECTION("Distributary and Harbor nodes return false even when hydro node is dry") {
        MapNode dist_node(HabitatType::Distributary, 100.0f, 0.0f, 0.0f);
        dist_node.nearestHydroNode = &hydro_model.hydroNodes[0];

        MapNode dist_edge_node(HabitatType::DistributaryEdge, 100.0f, 0.0f, 0.0f);
        dist_edge_node.nearestHydroNode = &hydro_model.hydroNodes[0];

        MapNode harbor_node(HabitatType::Harbor, 100.0f, 0.0f, 0.0f);
        harbor_node.nearestHydroNode = &hydro_model.hydroNodes[0];

        hydro_model.updateTime(0); // hydro node is dry (is_wet == 0.0f)
        REQUIRE_FALSE(hydro_model.isDry(dist_node));
        REQUIRE_FALSE(hydro_model.isDry(dist_edge_node));
        REQUIRE_FALSE(hydro_model.isDry(harbor_node));

        hydro_model.updateTime(1); // hydro node is wet (is_wet == 1.0f)
        REQUIRE_FALSE(hydro_model.isDry(dist_node));
        REQUIRE_FALSE(hydro_model.isDry(dist_edge_node));
        REQUIRE_FALSE(hydro_model.isDry(harbor_node));
    }

    SECTION("Other habitat types return true when dry and false when wet") {
        MapNode bc_node(HabitatType::BlindChannel, 100.0f, 0.0f, 0.0f);
        bc_node.nearestHydroNode = &hydro_model.hydroNodes[0];

        MapNode nearshore_node(HabitatType::Nearshore, 100.0f, 0.0f, 0.0f);
        nearshore_node.nearestHydroNode = &hydro_model.hydroNodes[0];

        MapNode impoundment_node(HabitatType::Impoundment, 100.0f, 0.0f, 0.0f);
        impoundment_node.nearestHydroNode = &hydro_model.hydroNodes[0];

        hydro_model.updateTime(0); // hydro node is dry (is_wet == 0.0f)
        REQUIRE(hydro_model.isDry(bc_node));
        REQUIRE(hydro_model.isDry(nearshore_node));
        REQUIRE(hydro_model.isDry(impoundment_node));

        hydro_model.updateTime(1); // hydro node is wet (is_wet == 1.0f)
        REQUIRE_FALSE(hydro_model.isDry(bc_node));
        REQUIRE_FALSE(hydro_model.isDry(nearshore_node));
        REQUIRE_FALSE(hydro_model.isDry(impoundment_node));
    }
}
