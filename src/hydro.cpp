#include "hydro.h"
#include "load.h"

#include <cmath>
#include <iostream>

#define MIN_WATER_TEMP 0.01f
#define MIN_WATER_TEMP_DISTRIBUTARY 4.0f
#define MAX_WATER_TEMP 30.0f

#define MIN_DEPTH 0.0f
#define MIN_DEPTH_DISTRIBUTARY 0.2f

HydroModel::HydroModel() :
    hydroNodes(),
    hydroTimeIntercept(0),
    currTimestep(0)
{
    this->updateTime(0L);
}

// Initialize a hydro model from datafiles at the provided paths and a timestep offset into the data
HydroModel::HydroModel(
    std::string flowSpeedFilename,
    int hydroTimeIntercept
) :
    hydroNodes(),
    hydroTimeIntercept(hydroTimeIntercept)
{
    loadDistribHydro(flowSpeedFilename, this->hydroNodes);
    this->updateTime(0L);
}

long HydroModel::getTime() const {
    return currTimestep + hydroTimeIntercept;
}

void HydroModel::updateTime(long newTime) {
    this->currTimestep = newTime;
}


// Get the current horizontal (E/W) flow velocity in m/s at the given node
float HydroModel::getCurrentU(const MapNode &node) const {
    return this->getCurrentU(*node.nearestHydroNode);
}
float HydroModel::getCurrentU(const DistribHydroNode &hydroNode) const {
    return hydroNode.us[this->getTime()];
}

// Get the current vertical (N/S) flow velocity in m/s at the given node
float HydroModel::getCurrentV(const MapNode &node) const {
    return this->getCurrentV(*node.nearestHydroNode);
}
float HydroModel::getCurrentV(const DistribHydroNode &hydroNode) const {
    return hydroNode.vs[this->getTime()];
}

// Get the total flow velocity in m/s at the given node
float HydroModel::getUnsignedFlowSpeedAtHydroNode(DistribHydroNode &hydroNode) {
    float currU = this->getCurrentU(hydroNode);
    float currV = this->getCurrentV(hydroNode);
    return sqrt(currU*currU + currV*currV);
}

FlowVelocity HydroModel::getScaledFlowVelocityAt(const MapNode &node) {
    auto scalar = static_cast<float>(calculateFlowSpeedScalar(node));
    return {getCurrentU(node) * scalar, getCurrentV(node) * scalar};
}

double HydroModel::calculateFlowSpeedScalar(const MapNode &node) {
    if (!isBlindChannel(node.type) && !isImpoundment(node.type)) {
        return 1.0;
    }
    const double hydroFlowSpeed = this->getUnsignedFlowSpeedAtHydroNode(*node.nearestHydroNode);
    const double hydroWidth = pow((hydroFlowSpeed / 0.04479583), (1.0 / 0.45896));
    const double blindChannelWidth = sqrt(node.area);
    double scalar = blindChannelWidth / hydroWidth;

    if (scalar > 1.0) {
        scalar = 1.0;
    }
    if (isImpoundment(node.type)) {
        constexpr double IMPOUNDMENT_MIN_FLOW_ADDL_SCALAR = 0.1;
        scalar *= IMPOUNDMENT_MIN_FLOW_ADDL_SCALAR;
    }
    return scalar;
}

float HydroModel::scaledFlowSpeed(const float flowSpeed, const MapNode &node) {
    double scalar = calculateFlowSpeedScalar(node);
    const double scaledFlowSpeed = scalar * flowSpeed;
    return static_cast<float>(scaledFlowSpeed);
}


float HydroModel::getUnsignedFlowSpeedAt(MapNode &node) {
    const float velocity = this->getUnsignedFlowSpeedAtHydroNode(*node.nearestHydroNode);
    return scaledFlowSpeed(velocity, node);
}

float limitWaterTemp(float waterTemp, HabitatType nodeType) {
    float waterTemperature = waterTemp;
    if (waterTemperature > MAX_WATER_TEMP) {
        waterTemperature = MAX_WATER_TEMP;
    }
    const float minimum_water_temperature = isDistributaryOrHarbor(nodeType) ? MIN_WATER_TEMP_DISTRIBUTARY : MIN_WATER_TEMP;
    if (waterTemperature < minimum_water_temperature) {
        waterTemperature = minimum_water_temperature;
    }

    return waterTemperature;
}

// Get the current temperature (C) at the given node
float HydroModel::getTemp(MapNode &node) {
    const float hydroTemp = node.nearestHydroNode->temps[this->getTime()];
    return limitWaterTemp(hydroTemp, node.type);
}

// Get the current salinity (psu) at the given node
float HydroModel::getSalinity(MapNode &node) {
    return node.nearestHydroNode->salinity[this->getTime()];
}

bool HydroModel::isDry(MapNode &node) {
    if (isDistributaryOrHarbor(node.type))
        return false;

    return node.nearestHydroNode->is_wet[this->getTime()] == 0.0f;
}

float limitDepth(const float depth, const HabitatType nodeType) {
    const float min_depth = isDistributaryOrHarbor(nodeType) ? MIN_DEPTH_DISTRIBUTARY : MIN_DEPTH;
    return (depth < min_depth) ? min_depth : depth;
}

// Get the current depth (m) at the given node
// Depth is hacked to be 5m in distributary midchannel, 3m at distributary edges
// (based on blind channel model everywhere else)
float HydroModel::getDepth(MapNode &node) {
    const float depth = node.nearestHydroNode->wses[this->getTime()] - node.elev;
    return limitDepth(depth, node.type);
}