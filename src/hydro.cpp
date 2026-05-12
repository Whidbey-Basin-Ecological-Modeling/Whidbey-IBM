#include "hydro.h"
#include "load.h"

#include <cmath>
#include <iostream>

#define MIN_WATER_TEMP 0.01f
#define MIN_WATER_TEMP_DISTRIBUTARY 4.0f
#define MAX_WATER_TEMP 30.0f

#define MIN_DEPTH 0.0f
#define MIN_DEPTH_DISTRIBUTARY 0.2f

// Initialize a hydro model from datafiles at the provided paths and a timestep offset into the data
HydroModel::HydroModel(
    std::string cresTideFilename,
    std::string flowSpeedFilename,
    std::string distribWseTempFilename,
    int hydroTimeIntercept
) :
    cresTideData(loadFloatListInterleaved(cresTideFilename, 4)),
    hydroNodes(),
    useSimData(false),
    hydroTimeIntercept(hydroTimeIntercept)
{
    loadDistribHydro(flowSpeedFilename, distribWseTempFilename, this->hydroNodes);
    this->updateTime(0L);
}

HydroModel::HydroModel(
    std::vector<MapNode *> &map,
    std::vector<std::vector<float>> &depths,
    std::vector<std::vector<float>> &temps,
    float distFlow
) :
    useSimData(true), simDepths(), simTemps(), simDistFlow(distFlow), hydroTimeIntercept(0)
{
    this->updateTime(0L);
    for (size_t i = 0; i < map.size(); ++i) {
        this->simDepths[map[i]] = depths[i];
        this->simTemps[map[i]] = temps[i];
    }
}

long HydroModel::getTime() const {
    return currTimestep + hydroTimeIntercept;
}

void HydroModel::updateTime(long newTime) {
    this->currTimestep = newTime;
    if (!this->useSimData) {
        this->currCresTide = this->cresTideData[getTime()];
    }
}

bool HydroModel::isHighTide() {
    return this->getTime() - 1 > 0 && this->getTime() + 1 < (long) this->cresTideData.size()
        && this->currCresTide > this->cresTideData[this->getTime() - 1]
        && this->currCresTide > this->cresTideData[this->getTime() + 1];
}

// Get the current horizontal (E/W) flow velocity in m/s at the given node
float HydroModel::getCurrentU(const MapNode &node) const {
    return this->getCurrentU(this->hydroNodes[node.nearestHydroNodeID]);
}
float HydroModel::getCurrentU(const DistribHydroNode &hydroNode) const {
    return hydroNode.us[this->getTime()];
}

// Get the current vertical (N/S) flow velocity in m/s at the given node
float HydroModel::getCurrentV(const MapNode &node) const {
    return this->getCurrentV(this->hydroNodes[node.nearestHydroNodeID]);
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
    const double hydroFlowSpeed = this->getUnsignedFlowSpeedAtHydroNode(this->hydroNodes[node.nearestHydroNodeID]);
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
    if (this->useSimData) {
        return isDistributary(node.type) ? this->simDistFlow / (this->getDepth(node) * sqrt(node.area)) : 0.0f;
    }
    const float velocity = this->getUnsignedFlowSpeedAtHydroNode(this->hydroNodes[node.nearestHydroNodeID]);
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
    if (this->useSimData) {
        return this->simTemps[&node][this->getTime()];
    }

    const float hydroTemp = this->hydroNodes[node.nearestHydroNodeID].temps[this->getTime()];
    return limitWaterTemp(hydroTemp, node.type);
}

float limitDepth(const float depth, const HabitatType nodeType) {
    const float min_depth = isDistributaryOrHarbor(nodeType) ? MIN_DEPTH_DISTRIBUTARY : MIN_DEPTH;
    return (depth < min_depth) ? min_depth : depth;
}

// Get the current depth (m) at the given node
// Depth is hacked to be 5m in distributary midchannel, 3m at distributary edges
// (based on blind channel model everywhere else)
float HydroModel::getDepth(MapNode &node) {
    if (this->useSimData) {
        return this->simDepths[&node][this->getTime()];
    }

    const float depth = this->hydroNodes[node.nearestHydroNodeID].wses[this->getTime()] - node.elev;
    return limitDepth(depth, node.type);
}