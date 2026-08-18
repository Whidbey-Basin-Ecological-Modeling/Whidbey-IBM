#ifndef __FISH_HYDRO_H
#define __FISH_HYDRO_H

#include <vector>
#include "map.h"

// This struct stores cached hydrology model predictions for a single map location
typedef struct HydroNode {
    float temp; // temperature in degrees C
    float salinity; // salinity in psu
    float depth; // meters of water (distance from map elevation to water surface elevation)
    float flowSpeed; // flow speed in m/s
} HydroNode;

class HydroModel {
public:
    HydroModel();

    HydroModel(
        std::string flowSpeedFilename,
        int hydroTimeIntercept // Timesteps between midnight on Jan 1 and the start of the hydro data
    );

    virtual ~HydroModel() = default;

    // Return the flow speed in m/s at a given location
    virtual float getUnsignedFlowSpeedAt(MapNode &node);
    float getUnsignedFlowSpeedAtHydroNode(DistribHydroNode &hydroNode);
    virtual FlowVelocity getScaledFlowVelocityAt(const MapNode &node);

    double calculateFlowSpeedScalar(const MapNode &node);

    virtual float scaledFlowSpeed(float flowSpeed, const MapNode &node);
    // Return the temperature in degrees C at a given location
    virtual float getTemp(MapNode &node);
    // Return the salinity in psu at a given location
    virtual float getSalinity(MapNode &node);
    // Return the water depth in meters at a given location
    virtual float getDepth(MapNode &node);
    // Return true if the location is dry at the current timestep
    virtual bool isDry(MapNode &node);

    // Set the hydro model's timestep to a given timestep
    void updateTime(long newTime);

    long getTime() const;

public:
    virtual float getCurrentU(const MapNode& node) const; // m/s
    virtual float getCurrentV(const MapNode& node) const; // m/s
protected:
    float getCurrentU(const DistribHydroNode &hydroNode) const; // Get the current timestep's horizontal flow speed component (in m/s) at a given DistribHydroNode
    float getCurrentV(const DistribHydroNode &hydroNode) const; // Get the current timestep's vertical flow speed component (in m/s) at a given DistribHydroNode

public:
    // The loaded flow data, as DistribHydroNodes (see map.h)
    std::vector<DistribHydroNode> hydroNodes;

private:
    int hydroTimeIntercept;
    long currTimestep;

};

#endif