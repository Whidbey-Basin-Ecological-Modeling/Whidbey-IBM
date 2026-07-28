#ifndef __FISH_MAP_H
#define __FISH_MAP_H

#include <vector>
#include <string>

// This struct represents a point for which
// flow velocities, water surface elevations, and temperatures have been pre-calculated
typedef struct DistribHydroNode {
    unsigned id; // This node's index in HydroModel::distribHydro
    float x; // horizontal (latitudinal) UTM Zone 10N coordinate
    float y; // vertical (longitudinal) UTM Zone 10N coordinate
    std::vector<float> us; // horizontal component of the flow speed vector (m/s), in 1hr increments starting from midnight on Jan 1
    std::vector<float> vs; // vertical component of the flow speed vector (m/s), in 1hr increments starting from midnight on Jan 1
    std::vector<float> wses; // Water surface elevation (NAVD88) (m) in 1hr increments starting from midnight on Jan 1
    std::vector<float> temps; // Water temperature (c) in 1hr increments starting from midnight on Jan 1
    std::vector<float> salinity; // Salinity (psu) in 1hr increments starting from midnight on Jan 1
    std::vector<float> is_wet; // Wet/dry status in 1hr increments starting from midnight on Jan 1
    DistribHydroNode(unsigned id) : id(id), us(), vs(), wses(), temps(), salinity(), is_wet() {}
} DistribHydroNode;

typedef struct FlowVelocity {
    float u; // horizontal component of flow speed (m/s)
    float v; // vertical component of flow speed (m/s)

    FlowVelocity() : u(0), v(0) {}
    FlowVelocity(float u, float v) : u(u), v(v) {}
} FlowVelocity;

class MapNode;

/*
* BlindChannel: location with minimal flow, potentially subject to intermittent drying
* Impoundment and LowTideTerrace are generally assumed to be subject to similar conditions as BlindChannel
* Distributary: location with high flow, usually part of a wide channel
* DistributaryEdge: location along the boundary of a distributary
* Nearshore: Adjacent to ocean, locations from which fish may exit the model
*/
enum class HabitatType {
    BlindChannel,
    Impoundment,
    LowTideTerrace,
    Distributary,
    DistributaryEdge,
    Harbor,
    Nearshore,

    // new types
    IntertidalMudFlat,
    OpenWater,
    Rock,
    SubtidalFlat,
    Exit
};

bool isDistributary(HabitatType t, bool includeDistributaryEdge = true);
bool isDistributaryOrHarbor(HabitatType t);
bool isDistributaryOrNearshore(HabitatType t);
bool isNearshore(HabitatType t);
bool isBlindChannel(HabitatType t);
bool isImpoundment(HabitatType t);

// Returns the mortality constant for a given habitat type
float habitatTypeMortalityConst(const HabitatType t, const float habitatMortalityMultiplier);

// Represents a link between two map locations
class Edge {
public:
    MapNode *source; // 'origin' of the edge
    MapNode *target; // 'destination' of the edge
    float length; // Edge length (m)
    Edge(MapNode *source, MapNode *target, float length);

    // Given one endpoint of this edge, return the other endpoint
    MapNode *otherEnd(const MapNode *node) const {
        return (node == source) ? target : source;
    }
};

class MapNode {
public:
    // ID (index in the map node list)
    int id;
    // Unified (directionless) edge list
    std::vector<Edge> edges;
    float x; // horizontal (longitudinal) UTM Zone 10N coordinate
    float y; // vertical (latitudinal) UTM Zone 10N coordinate
    // see HabitatType declaration above
    HabitatType type;
    // Area represented by this location (m^2)
    float area;
    // Ground-level elevation of this node (distance to NAVD88) in meters
    float elev;
    // Path distance (m) to the furthest upstream node
    float pathDist;
    // If this node is part of a multi-node distributary segment, this edge leads to one of the lateral neighbors
    Edge *crossChannelA;
    // If this node is part of a multi-node distributary segment, this edge leads to one of the lateral neighbors
    Edge *crossChannelB;

    DistribHydroNode *nearestHydroNode;
    unsigned nearestHydroNodeIndex;
    float hydroNodeDistance;
    // List of Fish::id of living fish such that Fish::location == this -- updated in Model::countAll
    std::vector<long> residentIds;
    // Population density of living fish at this location, in individuals/m^2 -- updated in Model::countAll
    float popDensity;
    // Median fish mass at this location (g) -- updated in Model::countAll
    float medMass;
    // Maximum fish mass at this location (g) -- updated in Model::countAll
    float maxMass;

    MapNode(HabitatType type, float area, float elev, float pathDist);
    MapNode(int id, float x, float y);
};

float getDistance(MapNode *a, MapNode *b);

// This struct represents a site at which biweekly sampling is conducted
typedef struct SamplingSite {
    // The human-readable site name
    std::string siteName;
    // The ID (used in snapshot files)
    size_t id;
    // The map locations to sample from
    std::vector<MapNode *> points;

    SamplingSite(std::string siteName, size_t id);
} SamplingSite;

#endif