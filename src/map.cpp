#include "map.h"
#include <vector>
#include <string>
#include <cmath>
#include <limits>

Edge::Edge(MapNode *source, MapNode *target, float length)
     : source(source), target(target), length(length)
     {}

MapNode::MapNode(Habitat habitat, float area, float elev, float pathDist)
        : id(-1), habitat(habitat), area(area), elev(elev), pathDist(pathDist),
        crossChannelA(nullptr), crossChannelB(nullptr),
        nearestHydroNode(nullptr), hydroNodeDistance(std::numeric_limits<float>::max()),
        popDensity(0.0f)
{}

MapNode::MapNode(HabitatType fineHabitat, float area, float elev, float pathDist)
        : MapNode(Habitat(fineHabitat), area, elev, pathDist)
{}

MapNode::MapNode(int id, float x, float y)
        : id(id), x(x), y(y), habitat(HabitatType::Distributary), area(0.0f), elev(0.0f), pathDist(0.0f),
        crossChannelA(nullptr), crossChannelB(nullptr),
        nearestHydroNode(nullptr), hydroNodeDistance(std::numeric_limits<float>::max()),
        popDensity(0.0f)
{}

SamplingSite::SamplingSite(std::string siteName, size_t id) : siteName(siteName), id(id), points() {}

float getDistance(MapNode *a, MapNode *b) {
    float dx = a->x - b->x;
    float dy = a->y - b->y;
    return std::sqrt(dx*dx + dy*dy);
}
