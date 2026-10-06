#include "map.h"
#include <vector>
#include <string>
#include <cmath>
#include <limits>

bool isDistributary(HabitatType t, bool includeDistributaryEdge) {
    return (t==HabitatType::Distributary) || (includeDistributaryEdge && t==HabitatType::DistributaryEdge);
}

bool isDistributary(Habitat h, bool includeDistributaryEdge) {
    return isDistributary(h.fineHabitat, includeDistributaryEdge);
}

bool isHarbor(HabitatType t) {
    return t == HabitatType::Harbor;
}

bool isHarbor(Habitat h) {
    return isHarbor(h.fineHabitat);
}

bool isNearshore(HabitatType t) {
    return t == HabitatType::Nearshore;
}

bool isNearshore(Habitat h) {
    return isNearshore(h.fineHabitat);
}

bool isBlindChannel(HabitatType t) {
    return t == HabitatType::BlindChannel;
}

bool isBlindChannel(Habitat h) {
    return isBlindChannel(h.fineHabitat);
}

bool isImpoundment(HabitatType t) {
    return t == HabitatType::Impoundment;
}

bool isImpoundment(Habitat h) {
    return isImpoundment(h.fineHabitat);
}

bool isDistributaryOrHarbor(const HabitatType t) {
    return isDistributary(t) || isHarbor(t);
}

bool isDistributaryOrHarbor(Habitat h) {
    return isDistributaryOrHarbor(h.fineHabitat);
}

bool isDistributaryOrNearshore(const HabitatType t) {
    return isDistributary(t) || isNearshore(t);
}

bool isDistributaryOrNearshore(Habitat h) {
    return isDistributaryOrNearshore(h.fineHabitat);
}

bool isDistributaryWithoutEdgeOrIsNearshore(HabitatType habitat) {
    return isDistributary(habitat, false) || isNearshore(habitat);
}

bool isDistributaryWithoutEdgeOrIsNearshore(Habitat habitat) {
    return isDistributaryWithoutEdgeOrIsNearshore(habitat.fineHabitat);
}

float habitatTypeMortalityConst(const HabitatType t, const float habitatMortalityMultiplier) {
    float defaultNoMultiplier = 1.0;
    if (isDistributaryWithoutEdgeOrIsNearshore(t)) {
        return habitatMortalityMultiplier;
    }
    return defaultNoMultiplier;
}

float habitatTypeMortalityConst(const Habitat h, const float habitatMortalityMultiplier) {
    return habitatTypeMortalityConst(h.fineHabitat, habitatMortalityMultiplier);
}

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
