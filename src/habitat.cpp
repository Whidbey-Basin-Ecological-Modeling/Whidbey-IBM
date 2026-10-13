#include "habitat.h"

bool Habitat::isDistributary(bool includeDistributaryEdge) const {
    return (fine == HabitatType::Distributary) || (includeDistributaryEdge && fine == HabitatType::DistributaryEdge);
}

bool Habitat::isHarbor() const {
    return fine == HabitatType::Harbor;
}

bool Habitat::isNearshore() const {
    return fine == HabitatType::Nearshore;
}

bool Habitat::isBlindChannel() const {
    return fine == HabitatType::BlindChannel;
}

bool Habitat::isImpoundment() const {
    return fine == HabitatType::Impoundment;
}

bool Habitat::isDistributaryOrHarbor() const {
    return isDistributary() || isHarbor();
}

bool Habitat::isDistributaryOrNearshore() const {
    return isDistributary() || isNearshore();
}

bool Habitat::isDistributaryWithoutEdgeOrIsNearshore() const {
    return isDistributary(false) || isNearshore();
}

float Habitat::getMortalityConst(const float habitatMortalityMultiplier) const {
    float defaultNoMultiplier = 1.0f;
    if (isDistributaryWithoutEdgeOrIsNearshore()) {
        return habitatMortalityMultiplier;
    }
    return defaultNoMultiplier;
}
