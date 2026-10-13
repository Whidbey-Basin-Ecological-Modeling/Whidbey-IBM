#include "habitat.h"
#include <string>
#include <unordered_map>
#include <algorithm>
#include <cctype>
#include <stdexcept>

namespace {

std::string normalizeName(const std::string& input) {
    size_t start = 0;
    while (start < input.size() && (std::isspace(static_cast<unsigned char>(input[start])) || input[start] == '\r' || input[start] == '\n')) {
        ++start;
    }
    size_t end = input.size();
    while (end > start && (std::isspace(static_cast<unsigned char>(input[end - 1])) || input[end - 1] == '\r' || input[end - 1] == '\n')) {
        --end;
    }
    std::string result = input.substr(start, end - start);
    std::transform(result.begin(), result.end(), result.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return result;
}

const std::unordered_map<std::string, HabitatType> HABITAT_TYPES_BY_NAME = {
    {"blind channel", HabitatType::BlindChannel},
    {"impoundment", HabitatType::Impoundment},
    {"low tide terrace", HabitatType::LowTideTerrace},
    {"distributary channel", HabitatType::Distributary},
    {"distributary", HabitatType::Distributary},
    {"distributary edge", HabitatType::DistributaryEdge},
    {"boat harbor", HabitatType::Harbor},
    {"harbor", HabitatType::Harbor},
    {"nearshore", HabitatType::Nearshore},
    {"shoreline", HabitatType::Nearshore},
    {"open water", HabitatType::OpenWater},
    {"intertidal mud flat", HabitatType::IntertidalMudFlat},
    {"intertidal mudflat", HabitatType::IntertidalMudFlat},
    {"rock", HabitatType::Rock},
    {"sub-tidal flat", HabitatType::SubtidalFlat},
    {"subtidal flat", HabitatType::SubtidalFlat},
    {"exit", HabitatType::Exit}
};

const std::unordered_map<std::string, LargeHabitatType> LARGE_HABITAT_TYPES_BY_NAME = {
    {"delta", LargeHabitatType::Delta},
    {"freshwater", LargeHabitatType::Freshwater},
    {"intertidal", LargeHabitatType::Intertidal},
    {"offshore", LargeHabitatType::Offshore}
};

} // namespace

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

std::string Habitat::toString() const {
    return toString(fine);
}

std::string Habitat::toString(HabitatType type) {
    switch (type) {
        case HabitatType::Impoundment:
            return "Impoundment";
        case HabitatType::Distributary:
            return "Distributary";
        case HabitatType::DistributaryEdge:
            return "Distributary edge";
        case HabitatType::BlindChannel:
            return "Blind channel";
        case HabitatType::LowTideTerrace:
            return "Low tide terrace";
        case HabitatType::Nearshore:
            return "Nearshore";
        case HabitatType::Harbor:
            return "Boat harbor";
        case HabitatType::OpenWater:
            return "Open water";
        case HabitatType::IntertidalMudFlat:
            return "Intertidal mud flat";
        case HabitatType::Rock:
            return "Rock";
        case HabitatType::SubtidalFlat:
            return "Sub-tidal flat";
        case HabitatType::Exit:
            return "Exit";
        default:
            return "Unknown";
    }
}

std::string Habitat::toString(LargeHabitatType type) {
    switch (type) {
        case LargeHabitatType::Delta:
            return "Delta";
        case LargeHabitatType::Freshwater:
            return "Freshwater";
        case LargeHabitatType::Intertidal:
            return "Intertidal";
        case LargeHabitatType::Offshore:
            return "Offshore";
        default:
            return "Unknown";
    }
}

LargeHabitatType Habitat::getDefaultLargeHabitat(HabitatType fine) {
    switch (fine) {
        case HabitatType::Distributary:
        case HabitatType::DistributaryEdge:
        case HabitatType::BlindChannel:
        case HabitatType::Impoundment:
        case HabitatType::LowTideTerrace:
            return LargeHabitatType::Delta;

        case HabitatType::IntertidalMudFlat:
        case HabitatType::Harbor:
        case HabitatType::Nearshore:
        case HabitatType::SubtidalFlat:
        case HabitatType::Rock:
            return LargeHabitatType::Intertidal;

        case HabitatType::OpenWater:
        case HabitatType::Exit:
            return LargeHabitatType::Offshore;

        default:
            return LargeHabitatType::Delta;
    }
}

bool Habitat::tryParse(const std::string& name, HabitatType& out) {
    std::string normalized = normalizeName(name);
    auto it = HABITAT_TYPES_BY_NAME.find(normalized);
    if (it != HABITAT_TYPES_BY_NAME.end()) {
        out = it->second;
        return true;
    }
    return false;
}

bool Habitat::tryParse(const std::string& name, LargeHabitatType& out) {
    std::string normalized = normalizeName(name);
    auto it = LARGE_HABITAT_TYPES_BY_NAME.find(normalized);
    if (it != LARGE_HABITAT_TYPES_BY_NAME.end()) {
        out = it->second;
        return true;
    }
    return false;
}

bool Habitat::tryParse(const std::string& name, Habitat& out) {
    HabitatType type;
    if (tryParse(name, type)) {
        out = Habitat(type);
        return true;
    }
    return false;
}

HabitatType Habitat::fromString(const std::string& name) {
    HabitatType type;
    if (tryParse(name, type)) {
        return type;
    }
    throw std::invalid_argument("Unknown habitat type: " + name);
}

LargeHabitatType Habitat::largeFromString(const std::string& name) {
    LargeHabitatType type;
    if (tryParse(name, type)) {
        return type;
    }
    throw std::invalid_argument("Unknown large habitat type: " + name);
}
