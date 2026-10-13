#ifndef __FISH_HABITAT_H
#define __FISH_HABITAT_H

#include <string>

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
    Exit,

    HabitatTypeCountSentinel
};

enum class LargeHabitatType {
    Delta,
    Freshwater,
    Intertidal,
    Offshore,

    LargeHabitatTypeCountSentinel
};

struct Habitat {
    HabitatType fine;
    LargeHabitatType large;

    Habitat() : fine(HabitatType::Distributary), large(getDefaultLargeHabitat(HabitatType::Distributary)) {}
    explicit Habitat(HabitatType fine) : fine(fine), large(getDefaultLargeHabitat(fine)) {}
    Habitat(HabitatType fine, LargeHabitatType large) : fine(fine), large(large) {}

    bool isDistributary(bool includeDistributaryEdge = true) const;
    bool isHarbor() const;
    bool isNearshore() const;
    bool isBlindChannel() const;
    bool isImpoundment() const;
    bool isDistributaryOrHarbor() const;
    bool isDistributaryOrNearshore() const;
    bool isDistributaryWithoutEdgeOrIsNearshore() const;

    float getMortalityConst(float habitatMortalityMultiplier) const;

    std::string toString() const;
    static std::string toString(HabitatType type);
    static std::string toString(LargeHabitatType type);
    static HabitatType fromString(const std::string& name);
    static LargeHabitatType largeFromString(const std::string& name);
    static bool tryParse(const std::string& name, HabitatType& out);
    static bool tryParse(const std::string& name, LargeHabitatType& out);
    static bool tryParse(const std::string& name, Habitat& out);

    static LargeHabitatType getDefaultLargeHabitat(HabitatType fine);

    bool operator==(const Habitat& other) const { return fine == other.fine && large == other.large; }
    bool operator!=(const Habitat& other) const { return !(*this == other); }
    bool operator==(HabitatType other) const { return fine == other; }
    bool operator!=(HabitatType other) const { return fine != other; }
    bool operator==(LargeHabitatType other) const { return large == other; }
    bool operator!=(LargeHabitatType other) const { return large != other; }
};

#endif // __FISH_HABITAT_H
