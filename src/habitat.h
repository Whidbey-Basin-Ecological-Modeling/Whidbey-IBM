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
    Impoundment, //TODO: remove
    LowTideTerrace, //TODO: remove
    DistributaryEdge, //TODO: remove
    Nearshore, //TODO: remove
    SubtidalFlat, //TODO: remove

    Distributary,
    BlindChannel,

    Creek,
    Mainstem,

    Beach,
    Mudflat,
    Rock,
    Harbor,
    Riprap,
    Eelgrass,
    Lagoon,

    Kelp,
    OpenWater,
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

enum class HabitatStructure {
    Simplified,
    Neutral,
    Complex,

    HabitatStructureCountSentinel
};

struct Habitat {
    HabitatType fine;
    LargeHabitatType large;
    HabitatStructure structure;

    Habitat() : fine(HabitatType::Distributary), large(getDefaultLargeHabitat(HabitatType::Distributary)), structure(HabitatStructure::Neutral) {}
    explicit Habitat(HabitatType fine) : fine(fine), large(getDefaultLargeHabitat(fine)), structure(getDefaultStructure(fine, getDefaultLargeHabitat(fine))) {}
    Habitat(HabitatType fine, LargeHabitatType large) : fine(fine), large(large), structure(getDefaultStructure(fine, large)) {}
    Habitat(HabitatType fine, LargeHabitatType large, HabitatStructure structure) : fine(fine), large(large), structure(structure) {}

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
    static std::string toString(HabitatStructure structure);
    static HabitatType fromString(const std::string& name);
    static LargeHabitatType largeFromString(const std::string& name);
    static HabitatStructure structureFromString(const std::string& name);
    static bool tryParse(const std::string& name, HabitatType& out);
    static bool tryParse(const std::string& name, LargeHabitatType& out);
    static bool tryParse(const std::string& name, HabitatStructure& out);
    static bool tryParse(const std::string& name, Habitat& out);

    static LargeHabitatType getDefaultLargeHabitat(HabitatType fine);
    static HabitatStructure getDefaultStructure(HabitatType fine, LargeHabitatType large);

    bool operator==(const Habitat& other) const { return fine == other.fine && large == other.large && structure == other.structure; }
    bool operator!=(const Habitat& other) const { return !(*this == other); }
    bool operator==(HabitatType other) const { return fine == other; }
    bool operator!=(HabitatType other) const { return fine != other; }
    bool operator==(LargeHabitatType other) const { return large == other; }
    bool operator!=(LargeHabitatType other) const { return large != other; }
    bool operator==(HabitatStructure other) const { return structure == other; }
    bool operator!=(HabitatStructure other) const { return structure != other; }
};

#endif // __FISH_HABITAT_H
