#include "predation.h"
#include <array>
#include <stdexcept>

namespace {

struct ForkLengthRange {
    double min_fl;
    double max_fl;
};

constexpr std::array<ForkLengthRange, static_cast<size_t>(PredatorGroup::PredatorGroupCountSentinel)> PREDATOR_SIZE_RANGES = {{
    {30.0, 100.0}, // SurfaceFish
    {30.0, 100.0}, // DemersalFish
    {80.0, 300.0}, // Otter
    {100.0, 500.0}, // Seal
    {100.0, 400.0}, // Porpoise
    {100.0, 1000.0}, // SeaLion
    {30.0, 300.0}, // DivingBird
    {30.0, 200.0}, // WadingBirdLg
    {30.0, 60.0},  // WadingBirdSm
    {150.0, 500.0}, // CarnivoreBird
    {30.0, 200.0}   // SurfacePeckingBird
}};

// Matrix indexed by [PredatorGroup][LargeHabitatType][TimeWindow]
// TimeWindow: 0 for hour < 2500 (t1), 1 for hour >= 2500 (t2)
// LargeHabitatType: Delta(0), Freshwater(1), Intertidal(2), Offshore(3)
constexpr double PREDATOR_RELATIVE_DENSITY[static_cast<size_t>(PredatorGroup::PredatorGroupCountSentinel)][static_cast<size_t>(LargeHabitatType::LargeHabitatTypeCountSentinel)][2] = {
    // SurfaceFish
    {
        {0.1, 0.3},   // Delta
        {0.05, 0.05}, // Freshwater
        {0.05, 0.15}, // Intertidal
        {0.1, 0.2}    // Offshore
    },
    // DemersalFish
    {
        {0.05, 0.1},  // Delta
        {0.02, 0.03}, // Freshwater
        {0.1, 0.2},   // Intertidal
        {0.2, 0.3}    // Offshore
    },
    // Otter
    {
        {0.15, 0.15}, // Delta
        {0.25, 0.25}, // Freshwater
        {0.1, 0.1},   // Intertidal
        {0.0, 0.0}    // Offshore
    },
    // Seal
    {
        {0.05, 0.15}, // Delta
        {0.0, 0.0},   // Freshwater
        {0.3, 0.3},   // Intertidal
        {0.1, 0.1}    // Offshore
    },
    // Porpoise
    {
        {0.0, 0.0}, // Delta
        {0.0, 0.0}, // Freshwater
        {0.1, 0.1}, // Intertidal
        {0.4, 0.4}  // Offshore
    },
    // SeaLion
    {
        {0.0, 0.0},   // Delta
        {0.0, 0.0},   // Freshwater
        {0.05, 0.1},  // Intertidal
        {0.25, 0.6}   // Offshore
    },
    // DivingBird
    {
        {0.05, 0.1},  // Delta
        {0.05, 0.1},  // Freshwater
        {0.1, 0.1},   // Intertidal
        {0.25, 0.25}  // Offshore
    },
    // WadingBirdLg
    {
        {0.2, 0.1},   // Delta
        {0.07, 0.03}, // Freshwater
        {0.4, 0.2},   // Intertidal
        {0.0, 0.0}    // Offshore
    },
    // WadingBirdSm
    {
        {0.2, 0.1},   // Delta
        {0.07, 0.03}, // Freshwater
        {0.4, 0.2},   // Intertidal
        {0.0, 0.0}    // Offshore
    },
    // CarnivoreBird
    {
        {0.1, 0.2},   // Delta
        {0.1, 0.1},   // Freshwater
        {0.1, 0.2},   // Intertidal
        {0.07, 0.13}  // Offshore
    },
    // SurfacePeckingBird
    {
        {0.04, 0.04}, // Delta
        {0.01, 0.01}, // Freshwater
        {0.2, 0.2},   // Intertidal
        {0.25, 0.25}  // Offshore
    }
};

} // namespace

double PredationMortality::getHabitatBaselineConst(HabitatStructure structure) {
    switch (structure) {
        case HabitatStructure::Complex:
            return 0.5;
        case HabitatStructure::Neutral:
            return 1.0;
        case HabitatStructure::Simplified:
            return 1.5;
        default:
            throw std::invalid_argument("Invalid HabitatStructure enum value");
    }
}

bool PredationMortality::isPredatorActive(PredatorGroup group, double forkLength) {
    auto groupIdx = static_cast<size_t>(group);
    if (groupIdx >= static_cast<size_t>(PredatorGroup::PredatorGroupCountSentinel)) {
        throw std::invalid_argument("Invalid PredatorGroup enum value");
    }
    const auto& range = PREDATOR_SIZE_RANGES[groupIdx];
    return forkLength >= range.min_fl && forkLength <= range.max_fl;
}

double PredationMortality::getPredatorRelativeDensity(PredatorGroup group, LargeHabitatType largeHabitat, int hour) {
    auto groupIdx = static_cast<size_t>(group);
    if (groupIdx >= static_cast<size_t>(PredatorGroup::PredatorGroupCountSentinel)) {
        throw std::invalid_argument("Invalid PredatorGroup enum value");
    }
    auto habIdx = static_cast<size_t>(largeHabitat);
    if (habIdx >= static_cast<size_t>(LargeHabitatType::LargeHabitatTypeCountSentinel)) {
        throw std::invalid_argument("Invalid LargeHabitatType enum value");
    }
    int timeIdx = (hour < PREDATION_TIME_WINDOW_CUTOFF_HOUR) ? 0 : 1;
    return PREDATOR_RELATIVE_DENSITY[groupIdx][habIdx][timeIdx];
}


double PredationMortality::calculateActivePredatorRelativeDensitySum(LargeHabitatType largeHabitat, int hour, double forkLength) {
    double sum = 0.0;
    for (size_t g = 0; g < static_cast<size_t>(PredatorGroup::PredatorGroupCountSentinel); ++g) {
        auto predatorGroup = static_cast<PredatorGroup>(g);
        if (isPredatorActive(predatorGroup, forkLength)) {
            sum += getPredatorRelativeDensity(predatorGroup, largeHabitat, hour);
        }
    }
    return sum;
}

double PredationMortality::calculateHabitatTypeConst(const Habitat& habitat, int hour, double forkLength) {
    double habitatConst = getHabitatBaselineConst(habitat.structure());
    double predatorSum = calculateActivePredatorRelativeDensitySum(habitat.largeType(), hour, forkLength);
    return PREDATION_Z_SCALING * habitatConst * (1.0 + predatorSum);
}
