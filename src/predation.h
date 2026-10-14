#ifndef __FISH_PREDATION_H
#define __FISH_PREDATION_H

#include "habitat.h"

enum class PredatorGroup {
    SurfaceFish,
    DemersalFish,
    Otter,
    Seal,
    Porpoise,
    SeaLion,
    DivingBird,
    WadingBirdLg,
    WadingBirdSm,
    CarnivoreBird,
    SurfacePeckingBird,

    PredatorGroupCountSentinel
};

class PredationMortality {
public:
    static constexpr double PREDATION_Z_SCALING = 0.6;
    static constexpr int PREDATION_TIME_WINDOW_CUTOFF_HOUR = 2500;

    static double getHabitatBaselineConst(HabitatStructure structure);
    static bool isPredatorActive(PredatorGroup group, double forkLength);
    static double getPredatorRelativeDensity(PredatorGroup group, LargeHabitatType largeHabitat, int hour);
    static double calculateActivePredatorRelativeDensitySum(LargeHabitatType largeHabitat, int hour, double forkLength);
    static double calculateHabitatTypeConst(const Habitat& habitat, int hour, double forkLength);
};

#endif // __FISH_PREDATION_H
