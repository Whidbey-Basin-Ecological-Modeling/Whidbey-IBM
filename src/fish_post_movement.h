#ifndef FISH_POST_MOVEMENT_H
#define FISH_POST_MOVEMENT_H

#include "util.h"

class Fish;

class FishPostMovement {
public:
    static float calculateExitProbability(float forkLength);
    static bool shouldExit(Fish& fish, float (*rand_func)() = unit_rand);
};

#endif // FISH_POST_MOVEMENT_H
