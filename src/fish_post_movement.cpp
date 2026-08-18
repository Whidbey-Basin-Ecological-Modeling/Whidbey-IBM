#include "fish_post_movement.h"
#include "fish.h"

#include <algorithm>

float FishPostMovement::calculateExitProbability(float forkLength) {
    float baseProb = (forkLength - 25.0f) / 100.0f;
    return std::clamp(baseProb, 0.0f, 1.0f);
}

bool FishPostMovement::shouldExit(Fish& fish, float (*/*rand_func*/)()) {
    if (fish.location == nullptr || fish.location->type != HabitatType::Exit) {
        return false;
    }
    return false;
}
