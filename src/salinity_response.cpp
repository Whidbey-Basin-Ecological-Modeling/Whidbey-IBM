#include "salinity_response.h"
#include "model.h"
#include "hydro.h"
#include "map.h"
#include <algorithm>
#include <cmath>
#include <iostream>

static constexpr double L_50 = 65.0;         // mm, size at which neutral preference is reached
static constexpr double K_STEEP = 0.1;       // steepness of the sigmoid
static constexpr double BIAS_WEIGHT = 0.2;   // global scaling for salinity importance, 0.0 - 1.0
static constexpr double SALINITY_MAX = 32.0;
static constexpr double SALINITY_MID = SALINITY_MAX / 2.0; // midpoint for salinity normalization

float SalinityResponse::calculateSalinityBias(float forkLength, float nodeSalinity) {
    // Intermediate directional variables range from -1.0 (fresh water) to 1.0 (salt water)
    const double directionalFishPreference = (2.0 / (1.0 + std::exp(-K_STEEP * (forkLength - L_50)))) - 1.0;
    const double clampedSalinity = std::clamp(static_cast<double>(nodeSalinity), 0.0, SALINITY_MAX);
    const double directionalSalinity = (clampedSalinity - SALINITY_MID) / SALINITY_MID;
    const double directionalPreferenceMatch = directionalFishPreference * directionalSalinity;
    const double scaledBoundedMultiplier = 1.0 + (BIAS_WEIGHT * directionalPreferenceMatch);
    return scaledBoundedMultiplier;
}

float SalinityResponse::calculateSalinityBias(Model &model, MapNode &loc, float forkLength) {
    float nodeSalinity = model.hydroModel.getSalinity(loc);
    return calculateSalinityBias(forkLength, nodeSalinity);
}
