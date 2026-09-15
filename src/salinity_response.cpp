#include "salinity_response.h"
#include "model.h"
#include "hydro.h"
#include "map.h"
#include <cmath>

static constexpr double L_50 = 65.0;      // mm, size at which 50% preference is reached
static constexpr double K_STEEP = 0.1;    // steepness of the sigmoid
static constexpr double BIAS_WEIGHT = 0.2;   // global scaling for salinity importance, 0.0 - 1.0
static constexpr double SALINITY_MAX = 32.0; // maximum salinity for normalization

float SalinityResponse::calculateSalinityBias(float forkLength, float nodeSalinity) {
    const double saltPreferenceSigmoidNormal = 1.0 / (1.0 + std::exp(-K_STEEP * (forkLength - L_50)));
    const double salinityNormal = std::min(nodeSalinity / SALINITY_MAX, 1.0);
    const double suitabilityMatchNormal = 1.0 - std::abs(saltPreferenceSigmoidNormal - salinityNormal);
    const double scaledBoundedMultiplier = 1.0 + BIAS_WEIGHT * (2.0 * suitabilityMatchNormal - 1.0);
    return scaledBoundedMultiplier;
}

float SalinityResponse::calculateSalinityBias(Model &model, MapNode &loc, float forkLength) {
    float nodeSalinity = model.hydroModel.getSalinity(loc);
    return calculateSalinityBias(forkLength, nodeSalinity);
}
