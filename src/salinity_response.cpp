#include "salinity_response.h"
#include "model.h"
#include "hydro.h"
#include "map.h"
#include <cmath>

static constexpr double L_50 = 75.0;      // mm, size at which 50% preference is reached
static constexpr double K_STEEP = 0.2;    // steepness of the sigmoid
static constexpr double BETA = 2.0;       // global scaling for salinity importance

float SalinityResponse::calculateSalinityBias(float forkLength, float nodeSalinity) {
    // 1. Calculate the physiological 'drive' (0.0 to 1.0) using double precision
    double drive = 1.0 / (1.0 + std::exp(-K_STEEP * (static_cast<double>(forkLength) - L_50)));
    
    // 2. Return the exponential weight calculated in double precision
    return static_cast<float>(std::exp(BETA * drive * static_cast<double>(nodeSalinity)));
}

float SalinityResponse::calculateSalinityBias(Model &model, MapNode &loc, float forkLength) {
    float nodeSalinity = model.hydroModel.getSalinity(loc);
    return calculateSalinityBias(forkLength, nodeSalinity);
}
