#include "salinity_response.h"
#include "model.h"
#include "hydro.h"
#include "map.h"
#include <cmath>
#include <iostream>

// static constexpr double L_50 = 65.0;      // mm, size at which 50% preference is reached
// static constexpr double K_STEEP = 0.1;    // steepness of the sigmoid
// static constexpr double BIAS_WEIGHT = 0.2;   // global scaling for salinity importance, 0.0 - 1.0
// static constexpr double SALINITY_MAX = 32.0; // maximum salinity for normalization
//
// float SalinityResponse::calculateSalinityBias(float forkLength, float nodeSalinity) {
//     const double saltPreferenceSigmoidNormal = 1.0 / (1.0 + std::exp(-K_STEEP * (forkLength - L_50)));
//     const double salinityNormal = std::min(nodeSalinity / SALINITY_MAX, 1.0);
//     const double suitabilityMatchNormal = 1.0 - std::abs(saltPreferenceSigmoidNormal - salinityNormal);
//     const double scaledBoundedMultiplier = 1.0 + BIAS_WEIGHT * (2.0 * suitabilityMatchNormal - 1.0);
//     if ( (forkLength > 70 && salinityNormal < 0.5) && nodeSalinity > 0.0) {
//         std::cout << "Fork length: " << forkLength
//                     << ", salt pref norm: " << saltPreferenceSigmoidNormal
//                     << ", salinity: " << nodeSalinity
//                     << ", salinity normalized: " << salinityNormal
//                     << ", suitability: " << suitabilityMatchNormal
//                     << ", scaled multiplier: " << scaledBoundedMultiplier
//                     << std::endl;
//     }
//     return scaledBoundedMultiplier;
// }

static constexpr double L_50 = 65.0;         // mm, size at which neutral preference is reached
static constexpr double K_STEEP = 0.1;       // steepness of the sigmoid
static constexpr double BIAS_WEIGHT = 0.9;   // global scaling for salinity importance, 0.0 - 1.0
static constexpr double SALINITY_MAX = 32.0;
static constexpr double SALINITY_MID = SALINITY_MAX / 2.0; // midpoint for salinity normalization

float SalinityResponse::calculateSalinityBias(float forkLength, float nodeSalinity) {
    // 1. Directional Fish Preference: ranges from ~ -1.0 (fresh) to ~ 1.0 (salt)
    const double saltPreferenceSigmoid = (2.0 / (1.0 + std::exp(-K_STEEP * (forkLength - L_50)))) - 1.0;

    // 2. Directional Salinity: ranges from -1.0 (0 salinity) to 1.0 (32 salinity)
    // Clamp node salinity just in case it exceeds MAX
    const double upperSalinityClamp = std::min((double)nodeSalinity, SALINITY_MAX);
    const double clampedSalinity = std::max(0.0, upperSalinityClamp);
    const double directionalSalinity = (clampedSalinity - SALINITY_MID) / SALINITY_MID;

    // 3. Match: positive if they agree, negative if they disagree
    const double match = saltPreferenceSigmoid * directionalSalinity;

    // 4. Scaled Multiplier: bounded between (1 - BIAS_WEIGHT) and (1 + BIAS_WEIGHT)
    const double scaledBoundedMultiplier = 1.0 + (BIAS_WEIGHT * match);
    //
    // if ( (forkLength > 70 && directionalSalinity < 0.0) && nodeSalinity > 0.0) {
    //     std::cout << "Fork length: " << forkLength
    //                 << ", salt pref (dir): " << saltPreferenceSigmoid
    //                 << ", salinity: " << nodeSalinity
    //                 << ", salinity (dir): " << directionalSalinity
    //                 << ", match: " << match
    //                 << ", scaled multiplier: " << scaledBoundedMultiplier
    //                 << std::endl;
    // }
    return scaledBoundedMultiplier;
}

float SalinityResponse::calculateSalinityBias(Model &model, MapNode &loc, float forkLength) {
    float nodeSalinity = model.hydroModel.getSalinity(loc);
    return calculateSalinityBias(forkLength, nodeSalinity);
}
