#include "salinity_response.h"
#include "model.h"
#include "hydro.h"
#include <algorithm>
#include <cmath>

static constexpr double SALINITY_MAX = 32.0;
static constexpr double SALINITY_MID = SALINITY_MAX / 2.0; // midpoint for salinity normalization

float SalinityResponse::calculateSalinityBias(
    float forkLength,
    float nodeSalinity,
    float attractionLength,
    float sigmoidSteepness,
    float biasWeight
) {
    // Intermediate directional variables range from -1.0 (fresh water) to 1.0 (salt water)
    const double directionalFishPreference = (2.0 / (1.0 + std::exp(-sigmoidSteepness * (forkLength - attractionLength)))) - 1.0;
    const double clampedSalinity = std::clamp(static_cast<double>(nodeSalinity), 0.0, SALINITY_MAX);
    const double directionalSalinity = (clampedSalinity - SALINITY_MID) / SALINITY_MID;
    const double directionalPreferenceMatch = directionalFishPreference * directionalSalinity;
    const double scaledBoundedMultiplier = 1.0 + (biasWeight * directionalPreferenceMatch);
    return scaledBoundedMultiplier;
}

float SalinityResponse::calculateSalinityBias(Model &model, MapNode &loc, float forkLength) {
    float nodeSalinity = model.hydroModel.getSalinity(loc);
    float attractionLength = model.getFloat(ModelParamKey::SalinityAttractionLength);
    float sigmoidSteepness = model.getFloat(ModelParamKey::SalinitySigmoidSteepness);
    float biasWeight = model.getFloat(ModelParamKey::SalinityBiasWeight);
    return calculateSalinityBias(forkLength, nodeSalinity, attractionLength, sigmoidSteepness, biasWeight);
}
