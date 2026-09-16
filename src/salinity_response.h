#ifndef SALINITY_RESPONSE_H
#define SALINITY_RESPONSE_H

class Model;
class MapNode;

class SalinityResponse {
public:
    static float calculateSalinityBias(
        float forkLength,
        float nodeSalinity,
        float attractionLength = 65.0f,
        float sigmoidSteepness = 0.1f,
        float biasWeight = 0.2f
    );
    static float calculateSalinityBias(Model &model, MapNode &loc, float forkLength);
};

#endif // SALINITY_RESPONSE_H
