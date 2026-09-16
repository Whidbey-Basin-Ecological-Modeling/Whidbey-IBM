#ifndef SALINITY_RESPONSE_H
#define SALINITY_RESPONSE_H

class Model;
class MapNode;

class SalinityResponse {
public:
    static float calculateSalinityBias(
        float forkLength,
        float nodeSalinity,
        float attractionLength,
        float sigmoidSteepness,
        float biasWeight
    );
    static float calculateSalinityBias(Model &model, MapNode &loc, float forkLength);
};

#endif // SALINITY_RESPONSE_H
