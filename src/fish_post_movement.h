#ifndef FISH_POST_MOVEMENT_H
#define FISH_POST_MOVEMENT_H

class Fish;

class FishPostMovement {
public:
    static float calculateExitProbability(float forkLength);
    static bool shouldExit(Fish& fish);
};

#endif // FISH_POST_MOVEMENT_H
