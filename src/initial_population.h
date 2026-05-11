//
// Created by Troy Frever on 4/7/26.
//

#ifndef RECRUIT_POPULATION_H
#define RECRUIT_POPULATION_H

#include <vector>
#include <rapidjson/document.h>

class MapNode;

class InitialPopulation {
public:
    InitialPopulation() = default;

    std::string name;

    // Loaded daily recruit counts (see CONFIG_README for file format)
    std::vector<int> recCounts;

    // Loaded weekly recruit size distributions (see CONFIG_README for file format)
    std::vector<std::vector<float>> recSizeDists;

    // Map locations at which recruits are added
    std::vector<MapNode *> recPoints;

    // A list of per-timestep recruit counts, resampled once per day such that sum(recDayPlan) == recCounts[day]
    std::vector<size_t> recDayPlan;

    // original config file initializer values
    std::string countsFile;
    std::string sizesFile;
    std::vector<unsigned> entryNodeIds;

    static std::vector<InitialPopulation> parseFromConfig(const rapidjson::Document& doc);
};

#endif
