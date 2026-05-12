//
// Created by Troy Frever on 5/11/26.
//

#include <fstream>
#include "initial_population.h"
#include "model.h"
#include "util.h"

#include <iostream>

#include "load.h"

std::vector<InitialPopulation> InitialPopulation::parseFromConfig(const rapidjson::Document& doc) {
    std::vector<InitialPopulation> allInitialPopulations;

    // Check if "recruitClasses" exists and is an array
    if (doc.HasMember("initialPopulations") && doc["initialPopulations"].IsArray()) {
        const rapidjson::Value& populationsArray = doc["initialPopulations"];

        // Iterate through each object in the array
        for (rapidjson::SizeType i = 0; i < populationsArray.Size(); i++) {
            const rapidjson::Value& populationObj = populationsArray[i];
            InitialPopulation population;

            if (populationObj.HasMember("name") && populationObj["name"].IsString()) {
                population.name = populationObj["name"].GetString();
            }

            if (populationObj.HasMember("entryNodes") && populationObj["entryNodes"].IsArray()) {
                const rapidjson::Value& nodesArray = populationObj["entryNodes"];
                for (rapidjson::SizeType j = 0; j < nodesArray.Size(); j++) {
                    if (nodesArray[j].IsInt()) {
                        population.entryNodeIds.push_back(nodesArray[j].GetInt());
                    }
                }
            }

            if (populationObj.HasMember("countsFile") && populationObj["countsFile"].IsString()) {
                population.countsFile = populationObj["countsFile"].GetString();
            }

            if (populationObj.HasMember("sizesFile") && populationObj["sizesFile"].IsString()) {
                population.sizesFile = populationObj["sizesFile"].GetString();
            }

            allInitialPopulations.push_back(population);
        }
    }
    return allInitialPopulations;
}

void InitialPopulation::loadRecSizeDists() {
    std::ifstream f;
    f.open(sizesFile);
    std::string line;
    bool first = true;
    // Get lines from the file until it's empty
    while (std::getline(f, line)) {
        if (first) {
            // Skip the first line since it's a header with field names
            first = false;
            continue;
        }

        if (!line.empty()) {
            // Put a new list (to hold this row) on the output list
            recSizeDists.emplace_back();
            // Get a reference to it
            std::vector<float> &dist = recSizeDists.back();
            // Convert each comma-separated field into a float
            for (const std::string& chunk : split(line, ',')) {
                dist.push_back(std::stof(chunk));
            }
        }
    }
}

void InitialPopulation::initializeRecDayPlan() {
        recDayPlan.resize(24, 0UL);
}

void InitialPopulation::loadRecruitCounts() {
        loadIntList(countsFile, recCounts);
}

void InitialPopulation::readAndInitializeData() {
    loadRecruitCounts();
    loadRecSizeDists();
    initializeRecDayPlan();
}

void InitialPopulation::setRecruitPoints(const std::vector<MapNode *> &dest,
    const std::unordered_map<unsigned int, unsigned int> &csvIdToInternalIndex) {
    for (unsigned id : entryNodeIds) {
        if (!csvIdToInternalIndex.count(id)) {
            std::cerr << "Recruitment node " << id << " doesn't exist" << std::endl;
            continue;
        }
        recPoints.push_back(dest[csvIdToInternalIndex.at(id)]);
    }
}

void InitialPopulation::recruit(Model &model) {
    // Get the current timestep's recruit count from the day's recruit "plan"
    size_t currRecCount = recDayPlan[model.time % 24];
    // Recruit that many fish
    for (size_t i = 0; i < currRecCount; ++i) {
        recruitSingle(model);
    }
}

void InitialPopulation::recruitSingle(Model &model) {
    // Get the current slice of the recruit size distribution data
    constexpr unsigned TIMESTEPS_IN_DAY = 24;
    constexpr unsigned DAYS_IN_WEEK = 7;
    constexpr unsigned TIMESTEPS_IN_WEEK = TIMESTEPS_IN_DAY * DAYS_IN_WEEK;
    const size_t recruitWeek = (model.time + model.recTimeIntercept) / (TIMESTEPS_IN_WEEK);
    const size_t recruitWeekIndex = std::min(recruitWeek, recSizeDists.size() - 1);
    const std::vector<float> &recSizeDist = recSizeDists[recruitWeekIndex];

    // Sample the fork length bucket index from the distribution
    unsigned flIdx = sample(recSizeDist.data(), recSizeDist.size());
    // Calculate the fork length from the bucket index
    float forkLength = 35.0f + 5.0f * flIdx + unit_rand() * 5.0f;
    // Construct a fish and place it in the *ALL* fish list
    model.individuals.emplace_back(
        // This gets the new fish's ID (current val of nextFishID) and then updates nextFishID
        model.nextFishID++,
        model.time,
        forkLength,
        // This samples a random (uniform) recruit start node
        recPoints[GlobalRand::int_rand(0, (int) recPoints.size() - 1)]
    );
    // model.addHistoryBuffers();
    const size_t last_id = model.individuals.back().id;
    model.tagIndividual(last_id);
    // Place the new fish's ID in the living fish list
    model.livingIndividuals.push_back(last_id);
}

void InitialPopulation::planRecruitment(long time, int recTimeIntercept) {
    // Wipe whatever's in the plan array right now
    for (size_t i = 0; i < 24; ++i) {
        recDayPlan[i] = 0;
    }
    // Get the day's daily recruit count
    size_t count = recCounts[(time + recTimeIntercept) / 24];
    // For each recruit in the day, place it in a random timestep's slot
    for (size_t i = 0; i < count; ++i) {
        size_t timestep = GlobalRand::int_rand(0, 23);
        ++recDayPlan[timestep];
    }
}

