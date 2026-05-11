//
// Created by Troy Frever on 5/11/26.
//

#include <fstream>
#include "initial_population.h"

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
    const std::unordered_map<unsigned int, unsigned int> &csvIdToLocalIndex) {
    for (unsigned id : entryNodeIds) {
        if (!csvIdToLocalIndex.count(id)) {
            std::cerr << "Recruitment node " << id << " doesn't exist" << std::endl;
        }
        recPoints.push_back(dest[csvIdToLocalIndex.at(id)]);
    }
}

