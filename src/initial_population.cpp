//
// Created by Troy Frever on 5/11/26.
//

#include "initial_population.h"

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
