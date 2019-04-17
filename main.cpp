//
//  main.cpp
//  InfluenceMaximization
//
//  Created by Madhavan R.P on 8/4/17.
//  Copyright © 2017 Madhavan R.P. All rights reserved.
//

#include <iostream>
#include "cxxopts.hpp"
#include "InfluenceMaximization/Graph.hpp"
#include "InfluenceMaximization/IMTree.hpp"
#include "InfluenceMaximization/EstimateNonTargets.hpp"
#include "InfluenceMaximization/TIMUtility.hpp"
#include "InfluenceMaximization/Phase2.hpp"
#include "InfluenceMaximization/SeedSet.hpp"
#include "InfluenceMaximization/Diffusion.hpp"
#include "InfluenceMaximization/IMResults/IMResults.h"
#include "InfluenceMaximization/memoryusage.h"
#include <string>
#include <chrono>
#include "InfluenceMaximization/log.h"
#include "InfluenceMaximization/DifferenceApproximator.hpp"
#include "InfluenceMaximization/GenerateGraphLabels.hpp"
#include "InfluenceMaximization/BaselineGreedy.hpp"
#include "InfluenceMaximization/BaselineGreedyTIM.hpp"
#include <stdio.h>

#include <iomanip>
#include <ctime>
#include <sstream>
#include <fstream>
#include <cstdio>
#include <algorithm>
#include <random>

using json = nlohmann::json;
using namespace std;

#define PHASE1TIM_PHASE2TIM 1;
#define PHASE1SIM_PHASE2SIM 2;

int budget;
int nonTargetThreshold;
string graphFileName;
int percentageTargets;
bool fromFile = false;
string nonTargetsFileName;
int method = PHASE1TIM_PHASE2TIM;
bool useIndegree = true;
float probability = 0;
int removeNodes = 0;
string modular;
int topBestThreshold = 100;
int initialSeed;
int newSeed;
int diffusion;
ofstream myfile;
bool fullgraph = false;
ofstream resultLogFile;

//Variables for experimenting
bool useMaxSeed = true;//Set to false if using random Seed for diffusion instead of using maxSeed => Experiment 3
bool someCondition = false;//Set to true if calculating maxSeed BEFORE removing any nodes. Remove nodes ONLY if they arent in maxSeed.

//These are my global variables for testing
vector<int> modNodesToRemoveUnsorted;
vector<int> tGraphNodesToRemoveUnsorted;
vector<int> modImpactNodesToRemoveUnsorted;
vector<int> subModNodesToRemoveUnsorted;
vector<int> nodeMappedToOutdegree;
//Global variables for testing end here


void setupLogger() {//Done
    time_t rawtime;
    //A struct (short for structure) allows us to group variables of mixed data types together into a single unit.
    struct tm *timeinfo;
    char buffer[80];

    time(&rawtime);
    timeinfo = localtime(&rawtime);

    strftime(buffer, sizeof(buffer), "%d-%m-%Y-%I:%M:%S", timeinfo);
    //size_t strftime (char* ptr, size_t maxsize, const char* format, const struct tm* timeptr );
    std::string str(buffer);//I believe this converts the buffer to a string since this is a string constructor?
    FILELog::ReportingLevel() = logDEBUG3;//#include "InfluenceMaximization/log.h"//Include this library
    string logFileName =
            "logs/influence-" + str + ".log";//Sample of logFileName: logs/influence-19-01-2019-02:20:39.log
    FILE *log_fd = fopen(logFileName.c_str(), "w");
    Output2FILE::Stream() = log_fd;
}

void print2DVector(const vector<vector<int>> myVector) {

    for (int i = 0; i < myVector.size(); i++) {
        if (myVector[i].size() > 0) {
            cout << i << " ---> ";
            for (int j = 0; j < myVector[i].size(); j++) {
                cout << myVector[i][j] << " -- ";
            }
            cout << endl;
        }
    }
    cout << "-----Completed Printing 2D Vector----" << endl;
}

void printVector(const vector<int> myVector) {

    for (int i = 0; i < myVector.size(); i++) {
        myfile << i << ":" << myVector[i] << " ";
    }
    myfile << endl;
    myfile << "-----Completed Printing Vector----" << endl;
}

void printSet(const set<int> myVector) {

    for (int const myInt: myVector) {
        cout << myInt << " ";
        myfile << myInt << " ";
    }

    cout << endl;
    myfile << endl;
    cout << "-----Completed Printing Set-----" << endl;
}

bool sortbysecdesc(const pair<int, int> &a, const pair<int, int> &b) {
    return (a.second > b.second);
}

bool sortBySecDescFloat(const pair<int, float> &a, const pair<int, float> &b) {
    return (a.second > b.second);
}

bool sortbydegree(const int &a, const int &b) {
    return (a > b);
}

void testApprox(Graph *graph, int budget, ApproximationSetting setting, bool extendPermutation) {
    DifferenceApproximator differenceApproximator(graph);
    differenceApproximator.setN(graph->n);
    set<int> seedSet;
    vector<int> permutation = differenceApproximator.generatePermutation();
    ModularApproximation modularApprox(permutation, setting);
    modularApprox.createTIMEvaluator(graph);
    modularApprox.findAllApproximations();
    if (setting == setting3) {
        if (!extendPermutation) {
            seedSet = differenceApproximator.executeAlgorithmApproximatingOneFunction(setting, budget);
        } else {
            seedSet = differenceApproximator.executeAlgorithmApproximatingOneFunctionExtendPermutation(setting, budget);
        }
    } else {
        if (!extendPermutation) {
            seedSet = differenceApproximator.executeGreedyAlgorithm(graph, &modularApprox, budget);
        } else {
            seedSet = differenceApproximator.executeGreedyAlgorithmAdjustingPermutation(setting, budget);
        }
    }
    pair<int, int> influence = findInfluenceUsingDiffusion(graph, seedSet, NULL);
    cout << "\n Results after Diffusion: ";
    cout << "\nInfluence Targets: " << influence.first;
    cout << "\nInfluence NT: " << influence.second;
    IMResults::getInstance().setApproximationInfluence(influence);

}

void loadResultsFileFrom(cxxopts::ParseResult result) {//Done, I guess?
    // Necessary paramters
    int budget = result["budget"].as<int>();
    string graphFileName = result["graph"].as<std::string>();
    int percentageTargets = result["percentage"].as<int>();
    float percentageTargetsFloat = (float) percentageTargets /
                                   (float) 100;//Local variable 'percentageTargetsFloat' is only assigned but never accessed
    string algorithm = result["algorithm"].as<string>();
    //  Stupid thing does not work
    //  newExe.exe --algorithm=bfs --seedset=10 --graph=anotherTry --budget=20 --percentage=15
    //  Ok, I was being stupid
    //  You need to define these variables in the options.add_options() method first

    //  Not sure what these are doing
    //  I think whats going on is that they are reading the inputs from the commandline
    //  and then storing the values in the corresponding variable somewhere
    IMResults::getInstance().setBudget(budget);
    IMResults::getInstance().setGraphName(graphFileName);
    IMResults::getInstance().setPercentageTargets(
            percentageTargets);//Quest: Shouldn't this be percentageTargetsFloat instead?
    IMResults::getInstance().setAlgorithm(algorithm);

    // Optional parameters
    if (result["threshold"].count() > 0) {
        int nonTargetThreshold = result["threshold"].as<int>();
        IMResults::getInstance().setNonTargetThreshold(nonTargetThreshold);
    }
    IMResults::getInstance().setPropagationProbability(
            "inDegree");//Quest: Shouldn't this be a necessary parameter then?
    if (result.count("p") > 0) {
        double probability = result["p"].as<double>();
        IMResults::getInstance().setPropagationProbability(probability);
    }

    if (result.count("ntfile") > 0) {
        string nonTargetsFileName = result["ntfile"].as<std::string>();
        IMResults::getInstance().setFromFile(true);
        IMResults::getInstance().setNonTargetFileName(nonTargetsFileName);
    }
}

void loadGraphSizeToResults(Graph *graph) {
    IMResults::getInstance().setNumberOfVertices(graph->getNumberOfVertices());
    IMResults::getInstance().setNumberOfEdges(graph->getNumberOfEdges());
}


void checkMod(string graphFileName, float percentageTargetsFloat, Graph *graph, set<int> seedSet, int budget,
              bool useIndegree, float probability) {
    //find seed set through modular approach
    set<int> modseedSet;
    Graph *modGraph = new Graph;
    modGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modGraph->setPropogationProbability(probability);
    }
    int n = (int) modGraph->getNumberOfVertices();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    modGraph->generateRandomRRSetsFromTargets(R, vector<int>(), "modular", resultLogFile);
    vector<pair<int, int>> SortedNodeidCounts = vector<pair<int, int>>();
    for (int i = 0; i < modGraph->NodeinRRsetsWithCounts.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = modGraph->NodeinRRsetsWithCounts[i];
        SortedNodeidCounts.push_back(node);
    }

    vector<int>().swap(modGraph->NodeinRRsetsWithCounts);

    std::sort(SortedNodeidCounts.begin(), SortedNodeidCounts.end(), sortbysecdesc);
    int j = 0;
    cout << "\n Order of mod SeedSet: " << flush;
    resultLogFile << "\n Order of mod SeedSet: " << flush;
    for (int i = 0; i < budget; i++) {
        modseedSet.insert(SortedNodeidCounts[i].first);
        cout << " " << SortedNodeidCounts[i].first;
        resultLogFile << " " << SortedNodeidCounts[i].first;
        if (seedSet.count(SortedNodeidCounts[i].first) == 1)
            j++;
    }
    cout << "\n Selected k mod SeedSet: " << flush;
    resultLogFile << "\n Selected k mod SeedSet: " << flush;
    for (auto item:modseedSet) {
        cout << item << " ";
        resultLogFile << item << " ";
    }
    cout << "\n intersection of submodular and modular " << j;
    resultLogFile << "\n intersection of submodular and modular " << j;
    //intersection of the nodes activated through mod seed set and submod seed set after diffusion
    /*vector<int> activatedSet=performDiffusion(graph,seedSet,NULL);
     cout << "\n submod activated size" <<activatedSet.size();
     
     vector<int> modActivatedSet=performDiffusion(modGraph,modseedSet,NULL);
     cout << "\n mod activated size" <<modActivatedSet.size();
     
     std::sort(modActivatedSet.begin(), modActivatedSet.end());
     std::sort(activatedSet.begin(), activatedSet.end());
     std::vector<int> v_intersection;
     std::set_intersection(modActivatedSet.begin(), modActivatedSet.end(),activatedSet.begin(), activatedSet.end(),std::back_inserter(v_intersection));
     cout << "\n influence intersection of mod and submod" <<v_intersection.size();*/
}

set<int>
getSeed(int numNodes, Graph *graph, vector<int> activatedSet, set<int> modNodes, set<int> subModNodes,
        set<int> removalModImpactNodes, set<int> tGraphNodes,
        vector<int> *seedOrder) {
    vector<vector<int>> lookupTable;
    TIMCoverage timCoverage(&lookupTable);
    double epsilon = 2;
    int n = graph->n;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    graph->generateRandomRRSets(R, true, resultLogFile);
    vector<vector<int>> *randomRRSets = graph->getRandomRRSets();
    timCoverage.initializeLookupTable(randomRRSets, graph->n);
    timCoverage.initializeDataStructures((int) randomRRSets->size(), graph->n);
    unordered_set<int> activatedNodes;
    activatedNodes.insert(activatedSet.begin(), activatedSet.end());
    set<int> seedSet = timCoverage.findTopKNodes(numNodes, randomRRSets, activatedNodes, modNodes,
                                                 removalModImpactNodes,
                                                 subModNodes, tGraphNodes, seedOrder);
    for (int i = 0; i < timCoverage.vectorTopKNodes.size(); i++) {
        myfile << timCoverage.vectorTopKNodes[i] << " ";
    }
    assert(("Discrepancy in seedSet size generated", seedSet.size() == numNodes));
    myfile << endl;
    return seedSet;
}


set<int>
removeVertices(Graph *influencedGraph, int removeNodes, set<int> maxSeedSet, vector<int> activatedSet, string modular) {

    bool tshoot = false;//Prints the graphTranspose after the nodes have been deleted
    bool tshoot1 = true;//Controls the assert statements

    //Random RR sets
    set<int> alreadyinSeed = set<int>();
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);
    cout << "R = " << R << endl;
    influencedGraph->generateRandomRRSetsFromTargets(R, activatedSet, modular, resultLogFile);
    cout << "\n RRsets done " << flush;
    resultLogFile << "\n RRsets done " << flush;

    int modStrength = 0;
    for (int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++) {
        modStrength += influencedGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n Initial Strength is " << modStrength << endl;
    resultLogFile << "\n \n Initial Strength is " << modStrength << endl;
    myfile << modStrength << " <-InitialStrength" << endl;

    //clearing the memory
//    vector<vector<int>>().swap(influencedGraph->rrSets);

    //Find nodes to be removed
    vector<pair<int, int>> SortedNodeidCounts = vector<pair<int, int>>();
    for (int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = influencedGraph->NodeinRRsetsWithCounts[i];
        SortedNodeidCounts.push_back(node);
    }

    //We need to store this initial influencedGraph->NodeinRRsetsWithCounts for the transposedGraph method
    influencedGraph->initialNodeinRRsetsWithCounts = vector<int>(n, 0);
    for (int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++) {
        influencedGraph->initialNodeinRRsetsWithCounts[i] = influencedGraph->NodeinRRsetsWithCounts[i];
    }


    std::sort(SortedNodeidCounts.begin(), SortedNodeidCounts.end(), sortbysecdesc);
    assert(SortedNodeidCounts.at(0).second >= SortedNodeidCounts.at(1).second);
//    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);

    set<int> nodesToRemove;
    int count = 0;
    int j = 0;
    while (j < removeNodes && j < SortedNodeidCounts.size()) {
        int nodeid = SortedNodeidCounts.at(count).first;
        if (nodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid) == 0) {
            nodesToRemove.insert(nodeid);
            //modNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            modNodesToRemoveUnsorted.push_back(nodeid);
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }
    vector<pair<int, int>>().swap(SortedNodeidCounts);
    cout << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing the nodes already in seed that were not added to modNodes" << endl;
    myfile << "Printing the nodes already in seed that were not added to removeNodes" << endl;
    printSet(alreadyinSeed);

    int numEdgesAtStart = influencedGraph->m;
    int totalNumEdgesToDelete = 0;


    for (int nodeToRemove:nodesToRemove) {

        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < influencedGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += influencedGraph->graphTranspose[k].size();
                if (k == nodeToRemove) {
                    numEdgesToDelete += influencedGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < influencedGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += influencedGraph->graph[k].size();
                if (k == nodeToRemove) {
                    numEdgesToDelete += influencedGraph->graph[k].size();
                }
            }
        }

        totalNumEdgesToDelete += numEdgesToDelete;
        influencedGraph->removeOutgoingEdges(nodeToRemove);
        assert(("Here . .. .", influencedGraph->graph[nodeToRemove].size() == 0));
        assert(("Here . .. .", influencedGraph->graphTranspose[nodeToRemove].size() == 0));
        influencedGraph->assertCorrectNodesAreDeleted(nodeToRemove, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                      totalEdgesInTransGraphPre);
    }
    assert(("Mismatch in modNodesToRemove", nodesToRemove.size() == removeNodes));


    if (tshoot1) {
        int totalNumOfEdges = 0;
        for (int k = 0; k < influencedGraph->graph.size(); k++) {
            totalNumOfEdges += influencedGraph->graph[k].size();
        }
        assert(("removeVertices() Divergence betn something", totalNumOfEdges ==
                                                              numEdgesAtStart - totalNumEdgesToDelete));
    }

    if (tshoot) {
        cout << "Printing the transposed graph after the nodes have been deleted: " << endl;
        print2DVector(influencedGraph->graphTranspose);
    }

    influencedGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    modStrength = 0;
    for (int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++) {
        modStrength += influencedGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n After removing Modular Strength is " << modStrength;
    resultLogFile << "\n \n After removing Modular Strength is " << modStrength;
    myfile << modStrength << " <-ModStrength\n";
//    vector<vector<int>>().swap(influencedGraph->rrSets);
//    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);
    return nodesToRemove;
}

set<int> tGraphRemoveVertices(Graph *transposedGraph, Graph *influencedGraph, int removeNodes, set<int> maxSeedSet,
                              vector<int> activatedSet, string modular) {

    bool tshoot = true;
    bool tshoot1 = true;//Control whether the assert statements are executed
    bool tshoot3 = true;//Comparing the results of transposedGraph and modular graph methods
    bool tshoot4 = false;//Comparing the no.of times the vertex was randomly picked with the final strength of that vertex

    set<int> tGraphNodesToRemove;//Stores the nodes that will be removed
    int n = (int) activatedSet.size();
    set<int> alreadyinSeed = set<int>();

    //Calculating R
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "R = " << R << endl;
    transposedGraph->generateRandomRRSetsFromTargets(R, activatedSet, modular, resultLogFile);
    cout << "\n RRsets done " << endl;
    resultLogFile << "\n RRsets done " << endl;

    //Calculating initial strength of the transposedGraph
    int tGraphStrength = 0;
    for (int i = 0; i < transposedGraph->NodeinRRsetsWithCounts.size(); i++) {
        tGraphStrength += transposedGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n\nInitial Strength of transposedGraph is " << tGraphStrength;
    resultLogFile << "\n\nInitial Strength of transposedGraph is " << tGraphStrength;
    myfile << tGraphStrength << " <-InitialStrength of transposedGraph\n";

    //Checking the distribution of the randomness
    if (tshoot4) {
        cout << "Checking the distribution of the randomness" << endl;
        for (int i = 0; i < transposedGraph->timesThisNodeWasPicked.size(); i++) {
            cout << "Vertex " << i << " : " << transposedGraph->timesThisNodeWasPicked[i] << endl;
        }
    }

    //Printing Best Node and its strength in transposed Graph
    if (tshoot) {
        vector<pair<int, int>> sorted = vector<pair<int, int>>();
        for (int i = 0; i < transposedGraph->NodeinRRsetsWithCounts.size(); i++) {
            pair<int, int> node = pair<int, int>();
            node.first = i;
            node.second = transposedGraph->NodeinRRsetsWithCounts[i];
            sorted.push_back(node);
        }

        std::sort(sorted.begin(), sorted.end(), sortbysecdesc);
        assert(sorted.at(0).second >= sorted.at(1).second);

        cout << "\nPrinting Best Node and its strength in transposed Graph" << endl;
        cout << "Node tGraph.Strength * originalGraph.Strength TimesItWasPicked " << endl;
        for (int i = 0; i < removeNodes; i++) {
            pair<int, int> node = sorted[i];
            cout << node.first << ": " << node.second << " * "
                 << influencedGraph->initialNodeinRRsetsWithCounts[node.first] << " " <<
                 (float) influencedGraph->initialNodeinRRsetsWithCounts[node.first] * node.second << " " <<
                 transposedGraph->timesThisNodeWasPicked[sorted[i].first] <<
                 endl;
        }
    }

    //Multiplying the strength of each node in influencedGraph->initialNodeinRRsetsWithCounts with transposedGraph->NodeinRRsetsWithCounts
    //This will give the combined strength of each vertex in the original as well as the transposedGrraph
    //This will then be used for selecting the nodes to be removed
    vector<pair<int, float>> SortedNodeIdByCount = vector<pair<int, float>>();
    for (int i = 0; i < transposedGraph->NodeinRRsetsWithCounts.size(); i++) {
        pair<int, float> node = pair<int, float>();
        node.first = i;
        node.second =
                (float) transposedGraph->NodeinRRsetsWithCounts[i] * influencedGraph->initialNodeinRRsetsWithCounts[i];
        assert(node.second >= 0);
        SortedNodeIdByCount.push_back(node);
    }

    std::sort(SortedNodeIdByCount.begin(), SortedNodeIdByCount.end(), sortBySecDescFloat);
    assert(SortedNodeIdByCount.at(0).second >= SortedNodeIdByCount.at(1).second);

    //Printing Best Node after multiplying
    if (tshoot) {
        cout << "Printing Best Node after multiplying" << endl;
        cout << "Node transposedGraph.strength influencedGraph.strength" << endl;
        for (int i = 0; i < removeNodes; i++) {
            cout << "Node: " << SortedNodeIdByCount[i].first << " - "
                 << transposedGraph->NodeinRRsetsWithCounts[SortedNodeIdByCount[i].first] << " * "
                 << influencedGraph->initialNodeinRRsetsWithCounts[SortedNodeIdByCount[i].first] << " = "
                 << SortedNodeIdByCount[i].second << endl;
        }
    }

    //Adding nodes to tGraphNodesToRemove
    int count = 0;
    int j = 0;
    tGraphNodesToRemoveUnsorted = vector<int>();

    while (j < removeNodes && j < SortedNodeIdByCount.size()) {
        int nodeid = SortedNodeIdByCount.at(count).first;
        if (tGraphNodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid)==0) {
            tGraphNodesToRemove.insert(nodeid);
            //tGraphNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            tGraphNodesToRemoveUnsorted.push_back(nodeid);
            j++;
        }else{
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }
    assert(("Mismatch in tGraphNodesToRemove", tGraphNodesToRemove.size() == removeNodes));

    //Nodes removed from modGraph with their transposedGraph values
    if (tshoot3) {
        cout << endl;
        cout << "Nodes removed from modGraph with their transposedGraph values" << endl;
        cout << "RemovedNode\tModGraphStrength\ttransposedGraphStrength\ttotalStrength" << endl;
        for (int i = 0; i < modNodesToRemoveUnsorted.size(); i++) {
            int currNode = modNodesToRemoveUnsorted[i];
            float totStr = influencedGraph->initialNodeinRRsetsWithCounts[currNode] *
                           transposedGraph->NodeinRRsetsWithCounts[currNode];
            cout << currNode << "-\t "
                 << influencedGraph->initialNodeinRRsetsWithCounts[currNode] << "*\t "
                 << transposedGraph->NodeinRRsetsWithCounts[currNode] << " =\t "
                 << totStr << endl;
        }

    }


    //Note: Edges will be removed from the original graph. Not the transposedGraph that we were using so far

    unique_ptr<Graph> originalGraphForTGraph = make_unique<Graph>();

    float percentageTargetsFloat = (float) percentageTargets / (float) 100;
    originalGraphForTGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    int numEdgesAtStart = originalGraphForTGraph->m;
    int totalNumEdgesToDelete = 0;

    for (int nodeToRemove:tGraphNodesToRemove) {

        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < originalGraphForTGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += originalGraphForTGraph->graphTranspose[k].size();
                if (k == nodeToRemove) {
                    numEdgesToDelete += originalGraphForTGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < originalGraphForTGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += originalGraphForTGraph->graph[k].size();
                if (k == nodeToRemove) {
                    numEdgesToDelete += originalGraphForTGraph->graph[k].size();
                }
            }

        }

        totalNumEdgesToDelete += numEdgesToDelete;
        originalGraphForTGraph->removeOutgoingEdges(nodeToRemove);

        if (tshoot1) {
            assert(("Here 1", originalGraphForTGraph->graph[nodeToRemove].size() == 0));
            assert(("Here 2", originalGraphForTGraph->graphTranspose[nodeToRemove].size() == 0));
            originalGraphForTGraph->assertCorrectNodesAreDeleted(nodeToRemove, numEdgesToDelete,
                                                                 totalEdgesInOrigGraphPre, totalEdgesInTransGraphPre);
        }

    }
    if (tshoot1) {
        int totalNumOfEdges = 0;
        for (int k = 0; k < originalGraphForTGraph->graph.size(); k++) {
            totalNumOfEdges += originalGraphForTGraph->graph[k].size();
        }
        assert(("Divergence betn something", totalNumOfEdges == numEdgesAtStart - totalNumEdgesToDelete));
    }

    cout << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing nodes already present in the seed Set that were not added to tGraphRemoveVertices set: " << endl;
    myfile << "Printing nodes already present in the seed Set that were not added to tGraphRemoveVertices set: " << endl;
    printSet(alreadyinSeed);

    //Calculating the strength of the resulting graph after removing the edges
    originalGraphForTGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    tGraphStrength = 0;
    for (int i = 0; i < originalGraphForTGraph->NodeinRRsetsWithCounts.size(); i++) {
        tGraphStrength += originalGraphForTGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n\n After removing nodes, transposedGraph Strength is " << tGraphStrength << endl;
    resultLogFile << "\n \n After removing transposedGraph Strength is " << tGraphStrength;
    myfile << tGraphStrength << " <-transposedGraph Strength\n";


    cout << "\nTransposed Graph end here" << endl;

    vector<vector<int>>().swap(influencedGraph->rrSets);
    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);

    return tGraphNodesToRemove;
}

void newDiffusion(Graph *newGraph, Graph *subNewGraph, Graph *modImpactGraph, Graph *tGraph, set<int> modNodes,
                  set<int> subModNodes,
                  set<int> *removalModImpact, set<int> tGraphNodes, vector<int> activatedSet, int newSeed,
                  float percentageTargetsFloat,
                  string convertedFile, set<int> prevSelectSeed) {

    bool tshoot = true;

    vector<int> modResults;
    vector<int> SubmodResults;
    vector<int> modImpactResults;
    vector<int> tGraphResults;

    cout << "\nnodes To remove in mod graph: ";
    resultLogFile << "\nnodes To remove in mod graph: ";

    int modAndTGraph = 0;//Stores common nodes betn modGraph and transposedGraph
    int modImpactAndTGraph = 0;//Stores common nodes betn modImpactGraph and transposedGraph
    int subModAndTGraph = 0;//Stores common nodes betn subModGraph and transposedGraph

    for (int i:modNodes) {

        if (tGraphNodes.count(i) == 1) modAndTGraph++;
        cout << i << " ";
        resultLogFile << i << " ";
    }

    cout << "\n nodes To remove in submod graph " << flush;
    resultLogFile << "\n nodes To remove in submod graph ";

    //modified don't remove anything from submod impact
    int A = 0;
    for (int i:subModNodes) {

        bool tshoot1 = true;

        cout << i << " ";
        resultLogFile << i << " ";

        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < subNewGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += subNewGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += subNewGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < subNewGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += subNewGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += subNewGraph->graph[k].size();
                }
            }
        }

        if (modNodes.count(i) == 1) A++;
        if (tGraphNodes.count(i) == 1) subModAndTGraph++;
        subNewGraph->removeOutgoingEdges(i);
        assert(subNewGraph->graph[i].size() == 0);
        assert(subNewGraph->graphTranspose[i].size() == 0);
        subNewGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                  totalEdgesInTransGraphPre);

    }

    cout << "\n nodes To remove in mod Impact graph " << flush;
    resultLogFile << "\n nodes To remove in mod Impact graph ";

    int B = 0;
    int C = 0;
    set<int> removalModImpactNodes;
    for (int i: *removalModImpact) {
        cout << i << " ";
        resultLogFile << i << " ";

        bool tshoot1 = true;
        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < modImpactGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += modImpactGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += modImpactGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < modImpactGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += modImpactGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += modImpactGraph->graph[k].size();
                }
            }
        }

        if (subModNodes.count(i) == 1) B++;
        if (modNodes.count(i) == 1) C++;
        if (tGraphNodes.count(i) == 1) modImpactAndTGraph++;
        modImpactGraph->removeOutgoingEdges(i);
        removalModImpactNodes.insert(i);

        assert(modImpactGraph->graph[i].size() == 0);
        assert(modImpactGraph->graphTranspose[i].size() == 0);
        modImpactGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                     totalEdgesInTransGraphPre);
    }

    for (int i:modNodes) {

        bool tshoot1 = true;
        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < newGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += newGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += newGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < newGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += newGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += newGraph->graph[k].size();
                }
            }
        }

        newGraph->removeOutgoingEdges(i);
        assert(newGraph->graph[i].size() == 0);
        assert(newGraph->graphTranspose[i].size() == 0);
        newGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                               totalEdgesInTransGraphPre);

    }

    cout << "\nnodes to remove in transposedGraph: ";
    resultLogFile << "\nnodes to remove in transposedGraph: ";

    for (int i:tGraphNodes) {
        cout << i << " ";
        resultLogFile << i << " ";

        bool tshoot1 = true;
        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < tGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += tGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += tGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < tGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += tGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += tGraph->graph[k].size();
                }
            }
        }

        tGraph->removeOutgoingEdges(i);
        assert(tGraph->graph[i].size() == 0);
        assert(tGraph->graphTranspose[i].size() == 0);
        tGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre, totalEdgesInTransGraphPre);

    }

    if (tshoot) {

        //Print out nodes to be removed only for myfile
        //Nodes are printed out in the order that they were added in - so most strength to least strength
        cout << flush;
        myfile << "\n\nnodes To remove in mod graph:\t ";
        for (int i:modNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in transposedGraph: ";
        for (int i:tGraphNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        myfile << "\nnodes To remove in mod Impact graph: ";
        for (int i: modImpactNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in submod graph:\t ";
        for (int i:subModNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;

    }

    cout << "\nintersection of mod and transposedGraph nodes to remove " << modAndTGraph;
    cout << "\nintersection of mod and submod nodes to remove " << A;
    cout << "\nintersection of mod and modImpact nodes to remove " << C;
    cout << "\nintersection of submod and modImpact nodes to remove " << B;
    cout << "\nintersection of submod and transposedGraph nodes to remove " << subModAndTGraph;
    cout << "\nintersection of modImpact and transposedGraph nodes to remove " << modImpactAndTGraph;

    resultLogFile << "\nintersection of mod and transposedGraph nodes to remove " << modAndTGraph;
    resultLogFile << "\nintersection of mod and submod nodes to remove " << A;
    resultLogFile << "\nintersection of mod and modImpact nodes to remove " << C;
    resultLogFile << "\nintersection of submod and modImpact nodes to remove " << B;
    resultLogFile << "\nintersection of submod and transposedGraph nodes to remove " << subModAndTGraph;
    resultLogFile << "\nintersection of modImpact and transposedGraph nodes to remove " << modImpactAndTGraph;

    myfile << "\n\nintersection of mod and transposedGraph nodes to remove " << modAndTGraph;
    myfile << "\nintersection of mod and submod nodes to remove " << A;
    myfile << "\nintersection of mod and modImpact nodes to remove " << C;
    myfile << "\nintersection of submod and modImpact nodes to remove " << B;
    myfile << "\nintersection of submod and transposedGraph nodes to remove " << subModAndTGraph;
    myfile << "\nintersection of modImpact and transposedGraph nodes to remove " << modImpactAndTGraph << "\n";



    //Random RR sets
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "\nRR sets are: " << R << endl;
    resultLogFile << "\nRR sets are: " << R << "\n";

    modImpactGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int modImapactStrength = 0;
    for (int i = 0; i < modImpactGraph->NodeinRRsetsWithCounts.size(); i++) {
        modImapactStrength += modImpactGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n After removing mod Impact Modular Strength is " << modImapactStrength << "\n";
    resultLogFile << "\n \n After removing mod Impact Modular Strength is " << modImapactStrength << "\n";

    myfile << modImapactStrength << " <- ModImpact Strength\n";
    vector<vector<int>>().swap(modImpactGraph->rrSets);
    vector<int>().swap(modImpactGraph->NodeinRRsetsWithCounts);

    set<int> maxInfluenceSeed;
    int maxInfluenceNum;
    set<int> seedSet;

    set<int> modseedSet = set<int>();
    set<int> subModseedSet = set<int>();
    set<int> modImpactseedSet = set<int>();
    set<int> tGraphSeedSet = set<int>();

    Graph *maxSeedGraph = new Graph;
    maxSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        maxSeedGraph->setPropogationProbability(probability);
    }

    //Running the experiments 2 OR 3

    set<int> maxSeed;//Stores the seedSet that will be used for diffusion in all of the 4 processes

    if(!someCondition) {
        cout << "\n \n******* Max influence start******** \n" << flush;
        myfile << "Max influence Seed Set in the original graph considering that we can remove all vertices: " << endl;
        maxInfluenceSeed = getSeed(budget, maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                                   NULL);
        vector<vector<int>>().swap(maxSeedGraph->rrSets);
        maxInfluenceNum = oldNewIntersection(maxSeedGraph, maxInfluenceSeed, activatedSet, resultLogFile);
        myfile << maxInfluenceNum << " <-MaxInfluence Num\n";
        cout << "\n \n******* Max influence end ******** \n" << flush;
        delete maxSeedGraph;

        //Calculating maxSeed to be used as the seed set for all the 4 methods:
        int inflOfMaxSeed;//Stores the influence of the max seed on the original graph G

        Graph *graph = new Graph;
        graph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
        if (!useIndegree) {
            graph->setPropogationProbability(probability);
        }

        if (useMaxSeed) {
            cout << "\n\n******* Calculating maxSeed to be used as the seed set for all the 4 methods ******** \n"
                 << endl;
            myfile << "Chosen Max influence Seed Set in the original graph considering that we can remove "
                      "only those vertices that are not present in any of the sets of verticesRemove " << endl;
            maxSeed = getSeed(budget, graph, activatedSet, modNodes, subModNodes, removalModImpactNodes, tGraphNodes,
                              NULL);
            assert(("Incorrect number of nodes added in max seed", maxSeed.size() == budget));
            vector<vector<int>>().swap(graph->rrSets);
            inflOfMaxSeed = oldNewIntersection(graph, maxSeed, activatedSet, resultLogFile);
            myfile << inflOfMaxSeed << " <-Influence of chosenMaxSeed on the original Graph G" << endl;
            cout << "\n \n******* Calculating maxSeed to be used ends ******** \n" << endl;
            delete graph;
        } else {
            cout << "\n\n******* Calculating random Seed to be used as the seed set for all the 4 methods ******** \n"
                 << endl;
            myfile << "Chosen random seed. Adding only those nodes that are not present in any of the removeNode Sets"
                   << endl;

            set<int> largerSet = set<int>();
            largerSet = getSeed(100, graph, activatedSet, modNodes, subModNodes, removalModImpactNodes, tGraphNodes,
                                NULL);
            vector<vector<int>>().swap(graph->rrSets);

            vector<int> placeholder = vector<int>();
            for (int const node: largerSet) {
                placeholder.push_back(node);
            }

            // obtain a time-based seed
            unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
            //randomly permute the placeholder
            shuffle(placeholder.begin(), placeholder.end(), std::default_random_engine(seed));
            //Add the first budget number of nodes to the maxSeed
            for (int i = 0; i < budget; i++) {
                maxSeed.insert(placeholder[i]);
            }
            assert(("Incorrect number of nodes added in random seed", maxSeed.size() == budget));
            inflOfMaxSeed = oldNewIntersection(graph, maxSeed, activatedSet, resultLogFile);
            myfile << inflOfMaxSeed << " <-Influence of chosenMaxSeed on the original Graph G" << endl;
            cout << "\n \n******* Calculating randomSeed to be used ends ******** \n" << endl;
            delete graph;
        }

    }

    if(someCondition){
        maxSeed = prevSelectSeed;
    }
    SeedSet *SeedClass = new SeedSet(newGraph, budget);

    /*
     * WARNING - Dont need this for now since using the same seedSet maxSeed as the seed for all the methods
    myfile <<"Unsorted Mod SeedSet: ";
    modseedSet = getSeed(newGraph, activatedSet, modNodes, set<int>(), set<int>(), set<int>(), NULL);
    myfile <<"Unsorted SubMod SeedSet: ";
    subModseedSet = getSeed(subNewGraph, activatedSet, subModNodes, set<int>(), set<int>(), set<int>(), NULL);
    myfile <<"Unsorted ModImpact SeedSet: ";
    modImpactseedSet = getSeed(modImpactGraph, activatedSet, removalModImpactNodes, set<int>(), set<int>(), set<int>(), NULL);
    myfile <<"Unsorted Transposed graph SeedSet: ";
    tGraphSeedSet = getSeed(tGraph, activatedSet, tGraphNodes, set<int>(), set<int>(), set<int>(), NULL);

    */
    if (tshoot) {

        cout << "\n\nMaxInfl Seed Set: " << endl;
        myfile << "\n\nMaxInfl Seed Set: " << endl;
        printSet(maxInfluenceSeed);

        cout << "\nChosen MaxInfl Seed Set to perform diffusion: " << endl;
        myfile << "\nChosen MaxInfl Seed Set to perform diffusion: " << endl;
        printSet(maxSeed);

        /*
        cout << "\nModular Seed Set: " << endl;
        myfile << "\nModular Seed Set: " << endl;
        printSet(modseedSet);

        cout << "\nSubModular Seed Set: " << endl;
        myfile << "\nSubModular Seed Set: " << endl;
        printSet(subModseedSet);

        cout << "\nModImpact Seed Set: " << endl;
        myfile << "\nModImpact Seed Set: " << endl;
        printSet(modImpactseedSet);

        cout << "\nTransposedGraph Seed Set: " << endl;
        myfile << "\nTransposedGraph Seed Set: " << endl;
        printSet(tGraphSeedSet);
        */

    }

    Graph* graph;
    myfile << "\n\nMOD SUBMOD MOD-IMPACT Transposed\n";

    int k = 0;
    while (k < 3) {
        switch (5) {

            case 0: //bestTim
                seedSet = getSeed(budget, newGraph, activatedSet, modNodes, subModNodes, removalModImpactNodes,
                                  tGraphNodes, NULL);
                vector<vector<int>>().swap(newGraph->rrSets);
                break;
            case 1:// best first Half Graph
                graph = new Graph;
                graph->readInfluencedHalfGraph(graphFileName, percentageTargetsFloat, convertedFile, 10 * k,
                                               resultLogFile, fullgraph);
                //graph->readHalfGraph(graphFileName, percentageTargetsFloat,8*k);
                if (!useIndegree) {
                    graph->setPropogationProbability(probability);
                }
                seedSet = getSeed(budget, graph, activatedSet, modNodes, subModNodes, removalModImpactNodes,
                                  tGraphNodes, NULL);
                delete graph;
                break;
            case 2: //random
                seedSet = SeedClass->getCompletelyRandom(modNodes, subModNodes);
                break;
            case 3: //random from OutDegree threshold nodes
                seedSet = SeedClass->outdegreeRandom(topBestThreshold, modNodes, subModNodes);
                break;
            case 4: //farthest from OutDegree threshold nodes
                seedSet = SeedClass->outdegreeFarthest(topBestThreshold);
                break;
            case 5: //seedSet=maxSeedSet;
                break;
        }

        cout << "\n********** k = " << k << " **********" << endl;

        cout << "\n \n Selected new SeedSet in original graph: " << flush;
        resultLogFile << "\n \n Selected new SeedSet in original graph: " << flush;
        for (auto item:maxSeed) {
            cout << item << " ";
            resultLogFile << item << " ";
        }

        int infNum = 0;

        cout << "\nMod Results: " << endl;
        resultLogFile << "\nMod Results: " << endl;
        infNum = oldNewIntersection(newGraph, maxSeed, activatedSet, resultLogFile);
        modResults.push_back(infNum);
        myfile << infNum << " ";

        cout << "\nSub Mod Results: " << endl;
        resultLogFile << "\nSub Mod Results: " << endl;
        infNum = oldNewIntersection(subNewGraph, maxSeed, activatedSet, resultLogFile);
        SubmodResults.push_back(infNum);
        myfile << infNum << " ";

        cout << "\nMod Impact Results: " << endl;
        resultLogFile << "\nMod Impact Results: " << endl;
        infNum = oldNewIntersection(modImpactGraph, maxSeed, activatedSet, resultLogFile);
        modImpactResults.push_back(infNum);
        myfile << infNum << " ";

        cout << "\nTransposed Graph Results: " << endl;
        resultLogFile << "\nTransposed Graph Results" << endl;
        infNum = oldNewIntersection(tGraph, maxSeed, activatedSet, resultLogFile);
        tGraphResults.push_back(infNum);
        myfile << infNum << "\n";

        k++;
    }
    double subModGain = 0;
    double ImapctGain = 0;
    for (int i = 0; i < k; i++) {
        subModGain += float(modResults[i] - SubmodResults[i]) / float(modResults[i]);
        ImapctGain += float(modResults[i] - modImpactResults[i]) / float(modResults[i]);
    }
    subModGain = (float) subModGain / k;
    ImapctGain = (float) ImapctGain / k;
    myfile << subModGain << " <-subModGain\n" << ImapctGain << " <-ModImpactGain\n";
    delete SeedClass;
}

set<int> subModularNodesRemove(Graph *influencedGraph, vector<int> activatedSet, int removeNodes, set<int> maxSeedSet,
                               set<int> *removalModImpact) {

    bool tshoot = false;//Prints the outdegree of each node in ASDegree.
    bool tshoot1 = true;//Prints the node being removed in each iteration
    bool tshoot2 = false;//Prints the outdegree values for the modNodes removed in Algo1

    clock_t subModReverseStartTime = clock();

    set<int> alreadyinSeed = set<int>();
    set<int> subModNodesToremove;
    vector<pair<int, int>> ASdegree;
    int removalNum = removeNodes;
    bool SubImpact = false;

    //Random RR sets
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "\nRR sets are: " << R << endl;
    resultLogFile << "\nRR sets are: " << R << endl;
    influencedGraph->generateRandomRRSetsFromTargets(R, activatedSet, modular, resultLogFile);

    cout << "\nNumber of edges created in EdgeMap: " << influencedGraph->RRas->noOfEdgesCreated << endl;
    cout << "Number of edges deleted from EdgeMap: " << influencedGraph->RRas->noOfEdgesDeleted << endl;
    cout << "Number of vertices created in VertexMap: " << influencedGraph->RRas->noOfVertices << endl;
    cout << "vertexMap.size(): " << influencedGraph->RRas->vertexMap.size() << endl;
    cout << "EdgeMap.size(): " << influencedGraph->RRas->EdgeMap.size() << endl;
    cout << "RRSetsSize - sizeof(influencedGraph->rrSets): " << sizeof(influencedGraph->rrSets);

    myfile << "Number of edges created in EdgeMap: " << influencedGraph->RRas->noOfEdgesCreated << endl;
    myfile << "Number of edges deleted from EdgeMap: " << influencedGraph->RRas->noOfEdgesDeleted << endl;
    myfile << "Number of vertices created in VertexMap: " << influencedGraph->RRas->noOfVertices << endl;
    myfile << "vertexMap.size(): " << influencedGraph->RRas->vertexMap.size() << endl;
    myfile << "EdgeMap.size(): " << influencedGraph->RRas->EdgeMap.size() << endl;
    myfile << "RRSetsSize - sizeof(influencedGraph->rrSets): " << sizeof(influencedGraph->rrSets);



    cout << "\nStarting to remove nodes by the modImpact and subMod methods" << endl;
    int h = 0;
    bool nodeInSeedSet = false;
    while (removeNodes != 0) {
        /*
        vector<pair<int,int>> SortedNodeidCounts=vector<pair<int,int>>();
        for(int i=0;i<influencedGraph->coverage.size();i++){
            pair<int,int> node= pair<int,int>();
            node.first=i;
            node.second=influencedGraph->coverage[i];
            SortedNodeidCounts.push_back(node);
        }
        std :: sort(SortedNodeidCounts.begin(),SortedNodeidCounts.end(), sortbysecdesc);
        assert(SortedNodeidCounts.at(0).second>=SortedNodeidCounts.at(1).second);*/

        //nodeMappedToOutdegree eg. Suppose at index 4 is stored 23.
        // It means - Node 4 has oudegree of 23
        nodeMappedToOutdegree = vector<int>(n, 0);

        if(!nodeInSeedSet) {
            ASdegree = vector<pair<int, int>>();
            for (auto it = influencedGraph->RRas->vertexMap.begin();
                 it != influencedGraph->RRas->vertexMap.end(); ++it) {
                pair<int, int> node = pair<int, int>();
                node.first = it->first;
                node.second = it->second->getOutDegree();
                ASdegree.push_back(node);
                nodeMappedToOutdegree.at(node.first) = node.second;
            }

            //Prints the outdegree of each node in ASDegree.
            if (tshoot) {
                myfile << "Started printing for removeNodes = " << removeNodes << endl;
                printVector(nodeMappedToOutdegree);
            }

            //Prints the outdegree values for the modNodes removed in Algo1
            if (tshoot2) {
                cout << "**************************************" << endl;
                cout << "Printing outdegree values for modNodes removed in Algo1" << endl;
                cout << "Node Outdegree" << endl;
                for (int i = 0; i < modNodesToRemoveUnsorted.size(); i++) {
                    for (int j = 0; j < ASdegree.size(); j++) {
                        if (ASdegree[j].first == modNodesToRemoveUnsorted[i]) {
                            cout << ASdegree[j].first << " " << ASdegree[j].second << endl;
                        }
                    }
                }
            }

            std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);
            assert(ASdegree.at(0).second >= ASdegree.at(1).second);

        }

        int index = 0;
        if (!SubImpact) {
            cout << "\n\n******* Running Mod Impact approach ********" << endl;
            resultLogFile << "\n\n******* Running Mod Impact approach ********"<< endl;
            for (int i = 0; i < removalNum; ) {
                int node = ASdegree.at(index).first;
                if (maxSeedSet.count(node) == 0) {
                    i++;
                    removalModImpact->insert(node);
                    modImpactNodesToRemoveUnsorted.push_back(node);
                    SubImpact = true;
                }else{
                    alreadyinSeed.insert(node);
                }
                index++;
            }
            assert(("Mismatch - removalModImpact and removeNodes", removalModImpact->size() == removalNum));

            /*
            int k=0;
            for(int i=0;i<removalNum;i++){
                if(seedSet.count(SortedNodeidCounts.at(i).first)==1){
                    k++;
                }
                removalModImpact->insert(SortedNodeidCounts.at(i).first);
                SubImpact=true;
            }*/

            cout << "\nassociated value is " << alreadyinSeed.size() << endl;
            cout << "\n Number of nodes for (mod impact) already present in seed set = " << alreadyinSeed.size() << endl;
            resultLogFile << "\n Number of nodes for (mod impact) already present in seed set = " << alreadyinSeed.size();
            cout << "Printing nodes in modImpact that were not added to removeNodes because they were in seesSet: " << endl;
            myfile << "Printing nodes in modImpact that were not added to removeNodes because they were in seesSet: " << endl;
            printSet(alreadyinSeed);

            clock_t subModImapctEndTime = clock();
            double totalModImapctTime =
                    double(subModImapctEndTime - subModReverseStartTime - influencedGraph->modImpactTime) /
                    (CLOCKS_PER_SEC * 60);
            cout << "\n Reverse submod impact algorithm time in minutes " << totalModImapctTime << endl;
            resultLogFile << "\n Reverse submod impact algorithm time in minutes " << totalModImapctTime << "\n";
            myfile << totalModImapctTime << " <-ModImpactTime\n";
            cout << "******* Completed Mod Impact approach ********" << endl;
            cout << "******* Running SubMod approach ********" << endl;
            //Clearing alreadyinSeed because it contains the modImpact nodes at this point
            alreadyinSeed.clear();
        }
        cout << endl;
        /*while(seedSet.count(SortedNodeidCounts.at(h).first)==1){+
         h++;
         }*/
        /*int node = SortedNodeidCounts.at(h).first;
        subModNodesToremove.insert(node);
        if(seedSet.count(node)==1){
            alreadyinSeed.insert(node);
        }*/
        int node = ASdegree.at(h).first;
        if (maxSeedSet.count(node) == 0) {
            subModNodesToremove.insert(node);
            subModNodesToRemoveUnsorted.push_back(node);
            //remove node from RRset
            if (tshoot1) {
                cout << "Removed node: " << node << endl;
            }
            influencedGraph->removeVertexFromRRassociatedGraph(node);
            //influencedGraph->removeNodeFromRRset(node);
            removeNodes--;
            h = 0;
            nodeInSeedSet = false;
        }else{
            h++;
            alreadyinSeed.insert(node);
            nodeInSeedSet = true;
        }
    }

    assert(("Mismatch - subModNodesToremove and removeNodes", subModNodesToremove.size() == removalNum));
    clock_t subModReverseEndTime = clock();

    vector<vector<int>>().swap(influencedGraph->rrSets);
    for (int i:subModNodesToremove) {

        bool tshoot1 = true;
        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < influencedGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += influencedGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += influencedGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < influencedGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += influencedGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += influencedGraph->graph[k].size();
                }
            }
        }

        influencedGraph->removeOutgoingEdges(i);
        assert(influencedGraph->graph[i].size() == 0);
        assert(influencedGraph->graphTranspose[i].size() == 0);
        influencedGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                      totalEdgesInTransGraphPre);

    }

    influencedGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int subModStrength = 0;
    for (int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++) {
        subModStrength += influencedGraph->NodeinRRsetsWithCounts[i];
    }

    cout << "\n Recalculated Initial strength was = " << influencedGraph->totalNumNodesInRRSets << endl;
    cout << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing nodes in alreadyinSeed that were not added to subModNodesToremove:" << endl;
    myfile << "Printing nodes in alreadyinSeed that were not added to subModNodesToremove:" << endl;
    printSet(alreadyinSeed);
    cout << "\n Submodular strength = " << subModStrength;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size();
    resultLogFile << "\n Submodular strength = " << subModStrength;
    myfile << influencedGraph->totalNumNodesInRRSets << " <-Recalculated Init Strength\n";
    myfile << subModStrength << " <-subModStrength\n";
    double totalAlgorithmTime = double(subModReverseEndTime - subModReverseStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\n Reverse submodular algorithm time in minutes " << totalAlgorithmTime;
    resultLogFile << "\n Reverse submodular algorithm time in minutes " << totalAlgorithmTime;
    myfile << totalAlgorithmTime << " <-SubModTime\n";
    return subModNodesToremove;
}

void convertInfluenceFile(string convertedFile, string influenceFile, set<int> seedSet, int n, int newVertices,
                          vector<int> *seedOrder) {
    vector<int> vertexIdMap = vector<int>(n, -1);
    ifstream myFile(influenceFile);
    ofstream newfile;
    newfile.open(convertedFile);
    newfile << newVertices << "\n";
    int u;
    int v;
    int numofEdges = 0;
    int i = -1;
    if (myFile.is_open()) {
        while (myFile >> u >> v) {
            numofEdges++;
            if (vertexIdMap[u] == -1) {
                vertexIdMap[u] = ++i;
                newfile << i;
            } else {
                newfile << vertexIdMap[u];
            }
            if (vertexIdMap[v] == -1) {
                vertexIdMap[v] = ++i;
                newfile << " " << i << "\n";
            } else {
                newfile << " " << vertexIdMap[v] << "\n";
            }
        }
    }
    newfile << -1 << " " << -1 << "\n";
    for (int i:seedSet) {
        newfile << i << " ";
    }
    newfile << "\n" << -1 << " " << -1 << "\n";
    for (int i: *seedOrder) {
        newfile << i << " ";
    }
    newfile.close();
    myFile.close();

    if (std::remove(influenceFile.c_str()) != 0)
        perror("Error deleting file");
    else
        puts("File successfully deleted");
}

int getNumberofVertices(string influenceFile) {
    ifstream myFile(influenceFile);
    unordered_set<int> vertices = unordered_set<int>();
    int u;
    int v;
    if (myFile.is_open()) {
        while (myFile >> u >> v) {
            vertices.insert(u);
            vertices.insert(v);
        }
    }
    return (int) vertices.size();
}


void executeTIMTIM(cxxopts::ParseResult result) {
    clock_t executionTimeBegin = clock();
    IMResults::getInstance().setFromFile(fromFile);
    float percentageTargetsFloat = (float) percentageTargets / (float) 100;

    //Generate graph
    Graph *graph = new Graph;
    int half_seed = initialSeed;
    if (initialSeed == 2) {
        graph->readHalfGraph(graphFileName, percentageTargetsFloat, 50, resultLogFile);
        initialSeed = 1;
    } else {
        graph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    }
    if (!useIndegree) {
        graph->setPropogationProbability(probability);
    }

    set<int> seedSet;
    vector<int> *seedOrder = new vector<int>(budget);
    SeedSet *SeedClass = nullptr;
    switch (initialSeed) {
        case 1://bestTim for  case1, besthalfGRaph for case 2
            seedSet = getSeed(budget, graph, vector<int>(), set<int>(), set<int>(), set<int>(), set<int>(), seedOrder);
            if (half_seed == 2) {
                graph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
                if (!useIndegree) {
                    graph->setPropogationProbability(probability);
                }
            }
            break;
        case 3: //random
            SeedClass = new SeedSet(graph, budget);
            seedSet = SeedClass->getCompletelyRandom(set<int>(), set<int>());
            break;
        case 4: //random from OutDegree threshold nodes
            SeedClass = new SeedSet(graph, budget);
            seedSet = SeedClass->outdegreeRandom(topBestThreshold, set<int>(), set<int>());
            break;
        case 5: //farthest from OutDegree threshold nodes
            SeedClass = new SeedSet(graph, budget);
            seedSet = SeedClass->outdegreeFarthest(topBestThreshold);
            break;
        default:
            break;
    }
    delete SeedClass;

    //Start Diffusion
    cout << "\n Diffusion on graph started" << flush;
    resultLogFile << "\n Diffusion on graph started";

    vector<int> activatedSet;
    string influenceFile;
    string convertedFile =
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            graphFileName + "_converted" + "_" + to_string(budget) + "_" + to_string(probability);
    int newVertices = 0;

    switch (diffusion) {
        case 1:
            activatedSet = performDiffusion(graph, seedSet, NULL);
            break;
        case 2:
            influenceFile = singleDiffusionInfluence(graph, seedSet, graphFileName, budget, probability);
            vector<vector<int>>().swap(graph->rrSets);
            newVertices = getNumberofVertices(influenceFile);
            convertInfluenceFile(convertedFile, influenceFile, seedSet, graph->n, newVertices, seedOrder);
            break;
            /*case 3:set<int> active=dagDiffusion(graph,seedSet);
             break;*/
        default:
            break;
    }
    delete graph;

    cout << "\n Creating Influenced Graph " << flush;
    resultLogFile << "\n Creating Influenced Graph ";

    Graph *influencedGraph = new Graph;
    //influencedGraph->readInfluencedGraph(graphFileName, percentageTargetsFloat,activatedSet);
    vector<int> *seedNodes = new vector<int>(budget);
    activatedSet = influencedGraph->writeInfluencedGraph(graphFileName, percentageTargetsFloat, convertedFile,
                                                         seedNodes, seedOrder);
    if (!useIndegree) {
        influencedGraph->setPropogationProbability(probability);
    }

    cout << "\n Selected original SeedSet: " << flush;
    resultLogFile << "\n Selected original SeedSet: ";

    for (int i: *seedNodes) {
        seedSet.insert(i);
        cout << i << " ";
        resultLogFile << i << " ";
    }
    cout << "\n Selected Order of SeedSet: " << flush;
    resultLogFile << "\n Selected Order of SeedSet: ";

    for (int j: *seedOrder) {
        cout << j << " ";
        resultLogFile << j << " ";
    }
    myfile << activatedSet.size() << " ";
    cout << "\n Targets activated = " << activatedSet.size();
    cout << "\n Non targets are = " << influencedGraph->getNumberOfNonTargets() << flush;

    resultLogFile << "\n Targets activated = " << activatedSet.size();
    resultLogFile << "\n Non targets are = " << influencedGraph->getNumberOfNonTargets();

    //get node to be removed
    set<int> modNodesToremove;
    cout << "\n ******* Running modular approach ******** \n" << flush;
    resultLogFile << "\n ******* Running modular approach ******** \n";

    clock_t ModReverseStartTime = clock();
    modNodesToremove = removeVertices(influencedGraph, removeNodes, seedSet, activatedSet, "modular");
    clock_t ModReverseEndTime = clock();
    double totalAlgorithmTime = double(ModReverseEndTime - ModReverseStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\n Reverse algorithm time in minutes \n" << totalAlgorithmTime << flush;
    resultLogFile << "\n Reverse algorithm time in minutes \n" << totalAlgorithmTime;

    myfile << totalAlgorithmTime << " ";
    delete influencedGraph;

    //else{
    cout << "\n \n ******* Running Sub Modular approach ******** \n" << flush;
    resultLogFile << "\n \n ******* Running Sub Modular approach ******** \n" << flush;
    Graph *subInfluencedGraph = new Graph;
    vector<int> SubactivatedSet;
    SubactivatedSet = subInfluencedGraph->writeInfluencedGraph(graphFileName, percentageTargetsFloat, convertedFile,
                                                               NULL, NULL);
    if (!useIndegree) {
        subInfluencedGraph->setPropogationProbability(probability);
    }
    set<int> *removalModImpact = new set<int>();
    set<int> subModNodesToremove = subModularNodesRemove(subInfluencedGraph, SubactivatedSet, removeNodes, seedSet,
                                                         removalModImpact);
    delete subInfluencedGraph;

    cout << "\n \n******* Node removed in all three approaches ******** \n" << flush;
    resultLogFile << "\n \n******* Node removed in all three approaches ******** \n" << flush;

    Graph *modNewGraph = new Graph;
    modNewGraph->writeInfluencedGraph(graphFileName, percentageTargetsFloat, convertedFile, NULL, NULL);
    if (!useIndegree) {
        modNewGraph->setPropogationProbability(probability);
    }

    Graph *modImpactGraph = new Graph;
    modImpactGraph->writeInfluencedGraph(graphFileName, percentageTargetsFloat, convertedFile, NULL, NULL);
    if (!useIndegree) {
        modImpactGraph->setPropogationProbability(probability);
    }

    set<int> newInfluenceSeed;
    newInfluenceSeed = getSeed(budget, modImpactGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                               NULL);
    oldNewIntersection(modImpactGraph, newInfluenceSeed, activatedSet, resultLogFile);
    cout << "\n \n******* New influence done******** \n" << flush;

    Graph *subNewGraph = new Graph;
    subNewGraph->writeInfluencedGraph(graphFileName, percentageTargetsFloat, convertedFile, NULL, NULL);
    if (!useIndegree) {
        subNewGraph->setPropogationProbability(probability);
    }
    //Uncomment this code if you are running this method
//    newDiffusion(modNewGraph, subNewGraph, modImpactGraph, modNodesToremove, subModNodesToremove, removalModImpact,
//                 activatedSet, newSeed, percentageTargetsFloat, convertedFile);

    clock_t executionTimeEnd = clock();
    double totalExecutionTime = double(executionTimeEnd - executionTimeBegin) / (CLOCKS_PER_SEC * 60);
    cout << "\n Elapsed time in minutes " << totalExecutionTime;
    resultLogFile << "\n Elapsed time in minutes " << totalExecutionTime;
}

void executeTIMTIMfullGraph(cxxopts::ParseResult result) {
    clock_t executionTimeBegin = clock();

    IMResults::getInstance().setFromFile(fromFile);
    // insert code here...
    float percentageTargetsFloat = (float) percentageTargets / (float) 100;


    Graph *influencedGraph = new Graph;
    influencedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        influencedGraph->setPropogationProbability(probability);
    }

    //Write the transposed graph to file to be used by the TransposedGraph method
    string nameOfTheGraph = graphFileName + "_transposed.txt";
    string pathToWriteGraph = "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\";
    influencedGraph->writeGraphToFile(influencedGraph->graphTranspose, nameOfTheGraph, pathToWriteGraph,
                                      influencedGraph->n, influencedGraph->m);

    vector<int> activatedSet = vector<int>(influencedGraph->n);
    for (int i = 0; i < influencedGraph->n; i++) {
        activatedSet[i] = i;
    }
    set<int> seedSet;
    /*
    int diffusionNum=0;
    double percentage=0;
    int influenceBudget=budget;
    budget=500;
    vector<int> maxinfluence;
    //diffusion with RR approach to get the maximum influence
    
        maxSeedSet=getSeed(influencedGraph,activatedSet,set<int>(),set<int>(),NULL);
        
        int n = (int)activatedSet.size();
        double epsilon = (double)EPSILON;
        int R = (8+2 * epsilon) * n * (2 * log(n) + log(2))/(epsilon * epsilon);
        cout<< "RR sets are: "<<R;
        influencedGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
        for(vector<int> v:influencedGraph->rrSets){
            for(int j:v){
                if(maxSeedSet.count(j)==1){
                    diffusionNum++;
                    break;
                }
            }
        }
        diffusionNum=((double)diffusionNum/R)*n;
        percentage= (float(diffusionNum)/(float)n)*100;
        //budget+=influenceBudget;
        vector<vector<int>>().swap(influencedGraph->rrSets);
    
    //budget=influenceBudget;
    cout << "\n Influenced graph by seed size = " << diffusionNum;
    resultLogFile << "\n Influenced graph by seed size = " << diffusionNum;
     */
    cout << "\n Targets activated = " << activatedSet.size();
    cout << "\n Non targets are = " << influencedGraph->getNumberOfNonTargets() << flush;


    //Calculating the maxSeed
    set<int> maxInfluenceSeed = set<int>();
    int maxInfluenceNum;
    if (someCondition) {
        Graph *maxSeedGraph = new Graph;
        maxSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
        if (!useIndegree) {
            maxSeedGraph->setPropogationProbability(probability);
        }

        cout << "\n \n******* Max influence start******** \n" << flush;
        myfile << "Max influence Seed Set in the original graph considering that we can remove all vertices: " << endl;
        maxInfluenceSeed = getSeed(budget, maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                                   NULL);
        vector<vector<int>>().swap(maxSeedGraph->rrSets);
        maxInfluenceNum = oldNewIntersection(maxSeedGraph, maxInfluenceSeed, activatedSet, resultLogFile);
        myfile << maxInfluenceNum << " <-MaxInfluence Num\n";
        cout << "\n \n******* Max influence end ******** \n" << flush;
        delete maxSeedGraph;
    }


    //get node to be removed
    set<int> modNodesToremove;
    cout << "\n ******* Running modular approach ******** \n" << flush;
    resultLogFile << "\n ******* Running modular approach ******** \n";

    clock_t ModReverseStartTime = clock();
    modNodesToremove = removeVertices(influencedGraph, removeNodes, maxInfluenceSeed, activatedSet, "modular");
    clock_t ModReverseEndTime = clock();
    double totalAlgorithmTime = double(ModReverseEndTime - ModReverseStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\n Reverse algorithm time in minutes \n" << totalAlgorithmTime << flush;
    resultLogFile << "\n Reverse algorithm time in minutes \n" << totalAlgorithmTime;

    myfile << totalAlgorithmTime << " <-ModStrengthTime\n";

    //******************************************************************************************************************

    cout << "\n ******* Running TransposedGraph approach ******** \n" << flush;
    resultLogFile << "\n ******* Running TransposedGraph approach ******** \n";

    set<int> tGraphNodesToremove;

    //Read the graph from the file and create the Graph object for the TransposedGraph
    Graph *transposedGraph = new Graph;

//    unique_ptr<Graph> transposedGraph = make_unique<Graph>();
    transposedGraph->readGraph(nameOfTheGraph, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        transposedGraph->setPropogationProbability(probability);
    }

    activatedSet = vector<int>(transposedGraph->n, 0);
    for (int i = 0; i < transposedGraph->n; i++) {
        activatedSet[i] = i;
    }

    clock_t tGraphStartTime = clock();
    tGraphNodesToremove = tGraphRemoveVertices(transposedGraph, influencedGraph, removeNodes, maxInfluenceSeed, activatedSet,
                                               "modular");

    clock_t tGraphEndTime = clock();
    double totaltGraphTime = double(tGraphEndTime - tGraphStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\nTransposed Graph algorithm time in minutes \n" << totaltGraphTime << flush;
    resultLogFile << "\nTransposed Graph algorithm time in minutes \n" << totaltGraphTime;

    myfile << totaltGraphTime << " <-transposedGraph Time\n";

    delete influencedGraph;
    delete transposedGraph;

    //******************************************************************************************************************

    cout << "\n \n ******* Running Sub Modular approach ******** \n" << flush;
    resultLogFile << "\n \n ******* Running Sub Modular approach ******** \n" << flush;

    Graph *subInfluencedGraph = new Graph;
    subInfluencedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subInfluencedGraph->setPropogationProbability(probability);
    }
    set<int> *removalModImpact = new set<int>();
    set<int> subModNodesToremove = subModularNodesRemove(subInfluencedGraph, activatedSet, removeNodes, maxInfluenceSeed,
                                                         removalModImpact);
    //delete subInfluencedGraph;

    cout << "\n \n******* Node removed in all four approaches ******** \n" << flush;
    resultLogFile << "\n \n******* Node removed in all four approaches ******** \n" << flush;

    Graph *modNewGraph = new Graph;
    modNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modNewGraph->setPropogationProbability(probability);
    }

    Graph *tGraph = new Graph;
    tGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        tGraph->setPropogationProbability(probability);
    }


    Graph *modImpactGraph = new Graph;
    modImpactGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modImpactGraph->setPropogationProbability(probability);
    }


    Graph *subNewGraph = new Graph;
    subNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subNewGraph->setPropogationProbability(probability);
    }

    string convertedFile =
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            graphFileName;
    newDiffusion(modNewGraph, subNewGraph, modImpactGraph, tGraph, modNodesToremove, subModNodesToremove,
                 removalModImpact, tGraphNodesToremove,
                 activatedSet, newSeed, percentageTargetsFloat, convertedFile, maxInfluenceSeed);

    clock_t executionTimeEnd = clock();
    double totalExecutionTime = double(executionTimeEnd - executionTimeBegin) / (CLOCKS_PER_SEC * 60);
    cout << "\n Elapsed time in minutes " << totalExecutionTime;
    resultLogFile << "\n Elapsed time in minutes " << totalExecutionTime;


}

//  How to run this code:
//  First compile to give the .exe file
//  g++ -Wall -std=c++14 TryingPrettyCode.cpp -o newExe
//  newExe.exe --algorithm=bfs --seedset=10 --graph=anotherTry
//  Moral of the story is the arguments do not need to be in the same order

//Apparently, the above process is wrong
//In order for the file to run properly you need to provide ALL of the files as arguments to the compiler
//So far, this si the correct way of running the program:
//g++ -Wall -std=c++14  TryingPrettyCode.cpp InfluenceMaximization/ApproximationSetting.hpp InfluenceMaximization/Edge.cpp InfluenceMaximization/Edge.hpp InfluenceMaximization/Graph.hpp InfluenceMaximization/Graph.cpp InfluenceMaximization/IMTree.hpp InfluenceMaximization/IMTree.cpp InfluenceMaximization/json.hpp InfluenceMaximization/log.h InfluenceMaximization/RRassociatedGraph.hpp InfluenceMaximization/RRassociatedGraph.cpp InfluenceMaximization/vertex.hpp InfluenceMaximization/vertex.cpp -o newExe
//Execution remains the same thoough:
//newExe.exe --algorithm=bfs --seedset=10 --graph=anotherTry --budget=20 --percentage=15 --threshold=17


int main(int argc, char **argv) {

    //    freopen("output.txt", "w", stdout);//Output to the file and not the console
    cout << "Starting program\n";

    string resultDataFile;
    //  srand() gives the random function a new seed, a starting point (usually random numbers are calculated by taking the
    //  previous number (or the seed) and then do many operations on that number to generate the next).
    //  time(0) gives the time in seconds since the Unix epoch, which is a pretty good "unpredictable" seed
    //  (you're guaranteed your seed will be the same only once, unless you start your program multiple times within the same second).
    srand(time(0));
    setupLogger();
    cout << "Setup logger \n";
    //  make an instance of cxxopts::Options: like so -
    //  cxxopts::Options options;
    cxxopts::Options options("Targeted Influence Maximization", "Experiments and research.");
    //  You can then add options like so:
    //  The options can be specified with a short option, which is a single character, or a long option,
    //  which is two or more characters, or both, separated by a comma; the short option must come first.
    options.add_options()
            ("algorithm", "Choose which algorithm to run", cxxopts::value<std::string>())
            ("graph", "Graph file name", cxxopts::value<std::string>())
            ("b,budget", "Budget size", cxxopts::value<int>())
            ("t,threshold", "NT threshold", cxxopts::value<int>())
            ("m,method", "TIM-TIM or SIM-SIM", cxxopts::value<int>())
            ("percentage", "Percentage of Targets", cxxopts::value<int>())
            ("n,ntfile", "Non Targets File name", cxxopts::value<std::string>())
            ("p,probability", "Propogation probability", cxxopts::value<double>())
            ("approximation", " Approximation Settings", cxxopts::value<int>())
            ("r,nodesRemove", " Remove nodes number", cxxopts::value<int>())
            ("w,modularity", " Modular selection", cxxopts::value<std::string>())
            ("f,fullgraph", " Full Graph selection", cxxopts::value<std::string>())
            ("s,seedset", " Seed set selection", cxxopts::value<int>())
            ("d,Diffusion", " Diffusion selection", cxxopts::value<int>())
            ("x,newSeedset", " New Seed set selection", cxxopts::value<int>())
            ("e,extend", "Extend the permutation");
    //  To parse the command line arguments, simple write:
    //  This will parse the arguments and modify argc and argv, removing all recognised arguments.
    //  options.parse(argc, argv);
    auto result = options.parse(argc, argv);
    //  To retrieve the parsed value, it can be accessed with operator[]. The value returned is a generic value
    //  which must be converted to the type of the value stored.
    //  For example, for the option "file" above, whose value is a string, it must be converted to a string using:
    string algorithm = result["algorithm"].as<string>();
    string fullgraphvalue;
    budget = result["budget"].as<int>();
    nonTargetThreshold = result["threshold"].as<int>();
    graphFileName = result["graph"].as<std::string>();
    percentageTargets = result["percentage"].as<int>();
    removeNodes = result["nodesRemove"].as<int>();
    initialSeed = result["seedset"].as<int>();
    modular = result["modularity"].as<std::string>();
    fullgraphvalue = result["fullgraph"].as<std::string>();
    if (fullgraphvalue.compare("true") == 0)
        fullgraph = true;
    else
        fullgraph = false;
    newSeed = result["newSeedset"].as<int>();
    diffusion = result["Diffusion"].as<int>();

    cout << "\n begin execution tim tim ";
    resultDataFile = graphFileName;
    resultDataFile += "_Budget_" + to_string(budget);
    resultDataFile += "_Removal_" + to_string(removeNodes);
    resultDataFile += "__RRapproach2_Log.txt";
    resultDataFile = "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\ResultData\\" + resultDataFile;
    resultLogFile.open(resultDataFile);

    //  Quest: Why have a separate method for these 4-5 arguments?...
    loadResultsFileFrom(result);
    //  Quest: ...if you could have just written them over here?

    if (result.count("method") > 0) {
        method = result["method"].as<int>();//method is a global int variable, which requires => #define PHASE1TIM_PHASE2TIM 1;
    }
    if (result.count("p") > 0) {
        probability = result["p"].as<double>();//probability is global int variable initialized to 0
        useIndegree = false;//useIndegree is global bool variable initialized to true
    }
    if (result.count("ntfile") > 0) {
        nonTargetsFileName = result["ntfile"].as<std::string>();//nonTargetsFileName is a global string variable
        fromFile = true;//fromFile is a global bool variable initialized to false
    }

    // Log information
    //  Quest: budget, nonTargetThreshold, percentageTargets are defined as global variables
    //  but they are also defined in loadResultsFileFrom() method. Is the variable shadowing intentional?
    //  No it isnt, you idiot.
    //  Quest: So if I run the program using the following arguments for example:
    //  newExe.exe --algorithm=bfs --seedset=10 --graph=anotherTry --budget=20 --percentage=15 --threshold=17
    //  I get the following output:
    //   Conducting experiments for:
    // Graph: anotherTry       Budget: 0       Non Target Threshod: 0  Percentage:  0  Method: 1       Nodes removed: 0        Seed selection case: 10         Top best outdegree threshold : 100
    //  As you can see in the above output, the values of budget, percentage and threshold are set to the default values,
    //  despite us providing arguments for them. This does not seem to be correct?

    cout << "\n Conducting experiments for:\n";
    cout << " Graph: " << graphFileName;
    cout << "\t Budget: " << budget;//global int variable, not initialised;
    cout << "\t Non Target Threshod: " << nonTargetThreshold;//global int variable, not initialised
    cout << "\t Percentage:  " << percentageTargets;//global int variable, not initialised
    cout << "\t Method: " << method;
    cout << "\t Nodes removed: " << removeNodes;//Global int variable initialised to 0
    cout << "\t Seed selection case: " << initialSeed;//global int variable, not initialised
    cout << "\t Top best outdegree threshold : " << topBestThreshold;//global int variable intialised to 100

    resultLogFile << "\n Conducting experiments for:\n";
    resultLogFile << " Graph: " << graphFileName;
    resultLogFile << "\t Budget: " << budget;
    resultLogFile << "\t Non Target Threshod: " << nonTargetThreshold;
    resultLogFile << "\t Percentage:  " << percentageTargets;
    resultLogFile << "\t Method: " << method;
    resultLogFile << "\t Nodes removed: " << removeNodes;
    resultLogFile << "\t Seed selection case: " << initialSeed;
    resultLogFile << "\t Top best outdegree threshold : " << topBestThreshold;

    if (useIndegree) {
        cout << "\t Probability: Indegree";
        resultLogFile << "\t Probability: Indegree";
    } else {
        cout << "\t Probability: " << probability;
        resultLogFile << "\t Probability: " << probability;
    }
    if (fromFile) {
        cout << "\n Reading Non targets from file: " << nonTargetsFileName;
        resultLogFile << "\n Reading Non targets from file: " << nonTargetsFileName;
    }

    FILE_LOG(logDEBUG) << "\n Conducting experiments for:\n";
    FILE_LOG(logDEBUG) << " Graph: " << graphFileName;
    FILE_LOG(logDEBUG) << "\t Budget: " << budget;
    FILE_LOG(logDEBUG) << "\t Non Target Threshod: " << nonTargetThreshold;
    FILE_LOG(logDEBUG) << "\t Percentage:  " << percentageTargets;
    FILE_LOG(logDEBUG) << "\t Method: " << method;
    if (fromFile) {
        FILE_LOG(logDEBUG) << "\n Reading Non targets from file: " << nonTargetsFileName;
    }

    string resultFile;
    resultFile = graphFileName;

    if (fullgraph) {
        resultFile += "_FullGraph_results.txt";
        resultFile =
                "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\results\\" +
                resultFile;
        myfile.open(resultFile, std::ios::app);
        myfile << "\n" << budget << " <-SeedSetSize\n" << removeNodes << " <-removeNodes\n";
        executeTIMTIMfullGraph(result);
    } else {
        resultFile += "_RRapproach_results.txt";
        resultFile =
                "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\results\\" +
                resultFile;
        myfile.open(resultFile, std::ios::app);
        myfile << "\n" << budget << " " << removeNodes << " ";
        executeTIMTIM(result);
    }
    disp_mem_usage("");
    return 0;
}
