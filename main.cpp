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
ofstream dependValues;
bool fullgraph = false;
ofstream resultLogFile;

//Variables for experimenting
bool useMaxSeed = true;//Applicable if someCondition = false. Set to false if using random Seed for diffusion instead of using maxSeed => Experiment 3
bool someCondition = true;//Set to true if calculating maxSeed BEFORE removing any nodes. Remove nodes ONLY if they arent in maxSeed.
bool useRandomSeed = false;//Set to true (someCondition should also be set to true) if using random Seed instead of max Seed as the initial seed BEFORE finding the vertices to be removed
bool useEnvelop = false;//Set to true if someCondition is set to true. Implies you are not removing nodes from the envelopedNodes as well. SeedSet is still fixed.

//These are my global variables for testing
vector<int> modNodesToRemoveUnsorted;
vector<int> subModTopKInflNodesToRemoveUnsorted;
vector<int> countNodesToRemoveUnsorted;
vector<int> tGraphNodesToRemoveUnsorted;
vector<int> modImpactNodesToRemoveUnsorted;
vector<int> nodeMappedToOutdegree;
double removeCritNodeFromDependencyVectorTopCritTime = 0;
double reComputeDependencyValuesTime = 0;
double repopulateDependencyMatrixAfterCritNodeRemovalTime = 0;
//Global variables for testing end here

/*List of warnings:
 * 1) If you are trying to find the best seed set for each set of methods and not at the start of the experiment, remember that you have added some additional
 * methods. And you are not passing the removeNode set<> into the getSeed() method for those newly added methods. SO make sure you chagne that if you
 * are going to run those experiments.
 *
 * 2) Uncomment the countGraph and the topKInfl metods if you want to run them
 *
 * 3) In removeSeedSetNodeFromDependencyVector() there is an assert statement. Set tshoot to false when actually running the program.
 * */


void setupLogger() {
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
        cout << myVector[i] << " ";
    }
    myfile << endl;
    myfile << "-----Completed Printing Vector----" << endl;
    cout << "-----Completed Printing Vector----" << endl;
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

void printSetOnlyInCout(const set<int> myVector) {

    for (int const myInt: myVector) {
        cout << myInt << " ";
    }
    cout << endl;
    cout << "-----Completed Printing Set-----" << endl;
}

void printNodesInEnvelopeButNotInSeedSet(const set<int> &alreadyinSeed, const set<int> &maxSeedSet,
                                         const set<int> &envelopedNodes) {

    for (int const currNode : alreadyinSeed) {
        if (maxSeedSet.count(currNode) == 0) {
            cout << currNode << " ";
            myfile << currNode << " ";
            assert(("Node not in envelopedNodes either", envelopedNodes.count(currNode) != 0));
        }
    }
    cout << endl;
    myfile << endl;
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
getSeed(int numNodes, unique_ptr<Graph> &graph, vector<int> activatedSet, set<int> modNodes, set<int> subModNodes,
        set<int> removalModImpactNodes, set<int> tGraphNodes, vector<int> *seedOrder) {
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
removeVertices(unique_ptr<Graph> &influencedGraph, int removeNodes, const set<int> &maxSeedSet,
               const set<int> &envelopedNodes, vector<int> activatedSet, string modular) {

    bool tshoot = false;//Prints the graphTranspose after the nodes have been deleted
    bool tshoot1 = true;//Controls the assert statements
    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet
    bool tshoot3 = false;//Prints the NodeInRRSets values for ALL of the nodes

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

    if (tshoot3) {
        dependValues << "Printing modular values for all of the nodes:" << endl;
        for (int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++) {
            dependValues << influencedGraph->NodeinRRsetsWithCounts[i] << endl;
        }
        dependValues << "-----DONE PRINTING------" << endl;
    }

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
        if (nodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid) == 0 && envelopedNodes.count(nodeid) == 0) {
            nodesToRemove.insert(nodeid);
            modNodesToRemoveUnsorted.push_back(nodeid);//modNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }
    if (tshoot2 && useEnvelop) {
        cout << "Mod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
             << endl;
        myfile << "Mod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
               << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
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
    vector<vector<int>>().swap(influencedGraph->rrSets);
//    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);
    return nodesToRemove;
}

set<int> tGraphRemoveVertices(unique_ptr<Graph> &transposedGraph, unique_ptr<Graph> &influencedGraph, int removeNodes,
                              const set<int> &maxSeedSet, const set<int> &envelopedNodes,
                              vector<int> activatedSet, string modular) {

    bool tshoot = true;
    bool tshoot1 = true;//Control whether the assert statements are executed
    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet
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
        node.second = (float) transposedGraph->NodeinRRsetsWithCounts[i] * influencedGraph->initialNodeinRRsetsWithCounts[i];
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
        if (tGraphNodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid) == 0 &&
            envelopedNodes.count(nodeid) == 0) {
            tGraphNodesToRemove.insert(nodeid);
            //tGraphNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            tGraphNodesToRemoveUnsorted.push_back(nodeid);
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }

    if (tshoot2 && useEnvelop) {
        cout << "Transposed Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        myfile << "Transposed Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }


    assert(("Mismatch in tGraphNodesToRemove", tGraphNodesToRemove.size() == removeNodes));

    //Nodes removed from modGraph with their transposedGraph values
    if (tshoot3) {
        cout << endl;
        cout << "Nodes removed from modGraph with their transposedGraph values" << endl;
        cout << "RemovedNode\tModGraphStrength\ttransposedGraphStrength\ttotalStrength" << endl;
        for (int i = 0; i < modNodesToRemoveUnsorted.size(); i++) {
            int currNode = modNodesToRemoveUnsorted[i];
            float totStr = (float) influencedGraph->initialNodeinRRsetsWithCounts[currNode] *
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

    cout << "\nNumber of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing nodes already present in the seed Set that were not added to tGraphRemoveVertices set: " << endl;
    myfile << "Printing nodes already present in the seed Set that were not added to tGraphRemoveVertices set: "
           << endl;
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

    vector<vector<int>>().swap(transposedGraph->rrSets);
    vector<int>().swap(transposedGraph->NodeinRRsetsWithCounts);
    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);
    vector<int>().swap(influencedGraph->initialNodeinRRsetsWithCounts);

    return tGraphNodesToRemove;
}

set<int>
countNodesRemoveVertices(unique_ptr<Graph> &countingNodesGraph, int removeNodes, const set<int> &maxSeedSet,
                         const set<int> &envelopedNodes, vector<int> activatedSet, string modular) {

    bool tshoot = false;//Prints the graphTranspose after the nodes have been deleted
    bool tshoot1 = true;//Controls the assert statements
    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    //Random RR sets
    set<int> alreadyinSeed = set<int>();
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    vector<int>().swap(countingNodesGraph->NodeinRRsetsWithCounts);
    cout << "R = " << R << endl;
    countingNodesGraph->generateRandomRRSetsFromTargets(R, activatedSet, modular, resultLogFile);
    cout << "\n RRsets done " << flush;
    resultLogFile << "\n RRsets done " << flush;

    //Find nodes to be removed
    vector<pair<int, int>> SortedNodeidCounts = vector<pair<int, int>>();
    for (int i = 0; i < countingNodesGraph->NodeinRRsetsWithCounts.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = countingNodesGraph->NodeinRRsetsWithCounts[i];
        SortedNodeidCounts.push_back(node);
    }

    std::sort(SortedNodeidCounts.begin(), SortedNodeidCounts.end(), sortbysecdesc);
    assert(SortedNodeidCounts.at(0).second >= SortedNodeidCounts.at(1).second);
//    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);

    set<int> nodesToRemove;
    int count = 0;
    int j = 0;
    while (j < removeNodes && j < SortedNodeidCounts.size()) {
        int nodeid = SortedNodeidCounts.at(count).first;
        if (nodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid) == 0 && envelopedNodes.count(nodeid) == 0) {
            nodesToRemove.insert(nodeid);
            countNodesToRemoveUnsorted.push_back(
                    nodeid);//countNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }
    if (tshoot2 && useEnvelop) {
        cout
                << "countNodes Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        myfile
                << "countNodes Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }

    vector<pair<int, int>>().swap(SortedNodeidCounts);
    cout << "\nNumber of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    resultLogFile << "\nNumber of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "\nPrinting the nodes already in seed that were not added to countNodes: " << endl;
    myfile << "Printing the nodes already in seed that were not added to countNodes: " << endl;
    printSet(alreadyinSeed);

    int numEdgesAtStart = countingNodesGraph->m;
    int totalNumEdgesToDelete = 0;

    for (int node:nodesToRemove) {

        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < countingNodesGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += countingNodesGraph->graphTranspose[k].size();
                if (k == node) {
                    numEdgesToDelete += countingNodesGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < countingNodesGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += countingNodesGraph->graph[k].size();
                if (k == node) {
                    numEdgesToDelete += countingNodesGraph->graph[k].size();
                }
            }
        }

        totalNumEdgesToDelete += numEdgesToDelete;
        countingNodesGraph->removeOutgoingEdges(node);
        assert(("Here . .. .", countingNodesGraph->graph[node].size() == 0));
        assert(("Here . .. .", countingNodesGraph->graphTranspose[node].size() == 0));
        countingNodesGraph->assertCorrectNodesAreDeleted(node, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                         totalEdgesInTransGraphPre);
    }
    assert(("Mismatch in modNodesToRemove", nodesToRemove.size() == removeNodes));


    if (tshoot1) {
        int totalNumOfEdges = 0;
        for (int k = 0; k < countingNodesGraph->graph.size(); k++) {
            totalNumOfEdges += countingNodesGraph->graph[k].size();
        }
        assert(("removeVertices() Divergence betn something", totalNumOfEdges ==
                                                              numEdgesAtStart - totalNumEdgesToDelete));
    }

    if (tshoot) {
        cout << "Printing the transposed graph after the nodes have been deleted: " << endl;
        print2DVector(countingNodesGraph->graphTranspose);
    }

    countingNodesGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int modStrength = 0;
    for (int i = 0; i < countingNodesGraph->NodeinRRsetsWithCounts.size(); i++) {
        modStrength += countingNodesGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n After removing Modular Strength is " << modStrength;
    resultLogFile << "\n \n After removing Modular Strength is " << modStrength;
    myfile << modStrength << " <-Count Strength\n";
    vector<vector<int>>().swap(countingNodesGraph->rrSets);
//    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);
    return nodesToRemove;
}

set<int>
topKInflNodesRemoveVertices(unique_ptr<Graph> &topKInflNodesGraph, int removeNodes, const set<int> &maxSeedSet,
                            const set<int> &envelopedNodes, vector<int> activatedSet, string modular) {

    bool tshoot = false;//Prints the graphTranspose after the nodes have been deleted
    bool tshoot1 = true;//Controls the assert statements
    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    //Calculating R
    double epsilon = (double) EPSILON;
    int n = (int) activatedSet.size();
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "R = " << R << endl;

    set<int> nodesToRemove;
    nodesToRemove = getSeed(removeNodes, topKInflNodesGraph, activatedSet, maxSeedSet, envelopedNodes, set<int>(),
                            set<int>(),
                            NULL);

    int numEdgesAtStart = topKInflNodesGraph->m;
    int totalNumEdgesToDelete = 0;

    for (int node:nodesToRemove) {

        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < topKInflNodesGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += topKInflNodesGraph->graphTranspose[k].size();
                if (k == node) {
                    numEdgesToDelete += topKInflNodesGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < topKInflNodesGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += topKInflNodesGraph->graph[k].size();
                if (k == node) {
                    numEdgesToDelete += topKInflNodesGraph->graph[k].size();
                }
            }
        }

        totalNumEdgesToDelete += numEdgesToDelete;
        topKInflNodesGraph->removeOutgoingEdges(node);
        assert(("Here . .. .", topKInflNodesGraph->graph[node].size() == 0));
        assert(("Here . .. .", topKInflNodesGraph->graphTranspose[node].size() == 0));
        topKInflNodesGraph->assertCorrectNodesAreDeleted(node, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                         totalEdgesInTransGraphPre);
    }
    assert(("Mismatch in modNodesToRemove", nodesToRemove.size() == removeNodes));


    if (tshoot1) {
        int totalNumOfEdges = 0;
        for (int k = 0; k < topKInflNodesGraph->graph.size(); k++) {
            totalNumOfEdges += topKInflNodesGraph->graph[k].size();
        }
        assert(("removeVertices() Divergence betn something", totalNumOfEdges ==
                                                              numEdgesAtStart - totalNumEdgesToDelete));
    }

    if (tshoot) {
        cout << "Printing the transposed graph after the nodes have been deleted: " << endl;
        print2DVector(topKInflNodesGraph->graphTranspose);
    }

    topKInflNodesGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int modStrength = 0;
    for (int i = 0; i < topKInflNodesGraph->NodeinRRsetsWithCounts.size(); i++) {
        modStrength += topKInflNodesGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n After removing Modular Strength is " << modStrength;
    resultLogFile << "\n \n After removing Modular Strength is " << modStrength;
    myfile << modStrength << " <-Count Strength\n";
    vector<vector<int>>().swap(topKInflNodesGraph->rrSets);
//    vector<int>().swap(influencedGraph->NodeinRRsetsWithCounts);
    return nodesToRemove;
}

void nodesToRemoveInCountGraph(unique_ptr<Graph> &countGraph, set<int> &countGraphNodes) {

    cout << "\nnodes to remove in countGraph: ";
    resultLogFile << "\nnodes to remove in countGraph: ";

    for (int i:countGraphNodes) {
        cout << i << " ";
        resultLogFile << i << " ";

        bool tshoot1 = true;
        int totalEdgesInCountGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < countGraph->graphTranspose.size(); k++) {
                totalEdgesInCountGraphPre += countGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += countGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < countGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += countGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += countGraph->graph[k].size();
                }
            }
        }

        countGraph->removeOutgoingEdges(i);
        assert(countGraph->graph[i].size() == 0);
        assert(countGraph->graphTranspose[i].size() == 0);
        countGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                 totalEdgesInCountGraphPre);
    }

}

void nodesToRemoveInTopKInflGraph(unique_ptr<Graph> &topKInflGraph, set<int> &topKInflGraphNodes) {
    cout << "\nnodes to remove in topKInflGraph: ";
    resultLogFile << "\nnodes to remove in topKInflGraph: ";

    for (int i:topKInflGraphNodes) {
        cout << i << " ";
        resultLogFile << i << " ";

        bool tshoot1 = true;
        int totalEdgesInTopKInflGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < topKInflGraph->graphTranspose.size(); k++) {
                totalEdgesInTopKInflGraphPre += topKInflGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += topKInflGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < topKInflGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += topKInflGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += topKInflGraph->graph[k].size();
                }
            }
        }

        topKInflGraph->removeOutgoingEdges(i);
        assert(topKInflGraph->graph[i].size() == 0);
        assert(topKInflGraph->graphTranspose[i].size() == 0);
        topKInflGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                    totalEdgesInTopKInflGraphPre);
    }
}

void removingNodesFromGraph(unique_ptr<Graph> &myGraph, set<int> &nodesToRemove) {

    int totalNumEdgesToDelete = 0;
    for (int i:nodesToRemove) {
        cout << i << " ";
        resultLogFile << i << " ";

        bool tshoot1 = true;
        int totalEdgesInTopKInflGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < myGraph->graphTranspose.size(); k++) {
                totalEdgesInTopKInflGraphPre += myGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += myGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < myGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += myGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += myGraph->graph[k].size();
                }
            }
        }

        totalNumEdgesToDelete += numEdgesToDelete;
        myGraph->removeOutgoingEdges(i);
        assert(myGraph->graph[i].size() == 0);
        assert(myGraph->graphTranspose[i].size() == 0);

        myGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre, totalEdgesInTopKInflGraphPre);
        if (tshoot1) {
            int totalNumOfEdges = 0;
            int numEdgesAtStart = myGraph->m;

            for (int k = 0; k < myGraph->graph.size(); k++) {
                totalNumOfEdges += myGraph->graph[k].size();
            }
            assert(("Divergence betn something", totalNumOfEdges == numEdgesAtStart - totalNumEdgesToDelete));
            totalNumOfEdges = 0;
            for (int k = 0; k < myGraph->graphTranspose.size(); k++) {
                totalNumOfEdges += myGraph->graphTranspose[k].size();
            }
            assert(("Divergence betn something", totalNumOfEdges == numEdgesAtStart - totalNumEdgesToDelete));
        }
    }
}

void removingNodesInSubModImpactTopCritGraph(unique_ptr<Graph> &subModImpactTopCritGraph, set<int>* subModImpactTopCritNodesRemove, set<int> &subModImpactTopCritNodesToRemove) {

    bool tshoot1 = true;

    cout << "\nnodes to remove in subModImpactTopCritGraph: ";
    resultLogFile << "\nnodes to remove in subModImpactTopCritGraph: ";

    int totalNumEdgesToDelete = 0;
    for (int i: *subModImpactTopCritNodesRemove) {
        cout << i << " ";
        resultLogFile << i << " ";

        bool tshoot1 = true;
        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < subModImpactTopCritGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += subModImpactTopCritGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += subModImpactTopCritGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < subModImpactTopCritGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += subModImpactTopCritGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += subModImpactTopCritGraph->graph[k].size();
                }
            }

            totalNumEdgesToDelete += numEdgesToDelete;
        }

        subModImpactTopCritGraph->removeOutgoingEdges(i);
        subModImpactTopCritNodesToRemove.insert(i);

        assert(subModImpactTopCritGraph->graph[i].size() == 0);
        assert(subModImpactTopCritGraph->graphTranspose[i].size() == 0);
        subModImpactTopCritGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                     totalEdgesInTransGraphPre);
    }

    if (tshoot1) {
        int totalNumOfEdges = 0;
        int numEdgesAtStart = subModImpactTopCritGraph->m;

        for (int k = 0; k < subModImpactTopCritGraph->graph.size(); k++) {
            totalNumOfEdges += subModImpactTopCritGraph->graph[k].size();
        }
        assert(("subModImpactTopCritGraph() Divergence betn something", totalNumOfEdges ==
                                                                            numEdgesAtStart - totalNumEdgesToDelete));
        totalNumOfEdges = 0;
        for (int k = 0; k < subModImpactTopCritGraph->graphTranspose.size(); k++) {
            totalNumOfEdges += subModImpactTopCritGraph->graphTranspose[k].size();
        }
        assert(("subModImpactTopCritGraph() Divergence betn something", totalNumOfEdges ==
                                                                            numEdgesAtStart - totalNumEdgesToDelete));
    }
}

void inflInCountGraph(int k, unique_ptr<Graph> &countGraph, set<int> &maxSeed, vector<int> &activatedSet,
                      vector<int> &countGraphResults) {

    cout << k << "---" << "\nCountNodes Graph Results: " << endl;
    resultLogFile << "\nCountNodes Graph Results" << endl;
    int infNum = oldNewIntersection(countGraph, maxSeed, activatedSet, resultLogFile);
    vector<vector<int>>().swap(countGraph->rrSets);
    countGraphResults.push_back(infNum);
    myfile << infNum << " ";

}

void inflInTopKInflGraph(int k, unique_ptr<Graph> &topKInflGraph, set<int> &maxSeed, vector<int> &activatedSet,
                         vector<int> &topKInflGraphResults) {

    cout << k << "---" << "\nTopKInfl Graph Results: " << endl;
    resultLogFile << "\nTopKInfl Graph Results" << endl;
    int infNum = oldNewIntersection(topKInflGraph, maxSeed, activatedSet, resultLogFile);
    vector<vector<int>>().swap(topKInflGraph->rrSets);
    topKInflGraphResults.push_back(infNum);
    myfile << infNum << "\n";

}

int calcIntersection(const set<int> &set1, const set<int> &set2){

    int count = 0;
    for (int i:set1) {
        if (set2.count(i) == 1) count++;
    }

    return count;
}

void newDiffusion(unique_ptr<Graph> &newModGraph, unique_ptr<Graph> &subNewGraph, unique_ptr<Graph> &modImpactGraph,
                  unique_ptr<Graph> &tGraph, unique_ptr<Graph> &countGraph, unique_ptr<Graph> &topKInflGraph,
                  unique_ptr<Graph> &subModtopKInflGraph, unique_ptr<Graph> &subModImpactTopCritGraph,
                  unique_ptr<Graph> &subModTopCritGraphNew,
                  set<int> modNodes, set<int> &subModNodes, set<int> *removalModImpact, set<int> tGraphNodes,
                  set<int> &countGraphNodes, set<int> &topKInflGraphNodes, set<int> &subModTopKInflNodesRemove,
                  set<int> *subModImpactNodesToRemove, set<int> &subModTopCritNodesToRemove,
                  vector<int> &activatedSet, int newSeed, float percentageTargetsFloat, string convertedFile,
                  set<int> prevSelectSeed, vector<int> &subModImpactNodesToRemoveUnsorted,
                  vector<int> &subModNodesToRemoveUnsorted, vector<int> &subModImpactTopCritNodesToRemoveUnsorted,
                  vector<int> &subModTopCritNodesToRemoveUnsorted) {

    bool tshoot = true;

    //Stores the influence values calculated finally in each of the k number of iterations
    vector<int> modResults;
    vector<int> SubmodResults;
    vector<int> modImpactResults;
    vector<int> tGraphResults;
    vector<int> countGraphResults;
    vector<int> topKInflGraphResults;
    vector<int> subModTopKInflResults;
    vector<int> subModImpactTopCritResults;
    vector<int> subModTopCritResults;

    cout << "\nnodes To remove in mod graph: ";
    removingNodesFromGraph(newModGraph, modNodes);

    cout << "\nnodes To remove in submod graph " << flush;
    removingNodesFromGraph(subNewGraph, subModNodes);

    cout << "\nnodes To remove in mod Impact graph " << flush;
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

        modImpactGraph->removeOutgoingEdges(i);
        removalModImpactNodes.insert(i);

        assert(modImpactGraph->graph[i].size() == 0);
        assert(modImpactGraph->graphTranspose[i].size() == 0);
        modImpactGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                     totalEdgesInTransGraphPre);
    }

    cout << "\nnodes to remove in transposedGraph: ";
    removingNodesFromGraph(tGraph, tGraphNodes);

    /*
     * Uncomment only if the countNodes method in executeTIMTIMfullGraph() method has been uncommented as well
     * Also uncomment the if(someCondition) block where you are calculating the infl in the resulting graph
     * Note that the else condition of that statement has not been written to take into account the additional 2 methods that we wrote

     nodesToRemoveInCountGraph(countGraph, countGraphNodes);
    nodesToRemoveInTopKInflGraph(topKInflGraph, topKInflGraphNodes);

     */

    cout << "\nnodes to remove in SubModtopKInflGraph: ";
    removingNodesFromGraph(subModtopKInflGraph, subModTopKInflNodesRemove);

    set<int> subModImpactTopCritNodesRemove;
    removingNodesInSubModImpactTopCritGraph(subModImpactTopCritGraph, subModImpactNodesToRemove,
                                            subModImpactTopCritNodesRemove);
    cout << "\nnodes to remove in subModTopCritGraphNew: ";
    removingNodesFromGraph(subModTopCritGraphNew, subModTopCritNodesToRemove);

    //Print out nodes to be removed only for myfile
    if (tshoot) {

        //Print out nodes to be removed only for myfile
        //Nodes are printed out in the order that they were added in - so most strength to least strength
        cout << flush;
        myfile << "\n\nnodes To remove in mod graph:\t ";
        for (int i:modNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in subModTopKInfl graph: ";
        for (int i:subModTopKInflNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in transposedGraph: ";
        for (int i:tGraphNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in mod Impact graph: ";
        for (int i: subModImpactNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in submod graph:\t ";
        for (int i:subModNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in subModImpactTopCritGraph graph: ";
        for (int i:subModImpactTopCritNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in subModTopCritGraphNew graph: ";
        for (int i:subModTopCritNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        /*
        myfile << "\nnodes To remove in countNodes graph:\t ";
        for (int i:countNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in topKInfl graph (sorted list):\t ";
        for (int i:topKInflGraphNodes) {
            myfile << i << " ";
        }
        cout << flush;
         */
        cout << flush;

    }

    cout << endl;
    myfile << endl;
    cout << "\nintersection of modTopKInfl and transposedGraph nodes to remove "    << calcIntersection(modNodes, tGraphNodes);
    cout << "\nintersection of modTopKInfl and SubModTopKInfl nodes to remove "     << calcIntersection(modNodes, subModTopKInflNodesRemove);
    cout << "\nintersection of modTopKInfl and submod nodes to remove "             << calcIntersection(modNodes, subModNodes);
    cout << "\nintersection of modTopKInfl and modImpact nodes to remove "          << calcIntersection(modNodes, removalModImpactNodes);
    cout << "\nintersection of modTopKInfl and subModImpactTopCrit nodes to remove "<< calcIntersection(modNodes, subModImpactTopCritNodesRemove);
    cout << "\nintersection of modTopKInfl and subModTopCrit nodes to remove "      << calcIntersection(modNodes, subModTopCritNodesToRemove) << endl;
    cout << "\nintersection of submod and transposedGraph nodes to remove "         << calcIntersection(subModNodes, tGraphNodes);
    cout << "\nintersection of submod and SubModTopKInfl nodes to remove "          << calcIntersection(subModNodes, subModTopKInflNodesRemove);
    cout << "\nintersection of submod and modImpact nodes to remove "               << calcIntersection(subModNodes, removalModImpactNodes);
    cout << "\nintersection of submod and subModImpactTopCrit nodes to remove "     << calcIntersection(subModNodes, subModImpactTopCritNodesRemove);
    cout << "\nintersection of submod and subModTopCrit nodes to remove "           << calcIntersection(subModNodes, subModTopCritNodesToRemove) << endl;
    cout << "\nintersection of modImpact and transposedGraph nodes to remove "      << calcIntersection(removalModImpactNodes, tGraphNodes);
    cout << "\nintersection of modImpact and SubModTopKInfl nodes to remove "       << calcIntersection(removalModImpactNodes, subModTopKInflNodesRemove);
    cout << "\nintersection of modImpact and subModImpactTopCrit nodes to remove "  << calcIntersection(removalModImpactNodes, subModImpactTopCritNodesRemove);
    cout << "\nintersection of modImpact and subModTopCrit nodes to remove "        << calcIntersection(removalModImpactNodes, subModTopCritNodesToRemove) << endl;
    cout << "\nintersection of SubModTopKInfl and subModImpactTopCrit nodes to remove " << calcIntersection(subModTopKInflNodesRemove, subModImpactTopCritNodesRemove);
    cout << "\nintersection of SubModTopKInfl and subModTopCrit nodes to remove "   << calcIntersection(subModTopKInflNodesRemove, subModTopCritNodesToRemove) << endl;
    cout << "\nintersection of subModImpactTopCrit and subModTopCrit nodes to remove " << calcIntersection(subModImpactTopCritNodesRemove, subModTopCritNodesToRemove) << endl;


    cout << endl;
    myfile << "\nintersection of modTopKInfl and transposedGraph nodes to remove "    << calcIntersection(modNodes, tGraphNodes);
    myfile << "\nintersection of modTopKInfl and SubModTopKInfl nodes to remove "     << calcIntersection(modNodes, subModTopKInflNodesRemove);
    myfile << "\nintersection of modTopKInfl and submod nodes to remove "             << calcIntersection(modNodes, subModNodes);
    myfile << "\nintersection of modTopKInfl and modImpact nodes to remove "          << calcIntersection(modNodes, removalModImpactNodes);
    myfile << "\nintersection of modTopKInfl and subModImpactTopCrit nodes to remove "<< calcIntersection(modNodes, subModImpactTopCritNodesRemove);
    myfile << "\nintersection of modTopKInfl and subModTopCrit nodes to remove "      << calcIntersection(modNodes, subModTopCritNodesToRemove) << endl;
    myfile << "\nintersection of submod and transposedGraph nodes to remove "         << calcIntersection(subModNodes, tGraphNodes);
    myfile << "\nintersection of submod and SubModTopKInfl nodes to remove "          << calcIntersection(subModNodes, subModTopKInflNodesRemove);
    myfile << "\nintersection of submod and modImpact nodes to remove "               << calcIntersection(subModNodes, removalModImpactNodes);
    myfile << "\nintersection of submod and subModImpactTopCrit nodes to remove "     << calcIntersection(subModNodes, subModImpactTopCritNodesRemove);
    myfile << "\nintersection of submod and subModTopCrit nodes to remove "           << calcIntersection(subModNodes, subModTopCritNodesToRemove) << endl;
    myfile << "\nintersection of modImpact and transposedGraph nodes to remove "      << calcIntersection(removalModImpactNodes, tGraphNodes);
    myfile << "\nintersection of modImpact and SubModTopKInfl nodes to remove "       << calcIntersection(removalModImpactNodes, subModTopKInflNodesRemove);
    myfile << "\nintersection of modImpact and subModImpactTopCrit nodes to remove "  << calcIntersection(removalModImpactNodes, subModImpactTopCritNodesRemove);
    myfile << "\nintersection of modImpact and subModTopCrit nodes to remove "        << calcIntersection(removalModImpactNodes, subModTopCritNodesToRemove) << endl;
    myfile << "\nintersection of SubModTopKInfl and subModImpactTopCrit nodes to remove " << calcIntersection(subModTopKInflNodesRemove, subModImpactTopCritNodesRemove);
    myfile << "\nintersection of SubModTopKInfl and subModTopCrit nodes to remove "   << calcIntersection(subModTopKInflNodesRemove, subModTopCritNodesToRemove) << endl;
    myfile << "\nintersection of subModImpactTopCrit and subModTopCrit nodes to remove " << calcIntersection(subModImpactTopCritNodesRemove, subModTopCritNodesToRemove) << endl;
    myfile << endl;

    //Random RR sets
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "\nRR sets are: " << R << endl;
    resultLogFile << "\nRR sets are: " << R << "\n";

    cout << "\nCalculating the ModImpactStrength using the Old method: " << endl;
    modImpactGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int modImapactStrength = 0;
    for (int i = 0; i < modImpactGraph->NodeinRRsetsWithCounts.size(); i++) {
        modImapactStrength += modImpactGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n After removing (OLD_METHOD) mod Impact Modular Strength is " << modImapactStrength << "\n";
    resultLogFile << "\n \n After removing mod Impact Modular Strength is " << modImapactStrength << "\n";

    myfile << modImapactStrength << " <- OLD_ModImpact_Strength\n";
    vector<vector<int>>().swap(modImpactGraph->rrSets);
    vector<int>().swap(modImpactGraph->NodeinRRsetsWithCounts);

    cout << "\nCalculating the ModImpactStrength using the NEW method: " << endl;
    subModImpactTopCritGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    modImapactStrength = 0;
    for (int i = 0; i < subModImpactTopCritGraph->NodeinRRsetsWithCounts.size(); i++) {
        modImapactStrength += subModImpactTopCritGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n\nAfter removing (NEW_METHOD) mod Impact Modular Strength is " << modImapactStrength << "\n";
    resultLogFile << "\n\nAfter removing mod Impact Modular Strength is " << modImapactStrength << "\n";

    myfile << modImapactStrength << " <- NEW_ModImpact_Strength\n";
    vector<vector<int>>().swap(subModImpactTopCritGraph->rrSets);
    vector<int>().swap(subModImpactTopCritGraph->NodeinRRsetsWithCounts);

    set<int> maxInfluenceSeed = set<int>();
    int maxInfluenceNum = 0;
    set<int> seedSet = set<int>();

    set<int> modseedSet = set<int>();
    set<int> subModseedSet = set<int>();
    set<int> modImpactseedSet = set<int>();
    set<int> tGraphSeedSet = set<int>();

    unique_ptr<Graph> maxSeedGraph = make_unique<Graph>();
    maxSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        maxSeedGraph->setPropogationProbability(probability);
    }

    set<int> maxSeed;//Stores the seedSet that will be used for diffusion in all of the 4 processes

    /*
    if (!someCondition) {
        cout << "\n \n******* Max influence start******** \n" << flush;
        myfile << "Max influence Seed Set in the original graph considering that we can remove all vertices: " << endl;
        maxInfluenceSeed = getSeed(budget, maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                                   NULL);
        vector<vector<int>>().swap(maxSeedGraph->rrSets);
        maxInfluenceNum = oldNewIntersection(maxSeedGraph, maxInfluenceSeed, activatedSet, resultLogFile);
        myfile << maxInfluenceNum << " <-MaxInfluence Num\n";
        cout << "\n \n******* Max influence end ******** \n" << flush;
        maxSeedGraph.reset();

        //Calculating maxSeed to be used as the seed set for all the 4 methods:
        int inflOfMaxSeed;//Stores the influence of the max seed on the original graph G

        unique_ptr<Graph> graph = make_unique<Graph>();
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
        }
    }
     */


    if (someCondition) {
        cout << "Setting max Seed to be the previously selected maxSeed" << endl;
        maxSeed = prevSelectSeed;
    }

//    SeedSet *SeedClass = new SeedSet(newGraph, budget);

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

//        cout << "\n\nMaxInfl Seed Set: " << endl;
//        myfile << "\n\nMaxInfl Seed Set: " << endl;
//        printSet(maxInfluenceSeed);

        cout << "\nChosen MaxInfl Seed Set to perform diffusion: " << endl;
        myfile << "\nChosen MaxInfl Seed Set to perform diffusion: " << endl;
        printSet(maxSeed);

    }

    Graph *graph;
    int k = 0;
    if (someCondition) {

        cout << "Using the best seed found at the start of the experiment" << endl;
        myfile << "Using the best seed found at the start of the experiment" << endl;
        /*
         * a) This condition is executed when the seed set is fixed before the start of the experiment.
         *      - either using the max seed as the seed set
         *      - or using the random seed as the seed set
         *
        */
        myfile << "\n\nmodTopK SubModTopK Old_SubMod New_SubMod Old_ModImpact New_ModImpact Transposed \n";
        while (k < 3) {

            /*switch (5) {

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
            }*/

            cout << "\n********** k = " << k << " **********" << endl;

            cout << "\n\nSelected SeedSet in original graph: " << flush;
            resultLogFile << "\n\nSelected SeedSet in original graph: " << flush;
            for (auto item:maxSeed) {
                cout << item << " ";
                resultLogFile << item << " ";
            }

            int infNum = 0;

            cout <<"\n" << k << "---" << "\nmodTopK Results: " << endl;
            infNum = oldNewIntersection(newModGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(newModGraph->rrSets);
            modResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nSubModTopK Graph Results: " << endl;
            infNum = oldNewIntersection(subModtopKInflGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subModtopKInflGraph->rrSets);
            subModTopKInflResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nOld_SubMod Results: " << endl;
            infNum = oldNewIntersection(subNewGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subNewGraph->rrSets);
            SubmodResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nNew_SubMod Results: " << endl;
            infNum = oldNewIntersection(subModTopCritGraphNew, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subModTopCritGraphNew->rrSets);
            subModTopCritResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nOld_ModImpact Results: " << endl;
            infNum = oldNewIntersection(modImpactGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(modImpactGraph->rrSets);
            modImpactResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nNew_Mod Impact Results: " << endl;
            infNum = oldNewIntersection(subModImpactTopCritGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subModImpactTopCritGraph->rrSets);
            subModImpactTopCritResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nTransposed Graph Results: " << endl;
            infNum = oldNewIntersection(tGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(tGraph->rrSets);
            tGraphResults.push_back(infNum);
            myfile << infNum << "\n";

            /*
             * Uncomment only if the countNodes method in executeTIMTIMfullGraph() method has been uncommented as well
             * Also uncomment the if(someCondition) block where you are calculating the infl in the resulting graph

             inflInCountGraph(k, countGraph, maxSeed, activatedSet, countGraphResults);
            inflInTopKInflGraph(k, countGraph, maxSeed, activatedSet, countGraphResults);

             */
            k++;
        }
    } else {
        cout << "\n\nUsing the best seed in EACH graph" << endl;
        myfile << "Using the best seed in EACH graph" << endl;
        /*
         * This code is executed when someCondition iset to false. So you are not fixing the seed set at the start of the experiment.
         * Instead you start off with the seed set being empty. So all nodes can be removed.
         * Now for each method, you find out the best nodes to remove. Remove those nodes.
         * Now In the resulting graph, find the best seed set. Use that to perform the influence diffusion.
         * So the seed set will be different for each of the methods.
         * */
        myfile << "Unsorted Mod SeedSet: ";
        cout << "Calculating Mod SeedSet: ";
        modseedSet = getSeed(budget, newModGraph, activatedSet, modNodes, set<int>(), set<int>(), set<int>(), NULL);
        myfile << "Unsorted SubMod SeedSet: ";
        cout << "Calculating SubMod SeedSet: ";
        subModseedSet = getSeed(budget, subNewGraph, activatedSet, subModNodes, set<int>(), set<int>(), set<int>(),
                                NULL);
        myfile << "Unsorted ModImpact SeedSet: ";
        cout << "Calculating ModImpact SeedSet: ";
        modImpactseedSet = getSeed(budget, modImpactGraph, activatedSet, removalModImpactNodes, set<int>(), set<int>(),
                                   set<int>(), NULL);
        myfile << "Unsorted Transposed graph SeedSet: ";
        cout << "Calculating Transposed graph SeedSet: ";
        tGraphSeedSet = getSeed(budget, tGraph, activatedSet, tGraphNodes, set<int>(), set<int>(), set<int>(), NULL);

        if (tshoot) {
            cout << "\n\nModular Seed Set: " << endl;
            printSetOnlyInCout(modseedSet);

            cout << "\nSubModular Seed Set: " << endl;
            printSetOnlyInCout(subModseedSet);

            cout << "\nModImpact Seed Set: " << endl;
            printSetOnlyInCout(modImpactseedSet);

            cout << "\nTransposedGraph Seed Set: " << endl;
            printSetOnlyInCout(tGraphSeedSet);
        }

        myfile << "\n\nMOD SUBMOD MOD-IMPACT Transposed\n";
        while (k < 3) {

            /*switch (5) {

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
            }*/
            cout << "\n********** k = " << k << " **********" << endl;

//            cout << "\n \nSelected new SeedSet in original graph: " << flush;
//            resultLogFile << "\n \nSelected new SeedSet in original graph: " << flush;
//            for (auto item:maxSeed) {
//                cout << item << " ";
//                resultLogFile << item << " ";
//            }

            int infNum = 0;

            cout << "\n" << k << " - Mod Results: " << endl;
            resultLogFile << "\nMod Results: " << endl;
            infNum = oldNewIntersection(newModGraph, modseedSet, activatedSet, resultLogFile);
            vector<vector<int>>().swap(newModGraph->rrSets);
            modResults.push_back(infNum);
            myfile << infNum << " ";

            cout << "\n" << k << " - Sub Mod Results: " << endl;
            resultLogFile << "\nSub Mod Results: " << endl;
            infNum = oldNewIntersection(subNewGraph, subModseedSet, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subNewGraph->rrSets);
            SubmodResults.push_back(infNum);
            myfile << infNum << " ";

            cout << "\n" << k << " - Mod Impact Results: " << endl;
            resultLogFile << "\nMod Impact Results: " << endl;
            infNum = oldNewIntersection(modImpactGraph, modImpactseedSet, activatedSet, resultLogFile);
            vector<vector<int>>().swap(modImpactGraph->rrSets);
            modImpactResults.push_back(infNum);
            myfile << infNum << " ";

            cout << "\n" << k << " - Transposed Graph Results: " << endl;
            resultLogFile << "\nTransposed Graph Results" << endl;
            infNum = oldNewIntersection(tGraph, tGraphSeedSet, activatedSet, resultLogFile);
            vector<vector<int>>().swap(tGraph->rrSets);
            tGraphResults.push_back(infNum);
            myfile << infNum << "\n";

            k++;
        }
    }


    double subModGain = 0;
    double ImapctGain = 0;
    double newSubModGain = 0;
    double newImpactGain = 0;
    for (int i = 0; i < k; i++) {
        subModGain += float(modResults[i] - SubmodResults[i]) / float(modResults[i]);
        ImapctGain += float(modResults[i] - modImpactResults[i]) / float(modResults[i]);
        newSubModGain += float(subModTopKInflResults[i] - subModTopCritResults[i]) / float(subModTopKInflResults[i]);
        newImpactGain += float(subModTopKInflResults[i] - subModImpactTopCritResults[i]) / float(subModTopKInflResults[i]);
    }
    subModGain = (float) subModGain / k;
    ImapctGain = (float) ImapctGain / k;
    newSubModGain = (float) newSubModGain / k;
    newImpactGain = (float) newImpactGain / k;
    myfile << subModGain << " <-subModGain\n" << ImapctGain << " <-ModImpactGain\n";
    myfile << newSubModGain << " <-newSubModGain\n" << newImpactGain << " <-newImpactGain\n";
}


/************************************************ OLD SUB MODULAR METHOD STARTS *********************************************************************/


//reComputeDependencyValues: dont have to redo all the computation from scratch
void reComputeDependencyValues(vector<int> &dependencyValues, unique_ptr<Graph> &influencedGraph,
                               vector<pair<int, int>> &ASdegree) {

    clock_t startTime = clock();
    bool tshoot = true;//Prints values to file

    ASdegree = vector<pair<int, int>>();//Because we are recalculating the dependency values, we need to initialise ASdegree to empty again
    for (int i = 0; i < dependencyValues.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = dependencyValues[i];
        ASdegree.push_back(node);
        if (tshoot) {
            dependValues << dependencyValues[i] << endl;
        }
    }

    dependValues << "---------------------------------------" << endl;
    std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);
    assert(ASdegree.at(0).second >= ASdegree.at(1).second);
    reComputeDependencyValuesTime += (clock() - startTime);
}

void computeDependencyValues(vector<int> &dependencyValues, unique_ptr<Graph> &influencedGraph,
                             vector<pair<int, int>> &ASdegree) {

    bool tshoot = true;//prints values to file
    cout << "Calculating Dependency Values" << endl;

    for (int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++) {                              //for each RRSet in dependancyVector
        for (int rowIdx = 0; rowIdx < influencedGraph->dependancyVector[rrSetId]->size(); rowIdx++) {                   //for each row in the dependancyMatrix
            int vertex = (*influencedGraph->indexToVertex[rrSetId])[rowIdx];                                            //find the vertex that was mapped to that index
            for (int colIdx = 0; colIdx < (*influencedGraph->dependancyVector[rrSetId])[rowIdx].size(); colIdx++) {     //for each col in that row
//                dependencyValues[vertex] += influencedGraph->dependancyVector[rrSetId][rowIdx][colIdx];               //Add the value to the existing dependencyValues of that vertex
                if ((*influencedGraph->dependancyVector[rrSetId])[rowIdx][colIdx]) {
                    dependencyValues[vertex] += 1;
                }
            }
        }
    }

    ASdegree = vector<pair<int, int>>();
    for (int i = 0; i < dependencyValues.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = dependencyValues[i];
        ASdegree.push_back(node);

        if (tshoot) {
            dependValues << dependencyValues[i] << endl;
        }
    }
    dependValues << "------------------------------------------------------------" << endl;
    std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);//THis is where it crashes.
    assert(ASdegree.at(0).second >= ASdegree.at(1).second);
}

void
computeModImpactNodes(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues,
                      vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet, const set<int> envelopedNodes,
                      set<int> *removalModImpact, vector<int> &nodesToRemoveUnsorted) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    set<int> alreadyinSeed = set<int>();
    ASdegree = vector<pair<int, int>>();

    computeDependencyValues(dependencyValues, influencedGraph, ASdegree);

    cout << "Impact Nodes Sorted!" << endl;

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            removalModImpact->insert(node);
            nodesToRemoveUnsorted.push_back(node);
        } else {
            alreadyinSeed.insert(node);
        }
        index++;
    }

    if (tshoot2 && useEnvelop) {
        cout    << "ModImpact Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        myfile  << "ModImpact Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }

    assert(("Mismatch - removalModImpact and removeNodes", removalModImpact->size() == removeNodes));

//    cout << "Node to be removed by the mod Impact process" << endl;
//    printVector(modImpactNodesToRemoveUnsorted);

    cout << "\nassociated value is: " << alreadyinSeed.size() << endl;
    cout << "Number of nodes for (mod impact) already present in seed set = " << alreadyinSeed.size() << endl;
    resultLogFile << "Number of nodes for (mod impact) already present in seed set = " << alreadyinSeed.size();
    cout << "Printing nodes in modImpact that were not added to removeNodes because they were in seesSet: " << endl;
    myfile << "Printing nodes in modImpact that were not added to removeNodes because they were in seesSet: " << endl;
    printSet(alreadyinSeed);

    //Clearing alreadyinSeed because it contains the modImpact nodes at this point
    alreadyinSeed.clear();
}

//node is the vertex being deleted from all of the dependencyMatrices
void removeFromDependencyVector(int node, unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues,
                                vector<pair<int, int>> &ASdegree) {

    /*Update the dependencyVector datastructure
     *
     * In each RRSet
     *  if node occurs in that RRSet
     *      set all elements in the row index corresponding to that node to 0
     *      set all elements in the column index corresponding to that node to 0
     */

    cout << "Removing vertex: " << node << endl;
    dependValues << "Removing vertex: " << node << endl;
//    vector<int> dependencyValues = vector<int>(influencedGraph->n, 0);

    for (int i = 0; i < influencedGraph->inRRSet[node].size(); i++) {                                                   //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(node);              //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found
            //WARNING: Seemingly both of these work. WHY?
//            fill(influencedGraph->dependancyVector[rrSetId][got->second].begin(), influencedGraph->dependancyVector[rrSetId][got->second].end(), 0);  //Replace all elements in the vertex row with 0;
            fill((*influencedGraph->dependancyVector[rrSetId])[got->second].begin(),
                 (*influencedGraph->dependancyVector[rrSetId])[got->second].end(), false);
            for (int row = 0; row < influencedGraph->dependancyVector[rrSetId]->size(); row++) {                        //Replace all elements in the vertex column with 0;
//                influencedGraph->dependancyVector[rrSetId][row][got->second] = 0;
//                influencedGraph->dependancyVector[rrSetId]->at(row).at(got->second)= 0;
                if ((*influencedGraph->dependancyVector[rrSetId])[row][got->second]) {
                    (*influencedGraph->dependancyVector[rrSetId])[row][got->second] = false;
                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[row]] -= 1;
                }

            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

    dependencyValues[node] = 0;                                                 //Set the value to be 0 manually because we are using reComputeDependencyValues() and not computeDependencyValues() now.
    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed

}

void computeSubModNodes(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues,
                              vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet,
                              const set<int> &envelopedNodes, set<int> &subModNodesToremove, vector<int> &nodesToRemoveUnsorted, set<int> &alreadyinSeed) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            subModNodesToremove.insert(node);
            nodesToRemoveUnsorted.push_back(node);
            if (i < removeNodes) {//Dont call if final vertex to be removed has been found
                removeFromDependencyVector(node, influencedGraph, dependencyValues, ASdegree);
            }
            index = 0;
        } else {
            alreadyinSeed.insert(node);
            index++;
        }
    }

    if (tshoot2 && useEnvelop) {
        cout << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
             << endl;
        myfile
                << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }
}


//node is the vertex being deleted from all of the dependencyMatrices
void testRemoveFromDependencyVector(int node, unique_ptr<Graph> &influencedGraph, vector<int> &testDependencyValues,
                                    vector<pair<int, int>> &testASdegree) {

    /*Update the dependencyVector datastructure
     *
     * In each RRSet
     *  if node occurs in that RRSet
     *      set all elements in the row index corresponding to that node to 0
     *      set all elements in the column index corresponding to that node to 0
     */

    cout << "Removing vertex: " << node << endl;
    dependValues << "Removing vertex: " << node << endl;
    for (int i = 0; i < influencedGraph->inRRSet[node].size(); i++) {                                                   //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(node);              //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found
            fill((*influencedGraph->testDependancyVector[rrSetId])[got->second].begin(),
                 (*influencedGraph->testDependancyVector[rrSetId])[got->second].end(), false);
            for (int row = 0; row < influencedGraph->testDependancyVector[rrSetId]->size(); row++) {                    //Replace all elements in the vertex column with 0;
                if ((*influencedGraph->testDependancyVector[rrSetId])[row][got->second]) {
                    (*influencedGraph->testDependancyVector[rrSetId])[row][got->second] = false;
                    testDependencyValues[(*influencedGraph->indexToVertex[rrSetId])[row]] -= 1;
                }
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

    testDependencyValues[node] = 0;                                                     //Set the value to be 0 manually because we are using reComputeDependencyValues() and not computeDependencyValues() now.
    reComputeDependencyValues(testDependencyValues, influencedGraph, testASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed
}

void removingModNodesForTest(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &testDependencyValues,
                             vector<pair<int, int>> &testASdegree, const set<int> &maxSeedSet,
                             vector<int> &testModNodesToremove, set<int> &alreadyinSeed) {

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = testModNodesToremove[i];
        if (maxSeedSet.count(node) == 0) {
            i++;
            if (i < removeNodes) {//Dont call if final vertex to be removed has been found
                testRemoveFromDependencyVector(node, influencedGraph, testDependencyValues, testASdegree);
            }
            index = 0;
        } else {
            assert(("Shouldnt have reached here", false));
            alreadyinSeed.insert(node);
            index++;
        }
    }
}


set<int> subModularNodesRemove(unique_ptr<Graph> &influencedGraph, vector<int> &activatedSet, int removeNodes,
                               const set<int> &maxSeedSet, const set<int> &envelopedNodes,
                               set<int> *removalModImpact, vector<int> &subModImpactNodesToRemoveUnsorted,
                               vector<int> &subModNodesToRemoveUnsorted) {

    bool tshoot = true;//Prints the dependency values for each node to the file
    bool tshoot1 = true;//Prints the node being removed in each iteration
    bool tshoot2 = false;//Prints the outdegree values for the modNodes removed in Algo1

    clock_t subModReverseStartTime = clock();

    set<int> alreadyinSeed = set<int>();
    set<int> subModNodesToremove;
    vector<pair<int, int>> ASdegree;
    int removalNum = removeNodes;
    vector<int> dependencyValues = vector<int>(influencedGraph->n, 0);

    //Random RR sets
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "\nRR sets are: " << R << endl;
    resultLogFile << "\nRR sets are: " << R << endl;
    influencedGraph->generateRandomRRSetsFromTargets(R, activatedSet, modular, resultLogFile);

    cout << "\nComputing nodes to remove by the Mod Impact method" << endl;
    computeModImpactNodes(influencedGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet, envelopedNodes,
                          removalModImpact, subModImpactNodesToRemoveUnsorted);


    clock_t ModImpactEndTime = clock();
    double totalModImpactTime = double(ModImpactEndTime - subModReverseStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "Mod Impact impact algorithm time in minutes " << totalModImpactTime << endl;
    resultLogFile << "Mod Impact impact algorithm time in minutes" << totalModImpactTime << endl;
    myfile << totalModImpactTime << " <-ModImpactTime\n";
    cout << "******* Completed Mod Impact approach ********" << endl;
    cout << endl;
    cout << endl;

    dependValues << "\n\n******* Completed Mod Impact approach ********" << endl;
    /***************************************************************************************************************************************/

    /*
    cout << "Starting the test for removing mod nodes from dependencyVector" << endl;
    dependValues << "Starting the test for removing mod nodes from dependencyVector" << endl;

    set<int> testModNodesToRemove = set<int>();
    vector<pair<int, int>> testASdegree;
    vector<int> testDependencyValues = vector<int>(influencedGraph->n, 0);

    for(int i = 0; i < modNodesToRemoveUnsorted.size(); i++){
        testModNodesToRemove.insert(modNodesToRemoveUnsorted[i]);
    }
    for(int i = 0; i < dependencyValues.size(); i++){
        testDependencyValues[i] = dependencyValues[i];
        if(tshoot){//remove this since we are already printing the initial valeus while calculating modImpact nodes
            dependValues << dependencyValues[i] << endl;
        }
    }

    dependValues << "---------------------------------------" << endl;

    for(int i = 0; i < ASdegree.size(); i++){//this is also not reuqired
        pair<int, int> node = ASdegree.at(i);
        testASdegree.push_back(node);
    }

    influencedGraph->testDependancyVector = vector<vector<vector<bool>>*>(R);
    vector<vector<bool>>* myMatrix;
    //creating a copy of the dependencyVector
    for(int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++){
        myMatrix = new vector<vector<bool>>();
        for(int rowIdx = 0; rowIdx < (*influencedGraph->dependancyVector[rrSetId]).size(); rowIdx++){
            myMatrix->push_back(vector<bool>());
            for(int colIdx = 0; colIdx < (*influencedGraph->dependancyVector[rrSetId])[rowIdx].size(); colIdx++){
                (*myMatrix)[rowIdx].push_back((*influencedGraph->dependancyVector[rrSetId])[rowIdx][colIdx]);
            }
        }
        influencedGraph->testDependancyVector[rrSetId] = myMatrix;
    }

    removingModNodesForTest(influencedGraph, removeNodes, testDependencyValues, testASdegree, maxSeedSet, modNodesToRemoveUnsorted, alreadyinSeed);
    dependValues << "***************   TEST ENDS HERE   ***************" << endl;

    */

    /***************************************************************************************************************************************/
    cout << "******* Running OLD_SubMod approach ********" << endl;
    dependValues << "******* Running OLD_SubMod approach ********" << endl;

    alreadyinSeed = set<int>();
    computeSubModNodes(influencedGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet, envelopedNodes,
                             subModNodesToremove, subModNodesToRemoveUnsorted, alreadyinSeed);

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

    cout << endl;
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
    cout << "\nSubmodular strength = " << subModStrength << endl;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size();
    resultLogFile << "\n Submodular strength = " << subModStrength;
    myfile << influencedGraph->totalNumNodesInRRSets << " <-Recalculated Init Strength\n";
    myfile << subModStrength << " <-subModStrength\n";
    double totalAlgorithmTime = double(subModReverseEndTime - subModReverseStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\nReverse submodular algorithm time in minutes " << totalAlgorithmTime << endl;
    cout << "Breakup of time taken: " << endl;
    cout << "Total time taken by randomNumGenerator: " << influencedGraph->randomNumGen / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by outer while Loop: " << influencedGraph->whileLoopTime / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Breakup of time taken by outer while Loop: " << endl;
    cout << "Total time taken by initialization: " << influencedGraph->initTime / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by only the loop: " << influencedGraph->onlyLoopTime / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Total time taken by calcDependancyMatrix(): " << influencedGraph->matrixTime / (CLOCKS_PER_SEC * 60)
         << endl;
    cout << "Total time taken by BFS(): " << influencedGraph->bfsTime / (CLOCKS_PER_SEC * 60) << endl;
    resultLogFile << "\n Reverse submodular algorithm time in minutes " << totalAlgorithmTime;
    myfile << totalAlgorithmTime << " <-SubModTime\n";
    return subModNodesToremove;
}


/********************************************************* OLD SUB MODULAR METHOD ENDS *************************************************************/


/************************************************ NEW SUB MODULAR TOP CRIT NEW METHOD STARTS *******************************************************/


//This method is different from repopulateDependencyMatrix() because: --------------------------------------------------
//critNode is the node that was removed since it was chosen as the most critical vertex
//miniRRGraph is the graph that has been created from the original graph after mapping each of the vertices to index
//node belonging to the critNode along with all of its outgoing edges has already been removed at this point
//nodeBeingRemoved is the vertex in the row of critNode (which did not depend upon the critNode for reachability) that has to be removed from the minRRGraph. So, we are basically checking:
//dependence of reachability of each node in the miniRRGraph (formed after removing outgoing edges from the critNode) starting from the origin given that
//nodeBeingRemoved is removed
//both critNode and nodeBeingRemoved are not the actual vertices, but the mapped vertices in this rrSet numbered rrSetId

void repopulateDependencyMatrixAfterCritNodeRemoval(unique_ptr<Graph> &influencedGraph, unique_ptr<vector<vector<int>>> &miniRRGraph, unique_ptr<vector<bool>> &reachableFromSeed,
                                   int rrSetId,
                                   int critNode, int nodeBeingRemoved, vector<int> &dependencyValues) {

    clock_t startTime = clock();
    vector<vector<int>> myGraph = *miniRRGraph;
    vector<bool> prevDependencyValues = (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved];                //Store the previous values so that they can be compared for the dependencyValues vector to be changed
    myGraph[nodeBeingRemoved].clear();

    for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved].size(); i++){                    //Initialize all row entries to TRUE
        if((*reachableFromSeed)[i]){                                                                                    //if the particular node was not originally reachable
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = false;                                 //from the seedSetNode
        }else{
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = true;
        }
    }
//    (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][critNode] = true;                                 //because if reachability of the the seedSetNode depends upon the nodeBeingRemoved,
                                                                                                                        //then we want to capture that information in the dependencyMatrix row corresp. to nodeBeingRemoved

    vector<bool> visitedBFS = vector<bool>(miniRRGraph->size(), false);                                                 //Mark all the vertices as not visited
    deque<int> queue;                                                                                                   //Create a queue for BFS
    visitedBFS[0] = true;                                                                                               //Mark the starting node as visited. starting node will always be node numbered 0
    queue.push_back(0);                                                                                                 //And add it to the queue
    if(nodeBeingRemoved != 0){
        (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][0] = false;                                     //since we are starting the BFS from the node 0, dependence of reachability of 0 from 0 given that the ndoeBeingRemoved is removed is "false"
    }

    while (!queue.empty()) {
        int u = queue.front();
        queue.pop_front();
        for (int i = 0; i < myGraph[u].size(); i++) {
            int v = myGraph[u][i];
            if (!visitedBFS[v]) {
                visitedBFS[v] = true;
                queue.push_back(v);
                if (nodeBeingRemoved != v) {                                                                            //Because reachability of vertexRemoved will depend on itself
                    (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][v] = false;                         //Since v was still reachable after removing vertexRemoved.
                }
            }
        }
    }

    for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved].size(); i++){
        if(prevDependencyValues[i] && !((*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i]) ){             //If in the dependencyMatrix of the row containing nodeBeingRemoved, if the earlier value for vertex w was TRUE but the new value is FALSE
            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[nodeBeingRemoved]] -= 1;                        //Reduce the dependencyValue for the node nodeBeingRemoved
        }else if ( (!prevDependencyValues[i]) && (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] ){      //else if
            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[nodeBeingRemoved]] += 1;                        //Increase the dependencyValue for the node nodeBeingRemoved
        }
    }

    repopulateDependencyMatrixAfterCritNodeRemovalTime += (clock() - startTime);
}

//node is the vertex being deleted from all of the dependencyMatrices
//Different from the earlier removeFromDependencyVector() method because:-----------------------------------------------
void removeCritNodeFromDependencyVectorTopCrit(int node, unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues,
                                   vector<pair<int, int>> &ASdegree) {
    clock_t startInnerLoop = clock();
    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    /*Update the dependencyVector datastructure
     *
     * In each RRSet
     *  if seedSet node occurs in that RRSet
     *      set all elements in the row index corresponding to that node to 0
     *      if(condition) controls the good and the bad method.
     */

    cout << "Removing vertex: " << node << endl;
    dependValues << "Removing vertex: " << node << endl;

    for (int i = 0; i < influencedGraph->inRRSet[node].size(); i++) {                                                   //for each RRSet in inRRSet (each RRSet that contains node)

        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        if (tshoot1) {
            if (influencedGraph->rrSets[i].size() > 10) {
                cout << "PAUUUUUZZZE!!!" << endl;
            }
        }
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(node);              //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the seedSet vertex being removed
            if ( !(*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].empty() ) {                              //Idea is that if there are NO outgoing edges from the seedSetNode, then removing it will not have any affect on the datastr. So we can just ignore, and move to the next rrSetId
                (*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].clear();                                   //remove all the outgoing edges from seedSetNode in the RRGraph stored in rrSetId bucket
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){             //Update the vertices that are now reachable from the (seedSetNode + node)
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){
                        (*influencedGraph->reachableNodesVector[rrSetId])[j] = true;
                    }
                }
                for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++) {           //for each vertex j in the row containing the vertex to to be removed
                    if ((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second) {            //if dependence of reachability of j from source given that node is removed is true && j != node
                        (*influencedGraph->dependancyVector[rrSetId])[got->second][j] = false;
                        dependencyValues[node] -= 1;                                                                    //Because in the Matrix row for node, a TRUE was changed to FALSE
                        for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){               //For each node v whose reachability depends on node
                            if((*influencedGraph->dependancyVector[rrSetId])[j][k]){
                                (*influencedGraph->dependancyVector[rrSetId])[j][k] = false;
                                dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[j]] -= 1;                   //Reduce the dependencyValue for the node v
                            }
                        }
                        if (!(*influencedGraph->miniRRGraphsVector[rrSetId])[j].empty()) {                              //Remove all outgoing edges from j from this(rrSetId) miniRRGraph since the vertex j  is now no longer reachable from source
                            (*influencedGraph->miniRRGraphsVector[rrSetId])[j].clear();
                        }
                    } else if (!(*influencedGraph->dependancyVector[rrSetId])[got->second][j]) {                        //else if dependence of reachability of j from source given that node is removed is false
                        if( !(*influencedGraph->miniRRGraphsVector[rrSetId])[j].empty() ){                              //Same. Idea is that if there are NO outgoing edges from the seedSetNode, then removing it will not have any affect on the datastr. So we can just ignore, and move to the next rrSetId
                            repopulateDependencyMatrixAfterCritNodeRemoval(influencedGraph,
                                                                           influencedGraph->miniRRGraphsVector[rrSetId],
                                                                           influencedGraph->reachableNodesVector[rrSetId],
                                                                           rrSetId, got->second, j, dependencyValues);
                        }
                    }
                }
                (*influencedGraph->dependancyVector[rrSetId])[got->second][got->second] = false;                        //Doing this because of the (... && j != got->second) in the if condition
                dependencyValues[node] -= 1;                                                                            //Reduce the dependencyValue for the node
            }
            else{
                //Doing this because the seedSetNode might be the node at the end of a chain. 0->1->2->3.
                //If 3 was the seedSetNode, then its outgoing edges would be empty.
                //In that case, entry M[3][3] would never be changed to false.
                if((*influencedGraph->dependancyVector[rrSetId])[got->second][got->second]){
                    (*influencedGraph->dependancyVector[rrSetId])[got->second][got->second] = false;
                    dependencyValues[node] -= 1;                                                                        //Reduce the dependencyValue for the node
                }
                (*influencedGraph->reachableNodesVector[rrSetId])[got->second] = true;

                if(tshoot){
                    for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
                        assert(("Testing, not sure if this should hold", (*influencedGraph->dependancyVector[rrSetId])[got->second][j] == false));
                    }
                }
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed
//    assert(("Woohoo!!!", dependencyValues[node] == 0));
    removeCritNodeFromDependencyVectorTopCritTime += (clock() - startInnerLoop);
}

void computeSubModNodesUsingTopCrit(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues,
                                    vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet,
                                    const set<int> &envelopedNodes, set<int> &subModNodesToremove, vector<int> &nodesToRemoveUnsorted, set<int> &alreadyinSeed) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            subModNodesToremove.insert(node);
            nodesToRemoveUnsorted.push_back(node);
            if (i < removeNodes) {//Dont call if final vertex to be removed has been found
                removeCritNodeFromDependencyVectorTopCrit(node, influencedGraph, dependencyValues, ASdegree);
            }
            index = 0;
        } else {
            alreadyinSeed.insert(node);
            index++;
        }
    }

    if (tshoot2 && useEnvelop) {
        cout << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
             << endl;
        myfile
                << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }
}



//Newer version of the method. Use this method only if the dependencyValues have been already updated,
//and all you have to do is sort them in orfder to find out the top-k nodes to be removed by the subModImpactTopCrit method.
void computeModImpactTopCritNodes(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues,
                                  vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet,
                                  const set<int> &envelopedNodes,
                                  set<int> *removalModImpact, vector<int> &nodesToRemoveUnsorted) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    set<int> alreadyinSeed = set<int>();
    ASdegree = vector<pair<int, int>>();

    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);

    cout << "Impact Nodes Sorted!" << endl;
    cout << "Selected modImpact Nodes to remove: " << endl;

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            removalModImpact->insert(node);
            nodesToRemoveUnsorted.push_back(node);
            cout << node << endl;
        } else {
            alreadyinSeed.insert(node);
        }
        index++;
    }

    if (tshoot2 && useEnvelop) {
        cout    << "ModImpact Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        myfile  << "ModImpact Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }

    assert(("Mismatch - removalModImpact and removeNodes", removalModImpact->size() == removeNodes));

//    cout << "Node to be removed by the mod Impact process" << endl;
//    printVector(modImpactNodesToRemoveUnsorted);

    cout << "\nassociated value is: " << alreadyinSeed.size() << endl;
    cout << "Number of nodes for (ModImpactTopCrit) already present in seed set = " << alreadyinSeed.size() << endl;

    cout << "Printing nodes not added to ModImpactTopCrit because they were in seedSet: " << endl;
    myfile << "Printing nodes not added to ModImpactTopCrit because they were in seedSet: " << endl;
    printSet(alreadyinSeed);

    //Clearing alreadyinSeed because it contains the modImpact nodes at this point
    alreadyinSeed.clear();
}


//miniRRGraph is the graph that has been created from the original graph after mapping each of the vertices to index
//node belonging to the seedSet along with all of its outgoing edges has already been removed at this point
//nodeBeingRemoved is the vertex that has to be removed from the minRRGraph. So, we are basically checking:
//dependence of reachability of each node in the miniRRGraph (formed after removing outgoing edges from the seedSetNode) starting from the origin given that
//nodeBeingRemoved is removed
//both seedSetNode and otherNode are not the actual vertices, but the mapped vertices in this rrSet numbered rrSetId
void repopulateDependencyMatrixAfterSeedSetRemoval(unique_ptr<Graph> &influencedGraph,
                                                   unique_ptr<vector<vector<int>>> &miniRRGraph,
                                                   unique_ptr<vector<bool>> &reachableFromSeed,
                                                   int rrSetId,
                                                   int seedSetNode, int nodeBeingRemoved) {

    vector<vector<int>> myGraph = *miniRRGraph;
    myGraph[nodeBeingRemoved].clear();

    for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved].size(); i++){    //Initialize all row entries to TRUE
        if((*reachableFromSeed)[i]){                                                                    //if the particular node was not originally reachable
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = false;                 //from the seedSetNode
        }else{
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = true;
        }
    }
    (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][seedSetNode] = true;                //because if reachability of the the seedSetNode depends upon the nodeBeingRemoved,
    //then we want to capture that information in the dependencyMatrix row corresp. to nodeBeingRemoved

    vector<bool> visitedBFS = vector<bool>(miniRRGraph->size(), false);                                 //Mark all the vertices as not visited
    deque<int> queue;                                                                                   //Create a queue for BFS
    visitedBFS[0] = true;                                                                               //Mark the starting node as visited. starting node will always be node numbered 0
    queue.push_back(0);                                                                                 //And add it to the queue
    if(nodeBeingRemoved != 0){
        (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][0] = false;                     //since we are starting the BFS from the node 0, dependence of reachability of 0 from 0 given that the ndoeBeingRemoved is removed is "false"
    }

    while (!queue.empty()) {
        int u = queue.front();
        queue.pop_front();
        for (int i = 0; i < myGraph[u].size(); i++) {
            int v = myGraph[u][i];
            if (!visitedBFS[v]) {
                visitedBFS[v] = true;
                queue.push_back(v);
                if (nodeBeingRemoved != v) {                                                    //Because reachability of vertexRemoved will depend on itself
                    (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][v] = false; //Since v was still reachable after removing vertexRemoved.
                }
            }
        }
    }

}

//node is the seedSet node being removed from the dependencyVector
//miniRRGraphsVector contains the miniRRGraphs, not the actual RRgraphs. So all vertices will have to be mapped to indices
void removeSeedSetNodeFromDependencyVector(int seedSetNode, unique_ptr<Graph> &influencedGraph) {

    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    /*Update the dependencyVector datastructure
     *
     * In each RRSet
     *  if seedSet node occurs in that RRSet
     *      set all elements in the row index corresponding to that node to 0
     *      if(condition) controls the good and the bad method.
     */

    cout << "Removing seedSet vertex: " << seedSetNode << endl;
    dependValues << "Removing seedSet vertex: " << seedSetNode << endl;

    /*

    for (int i = 0; i < influencedGraph->inRRSet[node].size(); i++) {                                                   //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        unordered_map<int, int>::const_iterator removeIndex = influencedGraph->vertexToIndex[rrSetId]->find(node);      //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node. removeIndex contains the tuple <vertex, index>
        if (removeIndex != influencedGraph->vertexToIndex[rrSetId]->end()) {                                            //if vertex is found
            for (int col = 0; col < (*influencedGraph->dependancyVector[rrSetId])[removeIndex->second].size(); col++) {
                if ((*influencedGraph->dependancyVector[rrSetId])[removeIndex->second][col] &&
                    removeIndex->second != col) {
                    for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[col].size(); j++) {
                        if ((*influencedGraph->dependancyVector[rrSetId])[col][j]) {
                            (*influencedGraph->dependancyVector[rrSetId])[col][j] = false;
                            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[col]] -= 1;
                        }
                    }
                }else if(!( (*influencedGraph->dependancyVector[rrSetId])[removeIndex->second][col] )){
                    for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[col].size(); j++) {
                        if ((*influencedGraph->dependancyVector[rrSetId])[col][j] && ) {
                            (*influencedGraph->dependancyVector[rrSetId])[col][j] = false;
                            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[col]] -= 1;
                        }
                    }
                }
            }
            fill((*influencedGraph->dependancyVector[rrSetId])[removeIndex->second].begin(),
                 (*influencedGraph->dependancyVector[rrSetId])[removeIndex->second].end(), false);                      //Replace all elements in the vertex row (of the vertex being removed) with 0;
                 // Replace all elements in the vertex column with 0 => this part of code has been deleted, because...things
        } else {
            assert(("seedSet node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

     */

    for (int i = 0; i < influencedGraph->inRRSet[seedSetNode].size(); i++) {                                            //for each RRSet in inRRSet (each RRSet that contains node)

        int rrSetId = influencedGraph->inRRSet[seedSetNode][i];                                                         //get the next RRSet that the node to be removed is in

        if (tshoot1) {
            if (influencedGraph->rrSets[i].size() > 10) {
                cout << "PAUUUUUZZZE!!!" << endl;
            }
        }
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);       //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the seedSet vertex being removed
            if ( !(*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].empty() ) {                              //Idea is that if there are NO outgoing edges from the seedSetNode, then removing it will not have any affect on the datastr. So we can just ignore, and move to the next rrSetId
                (*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].clear();                                   //remove all the outgoing edges from seedSetNode in the RRGraph stored in rrSetId bucket
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){             //for each vertex j in the row containing the vertex to to be removed
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){                                  //if reachability of j depends on seedSetNode
                        (*influencedGraph->reachableNodesVector[rrSetId])[j] = true;                                    //set j to be "covered"
                    }
                }
                for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++) {           //for each vertex j in the row containing the vertex to to be removed
                    if ((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second) {            //if dependence of reachability of j from source given that node is removed is true && j != node
                        (*influencedGraph->dependancyVector[rrSetId])[got->second][j] = false;
                        for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                            if((*influencedGraph->dependancyVector[rrSetId])[j][k]){
                                (*influencedGraph->dependancyVector[rrSetId])[j][k] = false;
                            }
                        }
//                        fill((*influencedGraph->dependancyVector[rrSetId])[j].begin(),
//                             (*influencedGraph->dependancyVector[rrSetId])[j].end(),
//                             false);                                                                                    //fill the entire row of j with false, bec. j is no longer reachable from source since node has been removed. Removing seed set node, hence we do not change dependencyValues
                        if (!(*influencedGraph->miniRRGraphsVector[rrSetId])[j].empty()) {                              //Remove all outgoing edges from j from this(rrSetId) miniRRGraph since the vertex j  is now no longer reachable from source
                            (*influencedGraph->miniRRGraphsVector[rrSetId])[j].clear();
                        }
                    } /* else if (!(*influencedGraph->dependancyVector[rrSetId])[got->second][j]) {                        //else if dependence of reachability of j from source given that node is removed is false
                        if( !(*influencedGraph->miniRRGraphsVector[rrSetId])[j].empty() ){                              //Same. Idea is that if there are NO outgoing edges from the seedSetNode, then removing it will not have any affect on the datastr. So we can just ignore, and move to the next rrSetId
                            repopulateDependencyMatrixAfterSeedSetRemoval(influencedGraph,
                                                                          influencedGraph->miniRRGraphsVector[rrSetId],
                                                                          influencedGraph->reachableNodesVector[rrSetId],
                                                                          rrSetId, got->second, j);
                        }
                    } */
                }
                (*influencedGraph->dependancyVector[rrSetId])[got->second][got->second] = false;                        //Doing this because of the (... && j != got->second) in the if condition
            }
            else{
                //Doing this because the seedSetNode might be the node at the end of a chain. 0->1->2->3.
                //If 3 was the seedSetNode, then its outgoing edges would be empty.
                //In that case, entry M[3][3] would never be changed to false.
                //And seedSetNode would never have been added to being "covered"
                (*influencedGraph->dependancyVector[rrSetId])[got->second][got->second] = false;
                (*influencedGraph->reachableNodesVector[rrSetId])[got->second] = true;
                if(tshoot){
                    for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
                        assert(("Testing, not sure if this should hold", (*influencedGraph->dependancyVector[rrSetId])[got->second][j] == false ));
                    }
                }
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }

        for(int j = 0; j < (*influencedGraph->reachableNodesVector[rrSetId]).size(); j++){
            if((*influencedGraph->reachableNodesVector[rrSetId])[j]){
                for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                    assert(("Your assumption about if a vertex is reachable from seed then its row must contain all 0's is wrong",
                            (*influencedGraph->dependancyVector[rrSetId])[j][k] == false));
                }
            }
        }
    }

//    dependencyValues[node] = 0;                                                                                       //We do not do this step: Set the value to be 0.
}


//node is the seedSet node being removed from the dependencyVector
//miniRRGraphsVector contains the miniRRGraphs, not the actual RRgraphs. So all vertices will have to be mapped to indices
void removeSeedSetNodeFromDependencyVector_2(int seedSetNode, unique_ptr<Graph> &influencedGraph) {

    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    /*Update the dependencyVector datastructure
     *
     * In each RRSet
     *  if seedSet node occurs in that RRSet
     *      set all elements in the row index corresponding to that node to 0
     *      if(condition) controls the good and the bad method.
     */

    cout << "Removing seedSet vertex: " << seedSetNode << endl;
    dependValues << "Removing seedSet vertex: " << seedSetNode << endl;

    /*

    for (int i = 0; i < influencedGraph->inRRSet[node].size(); i++) {                                                   //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        unordered_map<int, int>::const_iterator removeIndex = influencedGraph->vertexToIndex[rrSetId]->find(node);      //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node. removeIndex contains the tuple <vertex, index>
        if (removeIndex != influencedGraph->vertexToIndex[rrSetId]->end()) {                                            //if vertex is found
            for (int col = 0; col < (*influencedGraph->dependancyVector[rrSetId])[removeIndex->second].size(); col++) {
                if ((*influencedGraph->dependancyVector[rrSetId])[removeIndex->second][col] &&
                    removeIndex->second != col) {
                    for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[col].size(); j++) {
                        if ((*influencedGraph->dependancyVector[rrSetId])[col][j]) {
                            (*influencedGraph->dependancyVector[rrSetId])[col][j] = false;
                            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[col]] -= 1;
                        }
                    }
                }else if(!( (*influencedGraph->dependancyVector[rrSetId])[removeIndex->second][col] )){
                    for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[col].size(); j++) {
                        if ((*influencedGraph->dependancyVector[rrSetId])[col][j] && ) {
                            (*influencedGraph->dependancyVector[rrSetId])[col][j] = false;
                            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[col]] -= 1;
                        }
                    }
                }
            }
            fill((*influencedGraph->dependancyVector[rrSetId])[removeIndex->second].begin(),
                 (*influencedGraph->dependancyVector[rrSetId])[removeIndex->second].end(), false);                      //Replace all elements in the vertex row (of the vertex being removed) with 0;
                 // Replace all elements in the vertex column with 0 => this part of code has been deleted, because...things
        } else {
            assert(("seedSet node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

     */

    for (int i = 0; i < influencedGraph->inRRSet[seedSetNode].size(); i++) {                                            //for each RRSet in inRRSet (each RRSet that contains node)

        int rrSetId = influencedGraph->inRRSet[seedSetNode][i];                                                         //get the next RRSet that the node to be removed is in

        if (tshoot1) {
            if (influencedGraph->rrSets[i].size() > 10) {
                cout << "PAUUUUUZZZE!!!" << endl;
            }
        }
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);       //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the seedSet vertex being removed
            if ( !(*influencedGraph->reachableNodesVector[rrSetId])[got->second] ) {                                    //Idea is that if there are NO outgoing edges from the seedSetNode, then removing it will not have any affect on the datastr. So we can just ignore, and move to the next rrSetId
//                (*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].clear();                                 //remove all the outgoing edges from seedSetNode in the RRGraph stored in rrSetId bucket
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){             //for each vertex j in the row containing the vertex to to be removed
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){                                  //if reachability of j depends on seedSetNode
                        (*influencedGraph->reachableNodesVector[rrSetId])[j] = true;                                    //set j to be "covered"
                    }
                }
                for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++) {           //for each vertex j in the row containing the vertex to to be removed
                    if ((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second) {            //if dependence of reachability of j from source given that node is removed is true && j != node
                        (*influencedGraph->dependancyVector[rrSetId])[got->second][j] = false;
                        for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                            if((*influencedGraph->dependancyVector[rrSetId])[j][k]){
                                (*influencedGraph->dependancyVector[rrSetId])[j][k] = false;
                            }
                        }
//                        fill((*influencedGraph->dependancyVector[rrSetId])[j].begin(),
//                             (*influencedGraph->dependancyVector[rrSetId])[j].end(),
//                             false);                                                                                  //fill the entire row of j with false, bec. j is no longer reachable from source since node has been removed. Removing seed set node, hence we do not change dependencyValues
//                        if (!(*influencedGraph->miniRRGraphsVector[rrSetId])[j].empty()) {                              //Remove all outgoing edges from j from this(rrSetId) miniRRGraph since the vertex j  is now no longer reachable from source
//                            (*influencedGraph->miniRRGraphsVector[rrSetId])[j].clear();
//                        }
                    } /* else if (!(*influencedGraph->dependancyVector[rrSetId])[got->second][j]) {                        //else if dependence of reachability of j from source given that node is removed is false
                        if( !(*influencedGraph->miniRRGraphsVector[rrSetId])[j].empty() ){                              //Same. Idea is that if there are NO outgoing edges from the seedSetNode, then removing it will not have any affect on the datastr. So we can just ignore, and move to the next rrSetId
                            repopulateDependencyMatrixAfterSeedSetRemoval(influencedGraph,
                                                                          influencedGraph->miniRRGraphsVector[rrSetId],
                                                                          influencedGraph->reachableNodesVector[rrSetId],
                                                                          rrSetId, got->second, j);
                        }
                    } */
                }
                (*influencedGraph->dependancyVector[rrSetId])[got->second][got->second] = false;                        //Doing this because of the (... && j != got->second) in the if condition
            }
//            else{
//                //Doing this because the seedSetNode might be the node at the end of a chain. 0->1->2->3.
//                //If 3 was the seedSetNode, then its outgoing edges would be empty.
//                //In that case, entry M[3][3] would never be changed to false.
//                //And seedSetNode would never have been added to being "covered"
//                (*influencedGraph->dependancyVector[rrSetId])[got->second][got->second] = false;
//                (*influencedGraph->reachableNodesVector[rrSetId])[got->second] = true;
//                if(tshoot){
//                    for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
//                        assert(("Testing, not sure if this should hold", (*influencedGraph->dependancyVector[rrSetId])[got->second][j] == false ));
//                    }
//                }
//            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }

        for(int j = 0; j < (*influencedGraph->reachableNodesVector[rrSetId]).size(); j++){
            if((*influencedGraph->reachableNodesVector[rrSetId])[j]){
                for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                    assert(("Your assumption about if a vertex is reachable from seed then its row must contain all 0's is wrong",
                            (*influencedGraph->dependancyVector[rrSetId])[j][k] == false));
                }
            }
        }
    }

//    dependencyValues[node] = 0;                                                                                       //We do not do this step: Set the value to be 0.
}

//This is for testing if the chagnes done to each of the dependencyMatrices is equivalent to the reduction in the dependencyValues by the
//removeSeedSetNodeWithoutMatrixUpdate() method.
void removeSeedSetNodeWithoutMatrixUpdate_TEST(int seedSetNode, unique_ptr<Graph> &influencedGraph,
                                               vector<int> &dependencyValues,
                                               vector<vector<vector<bool>>> &copyOfDependencyVector) {

    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    cout << "Removing seedSet vertex: " << seedSetNode << endl;
    dependValues << "Removing seedSet vertex: " << seedSetNode << endl;



    vector<int> valuesChangedInOrig = vector<int>();
    vector<int> valuesChangedInCopy = vector<int>();
    for (int i = 0; i < influencedGraph->inRRSet[seedSetNode].size(); i++) {                                            //for each RRSet in inRRSet (each RRSet that contains node)

        int rrSetId = influencedGraph->inRRSet[seedSetNode][i];                                                         //get the next RRSet that the node to be removed is in

        valuesChangedInOrig.clear();
        valuesChangedInCopy.clear();
        valuesChangedInOrig = vector<int>((*influencedGraph->vertexToIndex[rrSetId]).size(), 0);
        valuesChangedInCopy = vector<int>((*influencedGraph->vertexToIndex[rrSetId]).size(), 0);

        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);       //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the seedSet vertex being removed
            if ( !(*influencedGraph->reachableNodesVector[rrSetId])[got->second] ) {                                    //Idea is that if seedSetNode was already covered, then all of the nodes whose reachability depends on seedSetNode have also been covered by some previous iteration of seedSetNode, and hence we can move to the next rrSetId directly

                for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++) {           //for each vertex j in the row containing the vertex to to be removed
                    if ((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second) {            //if dependence of reachability of j from source given that node is removed is true && j != node

                        dependencyValues[seedSetNode] -= 1;                                                             //decrease ONLY THE DEPENDENCY VALUE of the seedSetNode by 1. Do not change the dependencyVector
                        valuesChangedInOrig[got->second] += 1;

                        if( !(*influencedGraph->reachableNodesVector[rrSetId])[j] ){
                            for (int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++) {
                                if ((*influencedGraph->dependancyVector[rrSetId])[j][k] /*&& !((*influencedGraph->reachableNodesVector[rrSetId])[k]) */) {

                                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[j]] -= 1;                //decrease ONLY THE DEPENDENCY VALUE of the seedSetNode by 1. Do not change the dependencyVector
                                    valuesChangedInOrig[j] += 1;

                                }
                            }
                        }
                    }
                }
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){             //for each vertex j in the row containing the vertex to to be removed
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){                                  //if reachability of j depends on seedSetNode
                        (*influencedGraph->reachableNodesVector[rrSetId])[j] = true;                                    //set j to be "covered"
                    }
                }
                dependencyValues[seedSetNode] -= 1;                                                                     //Doing this because of the (... && j != got->second) in the if condition
                valuesChangedInOrig[got->second] += 1;

                //Test Code
                for(int j = 0; j < copyOfDependencyVector[rrSetId][got->second].size(); j++){
                    if(copyOfDependencyVector[rrSetId][got->second][j] && j != got->second){

                        copyOfDependencyVector[rrSetId][got->second][j] = false;
                        valuesChangedInCopy[got->second] += 1;

                        for(int k = 0; k < copyOfDependencyVector[rrSetId][j].size(); k++){
                            if(copyOfDependencyVector[rrSetId][j][k]){

                                copyOfDependencyVector[rrSetId][j][k] = false;
                                valuesChangedInCopy[j] += 1;

                            }
                        }
                    }
                }
                copyOfDependencyVector[rrSetId][got->second][got->second] = false;
                valuesChangedInCopy[got->second] += 1;


                cout << "Removing vertex: " << seedSetNode << endl;
                cout << "RRSetID:" << rrSetId << endl;
                cout << "valuesChangedInOrig: ";
                for(int k = 0; k < valuesChangedInOrig.size(); k++){
                    cout << valuesChangedInOrig[k] << " ";
                }
                cout << endl;
                cout << "valuesChangedInCopy: ";
                for(int k = 0; k < valuesChangedInOrig.size(); k++){
                    cout << valuesChangedInCopy[k] << " ";
                }
                cout << endl;
                cout << "Nodes: ";
                for(int k = 0; k < (influencedGraph->rrSets[rrSetId]).size(); k++){
                    cout << influencedGraph->rrSets[rrSetId][k] << " ";
                }
                cout << endl;
                cout << "Graph: " << endl;
                for(int k = 0; k < (*influencedGraph->miniRRGraphsVector[rrSetId]).size(); k++){
                    cout << k << " -> ";
                    for(int l = 0; l < (*influencedGraph->miniRRGraphsVector[rrSetId])[k].size(); l++){
                        cout << (*influencedGraph->miniRRGraphsVector[rrSetId])[k][l] << " ";
                    }
                    cout << endl;
                }
                cout << "reachableNodes: ";
                for(int k = 0; k < (*influencedGraph->reachableNodesVector[rrSetId]).size(); k++){
                    cout << (*influencedGraph->reachableNodesVector[rrSetId])[k] << " ";
                }
                cout << endl;
                cout << "DependencyMatrix: " << endl;
                for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId]).size(); k++){
                    for(int l = 0; l < (*influencedGraph->dependancyVector[rrSetId])[k].size(); l++){
                        cout << (*influencedGraph->dependancyVector[rrSetId])[k][l] << " ";
                    }
                    cout << endl;
                }
                cout << "copyOfDependencyMatrix: " << endl;
                for(int k = 0; k < copyOfDependencyVector[rrSetId].size(); k++){
                    for(int l = 0; l < copyOfDependencyVector[rrSetId][k].size(); l++){
                        cout << copyOfDependencyVector[rrSetId][k][l] << " ";
                    }
                    cout << endl;
                }
                cout << endl;
                for(int j = 0; j < valuesChangedInOrig.size(); j++){
                    assert(("There you go now...", valuesChangedInOrig[j] == valuesChangedInCopy[j]));
                }
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }

    }

    assert(("Woohoo!!!", dependencyValues[seedSetNode] == 0));
}

//This is for testing if the "FINAL" values in the dependencyValues datastructure are the same between the following methods:
//a) removeSeedSetNodeWithoutMatrixUpdate()
//b) removing seedSetNode but by changing the dependencyVector datastructure i.e. in for every dependencyMatrix that contains the seedSetNode\
//we null out all the vertices v in the row containing the seedSetNode
//and also null out all the vertices in the row corresposing to each of the vertices v
void removeSeedSetNodeWithoutMatrixUpdate_TEST2(int seedSetNode, unique_ptr<Graph> &influencedGraph,
                                               vector<int> &dependencyValues,
                                               vector<vector<vector<bool>>> &copyOfDependencyVector) {

    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    cout << "Removing seedSet vertex: " << seedSetNode << endl;
    dependValues << "Removing seedSet vertex: " << seedSetNode << endl;



    vector<int> valuesChangedInOrig = vector<int>();
    vector<int> valuesChangedInCopy = vector<int>();
    for (int i = 0; i < influencedGraph->inRRSet[seedSetNode].size(); i++) {                                            //for each RRSet in inRRSet (each RRSet that contains node)

        int rrSetId = influencedGraph->inRRSet[seedSetNode][i];                                                         //get the next RRSet that the node to be removed is in

        valuesChangedInOrig.clear();
        valuesChangedInCopy.clear();
        valuesChangedInOrig = vector<int>((*influencedGraph->vertexToIndex[rrSetId]).size(), 0);
        valuesChangedInCopy = vector<int>((*influencedGraph->vertexToIndex[rrSetId]).size(), 0);

        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);       //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the seedSet vertex being removed
            if ( !(*influencedGraph->reachableNodesVector[rrSetId])[got->second] ) {                                    //Idea is that if seedSetNode was already covered, then all of the nodes whose reachability depends on seedSetNode have also been covered by some previous iteration of seedSetNode, and hence we can move to the next rrSetId directly

                for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++) {           //for each vertex j in the row containing the vertex to to be removed
                    if ((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second) {            //if dependence of reachability of j from source given that node is removed is true && j != node

                        dependencyValues[seedSetNode] -= 1;                                                             //decrease ONLY THE DEPENDENCY VALUE of the seedSetNode by 1. Do not change the dependencyVector
                        valuesChangedInOrig[got->second] += 1;

                        if( !(*influencedGraph->reachableNodesVector[rrSetId])[j] ){
                            for (int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++) {
                                if ((*influencedGraph->dependancyVector[rrSetId])[j][k] /*&& !((*influencedGraph->reachableNodesVector[rrSetId])[k]) */) {

                                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[j]] -= 1;                //decrease ONLY THE DEPENDENCY VALUE of the seedSetNode by 1. Do not change the dependencyVector
                                    valuesChangedInOrig[j] += 1;

                                }
                            }
                        }
                    }
                }
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){             //for each vertex j in the row containing the vertex to to be removed
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){                                  //if reachability of j depends on seedSetNode
                        (*influencedGraph->reachableNodesVector[rrSetId])[j] = true;                                    //set j to be "covered"
                    }
                }
                dependencyValues[seedSetNode] -= 1;                                                                     //Doing this because of the (... && j != got->second) in the if condition
                valuesChangedInOrig[got->second] += 1;

                //Test Code
                for(int j = 0; j < copyOfDependencyVector[rrSetId][got->second].size(); j++){
                    if(copyOfDependencyVector[rrSetId][got->second][j] && j != got->second){
                        copyOfDependencyVector[rrSetId][got->second][j] = false;
                        for(int k = 0; k < copyOfDependencyVector[rrSetId][j].size(); k++){
                                copyOfDependencyVector[rrSetId][j][k] = false;
                        }
                    }
                }
                copyOfDependencyVector[rrSetId][got->second][got->second] = false;

                /*
                cout << "Removing vertex: " << seedSetNode << endl;
                cout << "RRSetID:" << rrSetId << endl;
                cout << "valuesChangedInOrig: ";
                for(int k = 0; k < valuesChangedInOrig.size(); k++){
                    cout << valuesChangedInOrig[k] << " ";
                }
                cout << endl;
                cout << "valuesChangedInCopy: ";
                for(int k = 0; k < valuesChangedInOrig.size(); k++){
                    cout << valuesChangedInCopy[k] << " ";
                }
                cout << endl;
                cout << "Nodes: ";
                for(int k = 0; k < (influencedGraph->rrSets[rrSetId]).size(); k++){
                    cout << influencedGraph->rrSets[rrSetId][k] << " ";
                }
                cout << endl;
                cout << "Graph: " << endl;
                for(int k = 0; k < (*influencedGraph->miniRRGraphsVector[rrSetId]).size(); k++){
                    cout << k << " -> ";
                    for(int l = 0; l < (*influencedGraph->miniRRGraphsVector[rrSetId])[k].size(); l++){
                        cout << (*influencedGraph->miniRRGraphsVector[rrSetId])[k][l] << " ";
                    }
                    cout << endl;
                }
                cout << "reachableNodes: ";
                for(int k = 0; k < (*influencedGraph->reachableNodesVector[rrSetId]).size(); k++){
                    cout << (*influencedGraph->reachableNodesVector[rrSetId])[k] << " ";
                }
                cout << endl;
                cout << "DependencyMatrix: " << endl;
                for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId]).size(); k++){
                    for(int l = 0; l < (*influencedGraph->dependancyVector[rrSetId])[k].size(); l++){
                        cout << (*influencedGraph->dependancyVector[rrSetId])[k][l] << " ";
                    }
                    cout << endl;
                }
                cout << "copyOfDependencyMatrix: " << endl;
                for(int k = 0; k < copyOfDependencyVector[rrSetId].size(); k++){
                    for(int l = 0; l < copyOfDependencyVector[rrSetId][k].size(); l++){
                        cout << copyOfDependencyVector[rrSetId][k][l] << " ";
                    }
                    cout << endl;
                }
                cout << endl;
                for(int j = 0; j < valuesChangedInOrig.size(); j++){
                    assert(("There you go now...", valuesChangedInOrig[j] == valuesChangedInCopy[j]));
                }

                */
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }

    }

    assert(("Woohoo!!!", dependencyValues[seedSetNode] == 0));
}

//node is the seedSet node being removed from the dependencyVector
//miniRRGraphsVector contains the miniRRGraphs, not the actual RRgraphs. So all vertices will have to be mapped to indices
//This method is different from the earlier method removeSeedSetNodeFromDependencyVector() because:
//1) Now we are not making any changes to the Matrices present in the dependencyVector on removal of the seedSetNode
//We are only updating the dependencyValues datastructure
//2) We are not making any changes to the miniRRGraph. In some of the earlier versions of the method we were clearing the outgoing edges from
//the seedSetNode being removed. We are not doing that in this method.
//3) We are not using the size of the outgoing edges from the seedSetNode in any way to decide if the node is to be explored or not.
//Instead we are now using the reachableFromSeed datastructure in order to decide this.
//In fact, now that I think about it, we are not changing ANY datastructure in this code, save the dependencyValue. Which is kind of fucking incredible.
void removeSeedSetNodeWithoutMatrixUpdate(int seedSetNode, unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues) {

    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    cout << "Removing seedSet vertex: " << seedSetNode << endl;
    dependValues << "Removing seedSet vertex: " << seedSetNode << endl;

    for (int i = 0; i < influencedGraph->inRRSet[seedSetNode].size(); i++) {                                            //for each RRSet in inRRSet (each RRSet that contains node)

        int rrSetId = influencedGraph->inRRSet[seedSetNode][i];                                                         //get the next RRSet that the node to be removed is in
        if (tshoot1) {
            if (influencedGraph->rrSets[i].size() > 10) {
                cout << "PAUUUUUZZZE!!!" << endl;
            }
        }

        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);       //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the seedSet vertex being removed
            if ( !(*influencedGraph->reachableNodesVector[rrSetId])[got->second] ) {                                    //Idea is that if seedSetNode was already covered, then all of the nodes whose reachability depends on seedSetNode have also been covered by some previous iteration of seedSetNode, and hence we can move to the next rrSetId directly
                for (int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++) {           //for each vertex j in the row containing the vertex to to be removed
                    if ((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second) {            //if dependence of reachability of j from source given that node is removed is true && j != node
                        dependencyValues[seedSetNode] -= 1;                                                             //decrease ONLY THE DEPENDENCY VALUE of the seedSetNode by 1. Do not change the dependencyVector
                        if( !(*influencedGraph->reachableNodesVector[rrSetId])[j] ){
                            for (int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++) {
                                if ((*influencedGraph->dependancyVector[rrSetId])[j][k] /* &&   !((*influencedGraph->reachableNodesVector[rrSetId])[k]) */ ) {
                                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[j]] -= 1;                //decrease ONLY THE DEPENDENCY VALUE of the seedSetNode by 1. Do not change the dependencyVector
                                }
                            }
                        }

                    }
                }
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){             //for each vertex j in the row containing the vertex to to be removed
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){                                  //if reachability of j depends on seedSetNode
                        (*influencedGraph->reachableNodesVector[rrSetId])[j] = true;                                    //set j to be "covered"
                    }
                }
                dependencyValues[seedSetNode] -= 1;                                                                     //Doing this because of the (... && j != got->second) in the if condition
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }

    }

    assert(("Woohoo!!!", dependencyValues[seedSetNode] == 0));
}

void computeDependencyValuesWithoutASdegree(vector<int> &dependencyValues, unique_ptr<Graph> &influencedGraph) {

    bool tshoot = true;//prints values to file
    cout << "Calculating Dependency Values" << endl;

    for (int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++) {                              //for each RRSet in dependancyVector
        for (int rowIdx = 0; rowIdx < influencedGraph->dependancyVector[rrSetId]->size(); rowIdx++) {                   //for each row in the dependancyMatrix
            int vertex = (*influencedGraph->indexToVertex[rrSetId])[rowIdx];                                            //find the vertex that was mapped to that index
            for (int colIdx = 0; colIdx < (*influencedGraph->dependancyVector[rrSetId])[rowIdx].size(); colIdx++) {     //for each col in that row
                if ((*influencedGraph->dependancyVector[rrSetId])[rowIdx][colIdx]) {
                    dependencyValues[vertex] += 1;                                                                      //Add the value to the existing dependencyValues of that vertex
                }
            }
        }
    }


    for (int i = 0; i < dependencyValues.size(); i++) {
        if (tshoot) {
            dependValues << dependencyValues[i] << endl;
        }
    }
    if (tshoot) dependValues << "------------------------------------------------------------" << endl;

}

set<int> subModTopCritNodesRemove(unique_ptr<Graph> &subModTopCritGraph, vector<int> activatedSet, int removeNodes,
                                  const set<int> &maxSeedSet, const set<int> &envelopedNodes,
                                  set<int> *subModImpactNodesToRemove,
                                  vector<int> &subModImpactTopCritNodesToRemoveUnsorted,
                                  vector<int> &subModTopCritNodesToRemoveUnsorted) {

    bool tshoot = true;//Prints the dependency values for before the seedSetNodes are removed to the file
    bool tshoot1 = true;//Prints the node being removed in each iteration
    bool tshoot2 = false;//Prints the outdegree values for the modNodes removed in Algo1

    clock_t subModReverseStartTime = clock();

    set<int> alreadyinSeed = set<int>();
    set<int> subModTopCritNodesToRemove;
    vector<pair<int, int>> ASdegree;
    int removalNum = removeNodes;
    vector<int> dependencyValues = vector<int>(subModTopCritGraph->n, 0);
    vector<int> testDependencyValues = vector<int>(subModTopCritGraph->n, 0);

    //Random RR sets
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "\nRR sets are: " << R << endl;
    resultLogFile << "\nRR sets are: " << R << endl;
    subModTopCritGraph->generateRandomRRSetsFromTargets(R, activatedSet, "subModTopCrit", resultLogFile);

    clock_t timeForGeneratingRRSets = clock();

    //This is for testing to see what are the dependencyValues that we are starting with
    //HOWEVER: IF USING NEWER METHOD removeSeedSetNodeWithoutMatrixUpdate() OR removeSeedSetNodeFromDependencyVectorNew() & computeModImpactTopCritNodes() THIS STEP IS REQUIRED
    cout << "\nPopulating dependency values BEFORE removing the seedSet Nodes:" << endl;
    dependValues << "\nsubModTopCritNodesRemove()-Populating dependency values BEFORE removing the seedSet Nodes:"
                 << endl;
    computeDependencyValuesWithoutASdegree(dependencyValues, subModTopCritGraph);
    clock_t timeToComputeInitialDependencyValues = clock();

    clock_t timeToRemoveSeedSetNodesStart = clock();
    //Now we need to remove all of the nodes which are in the seedSet from each of the dependencyVector
    //For each vertex in the seedset, remove that vertex from all of the matrices in the dependancyVector

    //FOR TESTING ONLY::::::::
    /*
    vector<vector<vector<bool>>> copyOfDependencyVector = vector<vector<vector<bool>>>(subModTopCritGraph->dependancyVector.size());
    for(int rrSetId = 0; rrSetId < copyOfDependencyVector.size(); rrSetId++){
        copyOfDependencyVector[rrSetId] = vector<vector<bool>>((*subModTopCritGraph->dependancyVector[rrSetId]).size());
        for(int j = 0; j < (*subModTopCritGraph->dependancyVector[rrSetId]).size(); j++){
            copyOfDependencyVector[rrSetId][j] = (*subModTopCritGraph->dependancyVector[rrSetId])[j];
        }
    }
    */

    for(int nodeToRemove : maxSeedSet){
//        removeSeedSetNodeFromDependencyVector_2(nodeToRemove, subModTopCritGraph);
//        removeSeedSetNodeWithoutMatrixUpdate_TEST2(nodeToRemove, subModTopCritGraph, dependencyValues, copyOfDependencyVector);
//        removeSeedSetNodeWithoutMatrixUpdate_TEST(nodeToRemove, subModTopCritGraph, dependencyValues, copyOfDependencyVector);
        removeSeedSetNodeWithoutMatrixUpdate(nodeToRemove, subModTopCritGraph, dependencyValues);
    }

    //Computing the dependencyValues ONLY FOR TESTING removeSeedSetNodeWithoutMatrixUpdate_TEST2
    /*
    for (int rrSetId = 0; rrSetId < copyOfDependencyVector.size(); rrSetId++) {                                         //for each RRSet in dependancyVector
        for (int rowIdx = 0; rowIdx < copyOfDependencyVector[rrSetId].size(); rowIdx++) {                               //for each row in the dependancyMatrix
            int vertex = (*subModTopCritGraph->indexToVertex[rrSetId])[rowIdx];                                         //find the vertex that was mapped to that index
            for (int colIdx = 0; colIdx < copyOfDependencyVector[rrSetId][rowIdx].size(); colIdx++) {                   //for each col in that row
                if (copyOfDependencyVector[rrSetId][rowIdx][colIdx]) {
                    testDependencyValues[vertex] += 1;                                                                  //Add the value to the existing dependencyValues of that vertex
                }
            }
        }
    }


    for(int i = 0; i < dependencyValues.size(); i++){
        assert(("Now What?", dependencyValues[i] == testDependencyValues[i]));
    }

     */


    clock_t timeToRemoveSeedSetNodesEnd = clock();
    clock_t modImpactTimeStart = clock();

//    dependencyValues = vector<int>(subModTopCritGraph->n, 0);//THE MOTHERFUCKING LINE!!!!

    cout << "\nComputing nodes to remove by the NEW_Mod Impact method" << endl;
    dependValues << "\nsubModTopCritNodesRemove()-Populating dependency values AFTER removing the seedSet Nodes:" << endl;
//    computeModImpactNodes(subModTopCritGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet, envelopedNodes,
//                          subModImpactNodesToRemove, subModImpactTopCritNodesToRemoveUnsorted);

    //Newer method where we calculate the
    computeModImpactTopCritNodes(subModTopCritGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                                 envelopedNodes,
                                 subModImpactNodesToRemove, subModImpactTopCritNodesToRemoveUnsorted);

    clock_t ModImpactEndTime = clock();

    double totalModImpactTime = double(
            (timeForGeneratingRRSets - subModReverseStartTime) +
            (timeToComputeInitialDependencyValues - timeForGeneratingRRSets) +
            (timeToRemoveSeedSetNodesEnd - timeToRemoveSeedSetNodesStart) +
            (ModImpactEndTime - modImpactTimeStart))
                    / (CLOCKS_PER_SEC * 60);

    cout << "NEW_Mod Impact impact algorithm time in minutes " << totalModImpactTime << endl;
    resultLogFile << "NEW_Mod Impact impact algorithm time in minutes" << totalModImpactTime << endl;
    myfile << totalModImpactTime << " <-NEW_ModImpactTime\n";
    cout << "******* Completed NEW_Mod Impact approach ********" << endl;
    cout << endl;
    cout << endl;

    dependValues << "\n\n******* Completed NEW_Mod Impact approach ********" << endl;

    /***************************************************************************************************************************************/

    cout << "******* Running NEW_SubMod approach ********" << endl;
    dependValues << "******* Running NEW_SubMod approach ********" << endl;

    alreadyinSeed = set<int>();
    clock_t sumModCritTimeStart = clock();
    computeSubModNodesUsingTopCrit(subModTopCritGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                                   envelopedNodes,
                                   subModTopCritNodesToRemove, subModTopCritNodesToRemoveUnsorted, alreadyinSeed);

    assert(("Mismatch - subModNodesToremove and removeNodes", subModTopCritNodesToRemove.size() == removalNum));
    clock_t sumModCritTimeEnd = clock();

    vector<vector<int>>().swap(subModTopCritGraph->rrSets);
    cout << endl;
    cout << "Removed subModTopCrit Nodes from Graph: ";
    removingNodesFromGraph(subModTopCritGraph, subModTopCritNodesToRemove);
    cout << endl;

    /*
    for (int i:subModTopCritNodesToRemove) {

        bool tshoot1 = true;
        int totalEdgesInTransGraphPre = 0;
        int totalEdgesInOrigGraphPre = 0;
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < subModTopCritGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += subModTopCritGraph->graphTranspose[k].size();
                if (k == i) {
                    numEdgesToDelete += subModTopCritGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < subModTopCritGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += subModTopCritGraph->graph[k].size();
                if (k == i) {
                    numEdgesToDelete += subModTopCritGraph->graph[k].size();
                }
            }
        }

        subModTopCritGraph->removeOutgoingEdges(i);
        assert(subModTopCritGraph->graph[i].size() == 0);
        assert(subModTopCritGraph->graphTranspose[i].size() == 0);
        subModTopCritGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                      totalEdgesInTransGraphPre);
    }
    */

    cout << endl;
    subModTopCritGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int subModStrength = 0;
    for (int i = 0; i < subModTopCritGraph->NodeinRRsetsWithCounts.size(); i++) {
        subModStrength += subModTopCritGraph->NodeinRRsetsWithCounts[i];
    }

    cout << "\nNEW_Recalculated Initial strength was = " << subModTopCritGraph->totalNumNodesInRRSets << endl;
    cout << "\nNumber of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing nodes in alreadyinSeed that were not added to subModTopCritNodesToRemove:" << endl;
    myfile << "Printing nodes in alreadyinSeed that were not added to subModTopCritNodesToRemove:" << endl;
    printSet(alreadyinSeed);
    cout << "\nNEW_Submodular strength = " << subModStrength;

    myfile << subModTopCritGraph->totalNumNodesInRRSets << " <-NEW_Recalculated Init Strength\n";
    myfile << subModStrength << " <-NEW_subModStrength\n";

    double totalAlgorithmTime = totalModImpactTime + double(sumModCritTimeEnd - sumModCritTimeStart) / (CLOCKS_PER_SEC * 60) ;
    cout << "\nNEW_SubModCrit algorithm time in minutes " << totalAlgorithmTime << endl;
    cout << "Breakup of time taken: " << endl;
    cout << "Time for generating RRSets: " << double (timeForGeneratingRRSets - subModReverseStartTime) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for removing SeedSet Nodes: " << double (timeToRemoveSeedSetNodesEnd - timeToRemoveSeedSetNodesStart) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for ONLY the subModular part: " << double(sumModCritTimeEnd - sumModCritTimeStart) / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Breakup of time taken by the subModular part " << endl;
    cout << "Total time:" << double(removeCritNodeFromDependencyVectorTopCritTime) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for doing the BFS on nodes that are not reachable from seed:" << double(repopulateDependencyMatrixAfterCritNodeRemovalTime) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for recomputing dependencyValues:" << double(reComputeDependencyValuesTime) / (CLOCKS_PER_SEC * 60) << endl;

    /*
    cout << "Total time taken by randomNumGenerator: " << subModTopCritGraph->randomNumGen / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by outer while Loop: " << subModTopCritGraph->whileLoopTime / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Breakup of time taken by outer while Loop: " << endl;
    cout << "Total time taken by initialization: " << subModTopCritGraph->initTime / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by only the loop: " << subModTopCritGraph->onlyLoopTime / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Total time taken by calcDependancyMatrix(): " << subModTopCritGraph->matrixTime / (CLOCKS_PER_SEC * 60)
         << endl;
    cout << "Total time taken by BFS(): " << subModTopCritGraph->bfsTime / (CLOCKS_PER_SEC * 60) << endl;
    */

    myfile << totalAlgorithmTime << " <-NEW_SubModTime\n";
    return subModTopCritNodesToRemove;
}


void runSubModTopCrit(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &subModTopCritNodesToRemove,
                      set<int> *subModImpactNodesToRemove,
                      vector<int> &subModImpactTopCritNodesToRemoveUnsorted,
                      vector<int> &subModTopCritNodesToRemoveUnsorted) {

    float percentageTargetsFloat = (float) percentageTargets / (float) 100;

    unique_ptr<Graph> subModTopCritGraph = make_unique<Graph>();
    subModTopCritGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModTopCritGraph->setPropogationProbability(probability);
    }
    vector<int> activatedSet = vector<int>(subModTopCritGraph->n);
    for (int i = 0; i < subModTopCritGraph->n; i++) {
        activatedSet[i] = i;
    }
    subModTopCritNodesToRemove = subModTopCritNodesRemove(subModTopCritGraph, activatedSet, removeNodes,
                                                          maxInfluenceSeed, envelopedNodes, subModImpactNodesToRemove,
                                                          subModImpactTopCritNodesToRemoveUnsorted,
                                                          subModTopCritNodesToRemoveUnsorted);

    vector<vector<int>>().swap(subModTopCritGraph->rrSets);
    subModTopCritGraph->dependancyVector.clear();
    subModTopCritGraph->vertexToIndex.clear();
    subModTopCritGraph->indexToVertex.clear();
    subModTopCritGraph.reset();
}

/************************************************ SUB MODULAR TOP CRIT NEW METHOD ENDS *******************************************************/


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

/*
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
//            case 3:set<int> active=dagDiffusion(graph,seedSet);
//             break;
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
*/

void runCountingNodes(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &countNodesToremove) {

    cout << "\n \n ******* Running CountingNodes approach ******** \n" << endl;
    resultLogFile << "\n \n ******* Running CountingNodes approach ******** \n" << endl;

    float percentageTargetsFloat = (float) percentageTargets / (float) 100;

    unique_ptr<Graph> countingNodesGraph = make_unique<Graph>();
    countingNodesGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        countingNodesGraph->setPropogationProbability(probability);
    }
    vector<int> activatedSet = vector<int>(countingNodesGraph->n);
    for (int i = 0; i < countingNodesGraph->n; i++) {
        activatedSet[i] = i;
    }
    activatedSet = vector<int>(countingNodesGraph->n, 0);
    for (int i = 0; i < countingNodesGraph->n; i++) {
        activatedSet[i] = i;
    }
    clock_t countNodesStartTime = clock();
    countNodesToremove = countNodesRemoveVertices(countingNodesGraph, removeNodes, maxInfluenceSeed, envelopedNodes,
                                                  activatedSet, "countNodes");
    clock_t countNodesEndTime = clock();
    double totalCountNodesTime = double(countNodesEndTime - countNodesStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\nCountNodes Graph algorithm time in minutes \n" << totalCountNodesTime << endl;
    resultLogFile << "\nCountNodes Graph algorithm time in minutes \n" << totalCountNodesTime << endl;

    myfile << totalCountNodesTime << " <-CountNodes Time\n";
    countingNodesGraph.reset();
}

void runTopKInfluential(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &topKInflNodesToremove) {

    cout << "\n \n ******* Running topKInfluential approach ******** \n" << endl;
    resultLogFile << "\n \n ******* Running topKInfluential approach ******** \n" << endl;

    float percentageTargetsFloat = (float) percentageTargets / (float) 100;
    unique_ptr<Graph> topKInflNodesGraph = make_unique<Graph>();
    topKInflNodesGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        topKInflNodesGraph->setPropogationProbability(probability);
    }
    vector<int> activatedSet = vector<int>(topKInflNodesGraph->n);
    for (int i = 0; i < topKInflNodesGraph->n; i++) {
        activatedSet[i] = i;
    }
    activatedSet = vector<int>(topKInflNodesGraph->n, 0);
    for (int i = 0; i < topKInflNodesGraph->n; i++) {
        activatedSet[i] = i;
    }
    clock_t topKInflNodesStartTime = clock();

    topKInflNodesToremove = topKInflNodesRemoveVertices(topKInflNodesGraph, removeNodes, maxInfluenceSeed,
                                                        envelopedNodes,
                                                        activatedSet, "modular");
    clock_t topKInflNodesEndTime = clock();
    double totalTopKInflTime = double(topKInflNodesEndTime - topKInflNodesStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\ntopKInfluential Graph algorithm time in minutes \n" << totalTopKInflTime << endl;
    resultLogFile << "\ntopKInfluential Graph algorithm time in minutes \n" << totalTopKInflTime << endl;

    myfile << totalTopKInflTime << " <-topKInfluential Time\n";
    topKInflNodesGraph.reset();
}

set<int> subModTopKInflRemoveVertices(unique_ptr<Graph> &subModTopkInflGraph, int removeNodes, const set<int> &maxSeedSet,
                                      const set<int> &envelopedNodes, vector<int> &activatedSet, string modular) {


    bool tshoot = false;//Prints the graphTranspose after the nodes have been deleted
    bool tshoot1 = true;//Controls the assert statements
    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet
    bool tshoot3 = true;//Prints the NodeInRRSets values for ALL of the nodes

    //Calculate the value of R
    set<int> alreadyinSeed = set<int>();
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "R = " << R << endl;


    //Removing the nodes present in the maxSeedSet from the Graph
    int numEdgesAtStart = subModTopkInflGraph->m;
    int totalNumEdgesToDelete = 0;          //Stores the total no. of edges being deleted by removing all of the nodes in maxSeedSet
    for (int node:maxSeedSet) {

        int totalEdgesInTransGraphPre = 0;  //Stores the number of edges in transpose of the Graph
        int totalEdgesInOrigGraphPre = 0;   //Stores the number of edges in the original Graph
        int numEdgesToDelete = 0;           //Stores the total number of edges incident on each node being deleted in both the original and transposed graph

        if (tshoot1) {
            for (int k = 0; k < subModTopkInflGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += subModTopkInflGraph->graphTranspose[k].size();
                if (k == node) {
                    numEdgesToDelete += subModTopkInflGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < subModTopkInflGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += subModTopkInflGraph->graph[k].size();
                if (k == node) {
                    numEdgesToDelete += subModTopkInflGraph->graph[k].size();
                }
            }
        }

        totalNumEdgesToDelete += numEdgesToDelete;
        subModTopkInflGraph->removeOutgoingEdges(node);
        assert(("Here . .. .", subModTopkInflGraph->graph[node].size() == 0));
        assert(("Here . .. .", subModTopkInflGraph->graphTranspose[node].size() == 0));
        if(tshoot1){
            subModTopkInflGraph->assertCorrectNodesAreDeleted(node, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                              totalEdgesInTransGraphPre);
        }

    }

    //Assert: the total number of edges in the graph formed after removing the seedSet nodes is equal to
    //the difference betn the no. of edges in the original graph and the no. of edges that you actually had to delete
    if (tshoot1) {
        int totalNumOfEdges = 0;
        for (int k = 0; k < subModTopkInflGraph->graph.size(); k++) {
            totalNumOfEdges += subModTopkInflGraph->graph[k].size();
        }
        assert(("subModTopKInflRemoveVertices() Divergence betn something", totalNumOfEdges ==
                                                                            numEdgesAtStart - totalNumEdgesToDelete));
        totalNumOfEdges = 0;
        for (int k = 0; k < subModTopkInflGraph->graphTranspose.size(); k++) {
            totalNumOfEdges += subModTopkInflGraph->graphTranspose[k].size();
        }
        assert(("subModTopKInflRemoveVertices() Divergence betn something", totalNumOfEdges ==
                                                                            numEdgesAtStart - totalNumEdgesToDelete));
    }

    //Find the nodes to remove in the graph obtained after removing the nodes from the seedSet
    subModTopkInflGraph->generateRandomRRSetsFromTargets(R, activatedSet, modular, resultLogFile);
    cout << "\n RRsets done " << flush;
    resultLogFile << "\n RRsets done " << flush;

    int modStrength = 0;
    for (int i = 0; i < subModTopkInflGraph->NodeinRRsetsWithCounts.size(); i++) {
        modStrength += subModTopkInflGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n Initial Strength is " << modStrength << endl;
    resultLogFile << "\n \n Initial Strength is " << modStrength << endl;
    myfile << modStrength << " <-InitialStrength of subModTopkInfl" << endl;

    //Printing modular values for all of the nodes to the file
    if (tshoot3) {
        dependValues << "In subModTopKInflRemoveVertices:" << endl;
        dependValues << "Printing modular values for all of the nodes:" << endl;
        for (int i = 0; i < subModTopkInflGraph->NodeinRRsetsWithCounts.size(); i++) {
            dependValues << subModTopkInflGraph->NodeinRRsetsWithCounts[i] << endl;
        }
        dependValues << "-----DONE PRINTING------" << endl;
    }

    //Find nodes to be removed
    vector<pair<int, int>> SortedNodeidCounts = vector<pair<int, int>>();
    for (int i = 0; i < subModTopkInflGraph->NodeinRRsetsWithCounts.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = subModTopkInflGraph->NodeinRRsetsWithCounts[i];
        SortedNodeidCounts.push_back(node);
    }

    std::sort(SortedNodeidCounts.begin(), SortedNodeidCounts.end(), sortbysecdesc);
    assert(SortedNodeidCounts.at(0).second >= SortedNodeidCounts.at(1).second);

    set<int> nodesToRemove;
    int count = 0;
    int j = 0;
    while (j < removeNodes && j < SortedNodeidCounts.size()) {
        int nodeid = SortedNodeidCounts.at(count).first;
        if (nodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid) == 0 && envelopedNodes.count(nodeid) == 0) {
            nodesToRemove.insert(nodeid);
            subModTopKInflNodesToRemoveUnsorted.push_back(nodeid);//subModTopKInflNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }
    assert(("Mismatch in subModTopkInflNodesToRemove", nodesToRemove.size() == removeNodes));
    if (tshoot2 && useEnvelop) {
        cout << "Mod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
             << endl;
        myfile << "Mod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
               << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }

    vector<pair<int, int>>().swap(SortedNodeidCounts);
    cout << "\n Number of nodes Already present in seed set (should be 0)= " << alreadyinSeed.size() << endl;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing the nodes already in seed that were not added to removeNodes (should be empty)" << endl;
    myfile << "Printing the nodes already in seed that were not added to removeNodes (should be empty):" << endl;
    printSet(alreadyinSeed);



    //Remove the edges incident on the nodes to be removed

    //The Graph will have to be created again because we removed the nodes belonging to the seed set in subModTopkInflGraph
    float percentageTargetsFloat = (float) percentageTargets / (float) 100;
    subModTopkInflGraph.reset();
    subModTopkInflGraph = make_unique<Graph>();
    subModTopkInflGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModTopkInflGraph->setPropogationProbability(probability);
    }

    //Removing the nodes to be deleted (as generated by this algo) from the original graph
    numEdgesAtStart = subModTopkInflGraph->m;
    totalNumEdgesToDelete = 0;              //Stores the total no. of edges being deleted by removing all of the nodes in nodesToRemove
    for (int node:nodesToRemove) {

        int totalEdgesInTransGraphPre = 0;  //Stores the number of edges in transpose of the Graph
        int totalEdgesInOrigGraphPre = 0;   //Stores the number of edges in the original Graph
        int numEdgesToDelete = 0;

        if (tshoot1) {
            for (int k = 0; k < subModTopkInflGraph->graphTranspose.size(); k++) {
                totalEdgesInTransGraphPre += subModTopkInflGraph->graphTranspose[k].size();
                if (k == node) {
                    numEdgesToDelete += subModTopkInflGraph->graphTranspose[k].size();
                }
            }
            for (int k = 0; k < subModTopkInflGraph->graph.size(); k++) {
                totalEdgesInOrigGraphPre += subModTopkInflGraph->graph[k].size();
                if (k == node) {
                    numEdgesToDelete += subModTopkInflGraph->graph[k].size();
                }
            }
        }

        totalNumEdgesToDelete += numEdgesToDelete;
        subModTopkInflGraph->removeOutgoingEdges(node);
        assert(("Here . .. .", subModTopkInflGraph->graph[node].size() == 0));
        assert(("Here . .. .", subModTopkInflGraph->graphTranspose[node].size() == 0));
        subModTopkInflGraph->assertCorrectNodesAreDeleted(node, numEdgesToDelete, totalEdgesInOrigGraphPre,
                                                          totalEdgesInTransGraphPre);
    }

    //Assert: the total number of edges in the graph obtained after removing the nodes to ACTUALLY delete from the graph
    //is equal to the difference betn the no. of edges in the original graph and the no. of edges that you actually had to delete
    if (tshoot1) {
        int totalNumOfEdges = 0;
        for (int k = 0; k < subModTopkInflGraph->graph.size(); k++) {
            totalNumOfEdges += subModTopkInflGraph->graph[k].size();
        }
        assert(("subModTopKInflRemoveVertices() Divergence betn something", totalNumOfEdges ==
                                                                            numEdgesAtStart - totalNumEdgesToDelete));
        totalNumOfEdges = 0;
        for (int k = 0; k < subModTopkInflGraph->graphTranspose.size(); k++) {
            totalNumOfEdges += subModTopkInflGraph->graphTranspose[k].size();
        }
        assert(("subModTopKInflRemoveVertices() Divergence betn something", totalNumOfEdges ==
                                                                            numEdgesAtStart - totalNumEdgesToDelete));
    }

    if (tshoot) {
        cout << "Printing the transposed graph after the nodes have been deleted: " << endl;
        print2DVector(subModTopkInflGraph->graphTranspose);
    }

    vector<int>().swap(subModTopkInflGraph->NodeinRRsetsWithCounts);
    subModTopkInflGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    modStrength = 0;
    for (int i = 0; i < subModTopkInflGraph->NodeinRRsetsWithCounts.size(); i++) {
        modStrength += subModTopkInflGraph->NodeinRRsetsWithCounts[i];
    }
    cout << "\n \n After removing SubModTopKInfl Strength is " << modStrength;
    resultLogFile << "\n \n After removing SubMod TopKInfl Strength is " << modStrength;
    myfile << modStrength << " <-SubModTopKInflStrength\n";
    vector<vector<int>>().swap(subModTopkInflGraph->rrSets);

    return nodesToRemove;
}

void runSubModTopkInfl(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &subModTopKInflNodesRemove) {

    float percentageTargetsFloat = (float) percentageTargets / (float) 100;
    unique_ptr<Graph> subModTopkInflGraph = make_unique<Graph>();

    subModTopkInflGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModTopkInflGraph->setPropogationProbability(probability);
    }
    vector<int> activatedSet = vector<int>(subModTopkInflGraph->n);
    for (int i = 0; i < subModTopkInflGraph->n; i++) {
        activatedSet[i] = i;
    }
    clock_t subModtopKInflNodesStart = clock();
    subModTopKInflNodesRemove = subModTopKInflRemoveVertices(subModTopkInflGraph, removeNodes, maxInfluenceSeed,
                                                             envelopedNodes,
                                                             activatedSet, "modular");
    clock_t subModtopKInflNodesEnd = clock();
    double totalSubModTopkInfl = double(subModtopKInflNodesEnd - subModtopKInflNodesStart) / (CLOCKS_PER_SEC * 60);
    cout << "\ntotalSubModTopkInfl Graph algorithm time in minutes \n" << totalSubModTopkInfl << endl;
    resultLogFile << "\ntotalSubModTopkInfl Graph algorithm time in minutes \n" << totalSubModTopkInfl << endl;
    myfile << totalSubModTopkInfl << " <-subModtopKInfl Time\n";
}


void executeTIMTIMfullGraph(cxxopts::ParseResult result) {
    clock_t executionTimeBegin = clock();

    IMResults::getInstance().setFromFile(fromFile);
    // insert code here...
    float percentageTargetsFloat = (float) percentageTargets / (float) 100;

    unique_ptr<Graph> influencedGraph = make_unique<Graph>();
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
    set<int> seedSet = set<int>();
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
    set<int> envelopedNodes;//These are the nodes that should not be removed but are not a part of the seed
    int maxInfluenceNum;

    if (someCondition) {

        unique_ptr<Graph> maxSeedGraph = make_unique<Graph>();
        maxSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
        if (!useIndegree) {
            maxSeedGraph->setPropogationProbability(probability);
        }

        cout << "\n\n******* Calculating seed set******** \n" << flush;
        if (useRandomSeed) {
            set<int> top100Nodes = set<int>();
            cout << "Using Random Seed as the seed Set to calculate influence: " << endl;
            //We want to use the top 100 nodes that are returned by the getSeed() method as the larger set
            myfile << "Using Random Seed as the seed Set to calculate influence: " << endl;
            top100Nodes = getSeed(100, maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                                  NULL);
            vector<int> placeholder = vector<int>();
            for (int const node: top100Nodes) {
                placeholder.push_back(node);
            }
            // obtain a time-based seed
            unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
            //randomly permute the placeholder
            shuffle(placeholder.begin(), placeholder.end(), std::default_random_engine(seed));
            //Add the first budget number of nodes to the maxSeed
            for (int i = 0; i < budget; i++) {
                maxInfluenceSeed.insert(placeholder[i]);
            }
            assert(("Incorrect number of nodes added in random seed", maxInfluenceSeed.size() == budget));
            maxInfluenceNum = oldNewIntersection(maxSeedGraph, maxInfluenceSeed, activatedSet, resultLogFile);
            myfile << maxInfluenceNum << " <-Influence of chosen random seed on the original Graph G" << endl;
            cout << "\n \n******* Calculating randomSeed to be used ends ******** \n" << endl;

        } else {
            myfile << "Max influence Seed Set in the original graph: " << endl;
            cout << "Max influence Seed Set in the original graph: " << endl;

            if (useEnvelop) {
                //This code will run when someCondition is true AND envelopedNodes is true.
                //THis implies you cannot remove anything from the seed Set OR the envelopNodes as well
                envelopedNodes = getSeed((budget + 100), maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(),
                                         set<int>(),
                                         NULL);    //Find the top (budget + 100) nodes that will form a part of the envelop
            }

            maxInfluenceSeed = getSeed(budget, maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(),
                                       set<int>(),
                                       NULL);
            vector<vector<int>>().swap(maxSeedGraph->rrSets);
            maxInfluenceNum = oldNewIntersection(maxSeedGraph, maxInfluenceSeed, activatedSet, resultLogFile);
            myfile << maxInfluenceNum << " <-MaxInfluence Num\n";
            cout << "\n \n******* Max influence end ******** \n" << flush;
        }

    }


    //******************************************************************************************************************

    set<int> modNodesToremove;
    cout << "\n ******* Running modular approach ******** \n" << flush;
    resultLogFile << "\n ******* Running modular approach ******** \n";

    clock_t ModReverseStartTime = clock();
    modNodesToremove = removeVertices(influencedGraph, removeNodes, maxInfluenceSeed, envelopedNodes, activatedSet,
                                      "modular");
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
    unique_ptr<Graph> transposedGraph = make_unique<Graph>();

    transposedGraph->readGraph(nameOfTheGraph, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        transposedGraph->setPropogationProbability(probability);
    }

    activatedSet = vector<int>(transposedGraph->n, 0);
    for (int i = 0; i < transposedGraph->n; i++) {
        activatedSet[i] = i;
    }

    clock_t tGraphStartTime = clock();
    tGraphNodesToremove = tGraphRemoveVertices(transposedGraph, influencedGraph, removeNodes, maxInfluenceSeed,
                                               envelopedNodes,
                                               activatedSet,
                                               "modular");

    clock_t tGraphEndTime = clock();
    double totaltGraphTime = double(tGraphEndTime - tGraphStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\nTransposed Graph algorithm time in minutes \n" << totaltGraphTime << flush;
    resultLogFile << "\nTransposed Graph algorithm time in minutes \n" << totaltGraphTime;

    myfile << totaltGraphTime << " <-transposedGraph Time\n";

    influencedGraph.reset();
    transposedGraph.reset();

    //******************************************************************************************************************

    set<int> countNodesToremove;
    set<int> topKInflNodesToremove;
    /*
     * WARNING: Uncomment if you want to run this
     * You will also have to uncomment the corresponding methods in the newDiffusion() method

    runCountingNodes(maxInfluenceSeed, envelopedNodes, countNodesToremove);
    runTopKInfluential(maxInfluenceSeed, envelopedNodes, topKInflNodesToremove);
     */

    //******************************************************************************************************************

    cout << "\n ******* Running the subModular version of top-k-infl approach ******** \n" << endl;
    resultLogFile << "\n ******* Running the subModular version of top-k-infl approach ******** \n" << endl;

    set<int> subModTopKInflNodesRemove;
    runSubModTopkInfl(maxInfluenceSeed, envelopedNodes, subModTopKInflNodesRemove);


    //******************************************************************************************************************

    cout << "\n \n ******* Running Sub Modular approach ******** \n" << flush;
    resultLogFile << "\n \n ******* Running Sub Modular approach ******** \n" << flush;

    unique_ptr<Graph> subInfluencedGraph = make_unique<Graph>();
    subInfluencedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subInfluencedGraph->setPropogationProbability(probability);
    }
    set<int> *removalModImpact = new set<int>();
    vector<int> subModImpactNodesToRemoveUnsorted;
    vector<int> subModNodesToRemoveUnsorted;

    set<int> subModNodesToremove = subModularNodesRemove(subInfluencedGraph, activatedSet, removeNodes,
                                                         maxInfluenceSeed, envelopedNodes,
                                                         removalModImpact, subModImpactNodesToRemoveUnsorted,
                                                         subModNodesToRemoveUnsorted);
    vector<vector<int>>().swap(subInfluencedGraph->rrSets);

    /*
    for (int rrSetId = 0; rrSetId < subInfluencedGraph->dependancyVector.size(); rrSetId++) {                           //for each RRSet in dependancyVector
        vector<vector<bool>>().swap((*subInfluencedGraph->dependancyVector[rrSetId]));                                  //https://stackoverflow.com/questions/13944886/is-stdvector-memory-freed-upon-a-clear
        (*subInfluencedGraph->vertexToIndex[rrSetId]).clear();                                                          //https://stackoverflow.com/questions/2629018/how-do-i-force-my-stdmap-to-deallocate-memory-used
        vector<int>().swap((*subInfluencedGraph->indexToVertex[rrSetId]));
    }
    subInfluencedGraph->dependancyVector.clear();
    subInfluencedGraph->vertexToIndex.clear();
    subInfluencedGraph->indexToVertex.clear();
     */
    subInfluencedGraph.reset();
    //delete subInfluencedGraph;

    //******************************************************************************************************************

    cout << "\n ******* Running the subModular version of topCrit approach ******** \n" << endl;

    set<int> subModTopCritNodesToRemove;
    vector<int> subModImpactTopCritNodesToRemoveUnsorted;
    vector<int> subModTopCritNodesToRemoveUnsorted;
    set<int>* subModImpactTopCritNodesToRemove = new set<int>();//Stores the nodes removed by Method 3 (if you remember what it actually was...)

    runSubModTopCrit(maxInfluenceSeed, envelopedNodes, subModTopCritNodesToRemove, subModImpactTopCritNodesToRemove,
                     subModImpactTopCritNodesToRemoveUnsorted, subModTopCritNodesToRemoveUnsorted);

    //******************************************************************************************************************
    resultLogFile << "\n \n******* Node removed in all four approaches ******** \n" << flush;

    unique_ptr<Graph> modNewGraph = make_unique<Graph>();
    modNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modNewGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> tGraph = make_unique<Graph>();
    tGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        tGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> countNewGraph = make_unique<Graph>();
    countNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        countNewGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> topKInflNewGraph = make_unique<Graph>();
    topKInflNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        topKInflNewGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> subModtopKInflGraph = make_unique<Graph>();
    subModtopKInflGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModtopKInflGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> modImpactGraph = make_unique<Graph>();
    modImpactGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modImpactGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> subNewGraph = make_unique<Graph>();
    subNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subNewGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> subModImpactTopCritGraph = make_unique<Graph>();
    subModImpactTopCritGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModImpactTopCritGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> subModTopCritGraphNew = make_unique<Graph>();
    subModTopCritGraphNew->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModTopCritGraphNew->setPropogationProbability(probability);
    }

    string convertedFile =
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            graphFileName;
    newDiffusion(modNewGraph, subNewGraph, modImpactGraph, tGraph, countNewGraph, topKInflNewGraph, subModtopKInflGraph,
                 subModImpactTopCritGraph, subModTopCritGraphNew,
                 modNodesToremove, subModNodesToremove, removalModImpact, tGraphNodesToremove, countNodesToremove,
                 topKInflNodesToremove, subModTopKInflNodesRemove, subModImpactTopCritNodesToRemove, subModTopCritNodesToRemove,
                 activatedSet, newSeed, percentageTargetsFloat, convertedFile, maxInfluenceSeed,
                 subModImpactNodesToRemoveUnsorted, subModNodesToRemoveUnsorted, subModImpactTopCritNodesToRemoveUnsorted, subModTopCritNodesToRemoveUnsorted);

    clock_t executionTimeEnd = clock();
    double totalExecutionTime = double(executionTimeEnd - executionTimeBegin) / (CLOCKS_PER_SEC * 60) ;
    cout << "\n Elapsed time in minutes " << totalExecutionTime << endl;
    resultLogFile << "\n Elapsed time in minutes " << totalExecutionTime << endl;


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
    string storesResultFile;
    resultFile = graphFileName;

    if (fullgraph) {
        resultFile += "_FullGraph_results.txt";
        resultFile =
                "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\results\\" +
                resultFile;
        storesResultFile = resultFile + "_values";
        myfile.open(resultFile, std::ios::app);
        dependValues.open(storesResultFile, std::ios::app);
        myfile << "\n" << budget << " <-SeedSetSize\n" << removeNodes << " <-removeNodes\n";
        dependValues << "\n" << budget << " <-SeedSetSize\n" << removeNodes << " <-removeNodes\n";
        executeTIMTIMfullGraph(result);
    } else {
        resultFile += "_RRapproach_results.txt";
        resultFile =
                "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\results\\" +
                resultFile;
        myfile.open(resultFile, std::ios::app);
        myfile << "\n" << budget << " " << removeNodes << " ";
    }
    disp_mem_usage("");
    return 0;
}
