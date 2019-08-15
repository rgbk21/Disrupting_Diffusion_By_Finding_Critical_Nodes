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
ofstream tshootingFile;
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
vector<int> testMaxInfluenceSeed;
vector<int> testSubModNodesToRemove;
vector<int> testCritNodesRemovedSoFar;

double removeCritNodeFromDependencyVectorTopCritTime = 0;
double reComputeDependencyValuesTime = 0;
double repopulateDependencyMatrixAfterCritNodeRemovalTime = 0;
int nodeNumBeingRemovedGlobal = 20;
//Global variables for testing end here

/*List of warnings:
 * 1) If you are trying to find the best seed set for each set of methods and not at the start of the experiment, remember that you have added some additional
 * methods. And you are not passing the removeNode set<> into the getSeed() method for those newly added methods. SO make sure you chagne that if you
 * are going to run those experiments.
 *
 * 2) Uncomment the countGraph and the topKInfl metods if you want to run them
 *
 * 3) In removeSeedSetNodeFromDependencyVector() there is an assert statement. Set tshoot to false when actually running the program.
 * 4) //WARNING --- Dont call if final vertex to be removed has been found. Removed this for testing. Reintroduce if actually runnning.
 * 5) generateRRSetsForSubModTopCrit() has an assert statement that has been commented out. Reintroduce if testing code.
 * 6) removed a bunch of testMethods from the subModTopCrit method. Reintroduce if testing the code?
 * 7) removeCritNodeWithCriticalityUpdate() contains assert statements that have been disabled/enabled using the tshoot boolean.
 *    Check when actually running the code to ensure that tshoot is set to false.
 *
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

int calcIntersection(const set<int> &set1, const set<int> &set2){

    int count = 0;
    for (int i:set1) {
        if (set2.count(i) == 1) count++;
    }

    return count;
}

void generateRRSetsFromSpecificNode(unique_ptr<Graph> &combinedGraph, int node, set<int> &nodesRchbl){

    int R = 10000;
    std::random_device rd;  // obtain a random number from hardware
    std::mt19937 eng(rd()); // seed the generator
//    std::uniform_int_distribution<> distr(0, n-1);
    deque<int> q = deque<int>();
    vector<int> visitMark = vector<int>(combinedGraph->n);
    vector<bool> visited = vector<bool>(combinedGraph->n, false);

    for (int i = 0; i < R; i++) {
        q.clear();
        q.push_back(node);
        int nVisitMark = 0;
        visitMark[nVisitMark++] = node;
        visited[node] = true;
        while (!q.empty()) {
            int expand = q.front();
            q.pop_front();
            for (int j = 0; j < (int) combinedGraph->graphTranspose[expand].size(); j++) {
                int v = combinedGraph->graphTranspose[expand][j];
                uniform_int_distribution<> dis(1, combinedGraph->inDegree[expand]);// define the range
                int randomNumber = dis(eng);
                if (randomNumber != 1) continue;
                if (visited[v]) continue;
                if (!visited[v]) {
                    visitMark[nVisitMark++] = v;
                    visited[v] = true;
                }
                q.push_back(v);
                nodesRchbl.insert(v);
            }
        }
        for (int j = 0; j < nVisitMark; j++) {
            visited[visitMark[j]] = false;
        }
    }
}

/*
 * The problem is: removing nodes as per the subMod algorithm, in some cases, gives a higher influence value as compared to removing nodes by the mod method
 * The logic behind the below validationCheck() is as follows:
 * Suppose 10 nodes were being removed. There will be some nodes that will be selected by both subMod and mod algos for removal.
 * Let C be the common nodes
 * Let the nodes removed only by the subMod be S1
 * Let the nodes removed only by the Mod be S2
 * What we are going to do is this:
 * Starting from every node in S1, do a reverse reachabilty test in the
 * */
void validationCheck(set<int> *modImpactNodesToRemove, set<int> &subModTopCritNodesToRemove,
                     float percentageTargetsFloat) {

    //Initialising the Graph
    unique_ptr<Graph> combinedGraph = make_unique<Graph>();//combinedGraph is the Graph from which the common nodes from the subMod and the mod method will be removed
    combinedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        combinedGraph->setPropogationProbability(probability);
    }
    vector<int> activatedSet = vector<int>(combinedGraph->n);
    for (int i = 0; i < combinedGraph->n; i++) {
        activatedSet[i] = i;
    }

    //Finding the common nodes as selected by the subMod and the mod algorithms
    set<int> commonNodes = set<int>();
    set<int> nodesOnlyInSubMod = set<int>();
    set<int> nodesOnlyInMod = set<int>();

    for(int node : subModTopCritNodesToRemove){
        if(modImpactNodesToRemove->count(node) > 0){
            commonNodes.insert(node);
        }else{
            nodesOnlyInSubMod.insert(node);
        }
    }
    for(int node : *modImpactNodesToRemove){
        if(subModTopCritNodesToRemove.count(node) == 0){
            nodesOnlyInMod.insert(node);
        }
    }
    myfile << "\nValidating the influences obtained by subModTopCrit and modTopCrit" << endl;
    cout << "\nValidating the influences obtained by subModTopCrit and modTopCrit" << endl;
    cout << "Common nodes: ";
    myfile << "Common nodes: ";
    for(int node : commonNodes){
        cout << node << " ";
        myfile << node << " ";
    }
    cout << endl;
    myfile << endl;
    cout << "Nodes only in subMod: ";
    myfile << "Nodes only in subMod: ";
    for(int node : nodesOnlyInSubMod){
        cout << node << " ";
        myfile << node << " ";
    }
    cout << endl;
    myfile << endl;
    cout << "Nodes only in mod: ";
    myfile << "Nodes only in mod: ";
    for(int node : nodesOnlyInMod){
        cout << node << " ";
        myfile << node << " ";
    }
    cout << endl;
    myfile << endl;

    removingNodesFromGraph(combinedGraph, commonNodes);

    //Calculating nodes reached from the nodes in nodesOnlyInSubMod in G_T - by generating rrSets.
    set<int> nodesRchblFrmNodesOnlyInSubMod = set<int>();
    for(int node : nodesOnlyInSubMod){
        generateRRSetsFromSpecificNode(combinedGraph, node, nodesRchblFrmNodesOnlyInSubMod);
    }
    //Calculating nodes reached from the nodes in nodesOnlyInMod in G_T - by generating rrSets.
    set<int> nodesRchblFrmNodesOnlyInMod = set<int>();
    for(int node : nodesOnlyInMod){
        generateRRSetsFromSpecificNode(combinedGraph, node, nodesRchblFrmNodesOnlyInMod);
    }

    cout << "Nodes reachable only in subMod: ";
    myfile << "Nodes reachable only in subMod: ";
    for(int node : nodesRchblFrmNodesOnlyInSubMod){
        cout << node << " ";
        myfile << node << " ";
    }

    cout << endl;
    myfile << endl;
    cout << "Nodes reachable only in mod: ";
    myfile << "Nodes reachable only in mod: ";
    for(int node : nodesRchblFrmNodesOnlyInMod){
        cout << node << " ";
        myfile << node << " ";
    }
    cout << endl;
    myfile << endl;

    //Find influence of the nodes in nodesRchblFrmNodesOnlyInSubMod and nodesRchblFrmNodesOnlyInMod
    int k = 0;
    vector<int> subModResults = vector<int>();
    vector<int> modResults = vector<int>();
    int subModInflValue = 0;
    int modInflValue = 0;

    myfile << "SubModResults ModResults" << endl;
    while (k < 5) {

        cout << "\n********** k = " << k << " **********" << endl;

        int infNum = 0;

        cout << k << "---" << "\nNew_SubMod Results: " << endl;
        infNum = oldNewIntersection(combinedGraph, nodesRchblFrmNodesOnlyInSubMod, activatedSet, resultLogFile);
        vector<vector<int>>().swap(combinedGraph->rrSets);
        subModResults.push_back(infNum);
        myfile << infNum << "\t\t";

        cout << k << "---" << "\nNew_Mod Impact Results: " << endl;
        infNum = oldNewIntersection(combinedGraph, nodesRchblFrmNodesOnlyInMod, activatedSet, resultLogFile);
        vector<vector<int>>().swap(combinedGraph->rrSets);
        modResults.push_back(infNum);
        myfile << infNum << "\n";

        k++;
    }

    for (int i = 0; i < k; i++) {
        subModInflValue += subModResults[i];
        modInflValue += modResults[i];
    }

    subModInflValue = subModInflValue/5;
    modInflValue = modInflValue/5;

    cout << endl;
    myfile << endl;
    cout << "SubModInfl Value: " << subModInflValue << endl;
    cout << "modInfl Value: " << modInflValue << endl;
    myfile << "SubModInfl Value: " << subModInflValue << endl;
    myfile << "modInfl Value: " << modInflValue << endl;
}

void newDiffusion(unique_ptr<Graph> &newModGraph,
                  unique_ptr<Graph> &tGraph, unique_ptr<Graph> &subModtopKInflGraph,
                  unique_ptr<Graph> &modImpactGivenSeedGraph,
                  unique_ptr<Graph> &subModGivenSeedGraph,
                  set<int> modNodes, set<int> tGraphNodes,
                  set<int> &subModTopKInflNodesRemove,
                  set<int> &modImpactGivenSeedNodesToRemove, set<int> &subModGivenSeedNodesToRemove,
                  vector<int> &activatedSet, int newSeed, float percentageTargetsFloat, string convertedFile,
                  set<int> &prevSelectSeed,
                  vector<int> &modImpactGivenSeedNodesToRemoveUnsorted,
                  vector<int> &subModGivenSeedNodesToRemoveUnsorted) {

    bool tshoot = true;

    //Stores the influence values calculated finally in each of the k number of iterations
    vector<int> modResults;
    vector<int> tGraphResults;
    vector<int> countGraphResults;
    vector<int> topKInflGraphResults;
    vector<int> subModTopKInflResults;
    vector<int> modImpactGivenSeedResults;
    vector<int> subModGivenSeedResults;

    cout << "\nnodes To remove in mod graph: ";
    removingNodesFromGraph(newModGraph, modNodes);

    cout << "\nnodes to remove in transposedGraph: ";
    removingNodesFromGraph(tGraph, tGraphNodes);

    cout << "\nnodes to remove in SubModtopKInflGraph: ";
    removingNodesFromGraph(subModtopKInflGraph, subModTopKInflNodesRemove);

    cout << "\nnodes to remove in modImpactGivenSeedGraph: ";
    removingNodesFromGraph(modImpactGivenSeedGraph, modImpactGivenSeedNodesToRemove);

    cout << "\nnodes to remove in subModGivenSeedGraph: ";
    removingNodesFromGraph(subModGivenSeedGraph, subModGivenSeedNodesToRemove);

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
        myfile << "\nnodes To remove in modImpactGivenSeedGraph graph: ";
        for (int i:modImpactGivenSeedNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;
        myfile << "\nnodes To remove in subModGivenSeedGraph graph: ";
        for (int i:subModGivenSeedNodesToRemoveUnsorted) {
            myfile << i << " ";
        }
        cout << flush;

    }

    cout << endl;
    myfile << endl;
    cout << "\nintersection of modTopKInfl and transposedGraph nodes to remove "            << calcIntersection(modNodes, tGraphNodes);
    cout << "\nintersection of modTopKInfl and SubModTopKInfl nodes to remove "             << calcIntersection(modNodes, subModTopKInflNodesRemove);
    cout << "\nintersection of modTopKInfl and modImpactGivenSeed nodes to remove "         << calcIntersection(modNodes, modImpactGivenSeedNodesToRemove);
    cout << "\nintersection of modTopKInfl and subModGivenSeed nodes to remove "            << calcIntersection(modNodes, subModGivenSeedNodesToRemove);
    cout << "\nintersection of SubModTopKInfl and modImpactGivenSeed nodes to remove "      << calcIntersection(subModTopKInflNodesRemove, modImpactGivenSeedNodesToRemove);
    cout << "\nintersection of SubModTopKInfl and subModGivenSeed nodes to remove "         << calcIntersection(subModTopKInflNodesRemove, subModGivenSeedNodesToRemove);
    cout << "\nintersection of modImpactGivenSeed and subModGivenSeed nodes to remove "     << calcIntersection(modImpactGivenSeedNodesToRemove, subModGivenSeedNodesToRemove);


    cout << endl;
    myfile << "\nintersection of modTopKInfl and transposedGraph nodes to remove "            << calcIntersection(modNodes, tGraphNodes);
    myfile << "\nintersection of modTopKInfl and SubModTopKInfl nodes to remove "             << calcIntersection(modNodes, subModTopKInflNodesRemove);
    myfile << "\nintersection of modTopKInfl and modImpactGivenSeed nodes to remove "         << calcIntersection(modNodes, modImpactGivenSeedNodesToRemove);
    myfile << "\nintersection of modTopKInfl and subModGivenSeed nodes to remove "            << calcIntersection(modNodes, subModGivenSeedNodesToRemove);
    myfile << "\nintersection of SubModTopKInfl and modImpactGivenSeed nodes to remove "      << calcIntersection(subModTopKInflNodesRemove, modImpactGivenSeedNodesToRemove);
    myfile << "\nintersection of SubModTopKInfl and subModGivenSeed nodes to remove "         << calcIntersection(subModTopKInflNodesRemove, subModGivenSeedNodesToRemove);
    myfile << "\nintersection of modImpactGivenSeed and subModGivenSeed nodes to remove "     << calcIntersection(modImpactGivenSeedNodesToRemove, subModGivenSeedNodesToRemove);

    myfile << endl;

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

    if (someCondition) {
        cout << "Setting max Seed to be the previously selected maxSeed" << endl;
        maxSeed = prevSelectSeed;
    }

    if (tshoot) {

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
        myfile << "\n\nmodTopK SubModTopK ModImpactGivenSeed SubModGivenSeed Transposed \n";
        while (k < 3) {

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

            cout << k << "---" << "\nModImpactGivenSeed Results: " << endl;
            infNum = oldNewIntersection(modImpactGivenSeedGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(modImpactGivenSeedGraph->rrSets);
            modImpactGivenSeedResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nsubModGivenSeed Results: " << endl;
            infNum = oldNewIntersection(subModGivenSeedGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subModGivenSeedGraph->rrSets);
            subModGivenSeedResults.push_back(infNum);
            myfile << infNum << "\t\t ";

            cout << k << "---" << "\nTransposed Graph Results: " << endl;
            infNum = oldNewIntersection(tGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(tGraph->rrSets);
            tGraphResults.push_back(infNum);
            myfile << infNum << "\n";

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
//        subModseedSet = getSeed(budget, subNewGraph, activatedSet, subModNodes, set<int>(), set<int>(), set<int>(),
//                                NULL);
        myfile << "Unsorted ModImpact SeedSet: ";
        cout << "Calculating ModImpact SeedSet: ";
//        modImpactseedSet = getSeed(budget, modImpactGraph, activatedSet, removalModImpactNodes, set<int>(), set<int>(),
//                                   set<int>(), NULL);
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


            cout << "\n********** k = " << k << " **********" << endl;

            int infNum = 0;

            cout << "\n" << k << " - Mod Results: " << endl;
            resultLogFile << "\nMod Results: " << endl;
            infNum = oldNewIntersection(newModGraph, modseedSet, activatedSet, resultLogFile);
            vector<vector<int>>().swap(newModGraph->rrSets);
            modResults.push_back(infNum);
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


    double newSubModGain = 0;
    double newImpactGain = 0;
    double modImpactGivenSeedGain = 0;
    double subModGivenSeedGain = 0;
    for (int i = 0; i < k; i++) {
        modImpactGivenSeedGain  += float(modResults[i] - modImpactGivenSeedResults[i]) / float(modResults[i]);
        subModGivenSeedGain     += float(modResults[i] - subModGivenSeedResults[i]) / float(modResults[i]);
    }

    newSubModGain           = (float) newSubModGain / k;
    newImpactGain           = (float) newImpactGain / k;
    modImpactGivenSeedGain  = (float) modImpactGivenSeedGain / k;
    subModGivenSeedGain     = (float) subModGivenSeedGain / k;

    myfile << modImpactGivenSeedGain << " <-modImpactGivenSeedGain\n" << subModGivenSeedGain << " <-subModGivenSeedGain\n";
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

/********************************************************* OLD SUB MODULAR METHOD ENDS *************************************************************/


/************************************************ NEW SUB MODULAR TOP CRIT NEW METHOD STARTS *******************************************************/

//This branch of the code does not contain this method. This branch is only supposed to contain the GIVE_SEED method.
// Refer to another branch for this code. Branch name has not been decided yet.
//inSanityCheck() is the only method that is being used by the GIVEN_SEED method

void inSanityCheck(unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues){

    for (int i = 0; i < testMaxInfluenceSeed.size(); i++) {
        int seedSetNode = testMaxInfluenceSeed[i];
        assert(("Value of seedSetNode is weird", dependencyValues[seedSetNode] == 0));
    }

    for (int i = 0; i < testCritNodesRemovedSoFar.size(); i++) {
        int crtiNode = testCritNodesRemovedSoFar[i];
        assert(("Value of critNode is weird", dependencyValues[crtiNode] == 0));
    }

    for(int i = 0; i < dependencyValues.size(); i++){
        assert(("-ve dependencyValues!!!", dependencyValues[i] >= 0));
    }

}
/************************************************ SUB MODULAR TOP CRIT NEW METHOD ENDS *******************************************************/

/************************************************ SUB MODULAR GIVEN THE SEED SET NODES STARTS *******************************************************/

//This check validates that every vertex does in fact have its dependencyValue equal to the sum of
//all its rows of the dependencyMatrices.
void checkIfDValuesAreCorrectForGivenSeedMethod(unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues){

    vector<int> testDValues = vector<int>(influencedGraph->n, 0);
    for(int rrSetId = 0; rrSetId < influencedGraph->isCriticalVector.size(); rrSetId++){
        for(int i = 0; i < (*influencedGraph->isCriticalVector[rrSetId]).size(); i++){
            if((*influencedGraph->isCriticalVector[rrSetId])[i]){
                testDValues[(*influencedGraph->indexToVertex[rrSetId])[i]]++;
            }
        }
    }

    for(int i = 0; i < dependencyValues.size(); i++){
        assert(("Mismatch in dependencyValues", dependencyValues[i] == testDValues[i]));
    }
}

//This method removes all the outgoing edges from the nodeBeingRemoved. Then we do a BFS from the source, and check if the seedSetNode is still reachable
//If it is, it means the nodeBeingRemoved is not critical and hence we return FALSE.
//If no seedSetNodes can be reached, it means the nodeBeingRemoved was critical, in which case we return TRUE.
bool isVertexCritical(unique_ptr<Graph> &influencedGraph, int nodeBeingRemoved, int rrSetId, vector<vector<int>> myMiniRRGraph,
                      unique_ptr<vector<bool>> &isSeed) {

    if((*isSeed)[0]) return false;
    myMiniRRGraph[nodeBeingRemoved].clear();                                        //Remove all outgoing edges from the nodeBeingRemoved
    vector<bool> visitedBFS = vector<bool>(myMiniRRGraph.size(), false);            //Mark all the vertices as not visited
    deque<int> queue;                                                               //Create a queue for BFS
    visitedBFS[0] = true;                                                           //Mark the current node as visited
    queue.push_back(0);                                                             //And add it to the queue

    while (!queue.empty()) {
        int u = queue.front();
        queue.pop_front();
        for (int i = 0; i < myMiniRRGraph[u].size(); i++) {
            int v = myMiniRRGraph[u][i];
            if (!visitedBFS[v]) {
                visitedBFS[v] = true;
                queue.push_back(v);
                if((*isSeed)[v]){
                    return false;
                }
            }
        }
    }

    return true;
}

void populateCriticalityVector(unique_ptr<Graph> &subModGivenSeedGraph, vector<int> &dependencyValues, const set<int> &maxSeedSet){

    cout << "Populating the CriticalityVector" << endl;
    for(int rrSetId = 0; rrSetId < subModGivenSeedGraph->dependancyVector.size(); rrSetId++){
        unordered_map<int, int>::const_iterator got;
        unique_ptr<vector<bool>> isSeed = make_unique<vector<bool>>((*subModGivenSeedGraph->miniRRGraphsVector[rrSetId]).size(), false);//isSeed <1,1,0,0,1> : This means in this particular miniRRGraph, vertices 0,1,4 have been selected as the overall seed
        bool rrSetContainsSeed = false;
        for (int seedSetNode : maxSeedSet) {
            got = subModGivenSeedGraph->vertexToIndex[rrSetId]->find(seedSetNode);                                      //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the seedSetNode
            if (got != subModGivenSeedGraph->vertexToIndex[rrSetId]->end()) {
                (*isSeed)[got->second] = true;
                rrSetContainsSeed = true;
            }
        }
        subModGivenSeedGraph->isSeedVector[rrSetId] = move(isSeed);
        if(rrSetContainsSeed){
            vector<vector<int>> myMiniRRGraph = (*subModGivenSeedGraph->miniRRGraphsVector[rrSetId]);
            for(int i = 0; i < (*subModGivenSeedGraph->miniRRGraphsVector[rrSetId]).size(); i++){
                if (isVertexCritical(subModGivenSeedGraph, i, rrSetId, myMiniRRGraph, subModGivenSeedGraph->isSeedVector[rrSetId])) {
                    (*subModGivenSeedGraph->isCriticalVector[rrSetId])[i] = true;
                }
            }
        }
    }

}

void computeDependencyValuesGivenSeedSet(unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues,
                                         vector<pair<int, int>> &ASdegree){

    bool tshoot = true;//prints values to file
    cout << "Calculating Dependency Values Given SeedSet" << endl;

    for (int rrSetId = 0; rrSetId < influencedGraph->isCriticalVector.size(); rrSetId++) {                              //for each RRSet in isCriticalVector
        for (int index = 0; index < influencedGraph->isCriticalVector[rrSetId]->size(); index++) {                      //for each index in the isCriticalVector
            if ((*influencedGraph->isCriticalVector[rrSetId])[index]) {                                                 //if the index (vertex) was critical to the reachability of the seedSet nodes
                int vertex = (*influencedGraph->indexToVertex[rrSetId])[index];                                         //find the vertex that was mapped to that index
                dependencyValues[vertex] += 1;                                                                          //Add the value to the existing dependencyValues of that vertex
            }
        }
    }

    dependValues << "\nPopulating dependency values for modImpactGivenSeed method" << endl;
    for (int i = 0; i < dependencyValues.size(); i++) {
        if (tshoot) {
            dependValues << dependencyValues[i] << endl;
        }
    }
    if (tshoot) dependValues << "------------------------------------------------------------" << endl;

    ASdegree = vector<pair<int, int>>();
    for (int i = 0; i < dependencyValues.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = dependencyValues[i];
        ASdegree.push_back(node);
    }

    std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);
    assert(ASdegree.at(0).second >= ASdegree.at(1).second);
    cout << "Impact Nodes Sorted!" << endl;
}

//Newer version of the method. Use this method only if the dependencyValues have been already updated,
//and all you have to do is sort them in orfder to find out the top-k nodes to be removed by the subModImpactTopCrit method.
void computeModImpactGivenSeedNodesToRemove(unique_ptr<Graph> &subModGivenSeedGraph, int removeNodes, vector<int> &dependencyValues,
                                  vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet,
                                  const set<int> &envelopedNodes,
                                  set<int> &removalModImpact, vector<int> &nodesToRemoveUnsorted) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    set<int> alreadyinSeed = set<int>();

    cout << "Selected modImpactGivenSeed Nodes to remove: " << endl;

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            removalModImpact.insert(node);
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

    assert(("Mismatch - removalModImpact and removeNodes", removalModImpact.size() == removeNodes));

//    cout << "Node to be removed by the mod Impact process" << endl;
//    printVector(modImpactNodesToRemoveUnsorted);

    cout << "\nassociated value is: " << alreadyinSeed.size() << endl;
    cout << "Number of nodes for (modImpactGivenSeed method) already present in seed set = " << alreadyinSeed.size() << endl;

    cout << "Printing nodes not added to modImpactGivenSeed method because they were in seedSet: " << endl;
    myfile << "Printing nodes not added to modImpactGivenSeed method because they were in seedSet: " << endl;
    printSet(alreadyinSeed);

    //Clearing alreadyinSeed because it contains the modImpact nodes at this point
    alreadyinSeed.clear();
}

void removeCritNodeWithCriticalityUpdate(int critNode, unique_ptr<Graph> &influencedGraph,
                                    vector<int> &dependencyValues, vector<pair<int, int>> &ASdegree) {

    bool tshoot = true;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    cout << "Removing critNode: " << critNode << endl;
    dependValues << "Removing critNode: " << critNode << endl;
    tshootingFile << " -------------------------- " << endl;

    for (int i = 0; i < influencedGraph->inRRSet[critNode].size(); i++) {                                               //for each RRSet in inRRSet (each RRSet that contains critNode)
        int rrSetId = influencedGraph->inRRSet[critNode][i];                                                            //get the next RRSet that the node to be removed is in
        bool rrSetContainsSeed = false;
        for(int j = 0; j < (*influencedGraph->isSeedVector[rrSetId]).size(); j++){                                      //First we need to check if this rrSet actually contains some seedSetNode or not.
            if((*influencedGraph->isSeedVector[rrSetId])[j]){
                rrSetContainsSeed = true;
                break;
            }
        }
        if(rrSetContainsSeed){                                                                                          //Reduce the dependencyValue of the nodes in this rrSet only if they contains some seed
            for(int index = 0; index < (*influencedGraph->isCriticalVector[rrSetId]).size(); index++){                  //isCritical for a vertex v was supposed to be TRUE only if removing the vertex v disconnected all the seedSetNodes from the source
                if((*influencedGraph->isCriticalVector[rrSetId])[index]){                                               //Now since we are deleting v, all the other vertices in this rrSet for which isCritical was set to TRUE, should now become FALSE.
                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[index]] -= 1;                           //..and should have their dependencyValue reduced
                    (*influencedGraph->isCriticalVector[rrSetId])[index] = false;
                }
            }
        }
    }
    assert(("WELL. FUCKING. DONE.", dependencyValues[critNode] == 0));
    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed
    if(tshoot){
        inSanityCheck(influencedGraph, dependencyValues);
        checkIfDValuesAreCorrectForGivenSeedMethod(influencedGraph, dependencyValues);
    }
    nodeNumBeingRemovedGlobal++;
}

void computeSubModGivenSeedNodesToRemove(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues,
                                    vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet,
                                    const set<int> &envelopedNodes, set<int> &subModNodesToremove,
                                    vector<int> &nodesToRemoveUnsorted, set<int> &alreadyinSeed) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    int index = 0;
    testCritNodesRemovedSoFar.clear();
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            subModNodesToremove.insert(node);
            nodesToRemoveUnsorted.push_back(node);
            if (i < removeNodes) {//WARNING --- Dont call if final vertex to be removed has been found (Not calling Now)
                removeCritNodeWithCriticalityUpdate(node, influencedGraph, dependencyValues, ASdegree);
            }
            index = 0;
        } else {
            alreadyinSeed.insert(node);
            index++;
        }
    }

//    inSanityCheck_22(influencedGraph, dependencyValues, nodesToRemoveUnsorted);//write this method!!!!!!!!!!!!!!!!!!!!!!!!!!

    if (tshoot2 && useEnvelop) {
        cout << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
             << endl;
        myfile
                << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }
}


set<int> subModGivenSeedNodesRemove(unique_ptr<Graph> &subModGivenSeedGraph, const vector<int> &activatedSet, int removeNodes,
                                  const set<int> &maxSeedSet, const set<int> &envelopedNodes,
                                  set<int> &modImpactGivenSeedNodesToRemove,
                                  vector<int> &modImpactGivenSeedNodesToRemoveUnsorted,
                                  vector<int> &subModGivenSeedNodesToRemoveUnsorted) {

    bool tshoot = true;//Prints the dependency values for before the seedSetNodes are removed to the file
    bool tshoot1 = true;//Prints the node being removed in each iteration
    bool tshoot2 = false;//Prints the outdegree values for the modNodes removed in Algo1

    clock_t subModReverseStartTime = clock();

    set<int> alreadyinSeed = set<int>();
    set<int> subModGivenSeedNodesToRemove;
    vector<pair<int, int>> ASdegree;
    int removalNum = removeNodes;
    vector<int> dependencyValues = vector<int>(subModGivenSeedGraph->n, 0);
    vector<int> testDependencyValues = vector<int>(subModGivenSeedGraph->n, 0);

    //Random RR sets
    int n = (int) activatedSet.size();
    double epsilon = (double) EPSILON;
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "\nRR sets are: " << R << endl;
    resultLogFile << "\nRR sets are: " << R << endl;
    subModGivenSeedGraph->generateRandomRRSetsFromTargets(R, activatedSet, "subModGivenSeed", resultLogFile);

    clock_t timeForGeneratingRRSets = clock();
    populateCriticalityVector(subModGivenSeedGraph, dependencyValues, maxSeedSet);
    clock_t timeToPopulateCriticalityVector = clock();
    computeDependencyValuesGivenSeedSet(subModGivenSeedGraph, dependencyValues, ASdegree);
    testDependencyValues = dependencyValues;//???
    clock_t timeToComputeDependencyValues = clock();

    cout << "\nComputing nodes to remove by the modImpactGivenSeed method" << endl;
    computeModImpactGivenSeedNodesToRemove(subModGivenSeedGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                                   envelopedNodes, modImpactGivenSeedNodesToRemove,
                                   modImpactGivenSeedNodesToRemoveUnsorted);

    clock_t ModImpactEndTime = clock();

//    checkIfModImpactValuesWereCorrect(subModTopCritGraph, maxSeedSet, dependencyValues, testDependencyValues);

    double totalModImpactTime = double(
            (timeForGeneratingRRSets - subModReverseStartTime) +
            (timeToPopulateCriticalityVector - timeForGeneratingRRSets) +
            (timeToComputeDependencyValues - timeToPopulateCriticalityVector) +
            (ModImpactEndTime - timeToComputeDependencyValues))
                                / (CLOCKS_PER_SEC * 60);

    cout << "modImpactGivenSeed algorithm time in minutes " << totalModImpactTime << endl;
    myfile << totalModImpactTime << " <-modImpactGivenSeed_Time\n";

    cout << "Breakup of time taken: " << endl;
    cout << "Time for generating RRSets: " << double (timeForGeneratingRRSets - subModReverseStartTime) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for populating criticalityVector: " << double (timeToPopulateCriticalityVector - timeForGeneratingRRSets) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time to compute dValue by iterating over all RRSets: " << double(timeToComputeDependencyValues - timeToPopulateCriticalityVector) / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;

    cout << "******* Completed modImpactGivenSeed approach ********" << endl;
    cout << endl;
    cout << endl;

    dependValues << "\n\n******* Completed modImpactGivenSeed approach ********" << endl;



    cout << "******* Running SubMod GivenSeed approach ********" << endl;
    dependValues << "******* Running SubMod GivenSeed approach ********" << endl;

    alreadyinSeed = set<int>();
    clock_t sumModGivenSeedTimeStart = clock();

    computeSubModGivenSeedNodesToRemove(subModGivenSeedGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                                        envelopedNodes,
                                        subModGivenSeedNodesToRemove, subModGivenSeedNodesToRemoveUnsorted,
                                        alreadyinSeed);

    assert(("Mismatch - subModNodesToremove and removeNodes", subModGivenSeedNodesToRemove.size() == removalNum));
    clock_t sumModGivenSeedTimeEnd = clock();

    vector<vector<int>>().swap(subModGivenSeedGraph->rrSets);
    cout << endl;
    cout << "Removed subModTopCrit Nodes from Graph: ";
    removingNodesFromGraph(subModGivenSeedGraph, subModGivenSeedNodesToRemove);
    cout << endl;

    cout << endl;
    subModGivenSeedGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    int subModStrength = 0;
    for (int i = 0; i < subModGivenSeedGraph->NodeinRRsetsWithCounts.size(); i++) {
        subModStrength += subModGivenSeedGraph->NodeinRRsetsWithCounts[i];
    }

    cout << "\nRecalculated Initial strength was = " << subModGivenSeedGraph->totalNumNodesInRRSets << endl;
    cout << "\nNumber of nodes Already present in seed set = " << alreadyinSeed.size() << endl;
    cout << "Printing nodes in alreadyinSeed that were not added to subModGivenSeedNodesToRemove:" << endl;
    myfile << "Printing nodes in alreadyinSeed that were not added to subModGivenSeedNodesToRemove:" << endl;
    printSet(alreadyinSeed);
    cout << "\nsubModStrengthGivenSeed = " << subModStrength;

    myfile << subModGivenSeedGraph->totalNumNodesInRRSets << " <-subModStrengthGivenSeed Init Strength\n";
    myfile << subModStrength << " <-subModStrengthGivenSeed\n";

    double totalAlgorithmTime = totalModImpactTime + (double(sumModGivenSeedTimeEnd - sumModGivenSeedTimeStart)/ (CLOCKS_PER_SEC * 60));
    cout << "\nsubModGivenSeed algorithm time in minutes " << totalAlgorithmTime << endl;
    cout << "Breakup of time taken: " << endl;
    cout << "modImpact Time: " << totalModImpactTime << endl;
    cout << "subMod Time: " << (double (sumModGivenSeedTimeEnd - sumModGivenSeedTimeStart) / (CLOCKS_PER_SEC * 60)) << endl;

    myfile << totalAlgorithmTime << " <- subModGivenSeed Time\n";
    return subModGivenSeedNodesToRemove;
}

void runSubModGivenSeed(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &subModGivenSeedNodesToRemove,
                      set<int> &modImpactGivenSeedNodesToRemove,
                      vector<int> &subModGivenSeedNodesToRemoveUnsorted,
                      vector<int> &modImpactGivenSeedNodesToRemoveUnsorted){

    float percentageTargetsFloat = (float) percentageTargets / (float) 100;

    unique_ptr<Graph> subModGivenSeedGraph = make_unique<Graph>();
    subModGivenSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModGivenSeedGraph->setPropogationProbability(probability);
    }
    vector<int> activatedSet = vector<int>(subModGivenSeedGraph->n);
    for (int i = 0; i < subModGivenSeedGraph->n; i++) {
        activatedSet[i] = i;
    }
    subModGivenSeedNodesToRemove = subModGivenSeedNodesRemove(subModGivenSeedGraph, activatedSet, removeNodes,
                                                            maxInfluenceSeed, envelopedNodes,
                                                            modImpactGivenSeedNodesToRemove,
                                                            modImpactGivenSeedNodesToRemoveUnsorted,
                                                            subModGivenSeedNodesToRemoveUnsorted);

    vector<vector<int>>().swap(subModGivenSeedGraph->rrSets);
    subModGivenSeedGraph->dependancyVector.clear();
    subModGivenSeedGraph->vertexToIndex.clear();
    subModGivenSeedGraph->indexToVertex.clear();
    subModGivenSeedGraph.reset();
}


/************************************************ SUB MODULAR GIVEN THE SEED SET NODES ENDS *******************************************************/

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
            testMaxInfluenceSeed = vector<int>();
            cout << "Chosen maxSeedSet: ";
            for(int i:maxInfluenceSeed){
                cout << i << " ";
                testMaxInfluenceSeed.push_back(i);
            }
            cout << endl;
            cout << maxInfluenceNum << " <-MaxInfluence Num " << endl;
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

    cout << "\n ******* Running the subModular version of top-k-infl approach ******** \n" << endl;
    resultLogFile << "\n ******* Running the subModular version of top-k-infl approach ******** \n" << endl;

    set<int> subModTopKInflNodesRemove;
    runSubModTopkInfl(maxInfluenceSeed, envelopedNodes, subModTopKInflNodesRemove);

    //******************************************************************************************************************

    cout << "\n ******* Running the subModular algo GIVEN THE SEED SET NODES approach ******** \n" << endl;

    set<int> subModGivenSeedNodesToRemove;
    set<int> modImpactGivenSeedNodesToRemove;
    vector<int> subModGivenSeedNodesToRemoveUnsorted;
    vector<int> modImpactGivenSeedNodesToRemoveUnsorted;

    runSubModGivenSeed(maxInfluenceSeed, envelopedNodes, subModGivenSeedNodesToRemove, modImpactGivenSeedNodesToRemove,
                       subModGivenSeedNodesToRemoveUnsorted, modImpactGivenSeedNodesToRemoveUnsorted);

    //******************************************************************************************************************

    resultLogFile << "\n\n******* Node removed in all approaches ********\n" << flush;

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

    unique_ptr<Graph> subModtopKInflGraph = make_unique<Graph>();
    subModtopKInflGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModtopKInflGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> modImpactGivenSeedGraph = make_unique<Graph>();
    modImpactGivenSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modImpactGivenSeedGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> subModGivenSeedGraph = make_unique<Graph>();
    subModGivenSeedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subModGivenSeedGraph->setPropogationProbability(probability);
    }

    string convertedFile = "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" + graphFileName;

    newDiffusion(modNewGraph, tGraph, subModtopKInflGraph,
                 modImpactGivenSeedGraph, subModGivenSeedGraph,
                 modNodesToremove, tGraphNodesToremove,
                 subModTopKInflNodesRemove,
                 modImpactGivenSeedNodesToRemove, subModGivenSeedNodesToRemove,
                 activatedSet, newSeed, percentageTargetsFloat, convertedFile, maxInfluenceSeed,
                 modImpactGivenSeedNodesToRemoveUnsorted, subModGivenSeedNodesToRemoveUnsorted);

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
    string tshootingDataFile;
    resultFile = graphFileName;

    if (fullgraph) {
        resultFile += "_FullGraph_results.txt";
        resultFile =
                "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\results\\" +
                resultFile;
        storesResultFile = resultFile + "_values";
        tshootingDataFile = resultFile + "_tshootingData";
        myfile.open(resultFile, std::ios::app);
        dependValues.open(storesResultFile, std::ios::app);
        tshootingFile.open(tshootingDataFile, std::ios::app);
        myfile << "\n" << budget << " <-SeedSetSize\n" << removeNodes << " <-removeNodes\n";
        dependValues << "\n" << budget << " <-SeedSetSize\n" << removeNodes << " <-removeNodes\n";
        tshootingFile << "\n" << budget << " <-SeedSetSize\n" << removeNodes << " <-removeNodes\n";
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
