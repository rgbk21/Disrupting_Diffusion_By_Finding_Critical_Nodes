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

void newDiffusion(unique_ptr<Graph> &newModGraph, unique_ptr<Graph> &subNewGraph, unique_ptr<Graph> &modImpactGraph,
                  unique_ptr<Graph> &tGraph, unique_ptr<Graph> &subModtopKInflGraph,
                  unique_ptr<Graph> &subModImpactTopCritGraph,
                  unique_ptr<Graph> &subModTopCritGraphNew,
                  set<int> modNodes, set<int> &subModNodes, set<int> *removalModImpact, set<int> tGraphNodes,
                  set<int> &subModTopKInflNodesRemove,
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
        myfile << "\n\nmodTopK SubModTopK Old_SubMod New_SubMod Old_ModImpact New_ModImpact Transposed \n";
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


            cout << "\n********** k = " << k << " **********" << endl;

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


void printStuff(unique_ptr<Graph> &influencedGraph, int rrSetId, int critNode, vector<int> &dependencyValues){

    cout << "Current critNode: " << critNode << endl;
    cout << "RRSetID:" << rrSetId << endl;

    cout << "Nodes DependencyValue " << endl;
    for(int k = 0; k < (influencedGraph->rrSets[rrSetId]).size(); k++){
        cout << influencedGraph->rrSets[rrSetId][k] << " " << dependencyValues[(influencedGraph->rrSets[rrSetId])[k]] << endl;
    }
    cout << "Graph: " << endl;
    for(int k = 0; k < (influencedGraph->miniRRGraphsVector[rrSetId])->size(); k++){
        cout << k << " -> ";
        for(int l = 0; l < (*influencedGraph->miniRRGraphsVector[rrSetId])[k].size(); l++){
            cout << (*influencedGraph->miniRRGraphsVector[rrSetId])[k][l] << " ";
        }
        cout << endl;
    }
    cout << "reachableFromSource: ";
    for(int k = 0; k < (*influencedGraph->reachableFromSourceVector[rrSetId]).size(); k++){
        cout << (*influencedGraph->reachableFromSourceVector[rrSetId])[k] << " ";
    }
    cout << endl;

    cout << "dependentOnCritNode: ";
    for(int k = 0; k < (*influencedGraph->dependentOnCritNodesVector[rrSetId]).size(); k++){
        cout << (*influencedGraph->dependentOnCritNodesVector[rrSetId])[k] << " ";
    }
    cout << endl;

    cout << "DependencyMatrix: " << endl;
    for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId]).size(); k++){
        for(int l = 0; l < (*influencedGraph->dependancyVector[rrSetId])[k].size(); l++){
            cout << (*influencedGraph->dependancyVector[rrSetId])[k][l] << " ";
        }
        cout << endl;
    }
}

void printStuffToFile(unique_ptr<Graph> &influencedGraph, int rrSetId, int critNode, vector<int> &dependencyValues){

    tshootingFile << "Current critNode: " << critNode << endl;
    tshootingFile << "RRSetID:" << rrSetId << endl;

    tshootingFile << "Nodes DependencyValue " << endl;
    for(int k = 0; k < (influencedGraph->rrSets[rrSetId]).size(); k++){
        tshootingFile << influencedGraph->rrSets[rrSetId][k] << " " << dependencyValues[(influencedGraph->rrSets[rrSetId])[k]] << endl;
    }
    tshootingFile << "Graph: " << endl;
    for(int k = 0; k < (influencedGraph->miniRRGraphsVector[rrSetId])->size(); k++){
        tshootingFile << k << " -> ";
        for(int l = 0; l < (*influencedGraph->miniRRGraphsVector[rrSetId])[k].size(); l++){
            tshootingFile << (*influencedGraph->miniRRGraphsVector[rrSetId])[k][l] << " ";
        }
        tshootingFile << endl;
    }
    tshootingFile << "reachableFromSource: ";
    for(int k = 0; k < (*influencedGraph->reachableFromSourceVector[rrSetId]).size(); k++){
        tshootingFile << (*influencedGraph->reachableFromSourceVector[rrSetId])[k] << " ";
    }
    tshootingFile << endl;

    tshootingFile << "dependentOnCritNode: ";
    for(int k = 0; k < (*influencedGraph->dependentOnCritNodesVector[rrSetId]).size(); k++){
        tshootingFile << (*influencedGraph->dependentOnCritNodesVector[rrSetId])[k] << " ";
    }
    tshootingFile << endl;

    tshootingFile << "DependencyMatrix: " << endl;
    for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId]).size(); k++){
        for(int l = 0; l < (*influencedGraph->dependancyVector[rrSetId])[k].size(); l++){
            tshootingFile << (*influencedGraph->dependancyVector[rrSetId])[k][l] << " ";
        }
        tshootingFile << endl;
    }
}

void printStuffReduced(unique_ptr<Graph> &influencedGraph, int rrSetId, vector<vector<int>> &originalMiniRRGraph,
                       vector<bool> &copyOfDependencyRow) {

    cout << "RRSetID:" << rrSetId << endl;
    cout << "Nodes in this rrSet:" ;
    for(int i = 0; i < influencedGraph->rrSets[rrSetId].size(); i++){
        cout << influencedGraph->rrSets[rrSetId][i] << " " ;
    }
    cout << endl;

    cout << "Original Graph: " << endl;
    for(int k = 0; k < originalMiniRRGraph.size(); k++){
        cout << k << " -> ";
        for(int l = 0; l < originalMiniRRGraph[k].size(); l++){
            cout << originalMiniRRGraph[k][l] << " ";
        }
        cout << endl;
    }
    cout << "Modified Graph: " << endl;
    for(int k = 0; k < (influencedGraph->miniRRGraphsVector[rrSetId])->size(); k++){
        cout << k << " -> ";
        for(int l = 0; l < (*influencedGraph->miniRRGraphsVector[rrSetId])[k].size(); l++){
            cout << (*influencedGraph->miniRRGraphsVector[rrSetId])[k][l] << " ";
        }
        cout << endl;
    }
    cout << "reachableFromSource: ";
    for(int k = 0; k < (*influencedGraph->reachableFromSourceVector[rrSetId]).size(); k++){
        cout << (*influencedGraph->reachableFromSourceVector[rrSetId])[k] << " ";
    }
    cout << endl;

    cout << "dependentOnCritNode: ";
    for(int k = 0; k < (*influencedGraph->dependentOnCritNodesVector[rrSetId]).size(); k++){
        cout << (*influencedGraph->dependentOnCritNodesVector[rrSetId])[k] << " ";
    }
    cout << endl;

    cout << "Dependency Row: " << endl;
    for(int k = 0; k < copyOfDependencyRow.size(); k++){
        cout << copyOfDependencyRow[k] << " ";
    }
    cout << endl;
    cout << "Modified DependencyMatrix: " << endl;
    for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId]).size(); k++){
        for(int l = 0; l < (*influencedGraph->dependancyVector[rrSetId])[k].size(); l++){
            cout << (*influencedGraph->dependancyVector[rrSetId])[k][l] << " ";
        }
        cout << endl;
    }
}


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

//This method checks if every vertex that has been removed because it was the critNode infact does have all the values in its dependencyMatrix
//to be FALSE.
void
inSanityCheck_2(unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues, vector<int> &nodesToRemoveUnsorted,
                vector<vector<vector<bool>>> &copyOfDependencyVector, vector<vector<vector<int>>> &copyOfMiniRRGraphsVector) {

    for(int rrSetId = 0; rrSetId < influencedGraph->rrSets.size(); rrSetId++){
        for(int i = 0; i < nodesToRemoveUnsorted.size(); i++) {
            int critNode = nodesToRemoveUnsorted[i];
            unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(critNode);      //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
            if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
                    assert(("Removed critNode but MatrixRow containing critNode is still TRUE", !(*influencedGraph->dependancyVector[rrSetId])[got->second][j]));
                    if (copyOfDependencyVector[rrSetId][got->second][j]){
                        for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                            assert(("Vertex that depended on critNode for its reachability is still TRUE", !(*influencedGraph->dependancyVector[rrSetId])[j][k]));
                        }
                    }
                }
            }
        }
    }

    /*
    for(int rrSetId = 0; rrSetId < influencedGraph->rrSets.size(); rrSetId++){
        vector<bool> isCritNode = vector<bool>(influencedGraph->rrSets[rrSetId].size(), false);
        for(int i = 0; i < nodesToRemoveUnsorted.size(); i++) {
            int critNode = nodesToRemoveUnsorted[i];
            unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(critNode);      //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
            if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {
                copyOfMiniRRGraphsVector[rrSetId][got->second].clear();
                isCritNode[got->second] = true;
            }
        }
        for(int i = 0; i < copyOfMiniRRGraphsVector[rrSetId].size(); i++){
            vector<vector<int>> myMiniRRGraph = copyOfMiniRRGraphsVector[rrSetId];
            myMiniRRGraph[i].clear();
            vector<bool> dependencyRow = vector<bool>(copyOfMiniRRGraphsVector[rrSetId].size());
            //Initialization
            for(int j = 0; j < dependencyRow.size(); j++){
                if(isCritNode[j]){
                    dependencyRow[j] = false;
                }else{
                    dependencyRow[j] = true;
                }
            }

        }
    }
    */
    //This check validates that every vertex which is reachableFromSource does in fact have its dependencyValue equal to the sum of
    //all its rows of the dependencyMatrices.
    vector<int> testDValues = vector<int>(influencedGraph->n, 0);
    for(int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++){
        for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId]).size(); i++){
            if((*influencedGraph->reachableFromSourceVector[rrSetId])[i]){
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[i].size(); j++){
                    if((*influencedGraph->dependancyVector[rrSetId])[i][j]){
                        testDValues[(*influencedGraph->indexToVertex[rrSetId])[i]]++;
                    }
                }
            }
        }
    }

    for(int i = 0; i < dependencyValues.size(); i++){
        assert(("Final Mismatch in dependencyValues", dependencyValues[i] == testDValues[i] ));
    }

}

//This check validates that every vertex which is reachableFromSource does in fact have its dependencyValue equal to the sum of
//all its rows of the dependencyMatrices.
void checkIfDependencyValuesAreCorrect(unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues){

    vector<int> testDValues = vector<int>(influencedGraph->n, 0);
    for(int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++){
        for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId]).size(); i++){
            if((*influencedGraph->reachableFromSourceVector[rrSetId])[i]){
                for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[i].size(); j++){
                    if((*influencedGraph->dependancyVector[rrSetId])[i][j]){
                        testDValues[(*influencedGraph->indexToVertex[rrSetId])[i]]++;
                    }
                }
            }
        }
    }

    for(int i = 0; i < dependencyValues.size(); i++){
        assert(("Mismatch in dependencyValues", dependencyValues[i] == testDValues[i]));
    }
}

//originalMiniRRGraph is the miniRRGraph with no edges deleted. It is the miniRRGrpah that was generated as is by the randomRRSetsGeneration() method.
//copyOfDependencyMatrix is the original matrix that was generated by the randomRRSetsGeneration() method.
//myDependencyMatrix is the matrix that was generated after removing the critNode from the miniRRGraph. This is the matrix that we have to check.
//THe idea is that from the original miniRRGraph, we delete all the critNdoes that have been removed so far along with
//all the nodes whose reachability depended on the critNodes. In this new graph, we then do a test of reachability for each node.
//For each vertex, we then compare the values we obtain by the above method, and the values we obtained by the method we wrote.
void assertDependencyMatrixIsCorrect(unique_ptr<Graph> &influencedGraph, vector<vector<bool>> &copyOfDependencyMatrix,
                                     vector<vector<int>> &originalMiniRRGraph,
                                     const unique_ptr<vector<vector<bool>>> &myDependencyMatrix, int rrSetId, int critNode) {

    /*
    * Consider the following graph and Matrix:
    *  0 -> 1 -> 2 -> 3
    * Dependence of reachability of 2 starting from 0 given that 1 has been removed is:
    *
    *   0  1 (2)  3
    * 0 1  1  1  1
    * 1 0  1  1  1
    * 2 0  0  1  1
    * 3 0  0  0  1
    *
    * */


    vector<vector<int>> copyOfOriginalMiniRRGraph = originalMiniRRGraph;
    vector<bool> dependenceOfReachability = vector<bool>(copyOfOriginalMiniRRGraph.size(), true);
    vector<bool> isCriticalNode = vector<bool>(copyOfOriginalMiniRRGraph.size(), false);

//    cout << "----- Before deleting any edges----- " << endl;
//    printStuffReduced(influencedGraph, rrSetId, originalMiniRRGraph, dependenceOfReachability);

    //Remove all outgoing edges from the critNodes and the nodes whose reachability depends on the critNodes
    for(int i = 0; i < testCritNodesRemovedSoFar.size(); i++){
        int critNode = testCritNodesRemovedSoFar[i];
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(critNode);      //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {
            for(int j = 0; j < copyOfDependencyMatrix[got->second].size(); j++){
                if(copyOfDependencyMatrix[got->second][j]){
                    copyOfOriginalMiniRRGraph[j].clear();
                    isCriticalNode[got->second] = true;
                }
            }
        }
    }

    //Initialise the dependenceOfReachability values.
    //Any node that is not reachable from the source, should always have FALSE in its column.
    vector<bool> visitedBFS_init = vector<bool>(copyOfOriginalMiniRRGraph.size(), false);    //Mark all the vertices as not visited
    dependenceOfReachability = vector<bool>(copyOfOriginalMiniRRGraph.size(), false);   //Mark all the vertices as not reachable from source
    deque<int> queue_init;                                                                   //Create a queue for BFS
    visitedBFS_init[0] = true;                                                               //Mark the current node as visited
    queue_init.push_back(0);                                                                 //And add it to the queue
    if(!isCriticalNode[0]) dependenceOfReachability[0] = true;

    while (!queue_init.empty()) {
        int u = queue_init.front();
        queue_init.pop_front();
        for (int i = 0; i < copyOfOriginalMiniRRGraph[u].size(); i++) {
            int v = copyOfOriginalMiniRRGraph[u][i];
            if (!visitedBFS_init[v]) {
                visitedBFS_init[v] = true;
                queue_init.push_back(v);
                if(!isCriticalNode[v]) dependenceOfReachability[v] = true;
            }
        }
    }

    vector<vector<int>> copyOfGraphToDeleteEdgesIn;
    vector<bool> copyOfDependenceOfReachability;
    for(int i = 0; i < copyOfOriginalMiniRRGraph.size(); i++) {

        copyOfGraphToDeleteEdgesIn = copyOfOriginalMiniRRGraph;
        copyOfDependenceOfReachability = dependenceOfReachability;

//        cout << "Pre Values:" << endl;
//        cout << "Crit Nodes removed so far:" ;
//        for(int j = 0; j < testCritNodesRemovedSoFar.size(); j++){
//            cout << testCritNodesRemovedSoFar[j] << " ";
//        }
//        cout << endl;
//        cout << "Index Being Removed:" << i << endl;
//        printStuffReduced(influencedGraph, rrSetId, originalMiniRRGraph, copyOfDependenceOfReachability);

        int nodeBeingRemoved = i;
        copyOfGraphToDeleteEdgesIn[i].clear();
        vector<bool> visitedBFS = vector<bool>(copyOfGraphToDeleteEdgesIn.size(), false);               //Mark all the vertices as not visited
        deque<int> queue;                                                                               //Create a queue for BFS
        visitedBFS[0] = true;                                                                           //Mark the current node as visited
        queue.push_back(0);                                                                             //And add it to the queue
        if(nodeBeingRemoved != 0){
            copyOfDependenceOfReachability[0] = false;
        }
        while (!queue.empty()) {
            int u = queue.front();
            queue.pop_front();
            for (int j = 0; j < copyOfGraphToDeleteEdgesIn[u].size(); j++) {
                int v = copyOfGraphToDeleteEdgesIn[u][j];
                if (!visitedBFS[v]) {
                    visitedBFS[v] = true;
                    queue.push_back(v);
                    if(nodeBeingRemoved != v){
                        copyOfDependenceOfReachability[v] = false;
                    }
                }
            }
        }
//        cout << "Post Values:" << endl;
//        printStuffReduced(influencedGraph, rrSetId, originalMiniRRGraph, copyOfDependenceOfReachability);
        for(int j = 0; j < (*myDependencyMatrix)[i].size(); j++){
            assert(("SubModTopCrit DependencyMatrix is incorrect", (*myDependencyMatrix)[i][j] == copyOfDependenceOfReachability[j]));
        }
    }
}

                                        /* ALL CODE ABOVE THIS LINE IS CODE USED FOR ASSERTING STUFF */


vector<bool> BFS_Check(vector<vector<int>> &myMiniRRGraph) {

    vector<bool> visitedBFS = vector<bool>(myMiniRRGraph.size(), false);                //Mark all the vertices as not visited
    vector<bool> nodesReachableFromSource = vector<bool>(myMiniRRGraph.size(), false);  //Mark all the vertices as not reachable from source
    deque<int> queue;                                                                   //Create a queue for BFS
    visitedBFS[0] = true;                                                               //Mark the current node as visited
    queue.push_back(0);                                                                 //And add it to the queue
    nodesReachableFromSource[0] = true;

    while (!queue.empty()) {
        int u = queue.front();
        queue.pop_front();
        for (int i = 0; i < myMiniRRGraph[u].size(); i++) {
            int v = myMiniRRGraph[u][i];
            if (!visitedBFS[v]) {
                visitedBFS[v] = true;
                queue.push_back(v);
                nodesReachableFromSource[v] = true;
            }
        }
    }
    return nodesReachableFromSource;
}

vector<bool> checkForNewVerticesNotReachableFromSource(unique_ptr<Graph> &influencedGraph,
                                               unique_ptr<vector<vector<int>>> &miniRRGraph,
                                               unique_ptr<vector<bool>> &dependentOnCritNode,
                                               unique_ptr<vector<bool>> &reachableFromSource,
                                               int rrSetId,
                                               int critNode, vector<int> &dependencyValues){

    vector<vector<int>> myMiniRRGraph = (*miniRRGraph);
    for(int i = 0; i < reachableFromSource->size(); i++){                                                               //for every vertex v in reachableFromSource
        if(!(*reachableFromSource)[i]){                                                                                 //if !reachableFromSource[v]
            myMiniRRGraph[i].clear();                                                                                   //remove all outgoing edges from v
        }
    }
    return BFS_Check(myMiniRRGraph);

}

void repopulateOnlyMatrixRowWithoutDependencyValueUpdate(unique_ptr<Graph> &influencedGraph,
                                                         unique_ptr<vector<vector<int>>> &miniRRGraph,
                                                         unique_ptr<vector<bool>> &dependentOnCritNode,
                                                         int rrSetId,
                                                         int critNode, int nodeBeingRemoved,
                                                         vector<int> &dependencyValues) {

    clock_t startTime = clock();
    vector<vector<int>> myGraph = *miniRRGraph;
    vector<bool> oldDependencyValues = (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved];                 //Store the previous values so that they can be compared for the dependencyValues vector to be changed
    myGraph[nodeBeingRemoved].clear();

    //Initialize
    for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved].size(); i++){
        if((*dependentOnCritNode)[i] ){
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = false;                                 //All nodes whose reachability depended on critNodes are initialised to FALSE because these ndoes will no longer be reachable from the source node
        }else{
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = true;
        }
    }

    vector<bool> visitedBFS = vector<bool>(miniRRGraph->size(), false);                                                 //Mark all the vertices as not visited
    deque<int> queue;                                                                                                   //Create a queue for BFS
    visitedBFS[0] = true;                                                                                               //Mark the starting node as visited. starting node will always be node numbered 0
    queue.push_back(0);                                                                                                 //And add it to the queue
    if(nodeBeingRemoved != 0){
        (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][0] = false;                                                                                 //since we are starting the BFS from the node 0, dependence of reachability of 0 from 0 given that the ndoeBeingRemoved is removed is "false"
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
                    (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][v] = false;                                                                     //Since v was still reachable after removing vertexRemoved.
                }
            }
        }
    }

    repopulateDependencyMatrixAfterCritNodeRemovalTime += (clock() - startTime);
}


//critNode is the node that was removed since it was chosen as the most critical vertex
//miniRRGraph is the graph that has been created from the original graph after mapping each of the vertices to index
//node belonging to the critNode along with all of its outgoing edges has already been removed at this point
//nodeBeingRemoved is the vertex in the row of critNode (which did not depend upon the critNode for reachability) that has to be removed from the minRRGraph. So, we are basically checking:
//dependence of reachability of each node in the miniRRGraph (formed after removing outgoing edges from the critNode) starting from the origin given that
//nodeBeingRemoved is removed
//both critNode and nodeBeingRemoved are not the actual vertices, but the mapped vertices in this rrSet numbered rrSetId
void repopulateMatrixRowWithDependencyValueUpdate(unique_ptr<Graph> &influencedGraph,
                                                  unique_ptr<vector<vector<int>>> &miniRRGraph,
                                                  unique_ptr<vector<bool>> &dependentOnCritNode,
                                                  int rrSetId,
                                                  int critNode, int nodeBeingRemoved, vector<int> &dependencyValues) {

    clock_t startTime = clock();
    vector<vector<int>> myGraph = *miniRRGraph;
    vector<bool> oldDependencyValues = (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved];                 //Store the previous values so that they can be compared for the dependencyValues vector to be changed
    myGraph[nodeBeingRemoved].clear();

    //Initialize
    for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved].size(); i++){
        if((*dependentOnCritNode)[i] ){
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = false;                                 //All nodes whose reachability depended on critNodes are initialised to FALSE because these ndoes will no longer be reachable from the source node
        }else{
            (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] = true;
        }
    }

    vector<bool> visitedBFS = vector<bool>(miniRRGraph->size(), false);                                                 //Mark all the vertices as not visited
    deque<int> queue;                                                                                                   //Create a queue for BFS
    visitedBFS[0] = true;                                                                                               //Mark the starting node as visited. starting node will always be node numbered 0
    queue.push_back(0);                                                                                                 //And add it to the queue
    if(nodeBeingRemoved != 0){
        (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][0] = false;                                                                                 //since we are starting the BFS from the node 0, dependence of reachability of 0 from 0 given that the ndoeBeingRemoved is removed is "false"
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
                    (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][v] = false;                                                                     //Since v was still reachable after removing vertexRemoved.
                }
            }
        }
    }

    for(int i = 0; i < (*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved].size(); i++){
        if(!oldDependencyValues[i] && ((*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i]) ){           //If in the dependencyMatrix of the row containing nodeBeingRemoved, if the earlier value for vertex w was TRUE but the new value is FALSE
            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[nodeBeingRemoved]] += 1;                        //Reduce the dependencyValue for the node nodeBeingRemoved
        }else if ( (oldDependencyValues[i]) && !(*influencedGraph->dependancyVector[rrSetId])[nodeBeingRemoved][i] ){   //else if
            dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[nodeBeingRemoved]] -= 1;                        //Increase the dependencyValue for the node nodeBeingRemoved
        }
    }

    repopulateDependencyMatrixAfterCritNodeRemovalTime += (clock() - startTime);
}

void removeCritNodeWithMatrixUpdate(int critNode, unique_ptr<Graph> &influencedGraph,
                                    vector<int> &dependencyValues, vector<pair<int, int>> &ASdegree,
                                    vector<vector<vector<bool>>> &copyOfDependencyVector,
                                    vector<vector<vector<int>>> &copyOfMiniRRGraphsVector) {

    bool tshoot = false;//WARNING:controls assert statement
    bool tshoot1 = false;//Controls PAUUUUUZZZE

    cout << "Removing critNode: " << critNode << endl;
    dependValues << "Removing critNode: " << critNode << endl;
    tshootingFile << "---- Removing critNode: " << critNode << endl;
    testCritNodesRemovedSoFar.push_back(critNode);//Global variable that stores the critNodes removed so far. Used for testing.

    tshootingFile << "Number of rrSets in which critNode " << critNode << " was in:" << influencedGraph->inRRSet[critNode].size() << endl;
    tshootingFile << "dValue | totalValue " << endl;
    int dValue = 0;//Counts the actual dValue (add to final values only if reachableFromSource)
    int value = 0;  //Counts the total number of vertices whose reachability was dependent on critNode
    for(int i = 0; i < influencedGraph->inRRSet[critNode].size(); i++){
        int rrSetId = influencedGraph->inRRSet[critNode][i];
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(critNode);
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {
            for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
                if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){
                    if ((*influencedGraph->reachableFromSourceVector[rrSetId])[got->second]) dValue++;
                    value++;
                }
            }
        }
    }
    tshootingFile << dValue << " " << value << endl;
    tshootingFile << "Actual dependencyValue: " << dependencyValues[critNode] << endl;

    tshootingFile << " -------------------------- " << endl;

    for (int i = 0; i < influencedGraph->inRRSet[critNode].size(); i++) {                                               //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[critNode][i];                                                            //get the next RRSet that the node to be removed is in
        unordered_map<int, int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(critNode);          //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {                                                    //if vertex is found. got->second is the critNode being removed
            if(nodeNumBeingRemovedGlobal < 5){
                tshootingFile << "--------" << endl;
                tshootingFile << "\nPre Values in rrSet: " << rrSetId << endl;
                printStuffToFile(influencedGraph, rrSetId, critNode, dependencyValues);
            }
            if ((*influencedGraph->reachableFromSourceVector[rrSetId])[got->second]){                                   //this if condition is triggered if the critNode was reachable From Source
                tshootingFile << "rrSetId: " <<rrSetId << " - critNode reachable from Source" << endl;
                //for every vertex v in the row of M[critNode] for which M[critNode][v] == 1
                for(int v = 0; v < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); v++){             //for every vertex v in the row M[critNode]
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][v] && v != got->second){              //if M[critNode][v] == 1 and v != critNode
                        dependencyValues[critNode] -= 1;                                                                //dependencyValue[critNode] -= 1
                        if((*influencedGraph->reachableFromSourceVector[rrSetId])[v]){                                  //if (reachableFromSource[v])
                            for(int w = 0; w < (*influencedGraph->dependancyVector[rrSetId])[v].size(); w++){           //for every vertex w in the row M[v]
                                if((*influencedGraph->dependancyVector[rrSetId])[v][w]){                                //if M[v][w] == 1
                                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[v]] -= 1;               //dependencyValue[v] -= 1
                                }else{
                                    //don't do anything
                                }
                            }
                        }else{
                            //don't do anything because
                            //j is no longer reachable from the source, i.e. reachableFromSource[j] = FALSE
                            //which can mean either of the following 2 things:
                            //a) j was either a seedSetNode or a node whose reachability depended on the seed(s) and the node j got disconnected
                            //when the seedSetNodes were being removed during the computationof the modImpact nodes
                            //b) j was either a critNode or a node whose reachability depended on the critNode.
                            //reachableFromSource[j] was set ot FALSE when the outgoing edges from v were deleted. Since j has NO outgoing edges
                            //removal of critNode is not going to affect the vertices whose reachability depend on j, since j has no outgoing edges.
                        }
                        (*influencedGraph->reachableFromSourceVector[rrSetId])[v] = false;                              //reachableFromSource[v] = FALSE
                        (*influencedGraph->miniRRGraphsVector[rrSetId])[v].clear();                                     //miniRRGraph[v].clear()
                        (*influencedGraph->dependentOnCritNodesVector[rrSetId])[v] = true;                              //dependentOnCrit[v] = TRUE
                    }
                }
                //doing this because of the (... && v != got->second) condition
                dependencyValues[critNode] -= 1;                                                                        //dependencyValue[critNode] -= 1
                (*influencedGraph->reachableFromSourceVector[rrSetId])[got->second] = false;
                (*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].clear();
                (*influencedGraph->dependentOnCritNodesVector[rrSetId])[got->second] = true;

                //for every vertex v in the row of M[critNode] for which M[critNode][v] == 0
                for(int v = 0; v < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); v++){
                    if(!(*influencedGraph->dependancyVector[rrSetId])[got->second][v]){
                        if((*influencedGraph->reachableFromSourceVector[rrSetId])[v]){                                  //if reachableFromSource[v], we have to update the dependencyValue for v as well as the row of M[v]
                            repopulateMatrixRowWithDependencyValueUpdate(influencedGraph,
                                                                         influencedGraph->miniRRGraphsVector[rrSetId],
                                                                         influencedGraph->dependentOnCritNodesVector[rrSetId],
                                                                         rrSetId, got->second, v,
                                                                         dependencyValues);
                        }else if (!(*influencedGraph->reachableFromSourceVector[rrSetId])[v]){                          //else reachableFromSource[v] = FALSE, meaning  v does not make any contribution to the dependencyValue of v and we only need to update the Matrix row M[v]
                            repopulateOnlyMatrixRowWithoutDependencyValueUpdate(influencedGraph,
                                                                                influencedGraph->miniRRGraphsVector[rrSetId],
                                                                                influencedGraph->dependentOnCritNodesVector[rrSetId],
                                                                                rrSetId, got->second, v,
                                                                                dependencyValues);
                        }
                    }
                }
            }else if (!(*influencedGraph->reachableFromSourceVector[rrSetId])[got->second]){//critNode was NOT reachable From Source
                /*critNode might be not reachable from source in 2 cases:
                 * i) the reachability of critNode depended on the seedSetNode(s) that were removed earlier.
                 * As a result, removing the seedSetNodes also disconnected the critNode from the source.
                 * The critNode will still have outgoing edges in this case.
                 * Its dependencyValue will not be considered though.
                 * ii) the reachability of the critNode depended on some critNode that was deleted earlier.
                 * In this case, the critNode will have no outgoing edges.
                 * And its dependencyValues will not be considered in this case either.
                 * */
                tshootingFile << "rrSetId: " <<rrSetId << " - critNode NOT reachable from Source" << endl;
                //for every vertex v in the row of M[critNode] for which M[critNode][v] == 1
                for(int v = 0; v < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); v++) {            //for every vertex v in the row M[critNode]
                    if((*influencedGraph->dependancyVector[rrSetId])[got->second][v] && v != got->second) {             //if M[critNode][v] == 1 and v != critNode
                        (*influencedGraph->miniRRGraphsVector[rrSetId])[v].clear();                                     //miniRRGraph[v].clear()
                        (*influencedGraph->dependentOnCritNodesVector[rrSetId])[v] = true;                              //dependentOnCrit[v] = TRUE
                        (*influencedGraph->reachableFromSourceVector[rrSetId])[v] = false;                              //reachableFromSource[v] = FALSE
                    }
                }
                (*influencedGraph->miniRRGraphsVector[rrSetId])[got->second].clear();                                   //miniRRGraph[v].clear()
                (*influencedGraph->dependentOnCritNodesVector[rrSetId])[got->second] = true;                            //dependentOnCrit[v] = TRUE

                //for every vertex v in the row of M[critNode] for which M[critNode][v] == 0
                for(int v = 0; v < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); v++) {            //for every vertex v in the row M[critNode]
                    if(!(*influencedGraph->dependancyVector[rrSetId])[got->second][v]) {                                //if M[critNode][v] == 0
                        if((*influencedGraph->reachableFromSourceVector[rrSetId])[v]){                                  //if reachableFromSource[v], we have to update the dependencyValue for v as well as the row of M[v]
                            repopulateMatrixRowWithDependencyValueUpdate(influencedGraph,
                                                                         influencedGraph->miniRRGraphsVector[rrSetId],
                                                                         influencedGraph->dependentOnCritNodesVector[rrSetId],
                                                                         rrSetId, got->second, v,
                                                                         dependencyValues);
                        }else if (!(*influencedGraph->reachableFromSourceVector[rrSetId])[v]){                          //else reachableFromSource[v] = FALSE, meaning  v does not make any contribution to the dependencyValue of v and we only need to update the Matrix row M[v]
                            repopulateOnlyMatrixRowWithoutDependencyValueUpdate(influencedGraph,
                                                                                influencedGraph->miniRRGraphsVector[rrSetId],
                                                                                influencedGraph->dependentOnCritNodesVector[rrSetId],
                                                                                rrSetId, got->second, v,
                                                                                dependencyValues);
                        }
                    }
                }
            }
        } else {
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }

        //Updating the dependencyMatrix for the vertices that were deleted since they either they were the critNode or
        //vertices whose reachability depended on the critNode
        for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
            if((*influencedGraph->dependancyVector[rrSetId])[got->second][j] && j != got->second){
                for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                    if((*influencedGraph->dependancyVector[rrSetId])[j][k]){
                        (*influencedGraph->dependancyVector[rrSetId])[j][k] = false;
                    }
                }
            }
        }
        for(int j = 0; j < (*influencedGraph->dependancyVector[rrSetId])[got->second].size(); j++){
            if((*influencedGraph->dependancyVector[rrSetId])[got->second][j]){
                (*influencedGraph->dependancyVector[rrSetId])[got->second][j] = false;
            }
        }

        /*
        We have removed seedSetNodes and critNode at this point. There might have been a vertex v that had an edge from a seedSetNode and critNode.
        Therefore, the reachability of vertex v would not have been dependent on critNode.
        Hence, deleting critNode would not have changed reachableFromSource[v] to FALSE.
        However, v now only has an edge from seedSetNode. Hence it is no longer reachable from the source. So we have an error, and we need to correct it.
        This is what checkForNewVerticesNotReachableFromSource() method does.
         */

        vector<bool> newRFS = checkForNewVerticesNotReachableFromSource(influencedGraph,
                                                                       influencedGraph->miniRRGraphsVector[rrSetId],
                                                                       influencedGraph->dependentOnCritNodesVector[rrSetId],
                                                                       influencedGraph->reachableFromSourceVector[rrSetId],
                                                                       rrSetId, got->second,
                                                                       dependencyValues);
        for(int j = 0; j < newRFS.size(); j++){
            if((*influencedGraph->reachableFromSourceVector[rrSetId])[j] && !newRFS[j]){
                for(int k = 0; k < (*influencedGraph->dependancyVector[rrSetId])[j].size(); k++){
                    if((*influencedGraph->dependancyVector[rrSetId])[j][k]){
                        cout << "Triggerred" << endl;
                        dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[j]] -= 1;                           //dependencyValue[v] -= 1
                    }
                }
                (*influencedGraph->reachableFromSourceVector[rrSetId])[j] = false;
            } /* else if (!(*influencedGraph->reachableFromSourceVector[rrSetId])[j] && newRFS[j]){
                assert(("Didn't see that coming, did you?" , false));
            }*/
        }

        assertDependencyMatrixIsCorrect(influencedGraph, copyOfDependencyVector[rrSetId],
                                        copyOfMiniRRGraphsVector[rrSetId], influencedGraph->dependancyVector[rrSetId],
                                        rrSetId, critNode);

        if(nodeNumBeingRemovedGlobal < 5){
            tshootingFile << "\nPost Values in rrSet: " << rrSetId << endl;
            printStuffToFile(influencedGraph, rrSetId, critNode, dependencyValues);
            tshootingFile << "--------" << endl;
        }

    }
    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed

    inSanityCheck(influencedGraph, dependencyValues);
    checkIfDependencyValuesAreCorrect(influencedGraph, dependencyValues);
    assert(("Woohoo!!!", dependencyValues[critNode] == 0));
    nodeNumBeingRemovedGlobal++;
}

void computeSubModNodesUsingTopCrit(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues,
                                    vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet,
                                    const set<int> &envelopedNodes, set<int> &subModNodesToremove,
                                    vector<int> &nodesToRemoveUnsorted, set<int> &alreadyinSeed,
                                    vector<vector<vector<bool>>> &copyOfDependencyVector,
                                    vector<vector<vector<int>>> &copyOfMiniRRGraphsVector) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            subModNodesToremove.insert(node);
            nodesToRemoveUnsorted.push_back(node);
            if (i <= removeNodes) {//WARNING --- Dont call if final vertex to be removed has been found
//                removeCritNodeWithMatrixUpdate(node, influencedGraph, dependencyValues, ASdegree);//Actual method
                removeCritNodeWithMatrixUpdate(node, influencedGraph, dependencyValues, ASdegree, copyOfDependencyVector, copyOfMiniRRGraphsVector);//Test MEthod
            }
            index = 0;
        } else {
            alreadyinSeed.insert(node);
            index++;
        }
    }

    inSanityCheck_2(influencedGraph, dependencyValues, nodesToRemoveUnsorted, copyOfDependencyVector, copyOfMiniRRGraphsVector);

    if (tshoot2 && useEnvelop) {
        cout << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
             << endl;
        myfile
                << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet"
                << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }
}

void computeDependencyValuesForModImpact(vector<int> &dependencyValues, unique_ptr<Graph> &influencedGraph,
                                         vector<pair<int, int>> &ASdegree){

    bool tshoot = true;//prints values to file
    cout << "Calculating Dependency Values For ModImpact" << endl;

    for (int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++) {                              //for each RRSet in dependancyVector
        for (int rowIdx = 0; rowIdx < influencedGraph->dependancyVector[rrSetId]->size(); rowIdx++) {                   //for each row in the dependancyMatrix
            if((*influencedGraph->reachableFromSourceVector[rrSetId])[rowIdx]){                                         //if the rowIdx (vertex) was reachable from the source after removing all of the seedSetNodes from the miniRRGraphVector[rrSetId]
                int vertex = (*influencedGraph->indexToVertex[rrSetId])[rowIdx];                                        //find the vertex that was mapped to that index
                for (int colIdx = 0; colIdx < (*influencedGraph->dependancyVector[rrSetId])[rowIdx].size(); colIdx++) { //for each col in that row
                    if ((*influencedGraph->dependancyVector[rrSetId])[rowIdx][colIdx]) {
                        dependencyValues[vertex] += 1;                                                                  //Add the value to the existing dependencyValues of that vertex
                    }
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

    ASdegree = vector<pair<int, int>>();
    for (int i = 0; i < dependencyValues.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = dependencyValues[i];
        ASdegree.push_back(node);
    }

    std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);
    assert(ASdegree.at(0).second >= ASdegree.at(1).second);
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

//    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);//Used by the old version of subModTopCritNodesRemove_Old()
    computeDependencyValuesForModImpact(dependencyValues, influencedGraph, ASdegree);

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


void checkIfModImpactValuesWereCorrect(unique_ptr<Graph> &influencedGraph, const set<int> &maxSeedSet, vector<int> &dependencyValues, vector<int> &testDependencyValues){

    for (int seedSetNode : maxSeedSet) {
        assert(("Incorrectly calculated DependencyValues", dependencyValues[seedSetNode] == 0));
    }
    for(int i = 0; i < dependencyValues.size(); i++){
        assert(("-ve dependencyValues!!!", dependencyValues[i] >= 0));
        assert(("Not possible!!!", dependencyValues[i] <= testDependencyValues[i]));
    }

}

//This is only a test method. The idea was to check how many of the rrSets ACTUALLY contain the seedSetNode.
//For each rrSet, it prints out the number of seedSetNodes that were present in that set along with which seedSetNodes were present
void countingSeedSetNodesInEachRRGraph(unique_ptr<Graph> &influencedGraph, const set<int> &maxSeedSet){

    vector<vector<int>> seedNodesInEachRRSet = vector<vector<int>>(influencedGraph->miniRRGraphsVector.size(), vector<int>());
    vector<int> numberOfSeedSetNodes = vector<int>(influencedGraph->miniRRGraphsVector.size(), 0);
    for (int rrSetId = 0; rrSetId < influencedGraph->miniRRGraphsVector.size(); rrSetId++){
        unordered_map<int, int>::const_iterator got;   //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        vector<int> seedNodes = vector<int>();
        for (int seedSetNode : maxSeedSet) {
            got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);
            if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {
                numberOfSeedSetNodes[rrSetId]++;
                seedNodesInEachRRSet[rrSetId].push_back(seedSetNode);
            }
        }
    }

    dependValues << "Counting the number of seedSet nodes in each RRGraph: " << endl;
    dependValues << "22 1 means - rrSetID 22 had 1 seedSetVertex  " << endl;
    for(int i = 0; i < numberOfSeedSetNodes.size(); i++){
        if(numberOfSeedSetNodes[i] > 0){
            dependValues << i << " " << numberOfSeedSetNodes[i] << " : ";
            for(int j = 0; j < seedNodesInEachRRSet[i].size(); j++){
                dependValues << seedNodesInEachRRSet[i][j] << " ";
            }
            dependValues << endl;
        }
    }

}

//nodesReachableFromSource <1,1,0,0,1> : This means after removing all of the seedSetNodes from myMiniRRGraph
//vertices 2 and 3 were no longer reachable from the source node 0.
void BFS(unique_ptr<Graph> &influencedGraph, vector<vector<int>> &myMiniRRGraph, int rrSetId,
         unique_ptr<vector<bool>> &nodesReachableFromSource, vector<bool> isSeed) {

    vector<bool> visitedBFS = vector<bool>(myMiniRRGraph.size(), false);            //Mark all the vertices as not visited
    deque<int> queue;                                                               //Create a queue for BFS
    visitedBFS[0] = true;                                                           //Mark the current node as visited
    queue.push_back(0);                                                             //And add it to the queue
    (*nodesReachableFromSource)[0] = true;

    while (!queue.empty()) {
        int u = queue.front();
        queue.pop_front();
        for (int i = 0; i < myMiniRRGraph[u].size(); i++) {
            int v = myMiniRRGraph[u][i];
            if (!visitedBFS[v]) {
                visitedBFS[v] = true;
                queue.push_back(v);
                if(!isSeed[v]){
                    (*nodesReachableFromSource)[v] = true;
                }
            }
        }
    }
}

//IMP: We are setting the seedSetNodes to FALSE as well.
//So, the seedSetNodes, along with all of the vertices v, whose reachability depends on ALL of these seedSetNodes combined
//will have the reachableFromSource[rrSetId][v] set to FALSE
void removeSeedSetNodesFromAllRRGraphs(unique_ptr<Graph> &influencedGraph, const set<int> &maxSeedSet){

    for(int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++){
        unordered_map<int, int>::const_iterator got;   //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        vector<vector<int>> myMiniRRGraph = (*influencedGraph->miniRRGraphsVector[rrSetId]);
        vector<bool> isSeed = vector<bool>(myMiniRRGraph.size(), false);//isSeed <1,1,0,0,1> : This means in this particular miniRRGraph, vertices 0,1,4 have been selected as the overall seed
        bool rrSetContainsSeed = false;
        for (int seedSetNode : maxSeedSet) {
            got = influencedGraph->vertexToIndex[rrSetId]->find(seedSetNode);
            if (got != influencedGraph->vertexToIndex[rrSetId]->end()) {
                myMiniRRGraph[got->second].clear();
                isSeed[got->second] = true;
                rrSetContainsSeed = true;
            }
        }
        if(rrSetContainsSeed){
            //Initialize the reachableFromSource[rrSetId] datastructure
            for(int i = 0; i < (*influencedGraph->reachableFromSourceVector[rrSetId]).size(); i++){
                (*influencedGraph->reachableFromSourceVector[rrSetId])[i] = false;
            }
            if(!myMiniRRGraph[0].empty()){
                BFS(influencedGraph, myMiniRRGraph, rrSetId, influencedGraph->reachableFromSourceVector[rrSetId], isSeed);
            }
        }
    }
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
        //The dependencyValue of each vertex must ALTLEAST be the number of rrSets that it occurs in.
        assert(("Ooopsies!!" , dependencyValues[i] >= influencedGraph->inRRSet[i].size()));
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

//    cout << "Printing All RRSets" << endl;
//    for(int i = 0; i < subModTopCritGraph->rrSets.size(); i++){
//        for(int j = 0; j < subModTopCritGraph->rrSets[i].size(); j++){
//            cout << subModTopCritGraph->rrSets[i][j] << " ";
//        }
//        cout << endl;
//    }

    //This is for testing to see what are the dependencyValues that we are starting with
    cout << "\nPopulating dependency values BEFORE removing the seedSet Nodes:" << endl;
    dependValues << "\nsubModTopCritNodesRemove()-Populating dependency values BEFORE removing the seedSet Nodes:"
                 << endl;

    computeDependencyValuesWithoutASdegree(dependencyValues, subModTopCritGraph);
    testDependencyValues = dependencyValues;

    clock_t timeToComputeInitialDependencyValues = clock();
    clock_t timeToRemoveSeedSetNodesStart = clock();

    countingSeedSetNodesInEachRRGraph(subModTopCritGraph, maxSeedSet);
    removeSeedSetNodesFromAllRRGraphs(subModTopCritGraph, maxSeedSet);

    clock_t timeToRemoveSeedSetNodesEnd = clock();
    clock_t modImpactTimeStart = clock();

    cout << "\nComputing nodes to remove by the NEW_Mod Impact method" << endl;
    dependValues << "\nsubModTopCritNodesRemove()-Populating dependency values AFTER removing the seedSet Nodes:" << endl;

    //Newer method where we calculate the
    dependencyValues = vector<int>(subModTopCritGraph->n, 0);
    computeModImpactTopCritNodes(subModTopCritGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                                 envelopedNodes,
                                 subModImpactNodesToRemove, subModImpactTopCritNodesToRemoveUnsorted);
    clock_t ModImpactEndTime = clock();
    checkIfModImpactValuesWereCorrect(subModTopCritGraph, maxSeedSet, dependencyValues, testDependencyValues);

    double totalModImpactTime = double(
            (timeForGeneratingRRSets - subModReverseStartTime) +
            (timeToRemoveSeedSetNodesEnd - timeToRemoveSeedSetNodesStart) +
            (ModImpactEndTime - modImpactTimeStart))
                                / (CLOCKS_PER_SEC * 60);

    cout << "NEW_Mod Impact impact algorithm time in minutes " << totalModImpactTime << endl;
    myfile << totalModImpactTime << " <-NEW_ModImpactTime\n";

    cout << "Breakup of time taken: " << endl;
    cout << "Time for generating RRSets: " << double (timeForGeneratingRRSets - subModReverseStartTime) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for removing SeedSet Nodes: " << double (timeToRemoveSeedSetNodesEnd - timeToRemoveSeedSetNodesStart) / (CLOCKS_PER_SEC * 60) << endl;
    cout << "Time for computing the final dependencyValues only: " << double(ModImpactEndTime - modImpactTimeStart) / (CLOCKS_PER_SEC * 60) << endl;
    cout << endl;

    cout << "******* Completed NEW_Mod Impact approach ********" << endl;
    cout << endl;
    cout << endl;

    dependValues << "\n\n******* Completed NEW_Mod Impact approach ********" << endl;

    /***************************************************************************************************************************************/

    cout << "******* Running NEW_SubMod approach ********" << endl;
    dependValues << "******* Running NEW_SubMod approach ********" << endl;

    alreadyinSeed = set<int>();
    clock_t sumModCritTimeStart = clock();

    vector<vector<vector<bool>>> copyOfDependencyVector = vector<vector<vector<bool>>>(subModTopCritGraph->dependancyVector.size());
    for(int rrSetId = 0; rrSetId < copyOfDependencyVector.size(); rrSetId++){
        copyOfDependencyVector[rrSetId] = vector<vector<bool>>((*subModTopCritGraph->dependancyVector[rrSetId]).size());
        for(int j = 0; j < (*subModTopCritGraph->dependancyVector[rrSetId]).size(); j++){
            copyOfDependencyVector[rrSetId][j] = (*subModTopCritGraph->dependancyVector[rrSetId])[j];
        }
    }

    vector<vector<vector<int>>> copyOfMiniRRGraphVector = vector<vector<vector<int>>>(subModTopCritGraph->miniRRGraphsVector.size());
    for(int rrSetId = 0; rrSetId < copyOfMiniRRGraphVector.size(); rrSetId++){
        copyOfMiniRRGraphVector[rrSetId] = vector<vector<int>>((*subModTopCritGraph->miniRRGraphsVector[rrSetId]).size());
        for(int j = 0; j < (*subModTopCritGraph->miniRRGraphsVector[rrSetId]).size(); j++){
            copyOfMiniRRGraphVector[rrSetId][j] = (*subModTopCritGraph->miniRRGraphsVector[rrSetId])[j];
        }
    }
    /*

    computeSubModNodesUsingTopCrit_old(subModTopCritGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                               envelopedNodes,
                               subModTopCritNodesToRemove, subModTopCritNodesToRemoveUnsorted, alreadyinSeed, copyOfDependencyVector);
    */
    computeSubModNodesUsingTopCrit(subModTopCritGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet,
                                   envelopedNodes,
                                   subModTopCritNodesToRemove, subModTopCritNodesToRemoveUnsorted, alreadyinSeed,
                                   copyOfDependencyVector, copyOfMiniRRGraphVector);


    assert(("Mismatch - subModNodesToremove and removeNodes", subModTopCritNodesToRemove.size() == removalNum));
    clock_t sumModCritTimeEnd = clock();

    vector<vector<int>>().swap(subModTopCritGraph->rrSets);
    cout << endl;
    cout << "Removed subModTopCrit Nodes from Graph: ";
    removingNodesFromGraph(subModTopCritGraph, subModTopCritNodesToRemove);
    cout << endl;

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
    newDiffusion(modNewGraph, subNewGraph, modImpactGraph, tGraph, subModtopKInflGraph,
                 subModImpactTopCritGraph, subModTopCritGraphNew,
                 modNodesToremove, subModNodesToremove, removalModImpact, tGraphNodesToremove,
                 subModTopKInflNodesRemove, subModImpactTopCritNodesToRemove, subModTopCritNodesToRemove,
                 activatedSet, newSeed, percentageTargetsFloat, convertedFile, maxInfluenceSeed,
                 subModImpactNodesToRemoveUnsorted, subModNodesToRemoveUnsorted,
                 subModImpactTopCritNodesToRemoveUnsorted, subModTopCritNodesToRemoveUnsorted);

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
