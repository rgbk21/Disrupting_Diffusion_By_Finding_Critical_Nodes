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
bool useRandomSeed  = false;//Set to true (someCondition should also be set to true) if using random Seed instead of max Seed as the initial seed BEFORE finding the vertices to be removed
bool useEnvelop = false;//Set to true if someCondition is set to true. Implies you are not removing nodes from the envelopedNodes as well. SeedSet is still fixed.

//These are my global variables for testing
vector<int> modNodesToRemoveUnsorted;
vector<int> countNodesToRemoveUnsorted;
vector<int> tGraphNodesToRemoveUnsorted;
vector<int> modImpactNodesToRemoveUnsorted;
vector<int> subModNodesToRemoveUnsorted;
vector<int> nodeMappedToOutdegree;
//Global variables for testing end here

/*List of warnings:
 * 1) If you are trying to find the best seed set for each set of methods and not at the start of the experiment, remember that you have added some additional
 * methods. And you are not passing the removeNode set<> into the getSeed() method for those newly added methods. SO make sure you chagne that if you
 * are going to run those experiments.
 *
 * 2) Uncomment the countGraph and the topKInfl metods if you want to run them
 *
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

void printNodesInEnvelopeButNotInSeedSet(const set<int> &alreadyinSeed, const set<int> &maxSeedSet, const set<int> &envelopedNodes){

    for(int const currNode : alreadyinSeed){
        if(maxSeedSet.count(currNode) == 0){
            cout << currNode << " " ;
            myfile << currNode << " " ;
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
removeVertices(unique_ptr<Graph> &influencedGraph, int removeNodes, const set<int> &maxSeedSet, const set<int> &envelopedNodes, vector<int> activatedSet, string modular) {

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

    if(tshoot3){
        dependValues << "Printing modular values for all of the nodes:" << endl;
        for(int i = 0; i < influencedGraph->NodeinRRsetsWithCounts.size(); i++){
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
    if(tshoot2){
        cout << "Mod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
        myfile << "Mod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
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

set<int> tGraphRemoveVertices(unique_ptr<Graph> &transposedGraph, unique_ptr<Graph> &influencedGraph, int removeNodes, const set<int> &maxSeedSet, const set<int> &envelopedNodes,
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
        if (tGraphNodesToRemove.count(nodeid) == 0 && maxSeedSet.count(nodeid) == 0 && envelopedNodes.count(nodeid) == 0) {
            tGraphNodesToRemove.insert(nodeid);
            //tGraphNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            tGraphNodesToRemoveUnsorted.push_back(nodeid);
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }

    if(tshoot2){
        cout << "Transposed Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
        myfile << "Transposed Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
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
countNodesRemoveVertices(unique_ptr<Graph> &countingNodesGraph, int removeNodes, const set<int> &maxSeedSet, const set<int> &envelopedNodes, vector<int> activatedSet, string modular) {

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
            countNodesToRemoveUnsorted.push_back(nodeid);//countNodesToRemoveUnsorted: for printing out the nodes that are being removed in the order that they were added
            j++;
        } else {
            alreadyinSeed.insert(nodeid);
        }
        count++;
    }
    if(tshoot2){
        cout << "countNodes Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
        myfile << "countNodes Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
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
topKInflNodesRemoveVertices(unique_ptr<Graph> &topKInflNodesGraph, int removeNodes, const set<int> &maxSeedSet, const set<int> &envelopedNodes, vector<int> activatedSet, string modular) {

    bool tshoot = false;//Prints the graphTranspose after the nodes have been deleted
    bool tshoot1 = true;//Controls the assert statements
    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    //Calculating R
    double epsilon = (double) EPSILON;
    int n = (int) activatedSet.size();
    int R = (8 + 2 * epsilon) * n * (2 * log(n) + log(2)) / (epsilon * epsilon);
    cout << "R = " << R << endl;

    set<int> nodesToRemove;
    nodesToRemove = getSeed(removeNodes, topKInflNodesGraph, activatedSet, maxSeedSet, envelopedNodes, set<int>(), set<int>(),
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

void nodesToRemoveInCountGraph(unique_ptr<Graph> &countGraph, set<int> &countGraphNodes){

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
        countGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre, totalEdgesInCountGraphPre);
    }

}

void nodesToRemoveInTopKInflGraph(unique_ptr<Graph> &topKInflGraph, set<int> &topKInflGraphNodes){
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
        topKInflGraph->assertCorrectNodesAreDeleted(i, numEdgesToDelete, totalEdgesInOrigGraphPre, totalEdgesInTopKInflGraphPre);
    }
}

void inflInCountGraph(int k, unique_ptr<Graph> &countGraph, set<int> &maxSeed, vector<int> &activatedSet, vector<int> &countGraphResults){

    cout << k << "---" << "\nCountNodes Graph Results: " << endl;
    resultLogFile << "\nCountNodes Graph Results" << endl;
    int infNum = oldNewIntersection(countGraph, maxSeed, activatedSet, resultLogFile);
    vector<vector<int>>().swap(countGraph->rrSets);
    countGraphResults.push_back(infNum);
    myfile << infNum << " ";

}

void inflInTopKInflGraph(int k, unique_ptr<Graph> &topKInflGraph, set<int> &maxSeed, vector<int> &activatedSet, vector<int> &topKInflGraphResults){

    cout << k << "---" << "\nTopKInfl Graph Results: " << endl;
    resultLogFile << "\nTopKInfl Graph Results" << endl;
    int infNum = oldNewIntersection(topKInflGraph, maxSeed, activatedSet, resultLogFile);
    vector<vector<int>>().swap(topKInflGraph->rrSets);
    topKInflGraphResults.push_back(infNum);
    myfile << infNum << "\n";

}


void newDiffusion(unique_ptr<Graph> &newGraph, unique_ptr<Graph> &subNewGraph, unique_ptr<Graph> &modImpactGraph, unique_ptr<Graph> &tGraph, unique_ptr<Graph> &countGraph, unique_ptr<Graph> &topKInflGraph,
                set<int> modNodes, set<int> subModNodes, set<int> *removalModImpact, set<int> tGraphNodes, set<int> &countGraphNodes, set<int> topKInflGraphNodes,
                vector<int> activatedSet, int newSeed, float percentageTargetsFloat, string convertedFile, set<int> prevSelectSeed) {

    bool tshoot = true;

    vector<int> modResults;
    vector<int> SubmodResults;
    vector<int> modImpactResults;
    vector<int> tGraphResults;
    vector<int> countGraphResults;
    vector<int> topKInflGraphResults;

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

    cout << "\nnodes To remove in submod graph " << flush;
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

    cout << "\nnodes To remove in mod Impact graph " << flush;
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

    /*
     * Uncomment only if the countNodes method in executeTIMTIMfullGraph() method has been uncommented as well
     * Also uncomment the if(someCondition) block where you are calculating the infl in the resulting graph
     * Note that the else condition of that statement has not been written to take into account the additional 2 methods that we wrote

     nodesToRemoveInCountGraph(countGraph, countGraphNodes);
    nodesToRemoveInTopKInflGraph(topKInflGraph, topKInflGraphNodes);

     */
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
    }

    cout << endl;
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
        cout << "Settign max Seed to be the previously selected maxSeed" << endl;
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

        cout << "\n\nMaxInfl Seed Set: " << endl;
        myfile << "\n\nMaxInfl Seed Set: " << endl;
        printSet(maxInfluenceSeed);

        cout << "\nChosen MaxInfl Seed Set to perform diffusion: " << endl;
        myfile << "\nChosen MaxInfl Seed Set to perform diffusion: " << endl;
        printSet(maxSeed);

    }

    Graph *graph;
    int k = 0;
    if(someCondition){

        cout << "Using the best seed found at the start of the experiment" << endl;
        myfile << "Using the best seed found at the start of the experiment" << endl;
        /*
         * a) This condition is executed when the seed set is fixed before the start of the experiment.
         *      - either using the max seed as the seed set
         *      - or using the random seed as the seed set
         *
        */
        myfile << "\n\nMOD SUBMOD MOD-IMPACT Transposed \n";
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

            cout << "\n\nSelected new SeedSet in original graph: " << flush;
            resultLogFile << "\n\nSelected new SeedSet in original graph: " << flush;
            for (auto item:maxSeed) {
                cout << item << " ";
                resultLogFile << item << " ";
            }

            int infNum = 0;

            cout << k << "---" << "\nMod Results: " << endl;
            resultLogFile << "\nMod Results: " << endl;
            infNum = oldNewIntersection(newGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(newGraph->rrSets);
            modResults.push_back(infNum);
            myfile << infNum << " ";

            cout << k << "---" << "\nSub Mod Results: " << endl;
            resultLogFile << "\nSub Mod Results: " << endl;
            infNum = oldNewIntersection(subNewGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(subNewGraph->rrSets);
            SubmodResults.push_back(infNum);
            myfile << infNum << " ";

            cout << k << "---" << "\nMod Impact Results: " << endl;
            resultLogFile << "\nMod Impact Results: " << endl;
            infNum = oldNewIntersection(modImpactGraph, maxSeed, activatedSet, resultLogFile);
            vector<vector<int>>().swap(modImpactGraph->rrSets);
            modImpactResults.push_back(infNum);
            myfile << infNum << " ";

            cout << k << "---" << "\nTransposed Graph Results: " << endl;
            resultLogFile << "\nTransposed Graph Results" << endl;
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
    }
    else {
        cout << "\n\nUsing the best seed in EACH graph" << endl;
        myfile << "Using the best seed in EACH graph" << endl;
        /*
         * This code is executed when someCondition iset to false. So you are not fixing the seed set at the start of the experiment.
         * Instead you start off with the seed set being empty. So all nodes can be removed.
         * Now for each method, you find out the best nodes to remove. Remove those nodes.
         * Now In the resulting graph, find the best seed set. Use that to perform the influence diffusion.
         * So the seed set will be different for each of the methods.
         * */
        myfile <<"Unsorted Mod SeedSet: ";
        cout <<"Calculating Mod SeedSet: ";
        modseedSet = getSeed(budget, newGraph, activatedSet, modNodes, set<int>(), set<int>(), set<int>(), NULL);
        myfile <<"Unsorted SubMod SeedSet: ";
        cout <<"Calculating SubMod SeedSet: ";
        subModseedSet = getSeed(budget, subNewGraph, activatedSet, subModNodes, set<int>(), set<int>(), set<int>(), NULL);
        myfile <<"Unsorted ModImpact SeedSet: ";
        cout <<"Calculating ModImpact SeedSet: ";
        modImpactseedSet = getSeed(budget, modImpactGraph, activatedSet, removalModImpactNodes, set<int>(), set<int>(), set<int>(), NULL);
        myfile <<"Unsorted Transposed graph SeedSet: ";
        cout <<"Calculating Transposed graph SeedSet: ";
        tGraphSeedSet = getSeed(budget, tGraph, activatedSet, tGraphNodes, set<int>(), set<int>(), set<int>(), NULL);

        if(tshoot){
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

            cout << "\n" << k <<" - Mod Results: " << endl;
            resultLogFile << "\nMod Results: " << endl;
            infNum = oldNewIntersection(newGraph, modseedSet, activatedSet, resultLogFile);
            vector<vector<int>>().swap(newGraph->rrSets);
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
    for (int i = 0; i < k; i++) {
        subModGain += float(modResults[i] - SubmodResults[i]) / float(modResults[i]);
        ImapctGain += float(modResults[i] - modImpactResults[i]) / float(modResults[i]);
    }
    subModGain = (float) subModGain / k;
    ImapctGain = (float) ImapctGain / k;
    myfile << subModGain << " <-subModGain\n" << ImapctGain << " <-ModImpactGain\n";
}

//reComputeDependencyValues: dont have to redo all the computation from scratch
void reComputeDependencyValues(vector<int> &dependencyValues, unique_ptr<Graph> &influencedGraph, vector<pair<int, int>> &ASdegree){

    bool tshoot = true;//Prints values to file

    ASdegree = vector<pair<int, int>>();//Because we are recalculating the dependency values, we need to initialise ASdegree to empty again
    for (int i = 0; i < dependencyValues.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = dependencyValues[i];
        ASdegree.push_back(node);
        if(tshoot){
            dependValues << dependencyValues[i] << endl;
        }
    }

    dependValues << "---------------------------------------" << endl;
    std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);
    assert(ASdegree.at(0).second >= ASdegree.at(1).second);
}

void computeDependencyValues(vector<int> &dependencyValues, unique_ptr<Graph> &influencedGraph, vector<pair<int, int>> &ASdegree){

    bool tshoot = true;//prints values to file
    cout << "Calculating Dependency Values" << endl;

    for (int rrSetId = 0; rrSetId < influencedGraph->dependancyVector.size(); rrSetId++) {                              //for each RRSet in dependancyVector
        for (int rowIdx = 0; rowIdx < influencedGraph->dependancyVector[rrSetId]->size(); rowIdx++) {                   //for each row in the dependancyMatrix
            int vertex = (*influencedGraph->indexToVertex[rrSetId])[rowIdx];                                            //find the vertex that was mapped to that index
            for (int colIdx = 0; colIdx < (*influencedGraph->dependancyVector[rrSetId])[rowIdx].size(); colIdx++) {     //for each col in that row
//                dependencyValues[vertex] += influencedGraph->dependancyVector[rrSetId][rowIdx][colIdx];               //Add the value to the existing dependencyValues of that vertex
                if((*influencedGraph->dependancyVector[rrSetId])[rowIdx][colIdx]){
                    dependencyValues[vertex] += 1;
                }
                //dependencyValues[vertex] += (*influencedGraph->dependancyVector[rrSetId])[rowIdx][colIdx];            //WARNING Check if this can be faster

            }
        }
    }

    ASdegree = vector<pair<int, int>>();
    for (int i = 0; i < dependencyValues.size(); i++) {
        pair<int, int> node = pair<int, int>();
        node.first = i;
        node.second = dependencyValues[i];
        ASdegree.push_back(node);

        if(tshoot){
            dependValues << dependencyValues[i] << endl;
        }
    }
    dependValues << "------------------------------------------------------------" << endl;
    std::sort(ASdegree.begin(), ASdegree.end(), sortbysecdesc);
    assert(ASdegree.at(0).second >= ASdegree.at(1).second);
}

void
computeModImpactNodes(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues, vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet, const set<int> envelopedNodes,set<int> *removalModImpact) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    set<int> alreadyinSeed = set<int>();
    ASdegree = vector<pair<int, int>>();

    computeDependencyValues(dependencyValues, influencedGraph, ASdegree);

    cout << "ModImpact Nodes Sorted!" << endl;

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            removalModImpact->insert(node);
            modImpactNodesToRemoveUnsorted.push_back(node);
        } else {
            alreadyinSeed.insert(node);
        }
        index++;
    }

    if(tshoot2){
        cout << "ModImpact Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
        myfile << "ModImpact Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
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
void removeFromDependencyVector(int node, unique_ptr<Graph> &influencedGraph, vector<int> &dependencyValues, vector<pair<int,int>> &ASdegree){

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

    for(int i = 0; i < influencedGraph->inRRSet[node].size(); i++){                                                     //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        unordered_map<int,int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(node);               //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if(got !=  influencedGraph->vertexToIndex[rrSetId]->end()){                                                     //if vertex is found
            //WARNING: Seemingly both of these work. WHY?
//            fill(influencedGraph->dependancyVector[rrSetId][got->second].begin(), influencedGraph->dependancyVector[rrSetId][got->second].end(), 0);  //Replace all elements in the vertex row with 0;
            fill( (*influencedGraph->dependancyVector[rrSetId])[got->second].begin(),
                    (*influencedGraph->dependancyVector[rrSetId])[got->second].end(), false);
            for(int row = 0; row < influencedGraph->dependancyVector[rrSetId]->size(); row++){                          //Replace all elements in the vertex column with 0;
//                influencedGraph->dependancyVector[rrSetId][row][got->second] = 0;
//                influencedGraph->dependancyVector[rrSetId]->at(row).at(got->second)= 0;
                if((*influencedGraph->dependancyVector[rrSetId])[row][got->second]){
                    (*influencedGraph->dependancyVector[rrSetId])[row][got->second]= false;
                    dependencyValues[(*influencedGraph->indexToVertex[rrSetId])[row]] -= 1;
                }

            }
        }else{
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

    dependencyValues[node] = 0;                                                 //Set the value to be 0 manually because we are using reComputeDependencyValues() and not computeDependencyValues() now.
    reComputeDependencyValues(dependencyValues, influencedGraph, ASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed

}

void computeSubModImpactNodes(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &dependencyValues, vector<pair<int, int>> &ASdegree, const set<int> &maxSeedSet, const set<int> &envelopedNodes, set<int> &subModNodesToremove, set<int> &alreadyinSeed) {

    bool tshoot2 = true;//Prints the nodes that are in the envelopedNodes but not in the maxSeedSet

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = ASdegree.at(index).first;
        if (maxSeedSet.count(node) == 0 && envelopedNodes.count(node) == 0) {
            i++;
            subModNodesToremove.insert(node);
            subModNodesToRemoveUnsorted.push_back(node);
            if(i < removeNodes){//Dont call if final vertex to be removed has been found
                removeFromDependencyVector(node, influencedGraph, dependencyValues, ASdegree);
            }
            index = 0;
        } else {
            alreadyinSeed.insert(node);
            index++;
        }
    }

    if(tshoot2){
        cout << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
        myfile << "SubMod Method: Printing nodes chosen for removal that are in the envelopedNodes but not in the seedSet" << endl;
        printNodesInEnvelopeButNotInSeedSet(alreadyinSeed, maxSeedSet, envelopedNodes);
    }
}



//node is the vertex being deleted from all of the dependencyMatrices
void testRemoveFromDependencyVector(int node, unique_ptr<Graph> &influencedGraph, vector<int> &testDependencyValues, vector<pair<int,int>> &testASdegree){

    /*Update the dependencyVector datastructure
     *
     * In each RRSet
     *  if node occurs in that RRSet
     *      set all elements in the row index corresponding to that node to 0
     *      set all elements in the column index corresponding to that node to 0
     */

    cout << "Removing vertex: " << node << endl;
    dependValues << "Removing vertex: " << node << endl;
    for(int i = 0; i < influencedGraph->inRRSet[node].size(); i++){                                                     //for each RRSet in inRRSet (each RRSet that contains node)
        int rrSetId = influencedGraph->inRRSet[node][i];                                                                //get the next RRSet that the node to be removed is in
        unordered_map<int,int>::const_iterator got = influencedGraph->vertexToIndex[rrSetId]->find(node);               //get the unordered_map corresp to that rrSetId & in that search for the index assoc. with the vertex/node
        if(got !=  influencedGraph->vertexToIndex[rrSetId]->end()){                                                     //if vertex is found
            fill( (*influencedGraph->testDependancyVector[rrSetId])[got->second].begin(),
                    (*influencedGraph->testDependancyVector[rrSetId])[got->second].end(), false);
            for(int row = 0; row < influencedGraph->testDependancyVector[rrSetId]->size(); row++){                      //Replace all elements in the vertex column with 0;
                if((*influencedGraph->testDependancyVector[rrSetId])[row][got->second]){
                    (*influencedGraph->testDependancyVector[rrSetId])[row][got->second]= false;
                    testDependencyValues[(*influencedGraph->indexToVertex[rrSetId])[row]] -= 1;
                }
            }
        }else{
            assert(("node to be removed was not found in the RRSet. This shouldnt have happened!", false));
        }
    }

    testDependencyValues[node] = 0;                                                     //Set the value to be 0 manually because we are using reComputeDependencyValues() and not computeDependencyValues() now.
    reComputeDependencyValues(testDependencyValues, influencedGraph, testASdegree);    //Now recalculate the dependencyValues only for those nodes that have changed
}

void removingModNodesForTest(unique_ptr<Graph> &influencedGraph, int removeNodes, vector<int> &testDependencyValues, vector<pair<int, int>> &testASdegree, const set<int> &maxSeedSet, vector<int> &testModNodesToremove, set<int> &alreadyinSeed){

    int index = 0;
    for (int i = 0; i < removeNodes;) {
        int node = testModNodesToremove[i];
        if (maxSeedSet.count(node) == 0) {
            i++;
            if(i < removeNodes){//Dont call if final vertex to be removed has been found
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



set<int> subModularNodesRemove(unique_ptr<Graph> &influencedGraph, vector<int> activatedSet, int removeNodes, const set<int> &maxSeedSet, const set<int> &envelopedNodes,
                               set<int> *removalModImpact) {

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
    computeModImpactNodes(influencedGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet, envelopedNodes, removalModImpact);


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
    cout << "******* Running SubMod approach ********" << endl;
    dependValues << "******* Running SubMod approach ********" << endl;

    alreadyinSeed = set<int>();
    computeSubModImpactNodes(influencedGraph, removeNodes, dependencyValues, ASdegree, maxSeedSet, envelopedNodes, subModNodesToremove, alreadyinSeed);

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
    cout << "\n Submodular strength = " << subModStrength;
    resultLogFile << "\n Number of nodes Already present in seed set = " << alreadyinSeed.size();
    resultLogFile << "\n Submodular strength = " << subModStrength;
    myfile << influencedGraph->totalNumNodesInRRSets << " <-Recalculated Init Strength\n";
    myfile << subModStrength << " <-subModStrength\n";
    double totalAlgorithmTime = double(subModReverseEndTime - subModReverseStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\nReverse submodular algorithm time in minutes " << totalAlgorithmTime << endl;
    cout << "Breakup of time taken: " << endl;
    cout << "Total time taken by randomNumGenerator: " << influencedGraph->randomNumGen/(CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by outer while Loop: " << influencedGraph->whileLoopTime/(CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Breakup of time taken by outer while Loop: " << endl;
    cout << "Total time taken by initialization: " << influencedGraph->initTime/(CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by only the loop: " << influencedGraph->onlyLoopTime/(CLOCKS_PER_SEC * 60) << endl;
    cout << endl;
    cout << "Total time taken by calcDependancyMatrix(): " << influencedGraph->matrixTime/(CLOCKS_PER_SEC * 60) << endl;
    cout << "Total time taken by BFS(): " << influencedGraph->bfsTime/(CLOCKS_PER_SEC * 60) << endl;
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

void runCountingNodes(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &countNodesToremove){

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

void runTopKInfluential(set<int> &maxInfluenceSeed, set<int> &envelopedNodes, set<int> &topKInflNodesToremove){

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

    topKInflNodesToremove = topKInflNodesRemoveVertices(topKInflNodesGraph, removeNodes, maxInfluenceSeed, envelopedNodes,
                                                        activatedSet, "modular");
    clock_t topKInflNodesEndTime = clock();
    double totalTopKInflTime = double(topKInflNodesEndTime - topKInflNodesStartTime) / (CLOCKS_PER_SEC * 60);
    cout << "\ntopKInfluential Graph algorithm time in minutes \n" << totalTopKInflTime << endl;
    resultLogFile << "\ntopKInfluential Graph algorithm time in minutes \n" << totalTopKInflTime << endl;

    myfile << totalTopKInflTime << " <-topKInfluential Time\n";
    topKInflNodesGraph.reset();
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
        if(useRandomSeed){
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

        }else{
            myfile << "Max influence Seed Set in the original graph: " << endl;
            cout << "Max influence Seed Set in the original graph: " << endl;

            if(useEnvelop){
                //This code will run when someCondition is true AND envelopedNodes is true.
                //THis implies you cannot remove anything from the seed Set OR the envelopNodes as well
                envelopedNodes = getSeed((budget+100), maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                                         NULL);    //Find the top (budget + 100) nodes that will form a part of the envelop
            }

            maxInfluenceSeed = getSeed(budget, maxSeedGraph, activatedSet, set<int>(), set<int>(), set<int>(), set<int>(),
                                       NULL);
            vector<vector<int>>().swap(maxSeedGraph->rrSets);
            maxInfluenceNum = oldNewIntersection(maxSeedGraph, maxInfluenceSeed, activatedSet, resultLogFile);
            myfile << maxInfluenceNum << " <-MaxInfluence Num\n";
            cout << "\n \n******* Max influence end ******** \n" << flush;
        }

    }

                                                    /*get node to be removed*/
    //******************************************************************************************************************

    set<int> modNodesToremove;
    cout << "\n ******* Running modular approach ******** \n" << flush;
    resultLogFile << "\n ******* Running modular approach ******** \n";

    clock_t ModReverseStartTime = clock();
    modNodesToremove = removeVertices(influencedGraph, removeNodes, maxInfluenceSeed, envelopedNodes, activatedSet, "modular");
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
    tGraphNodesToremove = tGraphRemoveVertices(transposedGraph, influencedGraph, removeNodes, maxInfluenceSeed, envelopedNodes,
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



    //******************************************************************************************************************

    cout << "\n \n ******* Running Sub Modular approach ******** \n" << flush;
    resultLogFile << "\n \n ******* Running Sub Modular approach ******** \n" << flush;

    unique_ptr<Graph> subInfluencedGraph = make_unique<Graph>();
    subInfluencedGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        subInfluencedGraph->setPropogationProbability(probability);
    }
    set<int> *removalModImpact = new set<int>();
    set<int> subModNodesToremove = subModularNodesRemove(subInfluencedGraph, activatedSet, removeNodes,
                                                         maxInfluenceSeed, envelopedNodes,
                                                         removalModImpact);
    vector<vector<int>>().swap(subInfluencedGraph->rrSets);
    cout << "\n \n******* Node removed in all four approaches ******** \n" << flush;
    subInfluencedGraph.reset();
    //delete subInfluencedGraph;

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
        modNewGraph->setPropogationProbability(probability);
    }

    unique_ptr<Graph> topKInflNewGraph = make_unique<Graph>();
    topKInflNewGraph->readGraph(graphFileName, percentageTargetsFloat, resultLogFile);
    if (!useIndegree) {
        modNewGraph->setPropogationProbability(probability);
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

    string convertedFile =
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            graphFileName;
    newDiffusion(modNewGraph, subNewGraph, modImpactGraph, tGraph, countNewGraph, topKInflNewGraph,
                 modNodesToremove, subModNodesToremove, removalModImpact, tGraphNodesToremove, countNodesToremove, topKInflNodesToremove,
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
