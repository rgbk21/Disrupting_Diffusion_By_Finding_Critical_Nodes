//
//  Graph.hpp
//  InfluenceMaximization
//
//  Created by Madhavan R.P on 8/4/17.
//  Copyright © 2017 Madhavan R.P. All rights reserved.
//

#ifndef Graph_hpp
#define Graph_hpp

#include <stdio.h>
#include <iostream>
#include <vector>
#include <fstream>
#include <stdlib.h>
#include <queue>
#include <ctime>
#include <deque>
#include <string.h>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <string>
#include <random>
#include <memory>
#include "RRassociatedGraph.hpp"

using namespace std;
class CompareOutdegree {
public:
    bool operator()(const pair<int,int> &a,const pair<int,int> &b)
    {
        return (a.second > b.second);
    }
};


class Graph {
private:
    float propogationProbability;
    int propogationProbabilityNumber;
    bool standardProbability;
    string graphName;
    float percentageTargets;
    vector<int> nonTargets;
    int numberOfTargets;
    int numberOfNonTargets;

    

public:
    Graph();
    RRassociatedGraph *RRas;
    int n, m;
    long totalNumNodesInRRSets = 0;//Stores the total number of nodes in all of the RRSets
    double modImpactTime;
    vector<bool> alreadyVisited;
    //vector<unordered_map<AS,vector<AS>>> AStree;
    //vector<AS> *match;

    //Timings
    clock_t randomGenStart;
    clock_t outerWhileLoopStart;
    clock_t endOfInit;
    clock_t matrixStart;
    clock_t bfsStart;
    double bfsTime = 0;
    double matrixTime = 0;
    double whileLoopTime = 0;
    double initTime = 0;
    double onlyLoopTime = 0;
    double randomNumGen = 0;

    
    vector<vector<int> > graph;
    vector<vector<int> > graphTranspose;
    vector<vector<int>> rrSets;

    vector<unordered_map<int, int>*> vertexToIndex;
    vector<vector<int>*> indexToVertex;
    vector<vector<vector<bool>>*> dependancyVector;//Stores the dependancyMatrix generated in each RRSet Generation
    vector<vector<vector<bool>>*> testDependancyVector;//Used for the testing of what if modNodes were the ones removed

    vector<bool> labels;
    deque<int> q;
    deque<int> countingNodes_Q;
    vector<bool> countingNodes_Visited;
    vector<int> inDegree;
    vector<bool> visited;
    vector<int> visitMark;
    vector<int> NodeinRRsetsWithCounts;
    vector<int> initialNodeinRRsetsWithCounts;//Stores the counts before the nodes are removed by the removeVertices method. Used for transposedGraph
    vector<int> timesThisNodeWasPicked;//Stores the no. of times this node was picked as Random Vertex
    vector<int> outdegreeReducedFor;//Stores the reduction in outdegree for each node in 1 iteration of removeVertexFromRRassociatedGraph()
    vector<vector<int>> RRgraph;
    vector<vector<int>> miniRRGraph = vector<vector<int>>();//Stores the RRGraph but with mappedVertices instead of original vertices
    vector<vector<int>> inRRSet;//inRRSet contains the RRSetIds of the RRSets in which this vertex occurs

    vector<int> outdegree;
    priority_queue<pair<int,int>,vector<pair<int,int>>,CompareOutdegree> workQueue;
    //set<pair<int,int>,CompareOutdegree> workMap;
    vector<vector<set<int>>> associatedSet;
    vector<set<int>>nodeAS;
    vector<unordered_map<int,unordered_set<int>>> pairAssociatedSet;
    vector<int> coverage;

    void BFS(vector<vector<int>> &myGraph, vector<vector<bool>>* dependancyMatrix, int u, int rrSetSize, int vertexRemoved);
    void generateRandomRRSetwithRRgraphs(int randomVertex, int rrSetID);
    void calcDependancyMatrix(int randomVertex, int rrSetID, int rrSetSize, const vector<int> &verticesVisited);
    void generateRandomRRSetwithRRgraphs_Interleaved(int randomVertex, int rrSetID);
    void generateRandomRRSetCountingNodes(int randomVertex, int rrSetID);
    int BFSCountingNodes(int startVertex);
    void calcDependancyMatrix_Interleaved(const vector<vector<int>> &miniRRGraph, const int randomVertex, const int rrSetID, const int rrSetSize, const unordered_map<int, int>* mappedIndex);
    void readGraph(string fileName,std::ofstream& resultLogFile);
    void readGraph(string fileName, float percentage,std::ofstream& resultLogFile);
    void writeGraphToFile(vector<vector<int>> inputGraph, string graphName, string path, int n, int m);
    void readReverseGraph(string fileName, float percentage);
    void readInfluencedGraph(string fileName, float percentage,vector<int> activatedSet);
    vector<int> writeInfluencedGraph(string fileName, float percentage, string convertedFile, vector<int> *seedNodes,vector<int> *seedOrder);
    void readHalfGraph(string fileName, float percentage,int graphCutValue,std::ofstream& resultLogFile);
    void readInfluencedHalfGraph(string fileName, float percentage, string influenceFile,int graphCutValue,std::ofstream& resultLogFile,bool fullgraph);
    void readLabels(string fileName);
    void writeLabels(std::ofstream& resultLogFile);
    void setLabels(vector<bool> labels, float percentageTargets);
    void removeVertexFromRRassociatedGraph(int vertex);
    void printVector(const vector<int> &myVector);
    //Numbers
    int getNumberOfVertices();
    int getNumberOfEdges();
    int getNumberOfTargets();
    int getNumberOfNonTargets();
    
    //Data Structure
    vector<int> *getNonTargets();
    
    vector<vector<int>> constructTranspose(vector<vector<int> > aGraph);
    void generateRandomRRSets(int R, bool label,std::ofstream& resultLogFile);
    void generateRandomRRSetsFromTargets(int R, vector<int> activatedSet, string modular,std::ofstream& resultLogFile);
    
    vector<int> generateRandomRRSet(int randomVertex, int rrSetID);
    void generateRandomRRSetwithCount(int randomVertex, int rrSetID);
    void generateRandomRRSetwithCountMod(int randomVertex, int rrSetID);
    void BFSonRRgraphs(int Rid,int rrSetID);
    void UpdateAssociatedSetMatrix(int rrSetID);
    void clearRandomRRSets();
    vector<vector<int>>* getRandomRRSets();
    
    vector<int> oldRRSetGeneration(int randomVertex, int rrSetID);
    void assertTransposeIsCorrect();
    
    //Functions for propogation probability
    void setPropogationProbability(float p);
    bool flipCoinOnEdge(int u, int v);
    int generateRandomNumber(int u, int v);
    int getPropogationProbabilityNumber();
    void removeOutgoingEdges(int v);
    void removeNodeFromRRset(int v);
    void removeSetFromASmatrix(int row, int vertex, int rrSetID);
    void addSetintoASmatrix(int row, int vertex, int rrSetID);
    void print2DVector(const vector <vector<int>> &myVector);
    void assertCorrectNodesAreDeleted(int vertex, int numOfEdgesToDelete, int totalEdgesInOrigGraphPre, int totalEdgesInTransGraphPre);
};

#endif /* Graph_hpp */



