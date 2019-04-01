//
//  RRassociatedGraph.hpp
//  InfluenceMaximization
//
//  Created by Preeti on 4/18/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#ifndef RRassociatedGraph_hpp
#define RRassociatedGraph_hpp

#include <stdio.h>
#include <unordered_map>
#include <unordered_set>
#include "vertex.hpp"
#include <stdio.h>
#include <iostream>
#include <vector>
#include <fstream>
#include <stdlib.h>
#include <queue>
#include <ctime>
#include <deque>
#include <string.h>
#include <string>
#include <algorithm>
#include "Edge.hpp"
using namespace std;
/*
class pairHash{
public:
    size_t operator()(const pair<int, int> &k) const{
        return k.first * 100 + k.second;
    }
};*/

class RRassociatedGraph{

public:
    unordered_map<int,vertex*> vertexMap;
    std::unordered_map<std::string,Edge*> EdgeMap;
    int noOfEdges;
    
public:
    RRassociatedGraph();
    unordered_set<vertex> getVertices();
    int getNumberOfVertices();
    void addVertex(vertex v);
    vertex* find(int id);
    Edge* findedge(std::string id);
    void addEdge(int from, int to, int label);
    void removeEdge(int from, int to,int rrSetID);
};
#endif /* RRassociatedGraph_hpp */

