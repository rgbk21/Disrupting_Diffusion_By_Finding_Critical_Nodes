//
//  vertex.hpp
//  InfluenceMaximization
//
//  Created by Preeti on 4/18/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#ifndef vertex_hpp
#define vertex_hpp

#include <stdio.h>
#include <unordered_set>
#include <unordered_map>
#include <iostream>
#include <set>
#include <vector>
#include <utility>
#include <algorithm>
#include "Edge.hpp"

using namespace std;

class vertex{

public:
    int id;
    bool operator==(const vertex* &obj) const
    {
        return id==obj->id;
    }
    int outDegree;
    vector<Edge*> outGoingEdges;
    
public:
    
    vertex(int id);
    int getId();
    void setId(int id);
    int getOutDegree();
    void setOutDegree(int outDegree);
    vector<Edge*> getoutGoingEdges();
    void setOutBoundNeighbours(vector<Edge*> outGoingEdges);
    bool removeOutgoingEdge(Edge* e,int rrSetID);
    void addOutGoingEdges(Edge* v);
    void deleteOutBoundNeighbour();
};



#endif /* vertex_hpp */
