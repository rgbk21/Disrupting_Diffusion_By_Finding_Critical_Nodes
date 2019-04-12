//
//  Edge.hpp
//  InfluenceMaximization
//
//  Created by Preeti on 4/19/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#ifndef Edge_hpp
#define Edge_hpp

#include <stdio.h>
#include <iostream>
#include <vector>
#include <unordered_set>
#include <set>
#include <string>

using namespace std;

class Edge{
    
public:

    bool operator==(const Edge* &obj) const
    {
        return eid==obj->eid;
    }
    
    string eid;
    set<int> rrids;
    int sourceid;
    int destid;
    int strength;

public:
    Edge(string eid,int from,int to);
    string getId();
    void addRRid(int rrid);
    void removeRRid(int rrid);
    void setRRid(set<int> rrids);
    void setId(string eid);
};
#endif /* Edge_hpp */
