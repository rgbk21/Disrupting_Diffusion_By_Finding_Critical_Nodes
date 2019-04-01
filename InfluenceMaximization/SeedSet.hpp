//
//  SeedSet.hpp
//  InfluenceMaximization
//
//  Created by Preeti on 2/23/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#ifndef SeedSet_hpp
#define SeedSet_hpp
#include "Graph.hpp"
#include <set>
#include <algorithm>
using namespace std;

class SeedSet {
    
    private:
    Graph *graph;
    int budget;
    set<int> seedSet;
    int topBestThreshold;
    
    public:
    SeedSet(Graph *graph, int budget);

    set<int> getCompletelyRandom(set<int> modNodes,set<int> subModNodes);
    
    set<int> gethalfRandom(set<int> modNodes,set<int> subModNodes);
    
    set<int> outdegreeRandom(int topBestThreshold,set<int> modNodes,set<int> subModNodes);
    
    set<int> outdegreeFarthest(int topBestThreshold);
    
    vector<int> getTopOutdegreeNodes(int topBestThreshold);
};

#endif /* SeedSet_hpp */
