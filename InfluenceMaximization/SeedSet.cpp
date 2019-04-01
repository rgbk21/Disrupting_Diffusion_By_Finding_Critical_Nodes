//
//  SeedSet.cpp
//  InfluenceMaximization
//
//  Created by Preeti on 2/23/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#include "SeedSet.hpp"
#include <assert.h>
#include <sstream>
#include <iomanip>
#include <iterator>

SeedSet::SeedSet(Graph *graph, int budget) {
    this->graph =graph;
    this->budget=budget;
}

bool sortbypairdesc(const pair<int,int> &a,const pair<int,int> &b)
{
    return (a.second > b.second);
}

bool sortbypairasc(const pair<int,int> &a,const pair<int,int> &b)
{
    return (a.second < b.second);
}

//Randomly select from all vertices
set<int> SeedSet::getCompletelyRandom(set<int> modNodes,set<int> subModNodes) {
    int m = graph->getNumberOfVertices();
    for(int i=0;i<budget;){
        int randomVertex;
        randomVertex = rand() % m;
        if(seedSet.count(randomVertex)==0 && modNodes.count(randomVertex)==0 && subModNodes.count(randomVertex)==0){
            seedSet.insert(randomVertex);
            i++;
        }
    }
    return seedSet;
}

//Randomly selecting from topBestThreshold number of vertices with highest outdegree

set<int> SeedSet:: outdegreeRandom(int topBestThreshold,set<int> modNodes,set<int> subModNodes){
    //select best top number on the basis of outdegree
    vector<int> bestdegreenodes=getTopOutdegreeNodes(topBestThreshold);
    //randomly select number of budget nodes
    int m=(int)bestdegreenodes.size();
    for(int i=0;i<budget;){
        int randomVertex;
        randomVertex = bestdegreenodes[rand() % m];
        if(seedSet.count(randomVertex)==0 && modNodes.count(randomVertex)==0 && subModNodes.count(randomVertex)==0 ){
            seedSet.insert(randomVertex);
            i++;
        }
    }
    vector<int>().swap(bestdegreenodes);
    return seedSet;
}

//Farthest vertices selecting from topBestThreshold number of vertices with highest outdegree

set<int> SeedSet:: outdegreeFarthest(int topBestThreshold){
    //select best top number on the basis of outdegree
    vector<int> bestdegreenodes=getTopOutdegreeNodes(topBestThreshold);
    
    int i=0;
    int randomvertex;
    while(i<budget){
        randomvertex=rand() % bestdegreenodes.size();
        if(seedSet.count(bestdegreenodes[randomvertex])==0){
            vector<int> v1=graph->graph[bestdegreenodes[randomvertex]];
            vector<pair<int,int>> distance;
            for(int j=0;j<bestdegreenodes.size();j++){
                if(bestdegreenodes[j]!=bestdegreenodes[randomvertex] && seedSet.count(bestdegreenodes[j])==0){
                    vector<int> v2=graph->graph[bestdegreenodes[j]];
                    std::sort(v1.begin(), v1.end());
                    std::sort(v2.begin(), v2.end());
                    std::vector<int> v_intersection;
                    std::set_intersection(v1.begin(), v1.end(),v2.begin(), v2.end(),std::back_inserter(v_intersection));
                    pair<int,int> node;
                    node.first=bestdegreenodes[j];
                    node.second=(int)v_intersection.size();
                    distance.push_back(node);
                }
            }
            std :: sort(distance.begin(),distance.end(), sortbypairasc);
            seedSet.insert(distance.at(0).first);
            i++;
            if(i>=budget)
                break;
            seedSet.insert(bestdegreenodes[randomvertex]);
            i++;
        }
    }
    return seedSet;
}

vector<int> SeedSet:: getTopOutdegreeNodes(int topBestThreshold){
    int m = graph->getNumberOfVertices();
    vector<pair<int,int>> Outdegree;
    for(int i=0;i<m;i++){
        pair<int,int> node= pair<int,int>();
        node.first=i;
        node.second=(int)graph->graph[i].size();
        Outdegree.push_back(node);
    }
    std :: sort(Outdegree.begin(),Outdegree.end(), sortbypairdesc);
    //select best top number on the basis of outdegree
    vector<int> bestdegreenodes;
    for(int i=0;i<topBestThreshold;i++){
        bestdegreenodes.push_back(Outdegree.at(i).first);
    }
    vector<pair<int,int>>().swap(Outdegree);
    return bestdegreenodes;
}

