//
//  Diffusion.hpp
//  InfluenceMaximization
//
//  Created by Madhavan R.P on 9/15/17.
//  Copyright © 2017 Madhavan R.P. All rights reserved.
//

#ifndef Diffusion_hpp
#define Diffusion_hpp

#include <stdio.h>
#include <vector>
#include <set>
#include <cmath>
#include <deque>
#include "TIM-Models/TIMCoverage.hpp"
#include <assert.h>
#include <unordered_map>

#include "Graph.hpp"
using namespace std;

#define NUMBER_OF_SIMULATIONS 20000
#define EPSILON 2

/*bool sortmap(const int &a,const int &b)
{
    return a > b;
}

inline void dagSingleDiffusion(set<int> activatedSet, Graph *graph, set<int> seedSet,vector<int> *visitMark, vector<bool> *visited, deque<int> *queue, unordered_map<int,unordered_map<int,int>> aggregateReachableSetInDag, unordered_map<int,int> aggregateSizeOfReachableTargets) {
    
    int nVisitMark = 0;
    
    for(int seed: seedSet) {
        if(activatedSet.find(seed)==activatedSet.end()) {
            if(!(*visited)[seed]) {
                queue->push_front(seed);
            }
        }
        while(!queue->empty()) {
            int u = queue->front();
            (*visited)[u] = true;
            (*visitMark)[nVisitMark] = u;
            nVisitMark++;
            queue->pop_front();
            activatedSet.insert(u);
            for (int v : graph->graph[u]) {
                bool activeEdge = graph->flipCoinOnEdge(u, v);
                if (activeEdge) {
                    if(!(*visited)[v])
                        if (activatedSet.find(v)==activatedSet.end()) {
                            queue->push_front(v);
                        }
                }
            }
        }
        unordered_map<int,int> aggregateReachableNodesForNode=unordered_map<int,int>();
        int reachableNodesCount = 0;
        for(int reachableNode:activatedSet){
            reachableNodesCount++;
            if (aggregateReachableSetInDag.count(seed)==1) {
                aggregateReachableNodesForNode = aggregateReachableSetInDag.at(seed);
            }
            int currentFrequencyOFReachableNode = 0;
            if (aggregateReachableNodesForNode.count(reachableNode)==1) {
                currentFrequencyOFReachableNode = aggregateReachableNodesForNode.at(reachableNode);
            }
            currentFrequencyOFReachableNode++;
            aggregateReachableNodesForNode.insert(reachableNode, currentFrequencyOFReachableNode);
        }
        aggregateReachableSetInDag[seed]=aggregateReachableNodesForNode;
        int aggregateReachableSetSize = 0;
        if (aggregateSizeOfReachableTargets.count(seed)==1) {
            aggregateReachableSetSize = aggregateSizeOfReachableTargets.at(seed);
        }
        aggregateReachableSetSize += reachableNodesCount;
        aggregateSizeOfReachableTargets.insert(seed, aggregateReachableSetSize);
        
    }
    
    for(int i=0; i<nVisitMark; i++) {
        (*visited)[(*visitMark)[i]] = false;
    }
}


inline set<int> dagDiffusion(Graph *graph, set<int> seedSet) {
    vector<int> visitMark;
    vector<bool> visited;
    for(int i=0; i<graph->n; i++) {
        visitMark.push_back(0);
        visited.push_back(false);
    }
    unordered_map<int,unordered_map<int,int>> aggregateReachableSetInDag=unordered_map<int,unordered_map<int,int>>();
    unordered_map<int,int> aggregateSizeOfReachableTargets=unordered_map<int,int>();
    
    set<int> activatedSet = set<int>();
    deque<int> *diffusionQueue = new deque<int>();
    for (int i=0; i<NUMBER_OF_SIMULATIONS; i++) {
        dagSingleDiffusion(activatedSet, graph, seedSet, &visitMark, &visited, diffusionQueue, aggregateReachableSetInDag, aggregateSizeOfReachableTargets);
        activatedSet.clear();
    }
    delete diffusionQueue;
    set<int> avgReachableSet=set<int>();
    unordered_map<int, set<int>> result = unordered_map<int, set<int>>();
    for(unordered_map<int,unordered_map<int,int>>::iterator node = aggregateReachableSetInDag.begin(); node != aggregateReachableSetInDag.end(); ++node) {
        unordered_map<int,int> aggregateReachableNodeFrequencyMap = node->second;
        int avgReachableTargetsSize = round((float) aggregateSizeOfReachableTargets.at(node->first) / NUMBER_OF_SIMULATIONS);
        std :: sort(aggregateReachableNodeFrequencyMap.begin(),aggregateReachableNodeFrequencyMap.end(), sortmap);
        
        for(int i=0; i<avgReachableTargetsSize; i++) {
            avgReachableSet.insert(aggregateReachableNodeFrequencyMap.at(i));
        }
    }
    return avgReachableSet;
}
*/



inline string singleDiffusionInfluence(Graph *graph, set<int> seedSet,string graphFileName,int budget,float probability) {
    string influenceFile;
    vector<int> visitMark;
    vector<bool> visited;
    for(int i=0; i<graph->n; i++) {
        visitMark.push_back(0);
        visited.push_back(false);
    }
    
    set<int> *activatedSet = new set<int>();
    deque<int> *queue = new deque<int>();
    influenceFile=graphFileName;
    influenceFile+="_influenceFile.txt";
    influenceFile+="_" + to_string(budget);
    influenceFile+="_" + to_string(probability);
    ofstream myfile;
    influenceFile = "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" + influenceFile;
    myfile.open (influenceFile);
    int nVisitMark = 0;
    
    for(int seed: seedSet) {
        if(activatedSet->find(seed)==activatedSet->end()) {
            if(!(visited)[seed]) {
                queue->push_front(seed);
            }
        }
        while(!queue->empty()) {
            int u = queue->front();
            visited[u] = true;
            visitMark[nVisitMark] = u;
            nVisitMark++;
            queue->pop_front();
            activatedSet->insert(u);
            for (int v : graph->graph[u]) {
                bool activeEdge = graph->flipCoinOnEdge(u, v);
                if (activeEdge) {
                    myfile <<u<<" "<<v<<"\n";
                    if(!visited[v])
                        if (activatedSet->find(v)==activatedSet->end()) {
                            queue->push_front(v);
                            //modified
                           // myfile <<u<<" "<<v<<"\n";
                        }
                }
            }
        }
    }

    myfile.close();
    for(int i=0; i<nVisitMark; i++) {
        visited[visitMark[i]] = false;
    }
    return influenceFile;
}




inline void singleDiffusion(set<int> *activatedSet, Graph *graph, set<int> *seedSet, set<int> *alreadyActivated, vector<int> *visitMark, vector<bool> *visited, deque<int> *queue) {
    
    int nVisitMark = 0;
    if(alreadyActivated!=NULL) {
        //        activatedSet->insert(alreadyActivated->begin(), alreadyActivated->end());
    }
    for(int seed: *seedSet) {
        if(activatedSet->find(seed)==activatedSet->end()) {
            if(!(*visited)[seed]) {
                queue->push_front(seed);
            }
        }
        while(!queue->empty()) {
            int u = queue->front();
            (*visited)[u] = true;
            (*visitMark)[nVisitMark] = u;
            nVisitMark++;
            queue->pop_front();
            activatedSet->insert(u);
            for (int v : graph->graph[u]) {
                bool activeEdge = graph->flipCoinOnEdge(u, v);
                if (activeEdge) {
                    if(!(*visited)[v])
                        if (activatedSet->find(v)==activatedSet->end()) {
                            queue->push_front(v);
                        }
                }
            }
        }
    }
    
    for(int i=0; i<nVisitMark; i++) {
        (*visited)[(*visitMark)[i]] = false;
    }
}


inline vector<int> performDiffusion(Graph *graph, set<int> seedSet, set<int> *alreadyActivated) {
    int activatedFrequency[graph->n];
    vector<int> visitMark;
    vector<bool> visited;
    for(int i=0; i<graph->n; i++) {
        activatedFrequency[i] = 0;
        visitMark.push_back(0);
        visited.push_back(false);
    }
    
    int totalActiveSetSize = 0;
    set<int> *activatedSet = new set<int>();
    deque<int> *diffusionQueue = new deque<int>();
    for (int i=0; i<NUMBER_OF_SIMULATIONS; i++) {
        singleDiffusion(activatedSet, graph, &seedSet, alreadyActivated, &visitMark, &visited, diffusionQueue);
        diffusionQueue->clear();
        set <int> :: iterator itr;
        totalActiveSetSize+= activatedSet->size();
        for (itr = activatedSet->begin(); itr != activatedSet->end(); ++itr)
        {
            activatedFrequency[*itr]++;
        }
        activatedSet->clear();
    }
    delete activatedSet;
    delete diffusionQueue;
    
    priority_queue<pair<int, int>, vector<pair<int, int>>, QueueComparator> queue;
    
    int averageActiveSetSize = round((double)totalActiveSetSize/(double)NUMBER_OF_SIMULATIONS);
//    cout << "\n Total activated set size = " << totalActiveSetSize;
//    cout << "\n Average activated set size = " << averageActiveSetSize;
    for(int i=0; i<graph->n; i++) {
        queue.push(make_pair(i, activatedFrequency[i]));
    }
    
    vector<int> averageActivatedSet;
    for(int i=0; i<averageActiveSetSize; i++) {
        averageActivatedSet.push_back(queue.top().first);
//        cout << "\n For i = " << i << " Best is " << queue.top().second << " and node is  " << queue.top().first;
        queue.pop();
    }
    return averageActivatedSet;
}

inline pair<int, int> findInfluenceUsingDiffusion(Graph *graph, set<int> seedSet, set<int> *alreadyActivated) {
    vector<int>activatedSet = performDiffusion(graph, seedSet, alreadyActivated);
    int targetsActivated = 0;
    int nonTargetsActivated = 0;
    for(int activeNode:activatedSet) {
        if(graph->labels[activeNode]) targetsActivated++;
        else nonTargetsActivated++;
    }
    return make_pair(targetsActivated, nonTargetsActivated);
}

inline pair<int, int> findInfluenceUsingDiffusion(Graph *graph, set<int> seedSet) {
    return findInfluenceUsingDiffusion(graph, seedSet, NULL);
}

inline pair<pair<int, int>, set<int>> findActivatedSetAndInfluenceUsingDiffusion(Graph *graph, set<int> seedSet, set<int> *alreadyActivated) {
    vector<int>activatedSet = performDiffusion(graph, seedSet, alreadyActivated);
    set<int>activated;
    
    int targetsActivated = 0;
    int nonTargetsActivated = 0;
    for(int activeNode:activatedSet) {
        if(graph->labels[activeNode]) targetsActivated++;
        else nonTargetsActivated++;
        activated.insert(activeNode);
    }
    return make_pair(make_pair(targetsActivated, nonTargetsActivated), activated);
}

inline int oldNewIntersection(Graph *newGraph, set<int> seedSet,vector<int> activatedSet,std::ofstream& resultLogFile){
    //again diffusion on old graph after node removal
   // vector<int> NewactivatedSet=performDiffusion(newGraph,seedSet,NULL);

    int diffusionNum=0;
    //diffusion with RR approach
    int n = (int)activatedSet.size();
    double epsilon = (double)EPSILON;
    int R = (8+2 * epsilon) * n * (2 * log(n) + log(2))/(epsilon * epsilon);
    cout<< "\nRR sets are: "<< R << endl;
    newGraph->generateRandomRRSetsFromTargets(R, activatedSet, "modular", resultLogFile);
    for(vector<int> v:newGraph->rrSets){
        for(int j:v){
            if(seedSet.count(j)==1){
                diffusionNum++;
                break;
            }
        }
    }
    diffusionNum=((double)diffusionNum/R)*n;
    
    //find intersection of new and old activated set
    /*std::vector<int> intersect;
    std::sort(NewactivatedSet.begin(), NewactivatedSet.end());
    std::sort(activatedSet.begin(), activatedSet.end());
    std::set_intersection(activatedSet.begin(), activatedSet.end(),NewactivatedSet.begin(), NewactivatedSet.end(),std::back_inserter(intersect));*/
    
    //cout << "\n Old Targets activated = " << activatedSet.size();
    //cout << "\n New Targets activated = " << NewactivatedSet.size();
    
     cout << "\n New Targets activated = " << diffusionNum;
    resultLogFile<< "\n New Targets activated = " << diffusionNum;
    //cout << "\n intersection size "<<intersect.size();
    //cout << "\n Percentage of intersect with old " <<double((intersect.size()*100)/activatedSet.size())<<"%";
    return diffusionNum;
}

#endif /* Diffusion_hpp */
