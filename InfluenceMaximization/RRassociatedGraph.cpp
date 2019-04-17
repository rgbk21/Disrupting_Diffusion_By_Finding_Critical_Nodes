//
//  RRassociatedGraph.cpp
//  InfluenceMaximization
//
//  Created by Preeti on 4/18/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#include "RRassociatedGraph.hpp"
RRassociatedGraph::RRassociatedGraph() {
    noOfEdges=0;
    noOfEdgesCreated = 0;
    noOfEdgesDeleted = 0;
    noOfVertices = 0;
}

void RRassociatedGraph::addVertex(vertex v) {
    vertexMap.insert(pair<int,vertex*>(v.getId(), &v));
}

vertex* RRassociatedGraph::find(int id) {
    unordered_map<int,vertex*>::const_iterator got=vertexMap.find(id);
    if(got != vertexMap.end() )
        return got->second;
    return nullptr;
}

Edge* RRassociatedGraph::findedge(string id){
    unordered_map<std::string,Edge*>::const_iterator got=EdgeMap.find(id);
    if(got != EdgeMap.end() )
        return got->second;
    return nullptr;
}

void RRassociatedGraph::addEdge(int from, int to, int label) {
    
    vertex* fromVertex = find(from);
    if (fromVertex == nullptr) {
        fromVertex = new vertex(from);
        vertexMap.insert(pair<int,vertex*>(fromVertex->getId(), fromVertex));
        noOfVertices++;
    }
    
    vertex* toVertex = find(to);
    if (toVertex == nullptr) {
        toVertex = new vertex(to);
        vertexMap.insert(pair<int,vertex*>(toVertex->getId(), toVertex));
        noOfVertices++;
    }

    //For self loops, I believe?
    if(fromVertex==toVertex){
       // fromVertex->outDegree++;
        //cout<<fromVertex->getId()<<" "<<toVertex->getId()<<"\n";
        return;
    }
    string eid;
    eid=to_string(from);

//    eid+=std::to_string(to);

    eid = eid + "-" + std::to_string(to);//Correction to possible bug?

    Edge* edge=findedge(eid);
    if(edge==nullptr){
        edge=new Edge(eid,from,to);
        edge->addRRid(label);
        fromVertex->addOutGoingEdges(edge);
        EdgeMap.insert(pair<string,Edge*>(edge->getId(), edge));
        noOfEdges++;
        noOfEdgesCreated++;
    }
    else{
        /*So if the edge exists, you are incrementing the outdegree of the vertex.
         * Consider the vetex 4 in the graph MyCaGrqProcessed-50nodes. That vertex has only 2 outgoing edges: 4-0 and 4-2
         *But because you see the vertex 4 300+ times, those edges are traversed multiple times and this part of the code
         * is triggered causing the outdegree to become 368. Despite the actual number of outgoing edges to be only 2!
         * Why are you doing this?
         * - Well, think about it. If you don't count repetitions, that means you are just looking at the number
         * of paths from each node. This could be done by a single probabilistic BFS from each node.
         * You dont want that. You want to factor in the number of times a particular vertex was visited during the
         * probabilistic BFS because an edge from that vertex was selected.
         * Moral of the story: this is correct and the line should be uncommented
         * */
        edge->addRRid(label);
        fromVertex->outDegree++;
    }
    
}


void RRassociatedGraph::removeEdge(int from, int to,int rrSetID) {
    vertex* fromVertex = find(from);
    string eid;
    eid=to_string(from);

//    eid+=std::to_string(to);

    eid = eid + "-" + to_string(to);//Correction to possible bug?

    if(EdgeMap.count(eid)==1){
        Edge* e = EdgeMap.find(eid)->second;
        if(fromVertex->removeOutgoingEdge(e,rrSetID)){
            EdgeMap.erase(eid);
            delete e;
            noOfEdgesDeleted++;
        }
    }
}

