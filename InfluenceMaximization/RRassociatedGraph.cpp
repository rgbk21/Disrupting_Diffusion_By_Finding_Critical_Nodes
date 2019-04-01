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

Edge* RRassociatedGraph::findedge(std::string id){
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
    }
    
    vertex* toVertex = find(to);
    if (toVertex == nullptr) {
        toVertex = new vertex(to);
        vertexMap.insert(pair<int,vertex*>(toVertex->getId(), toVertex));
    }
    
    if(fromVertex==toVertex){
       // fromVertex->outDegree++;
        //cout<<fromVertex->getId()<<" "<<toVertex->getId()<<"\n";
        return;
    }
    std::string eid;
    eid=std::to_string(from);

//    eid+=std::to_string(to);

    eid = eid + "-" + std::to_string(to);//Correction to possible bug?

    Edge* edge=findedge(eid);
    if(edge==nullptr){
        edge=new Edge(eid,from,to);
        edge->addRRid(label);
        fromVertex->addOutGoingEdges(edge);
        EdgeMap.insert(pair<std::string,Edge*>(edge->getId(), edge));
        noOfEdges++;
    }
    else{
        edge->addRRid(label);
        fromVertex->outDegree++;
    }
    
}


void RRassociatedGraph::removeEdge(int from, int to,int rrSetID) {
    vertex* fromVertex = find(from);
    std::string eid;
    eid=std::to_string(from);

//    eid+=std::to_string(to);

    eid = eid + "-" + std::to_string(to);//Correction to possible bug?

    if(EdgeMap.count(eid)==1){
        Edge* e=EdgeMap.find(eid)->second;
        if(fromVertex->removeOutgoingEdge(e,rrSetID)){
            EdgeMap.erase(eid);
            delete e;
        }
    }
}

