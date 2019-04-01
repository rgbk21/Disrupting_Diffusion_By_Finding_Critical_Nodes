//
//  vertex.cpp
//  InfluenceMaximization
//
//  Created by Preeti on 4/18/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#include "vertex.hpp"
vertex:: vertex(int id) {
    this->id = id;
    this->outDegree = 0;
}

int vertex::getId() {
    return id;
}

void vertex::setId(int id) {
    this->id = id;
}


int vertex:: getOutDegree() {
    return outDegree;
}

void vertex:: setOutDegree(int outDegree) {
    this->outDegree = outDegree;
}

vector<Edge*> vertex::getoutGoingEdges() {
    return outGoingEdges;
}

void vertex::setOutBoundNeighbours(vector<Edge*> outBoundNeighbours) {
    this->outGoingEdges = outBoundNeighbours;
}


void vertex::addOutGoingEdges(Edge *e) {
        this->outGoingEdges.push_back(e);
        this->outDegree++;

}

bool vertex::removeOutgoingEdge(Edge* e, int rrSetID) {
    for(int i=0;i<this->outGoingEdges.size();i++){
        if(this->outGoingEdges[i]==e){
            this->outGoingEdges[i]->removeRRid(rrSetID);
            outDegree--;
            if(this->outGoingEdges[i]->rrids.size()==0){
                this->outGoingEdges.erase(this->outGoingEdges.begin()+i);
                return true;
            }
            return false;
        }
    }
    return false;
}


void vertex:: deleteOutBoundNeighbour(){
    this->outGoingEdges.clear();
    this->setOutDegree(0);
}

