//
//  Edge.cpp
//  InfluenceMaximization
//
//  Created by Preeti on 4/19/18.
//  Copyright © 2018 Madhavan R.P. All rights reserved.
//

#include "Edge.hpp"

Edge:: Edge(std::string eid,int from,int to) {
    this->sourceid=from;
    this->destid=to;
    this->eid = eid;
    this->strength=0;
}

std::string Edge:: Edge::getId() {
    return eid;
}

void Edge:: Edge::setId(std::string eid) {
    this->eid = eid;
}

void Edge::addRRid(int rrid){
    this->rrids.insert(rrid);
}

void Edge::setRRid(set<int> rrids){
    this->rrids=rrids;
}

void Edge::removeRRid(int rrid){
    this->rrids.erase(rrid);    
}
