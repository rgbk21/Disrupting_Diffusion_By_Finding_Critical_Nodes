//
//  Graph.cpp
//  InfluenceMaximization
//
//  Created by Madhavan R.P on 8/4/17.
//  Copyright © 2017 Madhavan R.P. All rights reserved.
//

#include "Graph.hpp"
#include <assert.h>
#include <sstream>
#include <iomanip>
#include <random>
#include <climits>
#include <deque>
#include <set>
#include <vector>


using namespace std;

void Graph::readGraph(string fileName, std::ofstream &resultLogFile) {
    readGraph(fileName, 0.8, resultLogFile);
}

bool sortbydegree(const set<int> &a, const set<int> &b) {
    return (a.size() > b.size());
}


Graph::Graph() {
    this->standardProbability = false;
}

/*
 AS::AS(int value, AS* n)
 {
 data=value;
 count=0;
 }
 */
void Graph::setPropogationProbability(float p) {
    this->propogationProbability = p;
    this->standardProbability = true;
    this->propogationProbabilityNumber = (float) 1 / p;
}

int Graph::getPropogationProbabilityNumber() {
    return this->propogationProbabilityNumber;
}

int Graph::generateRandomNumber(int u, int v) {

    int randomNumberLimit;

//    random_device rd; // obtain a random number from hardware
//    mt19937 eng(rd()); // seed the generator
//    uniform_int_distribution<> distr(0, INT_MAX); // define the range

    if (this->standardProbability) {
        randomNumberLimit = this->propogationProbabilityNumber;
    } else {
        randomNumberLimit = inDegree[v];
    }
    return rand() % randomNumberLimit;
//    return distr(eng) % randomNumberLimit;
}

bool Graph::flipCoinOnEdge(int u, int v) {
    int randomNumber = generateRandomNumber(u, v);
    return randomNumber == 0;
}

void Graph::readReverseGraph(string fileName, float percentage) {
    this->graphName = fileName;
    this->percentageTargets = percentage;
    cout << "\n Reading Reverse Influence graph: ";

    ifstream myFile(
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            fileName);
    string s;
    if (myFile.is_open()) {
        myFile >> n >> m;
        graph = vector<vector<int>>(n, vector<int>());
        visited = vector<bool>(n, false);
        labels = vector<bool>(n, true);
        inDegree = vector<int>(n, 0);

        int from, to;
        int maxDegree = 0;
        while (myFile >> from >> to) {
            graph[to].push_back(from);
            inDegree[to] = inDegree[to] + 1;
            if (inDegree[to] > maxDegree) {
                maxDegree = inDegree[to];
            }
        }
        myFile.close();
    }

    graphTranspose = constructTranspose(graph);
    visitMark = vector<int>(n);
    this->numberOfTargets = this->getNumberOfVertices();
    this->numberOfNonTargets = (int) nonTargets.size();
}

//********** Function for generating half graph ********
void Graph::readHalfGraph(string fileName, float percentage, int graphCutValue, std::ofstream &resultLogFile) {
    this->graphName = fileName;
    this->percentageTargets = percentage;
    cout << "\n Generating graph: " << 100 - graphCutValue << "%" << flush;
    resultLogFile << "\n Generating graph: " << 100 - graphCutValue << "%";

    ifstream myFile(
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            fileName);

    vector<vector<int>> oldGraph;


    string s;
    if (myFile.is_open()) {
        myFile >> n >> m;
        graph = vector<vector<int>>(n, vector<int>());
        oldGraph = vector<vector<int>>(n, vector<int>());
        visited = vector<bool>(n, false);
        labels = vector<bool>(n, false);
        inDegree = vector<int>(n, 0);

        int from, to;
        int maxDegree = 0;
        while (myFile >> from >> to) {
            oldGraph[from].push_back(to);
        }

        int X = n - (n * (float) graphCutValue / 100);
        for (int i = 0; i < X; i++) {
            int randomNum = rand() % n;
            labels[randomNum] = true;
            graph[randomNum] = oldGraph[randomNum];
            for (int j:graph[randomNum]) {
                inDegree[j] = inDegree[j] + 1;
                if (inDegree[j] > maxDegree) {
                    maxDegree = inDegree[j];
                }
                labels[j] = true;
            }
        }
        vector<vector<int>>().swap(oldGraph);
        myFile.close();
    }

    graphTranspose = constructTranspose(graph);
    visitMark = vector<int>(n);
    this->numberOfTargets = n;
    this->numberOfNonTargets = (int) nonTargets.size();
}

//********** Function for generating half graph ********
void Graph::readInfluencedHalfGraph(string fileName, float percentage, string convertedFile, int graphCutValue,
                                    std::ofstream &resultLogFile, bool fullgraph) {
    this->graphName = fileName;
    this->percentageTargets = percentage;
    cout << "\n Generating graph: " << 100 - graphCutValue << "%" << flush;
    ifstream myFile(convertedFile);
    vector<vector<int>> oldGraph;

    string s;
    if (myFile.is_open()) {
        if (fullgraph)
            myFile >> n >> m;
        else
            myFile >> n;
        graph = vector<vector<int>>(n, vector<int>());
        oldGraph = vector<vector<int>>(n, vector<int>());
        visited = vector<bool>(n, false);
        if (fullgraph)
            labels = vector<bool>(n, true);
        else {
            labels = vector<bool>(n, false);
        }
        inDegree = vector<int>(n, 0);

        int from, to;
        int maxDegree = 0;
        while (myFile >> from >> to) {
            if (from == -1 && to == -1) {
                break;
            }
            oldGraph[from].push_back(to);
        }

        int X = n - (n * (float) graphCutValue / 100);
        for (int i = 0; i < X; i++) {
            int randomNum = rand() % n;
            labels[randomNum] = true;
            graph[randomNum] = oldGraph[randomNum];
            for (int j:graph[randomNum]) {
                inDegree[j] = inDegree[j] + 1;
                if (inDegree[j] > maxDegree) {
                    maxDegree = inDegree[j];
                }
                labels[j] = true;
            }
        }
        vector<vector<int>>().swap(oldGraph);
        myFile.close();
    }

    graphTranspose = constructTranspose(graph);
    visitMark = vector<int>(n);
    this->numberOfTargets = n;
    this->numberOfNonTargets = (int) nonTargets.size();
}


vector<int> Graph::writeInfluencedGraph(string fileName, float percentage, string convertedFile, vector<int> *seedNodes,
                                        vector<int> *seedOrder) {
    this->graphName = fileName;
    this->percentageTargets = percentage;
    //cout << "\n Reading Reverse targets graph: ";
    unordered_set<int> activatedSet;
    ifstream myFile(convertedFile);
    string s;
    if (myFile.is_open()) {
        myFile >> n;
        graph = vector<vector<int>>(n, vector<int>());
        visited = vector<bool>(n, false);
        labels = vector<bool>(n, true);
        inDegree = vector<int>(n, 0);

        int from, to;
        int maxDegree = 0;

        while (myFile >> from >> to) {
            if (from == -1 && to == -1) {
                break;
            }
            graph[from].push_back(to);
            inDegree[to] = inDegree[to] + 1;
            if (inDegree[to] > maxDegree) {
                maxDegree = inDegree[to];
            }
            activatedSet.insert(from);
            activatedSet.insert(to);
        }
        if (seedNodes != NULL && seedOrder != NULL) {
            int str;
            int i = 0;
            while (myFile >> str) {
                if (str == -1)
                    break;
                (*seedNodes)[i] = str;
                i++;
            }
            //just to skip one more -1
            myFile >> str;
            i = 0;
            while (myFile >> str) {
                (*seedOrder)[i] = str;
                i++;
            }
        }
        myFile.close();
    }
    graphTranspose = constructTranspose(graph);
    visitMark = vector<int>(n);
    this->numberOfTargets = (int) activatedSet.size();
    this->numberOfNonTargets = (int) nonTargets.size();

    vector<int> activatedVector = vector<int>(activatedSet.size());
    int k = 0;
    for (int i:activatedSet) {
        activatedVector[k++] = i;
    }
    return activatedVector;
}


//********** Function only for the influenced graph ********
void Graph::readInfluencedGraph(string fileName, float percentage, vector<int> activatedSet) {
    this->graphName = fileName;
    this->percentageTargets = percentage;
    //cout << "\n Reading Reverse targets graph: ";

    ifstream myFile(
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            fileName);
    string s;
    if (myFile.is_open()) {
        myFile >> n >> m;
        graph = vector<vector<int>>(n, vector<int>());
        visited = vector<bool>(n, false);
        labels = vector<bool>(n, false);
        inDegree = vector<int>(n, 0);

        for (int i:activatedSet) {
            labels[i] = true;
        }

        int from, to;
        int maxDegree = 0;
        while (myFile >> from >> to) {
            graph[from].push_back(to);
            inDegree[to] = inDegree[to] + 1;
            if (inDegree[to] > maxDegree) {
                maxDegree = inDegree[to];
            }
        }
        myFile.close();
    }
    graphTranspose = constructTranspose(graph);
    visitMark = vector<int>(n);
    this->numberOfTargets = (int) activatedSet.size();
    this->numberOfNonTargets = (int) nonTargets.size();
}


void Graph::readGraph(string fileName, float percentage, std::ofstream &resultLogFile) {
    this->graphName = fileName;
    this->percentageTargets = percentage;
    cout << "\nReading all targets graph: " << endl;

    ifstream myFile(
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            fileName);
    string s;
    if (myFile.is_open()) {
        myFile >> n >> m;
        graph = vector<vector<int>>(n, vector<int>());
        visited = vector<bool>(n, false);
        labels = vector<bool>(n, true);
        inDegree = vector<int>(n, 0);

        int from, to;
        int maxDegree = 0;
        while (myFile >> from >> to) {
            graph[from].push_back(to);
            inDegree[to] = inDegree[to] + 1;
            if (inDegree[to] > maxDegree) {
                maxDegree = inDegree[to];
            }
        }
        myFile.close();
    }

    graphTranspose = constructTranspose(graph);
    visitMark = vector<int>(n);
    this->numberOfTargets = this->getNumberOfVertices();
    this->numberOfNonTargets = (int) nonTargets.size();
}

void Graph::writeGraphToFile(vector<vector<int>> inputGraph, string graphName, string path, int n, int m) {

    std::ofstream outfile(path + graphName);

    outfile << n << " " << m << endl;
    for (int i = 0; i < inputGraph.size(); i++) {
        for (int j = 0; j < inputGraph[i].size(); j++) {
            outfile << i << " " << inputGraph[i][j] << endl;
        }
    }
    outfile.close();
}


void Graph::readLabels(string fileName) {
    ifstream myFile(fileName);
    bool labelBool;
    if (myFile.is_open()) {
        int vertex;
        char label;
        while (myFile >> vertex >> label) {
            labelBool = (tolower(label) == 'a');
            labels[vertex] = labelBool;
            if (!labelBool) {
                nonTargets.push_back(vertex);
            }
        }
        myFile.close();
    }
    this->numberOfTargets = this->getNumberOfVertices() - (int) nonTargets.size();
    this->numberOfNonTargets = (int) nonTargets.size();
}

void Graph::writeLabels(std::ofstream &resultLogFile) {
    string s;
    stringstream stream;
    stream << fixed << setprecision(2) << this->percentageTargets;
    s = stream.str();
    string labelFileName =
            "C:\\Semester 3\\Thesis\\COPY_Changed_Path_Another_PrettyCode\\graphs\\" +
            this->graphName + "_" + s + "_labels.txt";

    ofstream myfile;
    string fileName = labelFileName;
    myfile.open(fileName);
    string targetLabel = "A";
    string nonTargetLabel = "B";
    for (int i = 0; i < this->n; i++) {
        if (this->labels[i]) {
            myfile << i << " " << targetLabel << "\n";
            cout << i << " " << targetLabel << "\n";
        } else {
            myfile << i << " " << nonTargetLabel << "\n";
            cout << i << " " << nonTargetLabel << "\n";
        }

    }
    myfile.close();
}

void Graph::setLabels(vector<bool> labels, float percentageTargets) {
    this->labels = labels;
    this->percentageTargets = percentageTargets;
}

int Graph::getNumberOfVertices() {
    return this->n;
}

int Graph::getNumberOfEdges() {
    return this->m;
}

int Graph::getNumberOfTargets() {
    return this->numberOfTargets;
}

int Graph::getNumberOfNonTargets() {
    return this->numberOfNonTargets;
}

vector<int> *Graph::getNonTargets() {
    return &this->nonTargets;
}

void Graph::UpdateAssociatedSetMatrix(int rrSetID) {
    //creation of associated set matrix

    pair<int, unordered_set<int>> node;

    for (int i = 0; i < nodeAS.size(); i++) {
        if (nodeAS[i].size() > 0) {
            for (int j:nodeAS[i]) {
                cout << "This is printed....." << endl;

                if (pairAssociatedSet[j].empty()) {
                    cout << "But this isn't....." << endl;
                    node = pair<int, unordered_set<int>>();
                    node.first = i;
                    node.second.insert(rrSetID);
                    pairAssociatedSet[j].insert(node);
                    coverage[j]++;
                } else {

                    cout << "Are we here? Did I get this backwards?" << endl;

                    std::unordered_map<int, unordered_set<int>>::iterator it = pairAssociatedSet[j].find(i);
                    if (it != pairAssociatedSet[j].end()) {
                        it->second.insert(rrSetID);
                        coverage[j]++;
                    } else {
                        node = pair<int, unordered_set<int>>();
                        node.first = i;
                        node.second.insert(rrSetID);
                        pairAssociatedSet[j].insert(node);
                        coverage[j]++;
                    }
                    //This line is not executed either!!!!!!!!
                    cout << "No, this is exited!" << endl;
                }
            }
            nodeAS[i].clear();
        }
    }
}

//********** Function only for the influenced graph ********
void
Graph::generateRandomRRSetsFromTargets(int R, vector<int> activatedSet, string modular, std::ofstream &resultLogFile) {
    clock_t begin = clock();
    visitMark = vector<int>(n);
    long totalSize = 0;
    timesThisNodeWasPicked = vector<int>(n, 0);

//    std::random_device rd; // obtain a random number from hardware
//    std::mt19937 eng(rd()); // seed the generator
//    std::uniform_int_distribution<> distr(0, n-1); // define the range

    this->rrSets = vector<vector<int>>();
    while (rrSets.size() < R) {
        rrSets.push_back(vector<int>());
    }
    //for mod influence
    if (modular == "modular") {
        NodeinRRsetsWithCounts = vector<int>(n, 0);
        if (activatedSet.size() == 0) {
            for (int i = 0; i < R; i++) {
                int randomVertex;
                randomVertex = rand() % n;
                while (!labels[randomVertex]) {
                    randomVertex = rand() % n;
                }
                generateRandomRRSetwithCountMod(randomVertex, i);
                totalSize += rrSets[i].size();
            }
        } else {
            int t = (int) activatedSet.size();
            for (int i = 0; i < R; i++) {
                int randomVertex;
                randomVertex = activatedSet[rand() % t];
                timesThisNodeWasPicked[randomVertex]++;
//                randomVertex = distr(eng);
                generateRandomRRSetwithCountMod(randomVertex, i);
                if (i == 10) cout << "Completed " << i << " RR Sets" << endl;
                if ((i % 100000) == 0) cout << "Completed " << i << " RR Sets" << endl;
                totalSize += rrSets[i].size();
            }
        }
    }
        //for submodular impact
    else if (modular == "submodular") {
        coverage = vector<int>(n, 0);
        pairAssociatedSet = vector<unordered_map<int, unordered_set<int>>>();
        nodeAS = vector<set<int>>(n);
        RRgraph = vector<vector<int>>(n);
        int t = (int) activatedSet.size();
        for (int i = 0; i < R; i++) {
            int randomVertex;
            randomVertex = activatedSet[rand() % t];
            generateRandomRRSetwithCount(randomVertex, i);
            totalSize += rrSets[i].size();
        }
    }
        //for modular Impact
    else {
        nodeAS = vector<set<int>>(n);
        //pairAssociatedSet=vector<unordered_map<int,unordered_set<int>>>(n);
        RRas = new RRassociatedGraph;
        alreadyVisited = vector<bool>(n, false);
        RRgraph = vector<vector<int>>(n);
        outdegree = vector<int>(n, n);
        dependancyVector = vector<vector<vector<int>>>(R);
        vertexToIndex = vector<unordered_map<int,int>>(R);
        indexToVertex = vector<vector<int>>(R);

        //Datastructures being used in the code:
        /* Datstructures:
         *
         * vertexToIndex: Stores the vector of unordered_maps which stores mapping of each vertex to an index
         * At index 10 of vertexToIndex is the mapping of RRSetId number 10
         * At index 10: inside the unordered_map
         * Trying to map - <int, int> => <24, 0> means that vertex 24 is mapped to index 0.
         *
         * indexToVertex: Stores a vector of vector<int>. Vector at index i corresponds to RRSetID i.
         * Inside RRSetID i bucket: each vector is -
         * Trying to map - index 0 contains 24 means that 0 corresponds to vertex 24
         *
         * dependancyVector: Stores an Array of Matrices.
         * Matrix at index i is the dependancyMatrix of RRSet number i
         * How to read them? Consider the following graph and Matrix:
         *  0 -> 1 -> 2 -> 3
         *
         * Dependence of reachability of 2 starting from 0 given that 1 has been removed is:
         *
         *   0  1 (2)  3
         * 0 1  1  1  1
         * 1 0  1  1  1
         * 2 0  0  1  1
         * 3 0  0  0  1
         *
         *
         * */

        modImpactTime = 0;
        coverage = vector<int>(n, 0);

        int t = (int) activatedSet.size();
        int doneRR = 1;
        for (int i = 0; i < R; i++) {
            int randomVertex;
            if (i == doneRR * 10000) {
                cout << "\n" << i << " " << flush;
                doneRR++;
            }
            randomVertex = activatedSet[rand() % t];
//            randomVertex = distr(eng);
            generateRandomRRSetwithRRgraphs(randomVertex, i);
            totalSize += rrSets[i].size();

        }
        totalNumNodesInRRSets = totalSize;
    }
    visitMark.clear();
    clock_t end = clock();

    double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
    cout << "\n Generated reverse: " << R << " RR sets" << endl;
    cout << "Elapsed time: " << elapsed_secs << endl;
    cout << " Time per RR Set is: " << elapsed_secs / R << endl;
    cout << "Total Size is: " << totalSize << endl;
    cout << "\n Average size is: " << (float) totalSize / (float) R;


    resultLogFile << "\n Generated reverse" << R << " RR sets\n";
    resultLogFile << "Elapsed time " << elapsed_secs;
    resultLogFile << " \n Time per RR Set is " << elapsed_secs / R;
    resultLogFile << "\n Total Size is " << totalSize << flush;
    resultLogFile << "\n Average size is " << (float) totalSize / (float) R;
}


//********** Function only for the influenced graph ********
void Graph::generateRandomRRSetwithRRgraphs(int randomVertex, int rrSetID) {
    q.clear();
    rrSets[rrSetID].push_back(randomVertex);
    q.push_back(randomVertex);
    int nVisitMark = 0;
    visitMark[nVisitMark++] = randomVertex;
    visited[randomVertex] = true;
    outdegree[randomVertex] = 0;

    while (!q.empty()) {
        int expand = q.front();
        q.pop_front();
        nodeAS[expand].insert(expand);

        clock_t startMOD = clock();
        //addSetintoASmatrix(expand, expand, rrSetID);
        //RRas->addEdge(expand, expand, rrSetID);
        clock_t endMOD = clock();
        modImpactTime += double(endMOD - startMOD);
        //coverage[expand]++;

        for (int j = 0; j < (int) graphTranspose[expand].size(); j++) {
            int v = graphTranspose[expand][j];
            if (!labels[v])
                continue;
            if (!this->flipCoinOnEdge(v, expand))
                continue;

            RRgraph[expand].push_back(v);
            if (visited[v]) {
                outdegree[v]++;
                continue;
            }

            if (!visited[v]) {
                outdegree[v] = 1;
                visitMark[nVisitMark++] = v;
                visited[v] = true;
            }
            q.push_back(v);
            rrSets[rrSetID].push_back(v);

        }
    }

//    BFSonRRgraphs(randomVertex, rrSetID);//THE method
    calcDependancyMatrix(randomVertex, rrSetID, rrSets[rrSetID].size());

    for (int i = 0; i < nVisitMark; i++){
        visited[visitMark[i]] = false;
        alreadyVisited[visitMark[i]] = false;
        nodeAS[visitMark[i]].clear();
        vector<int>().swap(RRgraph[visitMark[i]]);
        outdegree[visitMark[i]] = n;
    }

}

void Graph::calcDependancyMatrix(int randomVertex, int rrSetID, int rrSetSize) {

    bool tshoot = false;//Prints shit ton of data

    //Trying to map - <int, int> => <24, 0> means that 24 is mapped to 0.
    if(tshoot){
        cout << "Printing mappedIndex" << endl;
    }
    unordered_map<int, int> mappedIndex;
    for(int i = 0; i < rrSetSize; i++){
        mappedIndex.insert(make_pair(rrSets[rrSetID][i], i));
        if(tshoot){
            cout << rrSets[rrSetID][i] << " mapped to " << i << endl;
        }
    }
    vertexToIndex.at(rrSetID) = mappedIndex;

    //Trying to map - index 0 contains 24 means that 0 corresponds to vertex 24
    if(tshoot){
        cout << "Printing revMappedIndex" << endl;
    }
    vector<int> revMappedIndex = vector<int>(rrSetSize);
    for(int i = 0; i < rrSetSize; i++){
        revMappedIndex.at(i) = rrSets[rrSetID][i];
        if(tshoot){
            cout << i << " reverse mapped to " << rrSets[rrSetID][i] << endl;
        }
    }
    indexToVertex.at(rrSetID) = revMappedIndex;

    //Creating the miniRRGraph containing these mapped vertices from the original RRGraph
    vector<vector<int>> miniRRGraph = vector<vector<int>>(); //Just this wouldnt do.
    for(int i = 0; i < rrSetSize; i++){
        miniRRGraph.emplace_back(vector<int>());
    }
    for(int i = 0; i < RRgraph.size(); i++){
        for (int j = 0; j < RRgraph[i].size(); j++){
            int fromVertex = mappedIndex.at(i);
            int toVertex = mappedIndex.at(RRgraph[i][j]);
            miniRRGraph[fromVertex].push_back(toVertex);
        }
    }

    if(tshoot){
        cout << "Printing miniRRGraph: " << endl;
        print2DVector(miniRRGraph);
    }

    //Stores the dependsOn relation in each RRSet generation
    dependancyMatrix = vector<vector<int>> (rrSetSize,vector<int>(rrSetSize, 1));//Initialize matrix to contain all 1s initially
    for(int i = 0; i < rrSetSize; i++){//for every vertex u in the RRGraph
        int vertexRemoved = mappedIndex.at(rrSets[rrSetID][i]);
        if(vertexRemoved != mappedIndex.at(randomVertex)){//if u != randomVertex
            vector<vector<int>> myGraph = miniRRGraph;
            myGraph[vertexRemoved].clear();//Remove u and all its outgoing edges from the graph
            BFS(myGraph, mappedIndex.at(randomVertex), rrSetSize, vertexRemoved);//Do a BFS on the resulting graph starting from the randomVertex
        }
    }

    dependancyVector.at(rrSetID) = dependancyMatrix;
    /*  Freeing up the memory
     * In C++ there is a very simple rule of thumb:
     * All memory is automatically freed when it runs out of scope unless it has been allocated manually.


//    vector<vector<int>>().swap(dependancyMatrix);
//    vector<vector<int>>().swap(miniRRGraph);
//    vector<int>().swap(revMappedIndex);
//    unordered_map<int, int>().swap(mappedIndex);
     */
}

//myGraph is the graph on which you want to perform the BFS.
//All the outgoing edges from the removedVertex have been removed in this graph
//startVertex is the vertex from which you want to start the BFS
void Graph::BFS(vector<vector<int>> &myGraph, int startVertex, int rrSetSize, int vertexRemoved){

    vector<bool> visitedBFS = vector<bool>(rrSetSize, false);       //Mark all the vertices as not visited
    deque<int> queue;                                               //Create a queue for BFS
    visitedBFS[startVertex] = true;                                 //Mark the current node as visited
    queue.push_back(startVertex);                                   //And add it to the queue
    dependancyMatrix[vertexRemoved][startVertex] = 0;

    while(!queue.empty()){
        int u = queue.front();
        queue.pop_front();
        for (int i = 0; i < myGraph[u].size(); i++){
            int v = myGraph[u][i];
            if(!visitedBFS[v]){
                visitedBFS[v] = true;
                queue.push_back(v);
                if(vertexRemoved != v){//Because reachability of vertexRemoved will depend on itself
                    dependancyMatrix[vertexRemoved][v] = 0;//Since v was still reachable after removing vertexRemoved.
                }
            }
        }
    }
}

void Graph::BFSonRRgraphs(int randomVertex, int rrSetID) {

    workQueue.push(pair<int, int>(randomVertex, outdegree[randomVertex]));

    while (!workQueue.empty()) {
        int expand = workQueue.top().first;
        workQueue.pop();

        for (int v:RRgraph[expand]) {
            if (!alreadyVisited[v]) {
                outdegree[v]--;
                alreadyVisited[v] = true;
                workQueue.push(pair<int, int>(v, outdegree[v]));

                //Defining the dependsOn relationship
                for (int i:nodeAS[expand]) {
                    nodeAS[v].insert(i);
                    if (i != v) {
                        clock_t startMOD = clock();
                        RRas->addEdge(i, v, rrSetID);
                        coverage[i]++;

                        clock_t endMOD = clock();
                        modImpactTime += double(endMOD - startMOD);
                    }
                }
            } else {
                vector<int> symDifference;
                set_symmetric_difference(nodeAS[v].begin(), nodeAS[v].end(), nodeAS[expand].begin(),
                                         nodeAS[expand].end(), inserter(symDifference, symDifference.begin()));
                deque<pair<int, int>> store;
                while (!workQueue.empty()) {
                    pair<int, int> x = workQueue.top();
                    int temp = workQueue.top().first;
                    workQueue.pop();

                    if (temp == v) {
                        outdegree[v]--;
                        workQueue.push(pair<int, int>(v, outdegree[v]));
                        break;
                    }
                    store.push_front(x);
                }
                while (!store.empty()) {
                    workQueue.push(store.front());
                    store.pop_front();
                }
                for (int i:symDifference) {
                    if (i != v && i != expand) {
                        int e;
                        if (nodeAS[v].count(i) == 1) {
                            e = v;
                            nodeAS[v].erase(i);
                        } else {
                            e = expand;
                            nodeAS[expand].erase(i);
                        }

                        clock_t startMOD = clock();
                        RRas->removeEdge(i, e, rrSetID);
                        coverage[i]--;
                        clock_t endMOD = clock();
                        modImpactTime += double(endMOD - startMOD);
                    }
                }
            }
        }
    }
}


//********** Function only for the influenced graph with modular property********
void Graph::generateRandomRRSetwithCountMod(int randomVertex, int rrSetID) {
    NodeinRRsetsWithCounts[randomVertex]++;
    q.clear();
    rrSets[rrSetID].push_back(randomVertex);
    q.push_back(randomVertex);
    int nVisitMark = 0;
    visitMark[nVisitMark++] = randomVertex;
    visited[randomVertex] = true;
    while (!q.empty()) {
        int expand = q.front();
        q.pop_front();
        for (int j = 0; j < (int) graphTranspose[expand].size(); j++) {
            int v = graphTranspose[expand][j];
            if (!labels[v])
                continue;
            if (!this->flipCoinOnEdge(v, expand))
                continue;
            if (visited[v])
                continue;
            if (!visited[v]) {
                visitMark[nVisitMark++] = v;
                visited[v] = true;
            }
            q.push_back(v);
            rrSets[rrSetID].push_back(v);

            NodeinRRsetsWithCounts[v]++;
        }
    }
    for (int i = 0; i < nVisitMark; i++) {
        visited[visitMark[i]] = false;
    }
}

//********** Function only for the influenced graph ********
void Graph::generateRandomRRSetwithCount(int randomVertex, int rrSetID) {

    pair<int, unordered_set<int>> node;

    q.clear();
    rrSets[rrSetID].push_back(randomVertex);
    q.push_back(randomVertex);
    int nVisitMark = 0;
    visitMark[nVisitMark++] = randomVertex;
    visited[randomVertex] = true;
    while (!q.empty()) {
        int expand = q.front();
        nodeAS[expand].insert(expand);
        coverage[expand]++;
        q.pop_front();
        for (int j = 0; j < (int) graphTranspose[expand].size(); j++) {
            int v = graphTranspose[expand][j];
            if (!labels[v])
                continue;
            if (!this->flipCoinOnEdge(v, expand))
                continue;

            RRgraph[expand].push_back(v);
            if (visited[v]) {
                //find difference here
                /*std::vector<int> intersect;
               std::sort(nodeAS[expand].begin(), nodeAS[expand].end());
               std::sort(nodeAS[v].begin(), nodeAS[v].end());
               std::set_intersection(nodeAS[v].begin(), nodeAS[v].end(),nodeAS[expand].begin(), nodeAS[expand].end(),std::back_inserter(intersect));
              nodeAS[v]=intersect;
               nodeAS[v].push_back(v);
               nodeAS[expand]=intersect;
               nodeAS[expand].push_back(expand);
               deque<int> qu;
               qu.push_back(v);
               while(!qu.empty()){
                   int explore=qu.front();
                   qu.pop_front();
                   for(int i:RRgraph[explore]){
                       qu.push_back(i);
                       nodeAS[i]=intersect;
                       nodeAS[i].push_back(i);
                   }
               }*/
                continue;
            }

            if (!visited[v]) {
                visitMark[nVisitMark++] = v;
                visited[v] = true;

            }
            q.push_back(v);
            rrSets[rrSetID].push_back(v);

            //nodeAS[v].insert(nodeAS[v].end(), nodeAS[expand].begin(),nodeAS[expand].end());
        }
    }
    for (int i = 0; i < nVisitMark; i++) {
        visited[visitMark[i]] = false;
        vector<int>().swap(RRgraph[visitMark[i]]);
    }

    UpdateAssociatedSetMatrix(rrSetID);
}


void Graph::generateRandomRRSets(int R, bool label, std::ofstream &resultLogFile) {

    this->rrSets = vector<vector<int>>();
    long totalSize = 0;
    clock_t begin = clock();
    while (rrSets.size() < R) {
        rrSets.push_back(vector<int>());
    }
    //to do... random RR sets from activated nodes in Influenced graph

//    std::random_device rd; // obtain a random number from hardware
//    std::mt19937 eng(rd()); // seed the generator
//    std::uniform_int_distribution<> distr(0, n-1); // define the range

    for (int i = 0; i < R; i++) {
        int randomVertex;
        randomVertex = rand() % n;
//        randomVertex = distr(eng);
        while (!labels[randomVertex]) {
            randomVertex = rand() % n;
        }
        if (label) {
            generateRandomRRSet(randomVertex, i);
        } else
            generateRandomRRSetwithCount(randomVertex, i);
        totalSize += rrSets[i].size();
    }
    clock_t end = clock();
    double elapsed_secs = double(end - begin) / CLOCKS_PER_SEC;
    cout << "\n Generated " << R << " RR sets\n";
    cout << "Elapsed time " << elapsed_secs;
    cout << " \n Time per RR Set is " << elapsed_secs / R;
    cout << "\n Total Size is " << totalSize;
    cout << "\n Average size is " << (float) totalSize / (float) R;

    resultLogFile << "\n Generated " << R << " RR sets\n";
    resultLogFile << "Elapsed time " << elapsed_secs;
    resultLogFile << " \n Time per RR Set is " << elapsed_secs / R;
    resultLogFile << "\n Total Size is " << totalSize;
    resultLogFile << "\n Average size is " << (float) totalSize / (float) R;
}

vector<vector<int>> *Graph::getRandomRRSets() {
    return &rrSets;
}

void Graph::clearRandomRRSets() {
    rrSets.clear();
}

vector<int> Graph::generateRandomRRSet(int randomVertex, int rrSetID) {
    q.clear();
    rrSets[rrSetID].push_back(randomVertex);
    q.push_back(randomVertex);
    int nVisitMark = 0;
    visitMark[nVisitMark++] = randomVertex;
    visited[randomVertex] = true;
    while (!q.empty()) {
        int expand = q.front();
        q.pop_front();
        for (int j = 0; j < (int) graphTranspose[expand].size(); j++) {
            int v = graphTranspose[expand][j];
            if (!labels[v])
                continue;
            if (!this->flipCoinOnEdge(v, expand))
                continue;
            if (visited[v])
                continue;
            if (!visited[v]) {
                visitMark[nVisitMark++] = v;
                visited[v] = true;
            }
            q.push_back(v);
            rrSets[rrSetID].push_back(v);
        }
    }
    for (int i = 0; i < nVisitMark; i++) {
        visited[visitMark[i]] = false;
    }
    return rrSets[rrSetID];
}

vector<vector<int>> Graph::constructTranspose(vector<vector<int>> someGraph) {
    vector<vector<int>> transposedGraph = vector<vector<int>>();
    for (int i = 0; i < someGraph.size(); i++) {
        transposedGraph.push_back(vector<int>());
    }
    for (int i = 0; i < someGraph.size(); i++) {
        for (int v:someGraph[i]) {
            transposedGraph[v].push_back(i);
        }
    }
    return transposedGraph;
}

void Graph::assertTransposeIsCorrect() {
    assert(graph.size() == n);
    int edges = 0;

    for (int i = 0; i < n; i++) {
        edges += graph[i].size();
    }
    assert(edges == m);
    int edgeCount = 0;
    int reverseEdgeCount = 0;
    for (int i = 0; i < n; i++) {
        int u = i;
        for (int j = 0; j < graph[u].size(); j++) {
            edgeCount++;
            int v = graph[u][j];
            bool reverseEdgePresent = false;
            vector<int> reverseEdges = graphTranspose[v];
            for (int uPrime:reverseEdges) {
                if (uPrime == u) {
                    reverseEdgeCount++;
                    reverseEdgePresent = true;
                }
            }
            assert(reverseEdgePresent);
        }

    }
    assert(edgeCount == reverseEdgeCount);
    assert(edgeCount == m);

}

//vertex is the vertex that was removed in this iteration of the loop
void Graph::assertCorrectNodesAreDeleted(int vertex, int numOfEdgesToDelete, int totalEdgesInOrigGraphPre,
                                         int totalEdgesInTransGraphPre) {

    assert(("Failed: TransGraph Size is not n", graphTranspose.size() == n));
    assert(("Failed: OrigGraph Size is not n", graph.size() == n));

    int totalEdgesInOrigGraphPost = 0;
    int totalEdgesInTransGraphPost = 0;

    for (int i = 0; i < graphTranspose.size(); i++) {
        //Assert that the removed vertex is not an outgoing edge to any vertex
        assert(("Failed: Node not deleted in TransGraph",
                count(graphTranspose[i].begin(), graphTranspose[i].end(), vertex) == 0));
        totalEdgesInTransGraphPost += graphTranspose[i].size();
    }

    assert(("Failed: Mismatch in Edges deleted in TransGraph", totalEdgesInTransGraphPre - totalEdgesInTransGraphPost ==
                                                               numOfEdgesToDelete));

    for (int i = 0; i < graph.size(); i++) {
        //Assert that the removed vertex is not an outgoing edge to any vertex
        assert(("Failed: Node not deleted in OrigGraph", count(graph[i].begin(), graph[i].end(), vertex) == 0));
        totalEdgesInOrigGraphPost += graph[i].size();
    }
    assert(("Failed: Mismatch in Edges deleted in OrigGraph", totalEdgesInOrigGraphPre - totalEdgesInOrigGraphPost ==
                                                              numOfEdgesToDelete));
}


vector<int> Graph::oldRRSetGeneration(int randomVertex, int rrSetID) {
    //Most of this code is used from the source code of TIM - Influence Maximization: Near-Optimal Time Complexity Meets Practical Efficiency by Tang et al.
    // Source code - https://sourceforge.net/projects/timplus/
    // License GNU GENERAL PUBLIC LICENSE Version 3

    int n_visit_edge = 0;
    int uStart = randomVertex;
    int hyperiiid = rrSetID;

    int n_visit_mark = 0;
    q.clear();
    q.push_back(uStart);
    rrSets[hyperiiid].push_back(uStart);
    visitMark[n_visit_mark++] = uStart;
    visited[uStart] = true;
    while (!q.empty()) {
        int expand = q.front();
        q.pop_front();
        int i = expand;
        for (int j = 0; j < (int) graphTranspose[i].size(); j++) {
            int v = graphTranspose[i][j];
            n_visit_edge++;
            int randDouble = rand() % (int) (inDegree[i]);
            //     continue;
            if (randDouble != 0)
                continue;
            if (visited[v])
                continue;
            if (!visited[v]) {
                assert(n_visit_mark < n);
                visitMark[n_visit_mark++] = v;
                visited[v] = true;
            }
            q.push_back(v);
            assert((int) rrSets.size() > hyperiiid);
            rrSets[hyperiiid].push_back(v);
        }

    }
    for (int i = 0; i < n_visit_mark; i++)
        visited[visitMark[i]] = false;
    return rrSets[hyperiiid];
}

void Graph::removeOutgoingEdges(int vertex) {

    bool tshoot = false;

    inDegree[vertex] = 0;
    labels[vertex] = false;
    vector<int> outgoingNodes = vector<int>();
    outgoingNodes = graph[vertex];

    for (int i:outgoingNodes) {
        vector<int> outgoingEdges = vector<int>();
        vector<int> incomingEdges = vector<int>();
        for (int j:graphTranspose[i]) {
            if (j != vertex)
                outgoingEdges.push_back(j);
        }
        graphTranspose[i] = outgoingEdges;

        for (int j:graph[i]) {
            if (j != vertex)
                incomingEdges.push_back(j);
        }
        graph[i] = incomingEdges;
    }
    graph[vertex] = vector<int>();


    vector<int> incomingNodes = vector<int>();
    incomingNodes = graphTranspose[vertex];

    for (int i:incomingNodes) {
        vector<int> outgoingEdges = vector<int>();
        vector<int> incomingEdges = vector<int>();
        for (int j:graph[i]) {
            if (j != vertex)
                outgoingEdges.push_back(j);
        }
        graph[i] = outgoingEdges;

        for (int j:graphTranspose[i]) {
            if (j != vertex)
                incomingEdges.push_back(j);
        }
        graphTranspose[i] = incomingEdges;
    }
    graphTranspose[vertex] = vector<int>();

    if (tshoot) {
        cout << "Printing the graph after removing vertex: " << vertex << endl;
        print2DVector(graph);
        cout << "Printing the transposedGraph after removing vertex: " << vertex << endl;
        print2DVector(graphTranspose);
    }
}

void Graph::removeNodeFromRRset(int vertex) {
    for (pair<int, unordered_set<int>> RRpair : pairAssociatedSet[vertex]) {
        if (RRpair.second.size() > 0) {
            for (int RRi:RRpair.second) {
                for (int j:rrSets[RRi]) {
                    std::unordered_map<int, unordered_set<int>>::iterator it = pairAssociatedSet[j].find(RRpair.first);
                    if (it != pairAssociatedSet[j].end() && it->second.count(RRi) == 1) {
                        it->second.erase(RRi);
                        coverage[j]--;
                    }
                }
            }
        }
    }
    pairAssociatedSet[vertex].clear();
    coverage[vertex] = 0;
}

void Graph::removeVertexFromRRassociatedGraph(int v) {

    bool tshoot = false;
    int edgesDeleted = 0;

    vertex *node = RRas->vertexMap.at(v); //node to be deleted

    if(tshoot){
        cout << "Outdegree of node to be deleted: " << node->outDegree << endl;
    }
    outdegreeReducedFor = vector<int>(n,0);

    for (Edge *outEdges : node->getoutGoingEdges()) { //all outgoing edges of the node
        if (outEdges->rrids.size() > 0) {
            for (int RRi:outEdges->rrids) { //all the rrids from the edge
                for (int j:rrSets[RRi]) { // all the nodes associated with that rrid
                    if (RRas->vertexMap.count(j) == 1) {
                        vertex *ASnode = RRas->vertexMap.at(j);
                        string eid;
                        eid = to_string(ASnode->getId());
                        //bug
//                        eid += to_string(outEdges->destid); //making edge id from source and destination vertex

                        eid = eid + "-" + to_string(outEdges->destid);//Correction to possible bug?

                        if (eid != outEdges->getId()) {
                            //auto it is an iterator
                            auto it = RRas->EdgeMap.find(eid); //find that edge from edgeMap
                            if (it != RRas->EdgeMap.end() && it->second->rrids.count(RRi) == 1) {
                                it->second->rrids.erase(RRi);// remove rrid from the set
                                if(tshoot){
                                    outdegreeReducedFor[ASnode->id]++;
                                    edgesDeleted++;
                                }
                                ASnode->outDegree--;
                            }
                        }
                    }
                }
            }
            outEdges->rrids.clear();
        }
    }
    node->outDegree = 0;

    if(tshoot){
        cout << "Total outdegree reduced by:" << edgesDeleted << endl;
        cout << "Printing outdegreeReducedFor: " << endl;
        printVector(outdegreeReducedFor);
    }
}

/*
    cout<<"node"<<node->getId()<<"outdegree"<<node->outDegree<<"\n";
    clock_t start1=clock();
    int testtimed1=0;
    int testtimed2=0;
    int testtimed3=0;
    for ( Edge* outEdges : node->getoutGoingEdges() ){
        if(outEdges->rrids.size()>0){
            
            vertex* ASnode = RRas->vertexMap.at(outEdges->destid);
            
            for(Edge* inEdges:ASnode->getinComingEdges()){
                if(inEdges->rrids.size()>0){
                    if(outEdges!=inEdges){
                        clock_t start3=clock();
                        std::vector<int> difference;
                        std::set_difference (inEdges->rrids.begin(),inEdges->rrids.end(),outEdges->rrids.begin(),outEdges->rrids.end(), std::back_inserter(difference));
                        clock_t end3=clock();
                        testtimed3+= double(end3 - start3);
                        
                        vertex* INnode=RRas->vertexMap.at(inEdges->sourceid);
                        INnode->outDegree-= (inEdges->rrids.size()-difference.size());
                        clock_t start=clock();
                        inEdges->rrids.insert(difference.begin(),difference.end());
                        clock_t end = clock();
                        testtimed2+= double(end - start);
                    }
                }
            }
        }
    }
    clock_t end1 = clock();
    testtimed1+=double(end1 - start1);
    node->deleteOutBoundNeighbour();
    cout << "\n"<< "test time 1 " << double(testtimed1)/ (CLOCKS_PER_SEC*60);
    cout << "test time 2 " << double(testtimed2)/ (CLOCKS_PER_SEC*60);
    cout << "test time 3 " << double(testtimed3)/ (CLOCKS_PER_SEC*60)<<"\n";
}*/

void Graph::removeSetFromASmatrix(int row, int vertex, int rrSetID) {
    std::unordered_map<int, unordered_set<int>>::iterator it = pairAssociatedSet[row].find(vertex);
    if (it != pairAssociatedSet[row].end()) {
        it->second.erase(rrSetID);
    }
}

void Graph::addSetintoASmatrix(int row, int vertex, int rrSetID) {
    pair<int, unordered_set<int>> node;
    if (pairAssociatedSet[row].empty()) {
        node = pair<int, unordered_set<int>>();
        node.first = vertex;
        node.second.insert(rrSetID);
        pairAssociatedSet[row].insert(node);
    } else {
        std::unordered_map<int, unordered_set<int>>::iterator it = pairAssociatedSet[row].find(vertex);
        if (it != pairAssociatedSet[row].end()) {
            it->second.insert(rrSetID);
        } else {
            node = pair<int, unordered_set<int>>();
            node.first = vertex;
            node.second.insert(rrSetID);
            pairAssociatedSet[row].insert(node);
        }
    }
}

void Graph::print2DVector(const vector<vector<int>> myVector) {

    for (int i = 0; i < myVector.size(); i++) {
        if (myVector[i].size() > 0) {
            cout << i << " ---> ";
            for (int j = 0; j < myVector[i].size(); j++) {
                cout << myVector[i][j] << " -- ";
            }
            cout << endl;
        }
    }
    cout << "-----Completed Printing 2D Vector----" << endl;
}

void Graph::printVector(const vector<int> myVector) {

    for (int i = 0; i < myVector.size(); i++) {

        if(myVector[i] > 0){
            cout << i <<": "<< myVector[i] << endl;
        }
    }
    cout << endl;
    cout << "-----Completed Printing Vector----" << endl;
}






