# Disrupting Diffusion: Critical Nodes in Network

We formulate and study the problem of identifying nodes whose absence can maximally disrupt network-diffusion under independent cascade model. We refer to such nodes as critical nodes. We present the notion of impact and characterize critical nodes based on this notion. Informally, impact of a set of nodes quantifies the necessity of the nodes in the diffusion process. We prove that the impact is monotonic. Interestingly, unlike similar formulation of critical edges in the context of Linear Threshold diffusion model, impact is neither submodular nor supermodular. Hence, we develop heuristics that rely on greedy strategy and modular or submodular approximations of impact function. We empirically evaluate our heuristics by comparing the level of disruption achieved by identifying and removing critical nodes as opposed to that acheived by removing the most influential nodes.

## Code Structure
### executeTIMTIM
This is the implementation to create the influenced graph by using two strategies:
```
executeTIMTIM(result)
```
```
1. 20,000 simulations on the graph using best seed set
2. One diffusion using the best seed set
```
If the influenced file is already present in "graphs" folder, it will use the created one otherwise it will create the new influenced file represented as:
```
convertedFile="graphs/"+graphFileName+"_converted"+"_"+to_string(budget)+"_"+to_string(probability)
```
### executeTIMTIMfullGraph  
This is the implementation where complete graph is used as influenced graph.
```
executeTIMTIMfullGraph(result);
```
### Graph.cpp 
This includes the implementation of computation of Impact through Random reachability
```
function - generateRandomRRSetsFromTargets()
```
### SeedSet.cpp 
This implementation contains different approaches of selecting the seed set based on random selection, degree, best seed through random reachability. 

## How to Compile
We recommend using GCC 4.9 and greater.

Set the compiler path for CXX in Makefile
Make the influence target:
make influence
This will make an executable named "influence".


Store the graph file/labels file in the graphs folder. The graph file has the following format:
```
	First line: <number of node> <number of edges>
	From second line: <from node> <to node>
```
Set the following Parameters:
```
algorithm - "timtim"
fullgraph - true ( or false to create the influenced graph for the program)
seedset - 0 (selecting best seed to get the influenced graph)
Diffusion - 0 (Algorithm of one simulation to get the influenced graph)
percentage - The percentage of targets. 100 i.e. all nodes are Targets
budget - Set the seed set size
nodesRemove - number of nodes to be removed (the critical nodes)
newSeedset -  to get the new Seed set to calculate the imapct of critical nodes in all three approaches.
```
Example command:
```
./influence --algorithm timtim --fullgraph true --Diffusion 0 --newSeedset 5 --modularity modular2 --graph ca-GrQc-processed.txt --seedset 0 --budget 10 --percentage 100 --threshold 10 --nodesRemove 5 
```
## Download Graph Data
The graphs that we have used, along with labels file can be found in "graphs" folder of the code. If you want to use another graph file then place the file in graphs folder before running the program.

## Results
Results file will get created after every execution and can be found in results folder (if budget, graph name, nodeRemove are same then the program will append the exsisting file instead of generating new file). Log file will also get created and can be found in ResultsData folder.


