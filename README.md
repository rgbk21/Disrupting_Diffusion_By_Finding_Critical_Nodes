# Disrupting Diffusion: Critical Nodes in Network

We formulate and study the problem of identifying nodes whose absence can maximally disrupt network-diffusion under independent cascade model. We refer to such nodes as critical nodes. We present the notion of impact and characterize critical nodes based on this notion. Informally, impact of a set of nodes quantifies the necessity of the nodes in the diffusion process. We prove that the impact is monotonic. Interestingly, unlike similar formulation of critical edges in the context of Linear Threshold diffusion model, impact is neither submodular nor supermodular. Hence, we develop heuristics that rely on greedy strategy and modular or submodular approximations of impact function. We empirically evaluate our heuristics by comparing the level of disruption achieved by identifying and removing critical nodes as opposed to that acheived by removing the most influential nodes.

## How to Compile and run
We recommend using GCC 4.9 and greater.

Store the graph file/labels file in the graphs folder. The graph file has the following format:
```
	First line: <number of nodes> <number of edges>
	From second line: <from node> <to node>
```
Update the paths for the graph folder, results folder, and the ResultData folder in the code. These paths need to be updated in the Graph.cpp and main.cpp files.

Set the following Parameters:

Keep these unchanged:
```
algorithm - "timtim"
fullgraph - true ( or false to create the influenced graph for the program)
Diffusion - 0 (Algorithm of one simulation to get the influenced graph)
newSeedset - 5 (to get the new Seed set to calculate the imapct of critical nodes in all three approaches.)
modularity - modular2
seedset - 0 (selecting best seed to get the influenced graph)
percentage - The percentage of targets. 100 i.e. all nodes are Targets
threshold - 10
```
Change these as per requirements: 
```
graph - name of the graph you want to run the code on
budget - Set the seed set size
nodesRemove - number of nodes to be removed (the critical nodes)
```
Example command:
```
./influence --algorithm timtim --fullgraph true --Diffusion 0 --newSeedset 5 --modularity modular2  --seedset 0 --percentage 100 --threshold 10  --graph ca-GrQc-processed.txt --budget 10  --nodesRemove 5
```

## Versions of the Algorithm
There are 2 versions of the algorithm:

Version 1) Finding the critical nodes in the given graph when no seed set context has been provided

Version 2) Finding the critical nodes in the given graph when seed set has been provided

Version 1 of the algorithm is present in the branch: <i>CodeContaining_topCrit_WithoutAnySeedSetContextGiven_Exp2</i> 

When running this version of the algorithm, make sure to set the parameter <i>budget</i> to 0. Change the <i>nodesRemove</i> parameter to control how many critical nodes to you want to find in the network.

## Download Graph Data
The graphs that we have used, along with labels file can be found in "graphs" folder of the code. If you want to use another graph file then place the file in graphs folder before running the program.

## Results
Results file will get created after every execution and can be found in results folder (if budget, graph name, nodeRemove are same then the program will append the exsisting file instead of generating new file). Log file will also get created and can be found in ResultsData folder.


