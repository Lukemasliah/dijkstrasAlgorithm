#include <iostream>
#include <fstream>
#include <string>
#include <math.h>

using namespace std;

//--------------------------------------------//
//	CSCI203 - Data and Algorithms
//	Assignment 3
//	
//	ID:6273464 - Luke Masliah
//--------------------------------------------//

struct Vertice {
	// Coordinates
	int x;
	int y;

	Vertice(int _x, int _y)
		: x(_x), y(_y) {}
};

struct MinPos {
	int index;
	int weight;

	MinPos(int _index, int _weight)
		: index(_index), weight(_weight) {}
	MinPos() {};
};

struct SupportNodeHeap {
	MinPos* heap;
	int capacity;
	int crntSize;

	SupportNodeHeap(int cap)
	{
		crntSize = 0;
		capacity = cap;
		heap = new MinPos[cap];
	}

	int getParent(int i) { return (i - 1) / 2; }

	void swap(MinPos &pos1, MinPos &pos2)
	{
		MinPos temp = pos1;
		pos1 = pos2;
		pos2 = temp;
	}

	int getRoot()
	{
		if (crntSize <= 0)
			return -1;

		return heap[0].index;
	}

	void insert(MinPos val)
	{ 
		if (crntSize == capacity)
		{
			cout << "\nHeap has reached max capacity, could not insert value: " << val.weight << endl;
			return;
		}

		// Insert new value
		crntSize++;
		int rear = crntSize - 1;
		heap[rear] = val;

		// minHeapify new val
		while (rear != 0 && heap[getParent(rear)].weight > heap[rear].weight)
		{
			swap(heap[rear], heap[getParent(rear)]);
			rear = getParent(rear);
		}
	}
};

char intToAscii(int num)
{
	char asc = num + 97;
	return asc;
}

int asciiToInt(char c) { return ((int)c - 97); }

// Globals
static const int maxVertices = 20;
Vertice* vp[maxVertices];	// Array of Nodes
int weightMatrix[maxVertices*maxVertices] = { 0 };
int dist[maxVertices];	// holds shortest distance from source to i
int memDist[maxVertices];
int memoization[maxVertices] = {-1};
int verticesVisited;
int start;
int goal;
int pathWeight; // Keeps track of current path weight


void displayWeights()
{
	cout << "\nDisplay Weights for first 5 Vertices" << endl;
	cout << "----------------------------------------" << endl;
	for (int i = 0; i < 5; i++)
	{
		cout << intToAscii(i) << ":  ";
		for (int p = 0; p < maxVertices; p++)
		{
			if (weightMatrix[(i*maxVertices) + p] != 0)
				cout << intToAscii(p) << "(" << weightMatrix[(i*maxVertices) + p] << ")  ";
		}
		cout << endl;
	}
}

double calcEuclidianDistance(Vertice &v1, Vertice &v2)
{
	double distx = (v1.x - v2.x);
	double disty = (v1.y - v2.y);
	return sqrt((distx*distx) + (disty*disty));
}

// finds the vertex with minimum distance from the support set
int minDistance(bool aStar, bool supportSet[])
{
	int min = INT_MAX;
	SupportNodeHeap minHeap(maxVertices);	// record index w/ weight as object
	
	for(int i = 0; i < maxVertices; i++)
	{
		int distance = dist[i];
		if (aStar)
			distance += calcEuclidianDistance(*vp[i], *vp[goal]);

		if(supportSet[i] == false && distance <= min)
		{
			min = distance;
			MinPos minPos(i, distance);
			minHeap.insert(minPos);
		}		
	}
	return minHeap.getRoot();
}

void calcGoalPath(int goalPath[maxVertices], int path[maxVertices])
{
	int next = goal;	// Variable contains next vertex in path
	
	for(int i = 0; i < maxVertices; i++)	// intialize goalPath
		goalPath[i] = -1;
	
	// Create goalPath
	while(next != start)
	{
		goalPath[next] = path[next];
		next = path[next];
	}
}

void displayGoalPath(int goalPath[maxVertices])
{	
	for(int i = 0; i < maxVertices; i++)
	{
		if(goalPath[i] != -1)
		{
			cout << intToAscii(goalPath[i]) << " --> ";
		}
	}
	cout << intToAscii(goal) << endl;	// Add goal vertex to print
}

void Dijkstra(bool aStar, int path[maxVertices])
{
	bool visited[maxVertices]; 	// true if vertex i is included in path or if shortest distance from source to i is finalized
	verticesVisited = 1;	// Reset vertices counter, per search, counts starting node in search.

	for(int i = 0; i < maxVertices; i++)	// Initialise arrays
	{
		dist[i] = INT_MAX;
		visited[i] = false;
		path[i] = -1;
	}
	dist[start] = 0; 		// distance from source vertex to itself

	// Find shortest path
	for(int i = 0; i < maxVertices - 1; i++)
	{
		if (visited[goal] == true)	// Finish searching once the goal has been reached
			break;
			
		// Insert memoized data using for-loop counter where available
		if(memoization[i] != -1 && weightMatrix[(i*maxVertices) + memoization[i]] != 0)
		{
			path[i] = memoization[i];
			dist[i] = memDist[i];
			visited[i] = true;
		}

		int v = minDistance(aStar, visited);	// Find closest unvisited node
		visited[v] = true;
		verticesVisited++;
		
		//Update distance values for new vertex
		for(int u = 0; u < maxVertices; u++)
		{
			// Update dist[u] only if it:
			//1. isnt in support set, 2. there is an edge from u to v, 
			//3. The total weight of path from source to v via nextV is smaller than current value of dist[v]

			if (!visited[u] && weightMatrix[(v*maxVertices) + u] != 0 && dist[v] != INT_MAX
				&& dist[v] + weightMatrix[(v*maxVertices) + u] < dist[u])
			{
				dist[u] = dist[v] + weightMatrix[(v*maxVertices) + u];
				path[u] = v;
				
				// Record memoization information
				memoization[v] = v;
				memDist[u] = dist[v] + weightMatrix[(v*maxVertices) + u];
			}
		}
	}
}

void findSecondShortestPath(bool aStar, int secondShortestPath[maxVertices], int shortestPath[maxVertices], int originalGoalPath[maxVertices])
{
	int totalVerts = 0;	// Tracks total vertices visited to find second shortest path.
	pathWeight = INT_MAX;
	int newPath[maxVertices];
	int weightPlaceHolder;

	for(int i = 0; i < maxVertices; i++)
	{
		if(originalGoalPath[i] != -1)
		{
			// Remove an edge
			int to = i;
			int from = originalGoalPath[i];

			weightPlaceHolder = weightMatrix[(from*maxVertices) + to];
			weightMatrix[(from*maxVertices) + to] = 0;			
			
			Dijkstra(aStar, secondShortestPath);	// updates path distances with edge removed			
			int crntWeight = dist[goal];
			
			// Update shortest, store in newPath array
			if(crntWeight < pathWeight)
			{
				calcGoalPath(newPath, secondShortestPath);	// Update array when path is shorter
				pathWeight = crntWeight;
			}
			
			// Return edge to graph reset
			weightMatrix[(from*maxVertices) + to] = weightPlaceHolder;
			totalVerts += verticesVisited;
			calcGoalPath(originalGoalPath, shortestPath);	// reset goalPath
		}
	}
	
	if(aStar)
		cout << "Second shortest path using A* alg: " << endl;
	else
		cout << "Second shortest path using Dijkstra alg: " << endl;

	displayGoalPath(newPath);
	cout << "Path distance: " << pathWeight << endl;
	cout << "Number of vertices visited " << totalVerts << endl;
}

void findShortestPath(bool aStar, int shortestPath[maxVertices], int goalPath[maxVertices])
{
	Dijkstra(aStar, shortestPath);
	pathWeight = dist[goal];
	calcGoalPath(goalPath, shortestPath);
	if(aStar)
		cout << "\nShortest Path using A* alg: " << endl;
	else
		cout << "\nShortest Path using Dijkstra alg: " << endl;

	displayGoalPath(goalPath);		// Display path travelled from start to goal
	cout << "Path distance: " << pathWeight << endl;
	cout << "Number of vertices visited: " << verticesVisited << "\n" << endl;
}

void readFile()
{
	int nVertices;
	int nEdges;
	char verticePos;
	char vertice1; 
	char vertice2;
	int weight;
	int xCo;
	int yCo;
	char charStart;
	char charGoal;
	
	ifstream inFile;
	inFile.open("ass3.txt");
	
	if(inFile.is_open())
	{
		inFile >> nVertices;
		inFile >> nEdges;
		
		for (int i = 0; i < nVertices; i++)	// Create vertice objects w/ location
		{
			inFile >> verticePos >> xCo >> yCo;
			Vertice* newVert = new Vertice(xCo, yCo);
			vp[asciiToInt(verticePos)] = newVert;
		}
		inFile.clear();

		if (nVertices > maxVertices)	// Check space in weightMatrix
		{
			cout << "Insufficient storage space in weightMatrix" << endl;
		}
		else	// create matrix of weighted paths between nodes
		{
			for (int i = 0; i < nEdges; i++)
			{
				inFile >> vertice1 >> vertice2 >> weight;

				weightMatrix[(asciiToInt(vertice1) * maxVertices) + asciiToInt(vertice2)] = weight;
			}
			
			inFile >> charStart >> charGoal;
			start = asciiToInt(charStart);
			goal = asciiToInt(charGoal);
		}
	}	
	else
	{
		cerr << "File could not be opened" << endl;
		exit(0);
	}
}


int main()
{
	readFile();

	displayWeights();

	int shortestPath[maxVertices];
	int shortestGoalPath[maxVertices];
	int secondShortestPath[maxVertices];
	
	// Find shortest path using Dijkstra
	findShortestPath(false, shortestPath, shortestGoalPath);

	// Find second shortest path using Dijkstra
	findSecondShortestPath(false, secondShortestPath, shortestPath, shortestGoalPath);

	// Find shortest path using A*
	findShortestPath(true, shortestPath, shortestGoalPath);

	// Find second shortest path using A*
	findSecondShortestPath(true, secondShortestPath, shortestPath, shortestGoalPath);
}



/*
Luke Masliah - 6273464

Report:

Data Structures:
Priority heap - Used for storing and accessing minDistance vertex index in O(log n) and O(1) time respectively.
	Note - I chose to only implement the neccessary features of this heap that being: insert and getRoot,
		as insert maintains the minHeap property and the whole heap is dumped after each search.

Second Shortest Path Solution:
- My second shortest path solution involves recording the shortest path found in step 1, then procedually 
removing one edge at a time from this path and re-calculating the distances using Dijkstra's algorithm.
Each iteration, the new shortest path is recorded/updated if a shorter path is found.

Optimisation

1. Break out of dijkstras once goal vertex has been reached
2. Convert 2d matrix to single array of [maxdist * maxDist] to consolidate array information
   in memory- improve accessability.
3. Implement a heap to store min distance values as I find them. Then use getRoot() to immediately
   access smallest distance value.
4. Use A* algorithm to implement coordinate-orientated hueristic as a means of directing Dijkstra
   towards the goal vertex more efficiently.
5. Use memoization arrays to record shortest path/weight. Check these arrays before running the 
   expensive 'minDistance' function.



Q1. What if we require that the second shortest path be longer than the shortest path? 
- If we require the second shortest path to be longer than the shortest path then we need to optimise
  The original shortest path search method using a good hueristic (such as A*) to ensure that the
  actual shortest path is found first. We could alternatively use the method of removing edge by edge
  to search for shortest path before using it for second shortest path.

Q2. What if the graph contains cycles?
- If the graph contains cycles we would need to implement Bellman-Ford's algorithm to identify negative_sign
  cycles. This algorithm would update every vertex's distance information during every iteration
  of the search.

Q3. What if the graph is undirected? 
- If the graph is undirected we would need to store all extra edges in adjacency lists and also
  include these extra edges when finding minDistance for each vertex.

*/
