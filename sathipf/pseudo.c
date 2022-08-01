#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <stdlib.h>
#include<assert.h>

#define TIMER
//#define STATS
//#define PROGRESS
//#define DISPLAY_FLOW
//#define STDIN
//#define TEST
//#define Alloc
#define FIFO_BUCKET
//#define LOWEST_LABEL
//#define SIMPLE_INIT
//#define SAT_ALL_INIT
//#define SAT_SMALL_INIT
//#define SAT_LARGE_INIT
//#define AVNDCAP

typedef unsigned int uint;
typedef long int lint;
typedef long long int llint;
typedef unsigned long long int ullint;

#ifdef TIMER
double
timer (void)
{
  struct rusage r;

  getrusage(0, &r);
  return (double) (r.ru_utime.tv_sec + r.ru_utime.tv_usec / (double)1000000);
}
#endif // TIMER

struct node;

typedef struct arc
{
	struct node *from;
	struct node *to;
	uint flow;
//	ullint flow;
	uint capacity;
//	ullint capacity;
	uint direction;
} Arc;

typedef struct node
{
	uint visited;
	uint numAdjacent;
	uint number;
	uint label;
//	int excess;
	llint excess;
	struct node *parent;
	struct node *childList;
	struct node *nextScan;
	uint numOutOfTree;
	Arc **outOfTree;
	uint nextArc;
	Arc *arcToParent;
	struct node *next;
} Node;


typedef struct root
{
	Node *start;
	Node *end;
} Root;

//---------------  Global variables ------------------
static uint numNodes = 0;
static uint numArcs = 0;
static uint source = 0;
static uint sink = 0;

#if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
ullint allCap = 0;
double avCap = 0;
#endif

#ifdef LOWEST_LABEL
static uint lowestStrongLabel = 1;
#else
static uint highestStrongLabel = 1;
#endif

static Node *adjacencyList = NULL;
static Root *strongRoots = NULL;
static uint *labelCount = NULL;
static Arc *arcList = NULL;
//-----------------------------------------------------

#ifdef STATS
static ullint numPushes = 0;
static uint numMergers = 0;
static uint numRelabels = 0;
static uint numGaps = 0;
static ullint numArcScans = 0;


static ullint arcScanCntI  = 0;       /* number of initial arc scans */
static ullint arcScanCnt1  = 0;       /* number of arc scans at stage 1*/
static ullint arcScanCntGlbUp = 0;    /* number of arc scans during the global updating */
static ullint arcScanCntLab = 0;      /* number of arc scans during the labeling procedure */
static ullint arcScanCnt2  = 0;       /* number of arc scans at stage 2 */
static ullint nodeScanCntI  = 0;      /* number of initial node scans */
static ullint nodeScanCntGap  = 0;    /* number of node scans during the gap heuristic */
static ullint nodeScanCnt1  = 0;      /* number of node scans at stage 1*/
static ullint nodeScanCntGlbUp  = 0;  /* number of node scans during the global updating */
static ullint nodeScanCnt2  = 0;      /* number of node scans at stage 2 */
static ullint pushCnt  = 0;           /* number of pushes */
static ullint pushCntI = 0;           /* Initial pushes */
static ullint pushCnt1  = 0;          /* number of pushes at stage 1 */
static ullint pushCnt2  = 0;          /* number of pushes at stage 2 */
static ullint strPushCntI =0;         /* number of initial saturated pushes */
static ullint strPushCnt1 =0;         /* number of saturated pushes */
static ullint nStrPushCnt1 =0;        /* number of non-saturated pushes */
static ullint strPushCnt2 =0;         /* number of saturated pushes */
static ullint nStrPushCnt2 =0;        /* number of non-saturated pushes */
static ullint deplPush1 =0;           /* number of pushes that depleted node excesses */
static ullint nDeplPush1 =0;           /* number of pushes that do not depleted node excesses  */
static ullint deplPush2 =0;           /* number of pushes that depleted node excesses */
static ullint nDeplPush2 =0;           /* number of pushes that do not depleted node excesses  */
static ullint augCnt = 0;             /* number of augmentations */
static ullint relabelCntI   = 0;      /* number of relabels at the initial stage*/
static ullint relabelCnt   = 0;       /* number of relabels */
static ullint relabelCntGap   = 0;    /* number of relabels during the gap heuristic */
static ullint relabelCntGlbUp   = 0;  /* number of relabels during global updating*/
static ullint relabelCnt1   = 0;      /* number of relabels in the first stage */
static ullint relabelCnt2   = 0;      /* number of relabels in the second stage */
static ullint rootScanCnt1  =0;       /* number of root scans in the first stage */
static ullint numBreakRelationship =0;/* number of broken relationships */
static ullint numAddRelationship =0;/* number of added relationships */

#endif

#ifdef Alloc
static void
displayAlloc (void)
{
	uint i;


	for (i=0; i<numArcs; ++i)
	{
		printf("a %d %d %d\n", arcList[i].from->number, arcList[i].to->number, arcList[i].capacity);
	}
}
#endif

#ifdef DISPLAY_CUT
static void
displayCut (const uint gap)
{
	uint i;

	printf("c\nc Nodes in source set of min s-t cut:\n");

	for (i=0; i<numNodes; ++i)
	{
		if (adjacencyList[i].label >= gap)
		{
			printf("n %d\n", adjacencyList[i].number);
		}
	}
}
#endif

#ifdef DISPLAY_FLOW
static void
displayFlow (void)
{
	uint i;

	printf("c\nc Flow values on each arc:\n");

	for (i=0; i<numArcs; ++i)
	{
		printf("a %d %d %d\n", arcList[i].from->number, arcList[i].to->number, arcList[i].flow);
	}
}
#endif

static void
initializeNode (Node *nd, const uint n)
{
	nd->label = 0;
	nd->excess = 0;
	nd->parent = NULL;
	nd->childList = NULL;
	nd->nextScan = NULL;
	nd->nextArc = 0;
	nd->numOutOfTree = 0;
	nd->arcToParent = NULL;
	nd->next = NULL;
	nd->visited = 0;
	nd->numAdjacent = 0;
	nd->number = n;
	nd->outOfTree = NULL;
}

static void
initializeRoot (Root *rt)
{
	rt->start = NULL;
	rt->end = NULL;
}


static void
freeRoot (Root *rt)
{
	rt->start = NULL;
	rt->end = NULL;
}

#ifndef LOWEST_LABEL
static void
liftAll (Node *rootNode)
{
	Node *temp, *current=rootNode;

	current->nextScan = current->childList;

	-- labelCount[current->label];
	current->label = numNodes;

	#ifdef PROGRESS
        printf("\nThe label of node %d is set to %d\n", current->number, current->label);
    #endif // PROGRESS

	for ( ; (current); current = current->parent)
	{
		while (current->nextScan)
		{
			temp = current->nextScan;
			current->nextScan = current->nextScan->next;
			current = temp;
			current->nextScan = current->childList;

			-- labelCount[current->label];
			current->label = numNodes;
		}
	}
}
#endif

#ifdef FIFO_BUCKET
static void
addToStrongBucket (Node *newRoot, Root *rootBucket)
{
	if (rootBucket->start)
	{
		rootBucket->end->next = newRoot;
		rootBucket->end = newRoot;
		newRoot->next = NULL;
	}
	else
	{
		rootBucket->start = newRoot;
		rootBucket->end = newRoot;
		newRoot->next = NULL;
	}
	#ifdef PROGRESS
	printf("newRoot: %d \n", newRoot->number);
	#endif // PROGRESS
}

#else

static void
addToStrongBucket (Node *newRoot, Root *rootBucket)
{
	newRoot->next = rootBucket->start;
	rootBucket->start = newRoot;
}
#endif

static void
createOutOfTree (Node *nd)
{
	if (nd->numAdjacent)
	{
		if ((nd->outOfTree = (Arc **) malloc (nd->numAdjacent * sizeof (Arc *))) == NULL)
		{
			printf ("%s Line %d: Out of memory\n", __FILE__, __LINE__);
			exit (1);
		}
	}
}

static void
initializeArc (Arc *ac)
{
	ac->from = NULL;
	ac->to = NULL;
	ac->capacity = 0;
	ac->flow = 0;
	ac->direction = 1;
}

static void
addOutOfTreeNode (Node *n, Arc *out)
{
	n->outOfTree[n->numOutOfTree] = out;
	++ n->numOutOfTree;
}


static void
readDimacsFileCreateList (void)
{
	uint lineLength=1024, i, numLines = 0, from, to, first=0, last=0;
	ullint capacity;
	char *line, *word, ch, ch1;

#ifndef STDIN
	FILE *fp = fopen("allSatTst9.txt", "r");
#endif // STDIN

	if ((line = (char *) malloc ((lineLength+1) * sizeof (char))) == NULL)
	{
		printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
		exit (1);
	}

	if ((word = (char *) malloc ((lineLength+1) * sizeof (char))) == NULL)
	{
		printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
		exit (1);
	}
#ifndef STDIN
	while (fgets (line, lineLength, fp))
#else
	while (fgets (line, lineLength, stdin))
#endif // STDIN
	{
		++ numLines;

		switch (*line)
		{
		case 'p':

			sscanf (line, "%c %s %d %d", &ch, word, &numNodes, &numArcs);

			if ((adjacencyList = (Node *) malloc (numNodes * sizeof (Node))) == NULL)
			{
				printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
				exit (1);
			}

			if ((strongRoots = (Root *) malloc (numNodes * sizeof (Root))) == NULL)
			{
				printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
				exit (1);
			}

			if ((labelCount = (uint *) malloc (numNodes * sizeof (uint))) == NULL)
			{
				printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
				exit (1);
			}

			if ((arcList = (Arc *) malloc (numArcs * sizeof (Arc))) == NULL)
			{
				printf ("%s, %d: Could not allocate memory.\n", __FILE__, __LINE__);
				exit (1);
			}

			for (i=0; i<numNodes; ++i)
			{
				initializeRoot (&strongRoots[i]);
				initializeNode (&adjacencyList[i], (i+1));
				labelCount[i] = 0;
			}

			for (i=0; i<numArcs; ++i)
			{
				initializeArc (&arcList[i]);
			}

			first = 0;
			last = numArcs-1;

			break;

		case 'a':

			sscanf (line, "%c %d %d %d", &ch, &from, &to, &capacity);

			if ((from+to) % 2)
			{
				arcList[first].from = &adjacencyList[from-1];
				arcList[first].to = &adjacencyList[to-1];
				arcList[first].capacity = capacity;
#ifdef Alloc
                printf("a %d->%d %d\n", arcList[first].from->number, arcList[first].to->number, arcList[first].capacity);
#endif // Alloc

				++ first;
			}
			else
			{
				arcList[last].from = &adjacencyList[from-1];
				arcList[last].to = &adjacencyList[to-1];
				arcList[last].capacity = capacity;

#ifdef Alloc
				printf("a %d %d %d\n", arcList[last].from->number, arcList[last].to->number, arcList[last].capacity);
#endif // Alloc

				-- last;
			}

#if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
          allCap += capacity;
#endif
			++ adjacencyList[from-1].numAdjacent;
			++ adjacencyList[to-1].numAdjacent;

			break;


		case 'n':

			sscanf (line, "%c %d %c", &ch, &i, &ch1);

			if (ch1 == 's')
			{
				source = i;
			}
			else if (ch1 == 't')
			{
				sink = i;
			}
			else
			{
				printf ("Unrecognized character %c on line %d\n", ch1, numLines);
				exit (1);
			}

			break;
		}
	}

	for (i=0; i<numNodes; ++i)
	{
		createOutOfTree (&adjacencyList[i]);
	}

	for (i=0; i<numArcs; i++)
	{
		to = arcList[i].to->number;
		from = arcList[i].from->number;
		capacity = arcList[i].capacity;

		if (!((source == to) || (sink == from) || (from == to)))
		{
			if ((source == from) && (to == sink))
			{
				arcList[i].flow = capacity;
			}
#ifdef SIMPLE_INIT
			else if (from == source)
			{
				addOutOfTreeNode (&adjacencyList[from-1], &arcList[i]);
#ifdef PROGRESS
                    printf("Node: %d, addOutOfTreeNode from node %d to node %d \n", from, from, to);
#endif // PROGRESS
			}

			else if (to == sink)
			{
//			    printf("Within Read add %d -> %d to addOutOfTreeNode of node %d\n", from, to, to);
				addOutOfTreeNode (&adjacencyList[to-1], &arcList[i]);
#ifdef PROGRESS
                    printf("Node: %d, addOutOfTreeNode from node %d to node %d \n", to, from, to);
#endif // PROGRESS
			}
#endif // SIMPLE_INIT
			else
			{
				addOutOfTreeNode (&adjacencyList[from-1], &arcList[i]);

#ifdef PROGRESS
                    printf("Node: %d, addOutOfTreeNode from node %d to node %d \n", from, from, to);
#endif // PROGRESS
			}
		}
	}

	#ifdef PROGRESS
	for (i=1; i<=numNodes; ++i)
        printf("numOutOfTree of node %d is %d \n", adjacencyList[i-1].number, adjacencyList[i-1].numOutOfTree );
	#endif // PROGRESS

	free (line);
	line = NULL;

	free (word);
	word = NULL;
}

#ifdef SAT_ALL_INIT
static void
saturateAllInitialization (void)
{
	uint i, j, to, from;
	Arc *tempArc;
	Node *tempNode;

    //**********************************
    for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCntI++;
#endif // STATS
		tempNode = &adjacencyList[i];
        tempNode->nextArc = 0;
/*        size = tempNode->numOutOfTree; If size is used as a counter in the if condition
            below, we got an error because numOutOfTree will be changed but size if fixed.
            Thus,  tempNode->numOutOfTree must be used as a counter compariosn. */
		for (j=0; j<tempNode->numOutOfTree; ++j)
			{
#ifdef STATS
			    arcScanCntI++;
#endif // STATS
			    tempArc = tempNode->outOfTree[j];
#ifdef PROGRESS
                printf("Checking %d -> %d\n", tempArc->from->number, tempArc->to->number);
#endif // PROGRESS
//                tempArc->from->excess -= (llint) tempArc->capacity;
                tempArc->from->excess -= tempArc->capacity;
//                tempArc->to->excess += (llint) tempArc->capacity;
                tempArc->to->excess +=  tempArc->capacity;
                tempArc->flow += tempArc->capacity;
                tempArc->direction = 0;
                if (!(tempNode->number == source))
                    {
                        -- tempNode->numOutOfTree;
                        tempNode->outOfTree[j] = tempNode->outOfTree[tempNode->numOutOfTree];
                        -- j;
                    }
			}
	}

#ifdef PROGRESS
    printf("\nChecking after saturating all arcs.\n");
    for (i=0; i<numNodes; ++i)
    {
        uint size = adjacencyList[i].numOutOfTree;
        printf("\nNode %d has %d outOfTree\n", i+1, size);
        for (j=0; j< size; ++j)
        {
            tempArc = adjacencyList[i].outOfTree[j];
            printf("Checking %d -> %d\n", tempArc->from->number, tempArc->to->number);
        }
    }
#endif // PROGRESS

	for (i=0; i<numArcs; i++)
	{
#ifdef STATS
	    ++ arcScanCntI;
#endif // STATS
	    //tempNode = &arcList[i].to;
		to = arcList[i].to->number;
		from = arcList[i].from->number;

		//		if (!((source == to) || (sink == from) || (from == to)))
//		if (from != to)
        if ( !((source == to) || (sink == from) || (from == to) || (from == source) ) )
        {
#ifdef PROGRESS
            //printf("arcList[i].to: %d\n", tempNode->number);
            printf("\nNode: %d, addOutOfTreeNode arcList[%d] with direction %d from %d to %d\n",to, i+1, arcList[i].direction, from, to);
#endif // PROGRESS
            //addOutOfTreeNode (&arcList[i].to, &arcList[i]);
//            if (to == sink)
//                printf("Within Init add %d -> %d to addOutOfTreeNode of node %d\n", from, to, to);
            addOutOfTreeNode (&adjacencyList[to-1], &arcList[i]);
        }
	}

#ifdef PROGRESS
    printf("\nChecking after adding reverse arcs.\n");
    for (i=0; i<numNodes; ++i)
    {
        size = adjacencyList[i].numOutOfTree;
        printf("\nNode %d has %d outOfTree\n", i+1, size);
        for (j=0; j< size; ++j)
        {
            tempArc = adjacencyList[i].outOfTree[j];
            printf("Checking %d -> %d\n", tempArc->from->number, tempArc->to->number);
        }
    }
#endif // PROGRESS


	adjacencyList[source-1].excess = 0;
	adjacencyList[sink-1].excess = 0;

	for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCntI++;
#endif // STATS
		if (adjacencyList[i].excess > 0)
		{
		    adjacencyList[i].label = 1;
			++ labelCount[1];
#ifdef STATS
			++ relabelCntI;
#endif // STATS

			addToStrongBucket (&adjacencyList[i], &strongRoots[1]);

		}


	}

	adjacencyList[source-1].label = numNodes;
	adjacencyList[sink-1].label = 0;
	labelCount[0] = (numNodes - 2) - labelCount[1];

}

#elif defined SIMPLE_INIT

static void
simpleInitialization (void)
{
	uint i, j, size;
	Arc *tempArc;

#ifdef STATS
	nodeScanCntI++;
#endif // STATS
	size = adjacencyList[source-1].numOutOfTree;
	for (i=0; i<size; ++i)
	{
		tempArc = adjacencyList[source-1].outOfTree[i];
		tempArc->flow = tempArc->capacity;
//		tempArc->to->excess += (llint) tempArc->capacity;
		tempArc->to->excess +=  tempArc->capacity;
#ifdef STATS
	    arcScanCntI++;
		pushCntI++;
#endif // STATS
	}

#ifdef STATS
	nodeScanCntI++;
#endif // STATS
	size = adjacencyList[sink-1].numOutOfTree;
	for (i=0; i<size; ++i)
	{
		tempArc = adjacencyList[sink-1].outOfTree[i];
		tempArc->flow = tempArc->capacity;
//		tempArc->from->excess -= (llint) tempArc->capacity;
		tempArc->from->excess -= tempArc->capacity;
#ifdef STATS
	    arcScanCntI++;
		pushCntI++;
#endif // STATS
	}

	adjacencyList[source-1].excess = 0;
	adjacencyList[sink-1].excess = 0;

	for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCntI++;
#endif // STATS
		if (adjacencyList[i].excess > 0)
		{
		    adjacencyList[i].label = 1;
			++ labelCount[1];
#ifdef STATS
			++ relabelCntI;
#endif // STATS

			addToStrongBucket (&adjacencyList[i], &strongRoots[1]);
		}
	}

	adjacencyList[source-1].label = numNodes;
	adjacencyList[sink-1].label = 0;
	labelCount[0] = (numNodes - 2) - labelCount[1];

	#ifdef PROGRESS
	for (i=0; i<numNodes; ++i)
    {
        size = adjacencyList[i].numOutOfTree;
        for (j=0; j< size; ++j)
        {
            printf("adjacencyList[%d]->outOfTree[%d]: from: %d to: %d\n", i+1, j+1, adjacencyList[i].outOfTree[j]->from->number, adjacencyList[i].outOfTree[j]->to->number);
        }

    }
    #endif // PROGRESS
}

#elif (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
static void
satSpecInitialization (void)
{
	uint i, j, to, from;
	Arc *tempArc;
	Node *tempNode;
    int b;                         /* boolean variable */

#ifndef AVNDCAP
    avCap = (double)(allCap)/(double)(numArcs);
#else
    avCap = (double)(allCap)/(double)(numNodes); // the average capacity per node
#endif // AVNDCAP

    //**********************************
    for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCntI++;
#endif // STATS
		tempNode = &adjacencyList[i];
        tempNode->nextArc = 0;
/*        size = tempNode->numOutOfTree; If size is used as a counter in the if condition
            below, we got an error because numOutOfTree will be changed but size if fixed.
            Thus,  tempNode->numOutOfTree must be used as a counter compariosn. */
		for (j=0; j<tempNode->numOutOfTree; ++j)
        {
#ifdef STATS
			    arcScanCntI++;
#endif // STATS
            tempArc = tempNode->outOfTree[j];
#ifdef PROGRESS
                printf("Checking %d -> %d\n", tempArc->from->number, tempArc->to->number);
#endif // PROGRESS

#ifdef SAT_SMALL_INIT
        if ((tempArc->to->number != source) && (tempNode->number != sink) &&  ( ((tempArc->capacity>0) && (tempArc->capacity <= 1.05 *avCap)) ||
                (tempNode->number == source) || (tempArc->to->number == sink)) ) b = 1;
        else b = 0;
#elif defined SAT_LARGE_INIT
        if ((tempArc->to->number != source) && (tempNode->number != sink) &&  ( (tempArc->capacity >= 0.95 *avCap) ||
                (tempNode->number == source) || (tempArc->to->number == sink)) ) b = 1;
        else b = 0;
#endif // SAT_LARGE_INIT

            if (b)
            {
//                tempArc->from->excess -= (llint) tempArc->capacity;
//                tempArc->to->excess += (llint) tempArc->capacity;
                tempArc->from->excess -= tempArc->capacity;
                tempArc->to->excess += tempArc->capacity;
                tempArc->flow += tempArc->capacity;
                tempArc->direction = 0;
                if (!(tempNode->number == source))
                {
                    -- tempNode->numOutOfTree;
                    tempNode->outOfTree[j] = tempNode->outOfTree[tempNode->numOutOfTree];
                    -- j;
                }
            }
        }
	}

#ifdef PROGRESS
    printf("\nChecking after saturating all arcs.\n");
    for (i=0; i<numNodes; ++i)
    {
        uint size = adjacencyList[i].numOutOfTree;
        printf("\nNode %d has %d outOfTree\n", i+1, size);
        for (j=0; j< size; ++j)
        {
            tempArc = adjacencyList[i].outOfTree[j];
            printf("Checking %d -> %d\n", tempArc->from->number, tempArc->to->number);
        }
    }
#endif // PROGRESS

	for (i=0; i<numArcs; i++)
	{
#ifdef STATS
	    ++ arcScanCntI;
#endif // STATS
	    //tempNode = &arcList[i].to;
		to = arcList[i].to->number;
		from = arcList[i].from->number;

		//		if (!((source == to) || (sink == from) || (from == to)))
//		if (from != to)
        if ( (arcList[i].direction ==0 ) && (!((source == to) || (sink == from) || (from == to) || (from == source) )) )
        {
#ifdef PROGRESS
            //printf("arcList[i].to: %d\n", tempNode->number);
            printf("\nNode: %d, addOutOfTreeNode arcList[%d] with direction %d from %d to %d\n",to, i+1, arcList[i].direction, from, to);
#endif // PROGRESS
            //addOutOfTreeNode (&arcList[i].to, &arcList[i]);
//            if (to == sink)
//                printf("Within Init add %d -> %d to addOutOfTreeNode of node %d\n", from, to, to);
            addOutOfTreeNode (&adjacencyList[to-1], &arcList[i]);
        }
	}

#ifdef PROGRESS
    printf("\nChecking after adding reverse arcs.\n");
    for (i=0; i<numNodes; ++i)
    {
        uint size = adjacencyList[i].numOutOfTree;
        printf("\nNode %d has %d outOfTree\n", i+1, size);
        for (j=0; j< size; ++j)
        {
            tempArc = adjacencyList[i].outOfTree[j];
            printf("Checking %d -> %d\n", tempArc->from->number, tempArc->to->number);
        }
    }
#endif // PROGRESS


	adjacencyList[source-1].excess = 0;
	adjacencyList[sink-1].excess = 0;

	for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCntI++;
#endif // STATS
		if (adjacencyList[i].excess > 0)
		{
		    adjacencyList[i].label = 1;
			++ labelCount[1];
#ifdef STATS
			++ relabelCntI;
#endif // STATS

			addToStrongBucket (&adjacencyList[i], &strongRoots[1]);

		}


	}

	adjacencyList[source-1].label = numNodes;
	adjacencyList[sink-1].label = 0;
	labelCount[0] = (numNodes - 2) - labelCount[1];
}

#endif // SAT_ALL_INIT

static inline int
addRelationship (Node *newParent, Node *child)
{
#ifdef STATS
    numAddRelationship++;
#endif // STATS
	child->parent = newParent;
	child->next = newParent->childList;
	newParent->childList = child;

	return 0;
}

static inline void
breakRelationship (Node *oldParent, Node *child)
{
#ifdef STATS
    numBreakRelationship++;
#endif // STATS
	Node *current;

	child->parent = NULL;

	if (oldParent->childList == child)
	{
		oldParent->childList = child->next;
		child->next = NULL;
		return;
	}

	for (current = oldParent->childList; (current->next != child); current = current->next);

#ifdef STATS
    nodeScanCnt1++;
#endif // STATS
	current->next = child->next;
	child->next = NULL;
}

static void
merge (Node *parent, Node *child, Arc *newArc)
{
	Arc *oldArc;
	Node *current = child, *oldParent, *newParent = parent;

	#ifdef PROGRESS
	printf("Current node is %d and newParent is %d\n", child->number, parent->number);
	#endif // PROGRESS

#ifdef STATS
	++ numMergers;
#endif

	while (current->parent)
	{
#ifdef STATS
	    nodeScanCnt1++;
#endif // STATS
		oldArc = current->arcToParent;
		current->arcToParent = newArc;
		oldParent = current->parent;
		breakRelationship (oldParent, current);
		addRelationship (newParent, current);
		newParent = current;
		current = oldParent;
		newArc = oldArc;
		newArc->direction = 1 - newArc->direction;
	}

	current->arcToParent = newArc;
	addRelationship (newParent, current);
}


static inline void
pushUpward (Arc *currentArc, Node *child, Node *parent, const ullint resCap)
{
#ifdef STATS
	++ numPushes;
	pushCnt1++;
#endif

	if (resCap >= child->excess)
	{
	    if (resCap == child->excess)
        {
#ifdef STATS
        strPushCnt1++;
#endif // STATS
        }
		else
        {
#ifdef STATS
            nStrPushCnt1++;
#endif // STATS
        }

#ifdef PROGRESS
        printf("pushUpward from child: %d with label %d and excess %d to parent: %d with label %d and excess %d, pushed flow: %d \n",
               child->number, child->label, child->excess, parent->number, parent->label, parent->excess, child->excess);
#endif // PROGRESS

		parent->excess += child->excess;
//		currentArc->flow += (uint)child->excess;
		currentArc->flow += child->excess;
		child->excess = 0;
#ifdef STATS
    deplPush1++;
#endif // STATS
		return;
	}
#ifdef PROGRESS
    printf("pushUpward from child: %d with label %d and excess %d to parent: %d with label %d and excess %d, pushed flow: %d \n",
           child->number, child->label, child->excess, parent->number, parent->label, parent->excess, resCap);
#endif // PROGRESS

	currentArc->direction = 0;
//	parent->excess += (llint) resCap;
//	child->excess -= (llint) resCap;
	parent->excess +=  resCap;
	child->excess -=  resCap;
#ifdef STAT
	nDeplPush1++;
#endif // STAT
	currentArc->flow = currentArc->capacity;
	parent->outOfTree[parent->numOutOfTree] = currentArc;
#ifdef STATS
	strPushCnt1++;
#endif // STATS
	++ parent->numOutOfTree;


#ifdef PROGRESS
	printf("\n%d->%d direction is: %d\n", currentArc->from->number, currentArc->to->number, currentArc->direction);
	printf("%d->outOfTree[%d]->to: %d\n", parent->number, parent->numOutOfTree, currentArc->to->number);
    printf("%d->outOfTree[%d]->from: %d\n", parent->number, parent->numOutOfTree, currentArc->from->number);
	printf("breakRelationship between parent %d and child %d\n", parent->number, child->number);
#endif // PROGRESS

	breakRelationship (parent, child);

#ifdef LOWEST_LABEL
	lowestStrongLabel = child->label;
#endif

	addToStrongBucket (child, &strongRoots[child->label]);
}


static inline void
pushDownward (Arc *currentArc, Node *child, Node *parent, ullint flow)
{
#ifdef STATS
	++ numPushes;
	pushCnt1++;
#endif

	if (flow >= child->excess)
	{
	    if (flow == child->excess)
        {
#ifdef STATS
            strPushCnt1++;
#endif // STATS
        }
		else
        {
#ifdef STATS
            nStrPushCnt1++;
#endif // STATS
        }

#ifdef PROGRESS
        printf("pushDownward from child: %d with label %d and excess %d to parent: %d with label %d and excess %d, pushed flow: %d \n", child->number, child->label, child->excess, parent->number, parent->label, parent->excess, child->excess);
#endif // PROGRESS

		parent->excess += child->excess;
//		currentArc->flow -= (uint) child->excess;
		currentArc->flow -= child->excess;
		child->excess = 0;
#ifdef STATS
		deplPush1++;
#endif // STATS
		return;
	}
#ifdef PROGRESS
	printf("pushDownward from child: %d with label %d and excess %d to parent: %d with label %d and excess %d, pushed flow: %d  \n", child->number, child->label, child->excess, parent->number, parent->label, parent->excess, flow);
#endif // PROGRESS

#ifdef STATS
	strPushCnt1++;
#endif // STATS
	currentArc->direction = 1;
//	child->excess -= (llint) flow;
	child->excess -= flow;
#ifdef STATS
	nDeplPush1++;
#endif // STATS
//	parent->excess += (llint) flow;
	parent->excess += flow;
	currentArc->flow = 0;
	parent->outOfTree[parent->numOutOfTree] = currentArc;
	++ parent->numOutOfTree;

#ifdef PROGRESS
	printf("\n%d->%d direction is: %d\n", currentArc->from->number, currentArc->to->number, currentArc->direction);
	printf("%d->outOfTree[%d]->to: %d\n", parent->number, parent->numOutOfTree, currentArc->to->number);
    printf("%d->outOfTree[%d]->from: %d\n", parent->number, parent->numOutOfTree, currentArc->from->number);
	printf("breakRelationship between parent %d and child %d\n", parent->number, child->number);
#endif // PROGRESS

	breakRelationship (parent, child);

#ifdef LOWEST_LABEL
	lowestStrongLabel = child->label;
#endif

	addToStrongBucket (child, &strongRoots[child->label]);
}

static void
pushExcess (Node *strongRoot)
{
	Node *current, *parent;
	Arc *arcToParent;
	llint prevEx=1;

	for (current = strongRoot; (current->excess && current->parent); current = parent)
	{
#ifdef STAT
	    nodeScanCnt1++;
#endif // STAT
		parent = current->parent;
		prevEx = parent->excess;

		arcToParent = current->arcToParent;

		if (arcToParent->direction)
		{
			pushUpward (arcToParent, current, parent, (arcToParent->capacity - arcToParent->flow));
		}
		else
		{
			pushDownward (arcToParent, current, parent, arcToParent->flow);
		}
	}

	if ((current->excess > 0) && (prevEx <= 0))
	{

#ifdef LOWEST_LABEL
		lowestStrongLabel = current->label;
#endif
			addToStrongBucket (current, &strongRoots[current->label]);
	}
}


static Arc *
findWeakNode (Node *strongNode, Node **weakNode)
{
	uint i, size;
	Arc *out;



	size = strongNode->numOutOfTree;
#ifdef PROGRESS
	printf("size is: %d \n", size);
#endif // PROGRESS

//	for (i=strongNode->nextArc; i<size; ++i)
	for (i=strongNode->nextArc; i<strongNode->numOutOfTree; ++i)
	{
#ifdef PROGRESS
        printf("\n%d->%d direction is: %d\n", strongNode->outOfTree[i]->from->number, strongNode->outOfTree[i]->to->number, strongNode->outOfTree[i]->direction);
        //printf("%d->outOfTree[%d]->to: %d\n", strongNode->number, i+1, strongNode->outOfTree[i]->to->number);
        //printf("%d->outOfTree[%d]->from: %d\n", strongNode->number, i+1, strongNode->outOfTree[i]->from->number);

        printf("Checking %d -> %d\n", strongNode->outOfTree[i]->from->number, strongNode->outOfTree[i]->to->number);
#endif // PROGRESS

#ifdef STATS
		++ numArcScans;
		arcScanCnt1++;
#endif

#ifdef LOWEST_LABEL
		if (strongNode->outOfTree[i]->to->label == (lowestStrongLabel-1))
#else
		if (strongNode->outOfTree[i]->to->label == (highestStrongLabel-1))
#endif
		{
			strongNode->nextArc = i;
			out = strongNode->outOfTree[i];
			(*weakNode) = out->to;
			-- strongNode->numOutOfTree;
			strongNode->outOfTree[i] = strongNode->outOfTree[strongNode->numOutOfTree];
#ifdef PROGRESS
            if (strongNode->number == 708593)
                printf("Node %d  with excess %d has %d numOutOfTree within findWeakNode\n",
                strongNode, strongNode->excess, strongNode->numOutOfTree);
#endif // PROGRESS
#ifdef PROGRESS
			printf("WeakNode is %d with label %d and excess %d\n", out->to->number, out->to->label, out->to->excess);
#endif // PROGRESS

			return (out);
		}
#ifdef LOWEST_LABEL
		else if (strongNode->outOfTree[i]->from->label == (lowestStrongLabel-1))
#else
		else if (strongNode->outOfTree[i]->from->label == (highestStrongLabel-1))
#endif
		{
			strongNode->nextArc = i;
			out = strongNode->outOfTree[i];
			(*weakNode) = out->from;
			-- strongNode->numOutOfTree;
			strongNode->outOfTree[i] = strongNode->outOfTree[strongNode->numOutOfTree];
#ifdef PROGRESS
            if (strongNode->number == 708593)
                printf("Node %d  with excess %d has %d numOutOfTree within findWeakNode\n",
                strongNode->number, strongNode->excess, strongNode->numOutOfTree);
#endif // PROGRESS
#ifdef PROGRESS
			printf("WeakNode is %d with label %d and excess %d\n", out->from->number, out->from->label, out->from->excess);
#endif // PROGRESS

			return (out);
		}

		else
        {
#ifdef PROGRESS
           printf("Weak node is not found!\n");
#endif // PROGRESS
        }
	}

	strongNode->nextArc = strongNode->numOutOfTree;

	return NULL;
}


static void
checkChildren (Node *curNode)
{
#ifdef PROGRESS
#ifndef LOWEST_LABEL
    if(curNode->next)
        printf("curNode->next is %d with label %d\n", curNode->next->number, curNode->next->label);
#endif // LOWEST_LABEL
#endif // PROGRESS

	for ( ; (curNode->nextScan); curNode->nextScan = curNode->nextScan->next)
	{
#ifdef STAT
	    nodeScanCnt1++;
#endif // STAT
		if (curNode->nextScan->label == curNode->label)
		{
#ifdef PROGRESS
		    printf("curNode: %d, curNode->label: %d, curNode->nextScan: %d, curNode->nextScan->label: %d\n",
             curNode->number, curNode->label, curNode->nextScan->number, curNode->nextScan->label);
#endif // PROGRESS
			return;
		}
#ifdef PROGRESS
		    printf("curNode: %d, curNode->label: %d, curNode->nextScan: %d, curNode->nextScan->label: %d\n",
             curNode->number, curNode->label, curNode->nextScan->number, curNode->nextScan->label);
#endif // PROGRESS

	}

#ifdef PROGRESS
	printf("CurNode: %d\n", curNode->number);

    if(curNode->nextScan)
	printf("curNode: %d, curNode->label: %d, curNode->nextScan: %d, curNode->nextScan->label: %d\n",
        curNode->number, curNode->label, curNode->nextScan->number, curNode->nextScan->label);
#endif // PROGRESS

	-- labelCount[curNode->label];
#ifdef PROGRESS
	printf("\nlabelCount[%d] is %d\n", curNode->label, labelCount[curNode->label]);
#endif // PROGRESS
	++	curNode->label;
#ifdef PROGRESS
	printf("curNode label is %d\n", curNode->label);
#endif // PROGRESS
	++ labelCount[curNode->label];
#ifdef PROGRESS
	printf("labelCount[%d] is %d\n\n", curNode->label, labelCount[curNode->label]);
#endif // PROGRESS

#ifdef STATS
	++ numRelabels;
	++ relabelCnt1;
#endif

	curNode->nextArc = 0;

}

static void
processRoot (Node *strongRoot)
{

	Node *temp, *strongNode = strongRoot, *weakNode;
	Arc *out;

	strongRoot->nextScan = strongRoot->childList;

#ifdef PROGRESS
	if (strongRoot->childList)
	printf("strongRoot->nextScan = strongRoot->childList: %d -> %d\n", strongRoot->number, strongRoot->childList->number);
#endif // PROGRESS

	if ((out = findWeakNode (strongRoot, &weakNode)))
	{
#ifdef PROGRESS
	    printf("weakNode is found from the strongRoot %d with label %d and excess %d\n", strongNode->number, strongNode->label, strongNode->excess);
#endif // PROGRESS

		merge (weakNode, strongNode, out);
		pushExcess (strongRoot);
		return;
	}

#ifdef PROGRESS
	printf("strongRoot before checkChildren is : %d\n", strongRoot->number);
#endif // PROGRESS

	checkChildren (strongRoot);

#ifdef PROGRESS
	printf("strongRoot after checkChildren is : %d\n", strongRoot->number);
#endif // PROGRESS

	while (strongNode)
	{

#ifdef STATS
    rootScanCnt1++;
#endif // STATS

		while (strongNode->nextScan)
		{
#ifdef PROGRESS
		    if(strongNode->nextScan->next)
		    printf("strongNode->nextScan: %d, strongNode->nextScan->next", strongNode->nextScan->number, strongNode->nextScan->next->number);
#endif // PROGRESS

#ifdef STATS
    nodeScanCnt1++;
#endif // STATS
			temp = strongNode->nextScan;
			strongNode->nextScan = strongNode->nextScan->next;
			strongNode = temp;
			strongNode->nextScan = strongNode->childList;

			if ((out = findWeakNode (strongNode, &weakNode)))
			{
#ifdef PROGRESS
                printf("weakNode is found from the strongRoot %d with label %d and excess %d\n", strongNode->number, strongNode->label, strongNode->excess);
#endif // PROGRESS

				merge (weakNode, strongNode, out);
				pushExcess (strongRoot);
				return;
			}

			checkChildren (strongNode);
		}

		if ((strongNode = strongNode->parent))
		{
			checkChildren (strongNode);
		}
	}

	addToStrongBucket (strongRoot, &strongRoots[strongRoot->label]);

#ifdef PROGRESS
	printf("Root %d is added to strongRoots[%d]\n", strongRoot->number, strongRoot->label);
#endif // PROGRESS

#ifndef LOWEST_LABEL
	++ highestStrongLabel;

#ifdef PROGRESS
	printf("highestStrongLabel: %d \n", highestStrongLabel);
#endif // PROGRESS

#endif // LOWEST_LABEL
}

#ifdef LOWEST_LABEL
static Node *
getLowestStrongRoot (void)
{
	uint i;
	Node *strongRoot;

	if (lowestStrongLabel == 0)
	{
		while (strongRoots[0].start)
		{
			strongRoot = strongRoots[0].start;
			strongRoots[0].start = strongRoot->next;
			strongRoot->next = NULL;

			strongRoot->label = 1;

#ifdef STATS
			++ numRelabels;
#endif

			-- labelCount[0];
			++ labelCount[1];

			addToStrongBucket (strongRoot, &strongRoots[strongRoot->label]);
		}
		lowestStrongLabel = 1;
	}

	for (i=lowestStrongLabel; i<numNodes; ++i)
	{
		if (strongRoots[i].start)
		{
			lowestStrongLabel = i;

			if (labelCount[i-1] == 0)
			{
#ifdef STATS
				++ numGaps;
#endif
				return NULL;
			}

			strongRoot = strongRoots[i].start;
			strongRoots[i].start = strongRoot->next;
			strongRoot->next = NULL;
			return strongRoot;
		}
	}

	lowestStrongLabel = numNodes;
	return NULL;
}

#else

static Node *
getHighestStrongRoot (void)
{
	uint i;
	Node *strongRoot;

	for (i=highestStrongLabel; i>0; --i)
	{
#ifdef STATS
	    nodeScanCnt1++;
#endif // STATS
		if (strongRoots[i].start)
		{
			highestStrongLabel = i;
			if (labelCount[i-1])
			{
				strongRoot = strongRoots[i].start;
				strongRoots[i].start = strongRoot->next;
				strongRoot->next = NULL;
				return strongRoot;
			}

			while (strongRoots[i].start)
			{

#ifdef STATS
				++ numGaps;
#endif
				strongRoot = strongRoots[i].start;
				strongRoots[i].start = strongRoot->next;
				liftAll (strongRoot);
			}
		}
	}

	if (!strongRoots[0].start)
	{
		return NULL;
	}

	while (strongRoots[0].start)
	{
		strongRoot = strongRoots[0].start;
		strongRoots[0].start = strongRoot->next;
		strongRoot->label = 1;
		-- labelCount[0];
		++ labelCount[1];

#ifdef STATS
		++ numRelabels;
		++ relabelCnt1;
#endif

		addToStrongBucket (strongRoot, &strongRoots[strongRoot->label]);
	}

	highestStrongLabel = 1;

	strongRoot = strongRoots[1].start;
	strongRoots[1].start = strongRoot->next;
	strongRoot->next = NULL;

	return strongRoot;
}

#endif

static void
pseudoflowPhase1 (void)
{
	Node *strongRoot;

#ifdef LOWEST_LABEL
	while ((strongRoot = getLowestStrongRoot ()))
#else
	while ((strongRoot = getHighestStrongRoot ()))
#endif
	{
#ifdef PROGRESS
	    printf("\nstrongRoot is %d with label %d and excess %d\n", strongRoot->number, strongRoot->label, strongRoot->excess);
#endif // PROGRESS
#ifdef PROGRESS
            if (strongRoot->number == 708593)
                printf("Node %d  with excess %d has %d numOutOfTree within pseudoflowPhase1\n",
                strongRoot->number, strongRoot->excess, strongRoot->numOutOfTree);
#endif // PROGRESS

		processRoot (strongRoot);
	}
}

static void
checkOptimality (const uint gap)
{
	uint i, check = 1;
	ullint mincut = 0;
	llint *excess = NULL;

	excess = (llint *) malloc (numNodes * sizeof (llint));
	if (!excess)
	{
		printf ("%s Line %d: Out of memory\n", __FILE__, __LINE__);
		exit (1);
	}

	for (i=0; i<numNodes; ++i)
	{
		excess[i] = 0;
	}

	for (i=0; i<numArcs; ++i)
	{
		if ((arcList[i].from->label >= gap) && (arcList[i].to->label < gap))
		{
			mincut += arcList[i].capacity;
		}

#ifdef PROGRESS
        printf("Node %d  has excess %d within checkOptimality\n", i+1, arcList[i].flow);
#endif // PROGRESS

		if ((arcList[i].flow > arcList[i].capacity) || (arcList[i].flow < 0))
		{
			check = 0;
			printf("c Capacity constraint violated on arc (%d, %d). Flow = %d, capacity = %d\n",
				arcList[i].from->number,
				arcList[i].to->number,
				arcList[i].flow,
				arcList[i].capacity);
		}
//		excess[arcList[i].from->number - 1] -= (llint) arcList[i].flow;
//		excess[arcList[i].to->number - 1] += (llint) arcList[i].flow;
		excess[arcList[i].from->number - 1] -= arcList[i].flow;
		excess[arcList[i].to->number - 1] += arcList[i].flow;
	}

	for (i=0; i<numNodes; i++)
	{
		if ((i != (source-1)) && (i != (sink-1)))
		{
			if (excess[i])
			{
				check = 0;
				printf ("c Flow balance constraint violated in node %d. Excess = %lld\n",
					i+1, excess[i]);
			}
		}
	}

	if (check)
	{
		// printf ("c\nc Solution checks as feasible.\n");


                 printf ("%lld, ", mincut);
                 printf ("Solution checks as feasible, ");
	}

	check = 1;

	if (excess[sink-1] != mincut)
	{
		check = 0;
		// printf("c Flow is not optimal - max flow does not equal min cut!\nc\n");
                   printf("Flow is not optimal - max flow does not equal min cut!, ");

	}

	if (check)
	{
		//printf ("c\nc Solution checks as optimal.\nc \n");
		//printf ("s Max Flow            : %lld\n", mincut);


                printf ("Solution checks as optimal");

	}

	free (excess);
	excess = NULL;
}


static void
quickSort (Arc **arr, const uint first, const uint last)
{
	uint i, j, left=first, right=last, x1, x2, x3, mid, pivot, pivotval;
	Arc *swap;

	if ((right-left) <= 5)
	{// Bubble sort if 5 elements or less
		for (i=right; (i>left); --i)
		{
			swap = NULL;
			for (j=left; j<i; ++j)
			{
#ifdef STAT
			    arcScanCnt2++;
#endif // STAT
				if (arr[j]->flow < arr[j+1]->flow)
				{
					swap = arr[j];
					arr[j] = arr[j+1];
					arr[j+1] = swap;
				}
			}

			if (!swap)
			{
				return;
			}
		}

		return;
	}

	mid = (first+last)/2;

	x1 = arr[first]->flow;
	x2 = arr[mid]->flow;
	x3 = arr[last]->flow;

	pivot = mid;

	if (x1 <= x2)
	{
		if (x2 > x3)
		{
			pivot = left;

			if (x1 <= x3)
			{
				pivot = right;
			}
		}
	}
	else
	{
		if (x2 <= x3)
		{
			pivot = right;

			if (x1 <= x3)
			{
				pivot = left;
			}
		}
	}

	pivotval = arr[pivot]->flow;

	swap = arr[first];
	arr[first] = arr[pivot];
	arr[pivot] = swap;

	left = (first+1);

	while (left < right)
	{
#ifdef STAT
	    arcScanCnt2++;
#endif // STAT
		if (arr[left]->flow < pivotval)
		{
			swap = arr[left];
			arr[left] = arr[right];
			arr[right] = swap;
			-- right;
		}
		else
		{
			++ left;
		}
	}

	swap = arr[first];
	arr[first] = arr[left];
	arr[left] = swap;

	if (first < (left-1))
	{
		quickSort (arr, first, (left-1));
	}

	if ((left+1) < last)
	{
		quickSort (arr, (left+1), last);
	}
}

static void
sort (Node * current)
{
	if (current->numOutOfTree > 1)
	{
		quickSort (current->outOfTree, 0, (current->numOutOfTree-1));
	}
}

static void
minisort (Node *current)
{
	Arc *temp = current->outOfTree[current->nextArc];
	uint i, size = current->numOutOfTree;
	ullint tempflow = temp->flow;

//	for(i=current->nextArc+1; ((i<size) && (tempflow < current->outOfTree[i]->flow)); ++i)
	for(i=current->nextArc+1; ((i<current->numOutOfTree) && (tempflow < current->outOfTree[i]->flow)); ++i)
	{
#ifdef STAT
	    arcScanCnt2++;
#endif // STAT
		current->outOfTree[i-1] = current->outOfTree[i];
	}
	current->outOfTree[i-1] = temp;
}

static void
decompose2 (Node *deficitNode, const uint sink, uint *iteration)
{
	Node *current = deficitNode;
	Arc *tempArc;
	ullint bottleneck = abs(deficitNode->excess);

	for ( ;(current->number != sink) && (current->visited < (*iteration));
				current = tempArc->to)
	{
#ifdef STAT
	    nodeScanCnt2++;
#endif // STAT
		current->visited = (*iteration);
		tempArc = current->outOfTree[current->nextArc];

		if (tempArc->flow < bottleneck)
		{
			bottleneck = tempArc->flow;
		}
	}

	if (current->number == sink)
	{
//		deficitNode->excess += (llint) bottleneck;
		deficitNode->excess += bottleneck;
		current = deficitNode;

#ifdef PROGRESS
    printf("\nBottleneck %d is added to the node: %d; new deficit is %d\n", bottleneck, deficitNode->number, deficitNode->excess);
#endif // PROGRESS



		while (current->number != sink)
		{
			tempArc = current->outOfTree[current->nextArc];
			tempArc->flow -= bottleneck;
#ifdef STATS
            nodeScanCnt2++;
            pushCnt2++;
#endif // STATS


#ifdef PROGRESS
        printf("Bottleneck %d is reduced from the arc: %d -> %d\n", bottleneck, tempArc->from->number, tempArc->to->number);
#endif // PROGRESS

			if (current->excess)
            {
#ifdef STAT
            nDeplPush2++;
#endif // STAT
            }
            else
            {
#ifdef STATS
                deplPush2++;
#endif // STATS
            }


			if (tempArc->flow)
			{
#ifdef STATS
			    nStrPushCnt2++;
#endif // STATS
				minisort(current);
			}
			else
			{
#ifdef STATS
			    strPushCnt2++;
#endif // STATS
				++ current->nextArc;
			}
			current = tempArc->to;
		}
		return;
	}

	++ (*iteration);

	bottleneck = current->outOfTree[current->nextArc]->flow;

	while (current->visited < (*iteration))
	{
#ifdef STATS
	    nodeScanCnt2++;
#endif // STATS
		current->visited = (*iteration);
		tempArc = current->outOfTree[current->nextArc];

		if (tempArc->flow < bottleneck)
		{
			bottleneck = tempArc->flow;
		}
		current = tempArc->to;
	}

	++ (*iteration);

	while (current->visited < (*iteration))
	{
		current->visited = (*iteration);
		tempArc = current->outOfTree[current->nextArc];
		tempArc->flow -= bottleneck;
#ifdef STATS
	    nodeScanCnt2++;
		pushCnt2++;
#endif // STATS

#ifdef PROGRESS
    printf("Bottleneck %d is reduced from the arc: %d -> %d\n", bottleneck, tempArc->from->number, tempArc->to->number);
#endif // PROGRESS

		if (current->excess - (llint) bottleneck)
        {
#ifdef STATS
            nDeplPush2++;
#endif // STATS
        }
        else
        {
#ifdef STATS
            deplPush2++;
#endif // STATS
        }

		if (tempArc->flow)
		{
#ifdef STATS
		    nStrPushCnt2++;
#endif // STATS
			minisort(current);
			current = tempArc->to;
		}
		else
		{
#ifdef STATS
		    strPushCnt2++;
#endif // STATS
			++ current->nextArc;
			current = tempArc->to;
		}
	}
}

static void
decompose (Node *excessNode, const uint source, uint *iteration)
{
	Node *current = excessNode;
	Arc *tempArc;
	ullint bottleneck = excessNode->excess;

#ifdef PROGRESS
    printf("\n-----------------------------------------\n");
    printf("Node %d with excess %d and %d outOfTree will be proceeded\n",
           current->number, current->excess, current->numOutOfTree);
#endif // PROGRESS

	for ( ;(current->number != source) && (current->visited < (*iteration));
				current = tempArc->from)
	{
#ifdef STATS
	    nodeScanCnt2++;
#endif // STATS
		current->visited = (*iteration);
		tempArc = current->outOfTree[current->nextArc];
#ifdef PROGRESS
    printf("Node %d has %d outOfTree\n", current->number, current->numOutOfTree);
    printf("Arc %d->%d\n", tempArc->from->number, tempArc->to->number);
#endif // PROGRESS

#ifdef OPTIM
		if ((!tempArc->flow) )
		{
//		    printf("Arc %d->%d with flow %d will be neglected!\n",
//             tempArc->from->number, tempArc->to->number, tempArc->flow);
            ++ current->nextArc;
            tempArc = current->outOfTree[current->nextArc];
			continue;
		}
//        assert(tempArc);
//        assert(tempArc->flow);
#endif // OPTIM
		if (tempArc->flow < bottleneck)
		{
			bottleneck = tempArc->flow;
#ifdef PROGRESS
    printf("Arc %d->%d: flow is %d and bottleneck is %d\n",
           tempArc->from->number, tempArc->to->number, tempArc->flow, bottleneck);
#endif // PROGRESS
		}
	}

	if (current->number == source)
	{
//		excessNode->excess -= (llint) bottleneck;
		excessNode->excess -= bottleneck;
		current = excessNode;

#ifdef PROGRESS
		printf("\nBottleneck %d is reduced from the node: %d; new excess is %d\n", bottleneck, excessNode->number, excessNode->excess);
#endif // PROGRESS

		while (current->number != source)
		{
			tempArc = current->outOfTree[current->nextArc];
			tempArc->flow -= bottleneck;
#ifdef STATS
		    nodeScanCnt2++;
			pushCnt2++;
#endif // STATS

#ifdef PROGRESS
			printf("Bottleneck %d is reduced from the arc: %d -> %d\n", bottleneck, tempArc->from->number, tempArc->to->number);
#endif // PROGRESS

			if (current->excess)
            {
#ifdef STATS
                nDeplPush2++;
#endif // STATS
            }
            else
            {
#ifdef STATS
                deplPush2++;
#endif // STATS
            }

			if (tempArc->flow)
			{
#ifdef STATS
                nStrPushCnt2++;
#endif // STATS
				minisort(current);
			}
			else
			{
#ifdef STATS
			    strPushCnt2++;
#endif // STATS
				++ current->nextArc;
			}
			current = tempArc->from;
		}
		return;
	}

	++ (*iteration);

	bottleneck = current->outOfTree[current->nextArc]->flow;

	while (current->visited < (*iteration))
	{
#ifdef STATS
	    nodeScanCnt2++;
#endif // STATS
		current->visited = (*iteration);
		tempArc = current->outOfTree[current->nextArc];
#ifdef OPTIM
		if (!tempArc->flow)
		{
//		    printf("Arc %d->%d with flow %d will be neglected!\n",
//             tempArc->from->number, tempArc->to->number, tempArc->flow);
            ++ current->nextArc;
            tempArc = current->outOfTree[current->nextArc];
			continue;
		}
#endif // OPTIM
		if (tempArc->flow < bottleneck)
		{
			bottleneck = tempArc->flow;
#ifdef PROGRESS
    printf("Arc %d->%d: flow is %d and bottleneck is %d\n",
           tempArc->from->number, tempArc->to->number, tempArc->flow, bottleneck);
#endif // PROGRESS
		}
		current = tempArc->from;
	}

	++ (*iteration);

	while (current->visited < (*iteration))
	{
#ifdef STATS
	    nodeScanCnt2++;
	    pushCnt2++;
#endif // STATS
		current->visited = (*iteration);
		tempArc = current->outOfTree[current->nextArc];
		tempArc->flow -= bottleneck;

		#ifdef PROGRESS
		printf("Bottleneck %d is reduced from the arc: %d -> %d\n", bottleneck, tempArc->from->number, tempArc->to->number);
		#endif // PROGRESS

//		if (current->excess - (llint) bottleneck)
		if (current->excess - bottleneck)
        {
#ifdef STATS
            nDeplPush2++;
#endif // STATS
        }
        else
        {
#ifdef STATS
            deplPush2++;
#endif // STATS
        }

		if (tempArc->flow)
		{
#ifdef STATS
		    nStrPushCnt2++;
#endif // STATS
			minisort(current);
			current = tempArc->from;
		}
		else
		{
#ifdef STATS
            strPushCnt2++;
#endif // STATS
			++ current->nextArc;
			current = tempArc->from;
		}
	}
}

static void
recoverFlow (const uint gap)
{
	uint i, j, iteration = 1;
	Arc *tempArc;
	Node *tempNode;

#ifdef SIMPLE_INIT
    /* Returning extra flow from the sink to its adjacent nodes with strict deficits In the simple initialization*/
	for (i=0; i<adjacencyList[sink-1].numOutOfTree; ++i)
	{
#ifdef STATS
	    arcScanCnt2++;
#endif // STATS
		tempArc = adjacencyList[sink-1].outOfTree[i];
		if (tempArc->from->excess < 0)
		{
#ifdef PROGRESS
		    printf("Deficit in node %d is %d\n", tempArc->from->number, tempArc->from->excess);
#endif // PROGRESS

			if ((tempArc->from->excess + (llint) tempArc->flow)  < 0)
			{
				tempArc->from->excess += (llint) tempArc->flow;
				tempArc->flow = 0;
#ifdef PROGRESS
                printf("Deficit in node %d becomes %d\n", tempArc->from->number, tempArc->from->excess);
#endif // PROGRESS
			}
			else
			{
				tempArc->flow = (ullint) (tempArc->from->excess + (llint) tempArc->flow);
				tempArc->from->excess = 0;
#ifdef PROGRESS
                printf("Deficit in node %d becomes %d\n", tempArc->from->number, tempArc->from->excess);
#endif // PROGRESS
			}
		}
	}
#endif // simple initialization

/* Dealing with excesses on nodes */
	for (i=0; i<adjacencyList[source-1].numOutOfTree; ++i)
	{
#ifdef STATS
	    arcScanCnt2++;
#endif // STATS
		tempArc = adjacencyList[source-1].outOfTree[i];
		addOutOfTreeNode (tempArc->to, tempArc);
	}

	adjacencyList[source-1].excess = 0;
	adjacencyList[sink-1].excess = 0;

	for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCnt2++;
#endif // STATS
		tempNode = &adjacencyList[i];

		if ((i == (source-1)) || (i == (sink-1)))
		{
			continue;
		}

		if (tempNode->label >= gap)
		{
			tempNode->nextArc = 0;
//			if ((tempNode->parent) && (tempNode->arcToParent->flow>0))
			if ((tempNode->parent) && (tempNode->arcToParent->flow))
			{
				addOutOfTreeNode (tempNode->arcToParent->to, tempNode->arcToParent);
			}
			for (j=0; j<tempNode->numOutOfTree; ++j)
			{
#ifdef STATS
            arcScanCnt2++;
#endif // STATS
//                printf("tempArc from %d to %d with flow %d will be checked\n",
//                       tempNode->outOfTree[j]->from->number, tempNode->outOfTree[j]->to->number, tempNode->outOfTree[j]->flow);

//				if (tempNode->outOfTree[j]->flow == 0)
				if (!tempNode->outOfTree[j]->flow)
				{
#ifdef PROGRESS
    printf("tempArc from %d to %d with flow %d will be removed\n",
           tempNode->outOfTree[j]->from->number, tempNode->outOfTree[j]->to->number, tempNode->outOfTree[j]->flow);

#endif // PROGRESS
					-- tempNode->numOutOfTree;
					tempNode->outOfTree[j] = tempNode->outOfTree[tempNode->numOutOfTree];
					-- j;
#ifdef PROGRESS
            if (tempNode->number == 708593)
                printf("Node %d  with excess %d has %d numOutOfTree within recoverFlow\n",
                tempNode->number, tempNode->excess, tempNode->numOutOfTree);
#endif // PROGRESS
				}
			}

			sort(tempNode);
		}
#ifdef OPTIM
        else
        {
            for (j=0; j<tempNode->numOutOfTree; ++j)
			{
#ifdef STATS
            arcScanCnt2++;
#endif // STATS
#ifdef PROGRESS
                printf("tempArc from %d to %d with flow %d will be checked\n",
                       tempNode->outOfTree[j]->from->number, tempNode->outOfTree[j]->to->number, tempNode->outOfTree[j]->flow);
#endif // PROGRESS
//				if (!tempNode->outOfTree[j]->flow)
				if (tempNode->outOfTree[j]->flow == 0)
				{
#ifdef PROGRESS
    printf("tempArc from %d to %d with flow %d will be removed\n",
           tempNode->outOfTree[j]->from->number, tempNode->outOfTree[j]->to->number, tempNode->outOfTree[j]->flow);

#endif // PROGRESS
					-- tempNode->numOutOfTree;
					tempNode->outOfTree[j] = tempNode->outOfTree[tempNode->numOutOfTree];
					-- j;
				}
			}
        }
#endif // OPTIM
	}

	for (i=0; i<numNodes; ++i)
	{
#ifdef STATS
	    nodeScanCnt2++;
#endif // STATS
		tempNode = &adjacencyList[i];
		while (tempNode->excess > 0)
		{
			++ iteration;
			decompose(tempNode, source, &iteration);
		}
	}

//move1 from here

//************************************************************************
/* Dealing with deficit nodes */
#ifndef SIMPLE_INIT
//adjacencyList[source-1].excess = 0;
//adjacencyList[sink-1].excess = 0;

/* move1 to here*/
    /* Arcs with positive flow and incoming to the weak nodes in the reverse directions are checked and added to their outOfTree; */
    int to, from;
		for (j=0; j< numArcs; ++j)
        {
            tempArc = &arcList[j];
            to = arcList[j].to->number;
            from = arcList[j].from->number;

            if (from == source)
		{
			continue;
		}

            if (arcList[j].flow)
            {
                if (adjacencyList[from-1].excess==0 || adjacencyList[from-1].excess<0)
                //if (!djacencyList[from-1].excess>0)
                {
#ifdef PROGRESS
            printf("\nNode: %d, addOutOfTreeNode arcList[%d] with direction %d from %d to %d\n", from, j+1,  arcList[j].direction, from, to);
#endif // PROGRESS
            addOutOfTreeNode (&adjacencyList[from-1], &arcList[j]);
                }
            }
        }
/* End of move1 */

for (i=0; i<numNodes; ++i)
	{
#ifdef STAT
	    nodeScanCnt2++;
#endif // STAT
		tempNode = &adjacencyList[i];

		if ((i == (source-1)) || (i == (sink-1)))
		{
			continue;
		}

/* move2 to here */
        /* Checking deficit nodes and removing arcs with zero flow or outgoing from the current node in the reverse direction */
		if (tempNode->excess <0 || tempNode->excess == 0)
		{
#ifdef PROGRESS
            printf("size of %d is %d:\n", tempNode->number, tempNode->numOutOfTree);
#endif // PROGRESS
			tempNode->nextArc = 0;
			for (j=0; j<tempNode->numOutOfTree; ++j)
			{
#ifdef PROGRESS
			    printf("%d -> %d, direction %d\n", tempNode->outOfTree[j]->from->number,
                    tempNode->outOfTree[j]->to->number, tempNode->outOfTree[j]->direction);
#endif // PROGRESS

#ifdef STAT
			    arcScanCnt2++;
#endif // STAT
				if ((!tempNode->outOfTree[j]->flow) || (tempNode->outOfTree[j]->to == tempNode))
				{
					-- tempNode->numOutOfTree;
					tempNode->outOfTree[j] = tempNode->outOfTree[tempNode->numOutOfTree];
					-- j;
				}
			}

#ifdef PROGRESS
            printf("size of %d within recoverflow becomes: %d\n", tempNode->number, tempNode->numOutOfTree);
            for (j=0; j<tempNode->numOutOfTree; ++j)
			{
			    printf("%d -> %d, direction %d\n", tempNode->outOfTree[j]->from->number,
                    tempNode->outOfTree[j]->to->number, tempNode->outOfTree[j]->direction);
			}
			printf("\n");
#endif // PROGRESS
        sort(tempNode);
		}
	}
/* End of move2 */

for (i=0; i<numNodes; ++i)
	{
#ifdef STAT
	    nodeScanCnt2++;
#endif // STAT
		tempNode = &adjacencyList[i];

#ifdef PROGRESS
		printf("Node %d still has deficit %d within the recovreflow process\n", tempNode->number, tempNode->excess);
#endif // PROGRESS

		while (tempNode->excess < 0)
		{
			++ iteration;
			decompose2(tempNode, sink, &iteration);
		}
	}
#ifdef PROGRESS
	printf("Iterations   , %d\n", iteration);
#endif // PROGRESS
#endif // SIMPLE_INIT
}


static void
freeMemory (void)
{
	uint i;

	for (i=0; i<numNodes; ++i)
	{
		freeRoot (&strongRoots[i]);
	}

	free (strongRoots);

	for (i=0; i<numNodes; ++i)
	{
		if (adjacencyList[i].outOfTree)
		{
			free (adjacencyList[i].outOfTree);
		}
	}

	free (adjacencyList);

	free (labelCount);

	free (arcList);
}

int
main(int argc, char ** argv)
{
	double readStart, readEnd, initStart, initEnd, solveStart, solveEnd, flowStart, flowEnd;
	uint gap;
/*
#ifdef LOWEST_LABEL
	printf ("c Lowest label pseudoflow algorithm (Version 3.23)\n");
#else
	printf ("c Highest label pseudoflow algorithm (Version 3.23)\n");
#endif

#ifdef FIFO_BUCKET
	printf ("c Using FIFO buckets\n");
#endif

#ifdef LIFO_BUCKET
	printf ("c Using LIFO buckets\n");
#endif
*/

#ifdef TIMER
	readStart = timer ();
#endif // TIMER
	readDimacsFileCreateList ();
#ifdef TIMER
	readEnd=timer ();
#endif // TIMER

#ifdef PROGRESS
    uint j, size;
    Node *tempNode;
    Arc *tempArc;

	printf ("c Finished reading file.\n"); fflush (stdout);
	for (uint i=0; i<numNodes; ++i)
    {
	printf("numOutOfTree node %d is %d\n", i+1, adjacencyList[i].numOutOfTree);
	for (j=0; j<adjacencyList[i].numOutOfTree; ++j)
    {
        tempArc = adjacencyList[i].outOfTree[j];
        assert(tempArc);
        assert(tempArc->to);
        assert(tempArc->to->number);
//        if (tempArc->to->number == 708593 )
            printf("Arcs %d->%d has flow %d\n",
                   tempArc->from->number, tempArc->to->number,
                   tempArc->flow);
    }
    }
//    printf("--------------------------------------------\n");
//    printf("numOutOfTree node 5 is %d\n", adjacencyList[4].numOutOfTree);
//	for (j=0; j<adjacencyList[4].numOutOfTree; ++j)
//    {
//        tempArc = adjacencyList[4].outOfTree[j];
//        assert(tempArc);
//        assert(tempArc->to);
//        assert(tempArc->to->number);
////        if (tempArc->to->number == 708593 )
//            printf("Arcs %d->%d has flow %d\n",
//                   tempArc->from->number, tempArc->to->number,
//                   tempArc->flow);
//    }
//
//     printf("--------------------------------------------\n");
//    printf("Node 708593  with excess %d has %d numOutOfTree\n",
//           adjacencyList[708592].excess, adjacencyList[708592].numOutOfTree);
//    for (j=0; j<adjacencyList[708592].numOutOfTree; ++j)
//    {
//        tempArc = adjacencyList[708592].outOfTree[j];
//        assert(tempArc);
//        assert(tempArc->to);
//        assert(tempArc->to->number);
//        if (tempArc->from->number == 2 )
//            printf("Arcs %d->%d has flow %d\n",
//                   tempArc->from->number, tempArc->to->number,
//                   tempArc->flow);
//    }

    printf("--------------------------------------------\n");
#endif // PROGRESS

#ifdef Alloc
	printf ("c Allocated data:\n"); fflush (stdout);

	displayAlloc ();
#endif

#ifdef TIMER
	initStart = readEnd;
#endif // TIMER

#ifdef SIMPLE_INIT
    simpleInitialization ();
#elif defined SAT_ALL_INIT
	saturateAllInitialization ();
#elif (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
    satSpecInitialization ();
#endif // SIMPLE_INIT

#ifdef TIMER
	initEnd=timer ();
#endif // TIMER

#ifdef PROGRESS
	printf ("\nc Finished initialization.\n\n"); fflush (stdout);
	for (uint i=0; i<numNodes; ++i)
    {
	printf("numOutOfTree node %d is %d\n", i+1, adjacencyList[i].numOutOfTree);
	for (uint j=0; j<adjacencyList[i].numOutOfTree; ++j)
    {
        Arc *tempArc = adjacencyList[i].outOfTree[j];
        assert(tempArc);
        assert(tempArc->to);
        assert(tempArc->to->number);
//        if (tempArc->to->number == 708593 )
            printf("Arcs %d->%d has flow %d\n",
                   tempArc->from->number, tempArc->to->number,
                   tempArc->flow);
    }
    }
#if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
        printf("\navCap is %f\n", avCap);
        printf("\nallCap is %d\n", allCap);
#endif
//    printf("--------------------------------------------\n");
//    printf("numOutOfTree node 5 is %d\n", adjacencyList[4].numOutOfTree);
//	for (j=0; j<adjacencyList[4].numOutOfTree; ++j)
//    {
//        tempArc = adjacencyList[4].outOfTree[j];
//        assert(tempArc);
//        assert(tempArc->to);
//        assert(tempArc->to->number);
////        if (tempArc->to->number == 708593 )
//            printf("Arcs %d->%d has flow %d\n",
//                   tempArc->from->number, tempArc->to->number,
//                   tempArc->flow);
//    }
//
//
//    printf("--------------------------------------------\n");
//    printf("Node 708593  with excess %d has %d numOutOfTree\n",
//           adjacencyList[708592].excess, adjacencyList[708592].numOutOfTree);
//    for (j=0; j<adjacencyList[708592].numOutOfTree; ++j)
//    {
//        tempArc = adjacencyList[708592].outOfTree[j];
//        assert(tempArc);
//        assert(tempArc->to);
//        assert(tempArc->to->number);
////        if (tempArc->to->number == 708593 )
//            printf("Arcs %d->%d has flow %d\n",
//                   tempArc->from->number, tempArc->to->number,
//                   tempArc->flow);
//    }
//
//    printf("--------------------------------------------\n");
#endif

	solveStart=initEnd;
	pseudoflowPhase1 ();
#ifdef TIMER
	solveEnd=timer ();
#endif // TIMER

#ifdef PROGRESS
	printf ("\nc Finished phase 1.\n\n"); fflush (stdout);

    for (uint i=0; i<numNodes; ++i)
    {
	printf("numOutOfTree node %d is %d\n", i+1, adjacencyList[i].numOutOfTree);
	for (uint j=0; j<adjacencyList[i].numOutOfTree; ++j)
    {
        Arc *tempArc = adjacencyList[i].outOfTree[j];
        assert(tempArc);
        assert(tempArc->to);
        assert(tempArc->to->number);
//        if (tempArc->to->number == 708593 )
            printf("Arcs %d->%d has flow %d\n",
                   tempArc->from->number, tempArc->to->number,
                   tempArc->flow);
    }
    }
//    printf("--------------------------------------------\n");
//    printf("Node 5  with excess %d has %d numOutOfTree\n",
//           adjacencyList[4].excess, adjacencyList[4].numOutOfTree);
//	for (j=0; j<adjacencyList[4].numOutOfTree; ++j)
//    {
//        tempArc = adjacencyList[4].outOfTree[j];
//        assert(tempArc);
//        assert(tempArc->to);
//        assert(tempArc->to->number);
////        if (tempArc->to->number == 708593 )
//            printf("Arcs %d->%d has flow %d\n",
//                   tempArc->from->number, tempArc->to->number,
//                   tempArc->flow);
//    }
//
//
//    printf("--------------------------------------------\n");
//    printf("Node 708593  with excess %d has %d numOutOfTree\n",
//           adjacencyList[708592].excess, adjacencyList[708592].numOutOfTree);
//    for (j=0; j<adjacencyList[708592].numOutOfTree; ++j)
//    {
//        tempArc = adjacencyList[708592].outOfTree[j];
//        assert(tempArc);
//        assert(tempArc->to);
//        assert(tempArc->to->number);
////        if (tempArc->to->number == 708593 )
//            printf("Arcs %d->%d has flow %d\n",
//                   tempArc->from->number, tempArc->to->number,
//                   tempArc->flow);
//    }
//
//    printf("--------------------------------------------\n");
//    for (uint i=0; i<numNodes; ++i)
//        if (!adjacencyList[i].excess ==0)
//            printf("Node %d  with excess %d has %d numOutOfTree\n",
//            i+1, adjacencyList[i].excess, adjacencyList[i].numOutOfTree);
//
//    printf("--------------------------------------------\n");
#endif

#ifdef LOWEST_LABEL
	gap = lowestStrongLabel;
#else
	gap = numNodes;
#endif

#ifdef PROGRESS
printf("gap: %d\n", gap);
#endif // PROGRESS
	flowStart = solveEnd;
	recoverFlow(gap);
#ifdef TIMER
	flowEnd=timer ();
#endif // TIMER

#ifdef PROGRESS
int i;
printf("Excesses After flow recovery:\n");
for (i=0; i<numNodes; ++i)
    printf("Node %d has excess %d\n", i+1, arcList[i].flow);
printf("***********************************************\n");
#endif // PROGRESS


#ifdef TEST
	printf ("nodes     , %d\n", numNodes);
	printf ("arcs      , %d\n", numArcs);
#ifdef TIMER
	printf ("Time to read        , %.3f\n", (readEnd-readStart));
	printf ("Time to initialize  , %.3f\n", (initEnd-initStart));
	printf ("Time to min cut     , %.3f\n", (solveEnd-initStart));
	printf ("Time to max flow    , %.3f\n", (flowEnd-initStart));
#endif // TIMER
#ifdef STATS
	//printf ("scans     , %lld\n", numArcScans);
	printf ("mergers   , %d\n", numMergers);
	//printf ("pushes    , %lld\n", numPushes);
	//printf ("relabels  , %d\n", numRelabels);
	printf ("gaps      , %d\n", numGaps);

	printf ("arcScanI   , %lld\n", arcScanCntI);
	printf ("nodeScanI  , %lld\n", nodeScanCntI);
	printf ("pushesI    , %lld\n\n", pushCntI);

    printf ("arcScan1   , %lld\n", arcScanCnt1);
	printf ("nodeScan1  , %d\n",   nodeScanCnt1);
	printf ("strPushes1 , %lld\n", strPushCnt1);
	printf ("nStrPushes1, %lld\n", nStrPushCnt1);
	printf ("pushes1    , %lld\n", pushCnt1);
	printf ("deplPushes1, %lld\n", deplPush1);
	printf ("nDeplPushes1, %lld\n",nDeplPush1);
	printf ("relabel1   , %lld\n", relabelCnt1);
	printf ("rootScan1  , %lld\n", rootScanCnt1);
	printf ("breakRel   , %lld\n", numBreakRelationship);
	printf ("addRel     , %lld\n\n", numAddRelationship);

	printf ("arcScan2   , %lld\n", arcScanCnt2);
	printf ("nodeScan2  , %d\n", nodeScanCnt2);
	printf ("strPushes2 , %lld\n", strPushCnt2);
	printf ("nStrPushes2, %lld\n", nStrPushCnt2);
	printf ("pushes2    , %lld\n", pushCnt2);
    printf ("deplPushes2, %lld\n", deplPush2);
	printf ("nDeplPushes2, %lld\n",nDeplPush2);
	printf ("relabel2    , %lld\n", relabelCnt2);
#endif // STATS
#else

    printf ("%d, ", numNodes);
	printf ("%d, ", numArcs);
#ifdef TIMER
	printf ("%.3f, ", (readEnd-readStart));
	printf ("%.3f, ", (initEnd-initStart));
	printf ("%.3f, ", (solveEnd-initStart));
	printf ("%.3f, ", (flowEnd-initStart));
#endif // TIMER
#ifdef STATS
	//printf ("%lld, ", numArcScans);
	printf ("%d, ", numMergers);
	//printf ("%lld, ", numPushes);
	//printf ("%d, ", numRelabels);
	printf ("%d, ", numGaps);
	printf ("%lld, ", arcScanCntI);
	printf ("%d, ", nodeScanCntI);
	printf ("%lld, ", pushCntI);

    printf ("%lld, ", arcScanCnt1);
	printf ("%d, ",   nodeScanCnt1);
	printf ("%lld, ", strPushCnt1);
	printf ("%lld, ", nStrPushCnt1);
	printf ("%lld, ", pushCnt1);
	printf ("%lld, ", deplPush1);
	printf ("%lld, ",nDeplPush1);
	printf ("%lld, ", relabelCnt1);
	printf ("%lld, ", rootScanCnt1);
	printf ("%lld, ", numBreakRelationship);
	printf ("%lld, ", numAddRelationship);

	printf ("%lld, ", arcScanCnt2);
	printf ("%d, ", nodeScanCnt2);
	printf ("%lld, ", strPushCnt2);
	printf ("%lld, ", nStrPushCnt2);
	printf ("%lld, ", pushCnt2);
    printf ("%lld, ", deplPush2);
	printf ("%lld, ",nDeplPush2);
	printf ("%lld, ", relabelCnt2);
#endif // STAT
#endif // TEST

	checkOptimality (gap);

#ifdef DISPLAY_CUT
	displayCut (gap);
#endif

#ifdef DISPLAY_FLOW
	displayFlow ();
#endif

	freeMemory ();

	return 0;
}
