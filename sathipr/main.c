/* Maximum flow - highest lavel push-relabel algorithm */
/* COPYRIGHT C 1995, 2000 by IG Systems, Inc., igsys@eclipse.net */
/* This code is modified to calculate nun-saturated pushes. Since the
algorithm deos not use the push-relabel strategy at the second phase,
that is, to recover the flow after detecting the maximum pre-flow,
the number of representative opertation counts is limmited just to
the first phase, which in fact is the phase of solving the
minum cut problem.*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <values.h>

#include "types.h"          /* type definitions */
#include "parser.c"         /* parser */
//#include "timer.c"          /* timing routine */

/* Values added from the header file values.h */
#define MAXLONG 1073741824
#define atoll (long long) atof

// #define EXCESS_TYPE_LONG
// #define OLD_INIT
// #define WAVE_INIT
#define PROGRESS
//#define PRINT_FLOW
// #define PRINT_CUT
#define CHECK_SOLUTION
// #define CUT_ONLY
#define STAT
//#define PRINT_STAT
//#define TEST
//#define TIME

//#define INIT_UPDATE
//#define SIMPLE_INIT
//#define SAT_ALL_INIT
//#define SAT_SMALL_INIT
#define SAT_LARGE_INIT


/*
#define GLOB_UPDT_FREQ 0.5
*/
#define GLOB_UPDT_FREQ 0.5
#define ALPHA 6
#define BETA 12

#define WHITE 0
#define GREY 1
#define BLACK 2

/* global variables */



long    n,                    /* number of nodes */
        m,                    /* number of arcs */
        nMin,                 /* smallest node id */
        dMax,                 /* maximum label */
        aMax,                 /* maximum active node label */
        aMin;                 /* minimum active node label */
ullint  nm;                   /* n + ALPHA * m */
double flow;                  /* flow value */

node   *nodes;               /* array of nodes */
arc    *arcs;                /* array of arcs */
bucket *buckets;             /* array of buckets */
cType  *cap;                 /* array of capacities */
node   *source;              /* source node pointer */
node   *sink;                /* sink node pointer */
//node   **queue;              /* queue for BFS */
//node   **qHead, **qTail, **qLast;     /* queue pointers */

#if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
cType  allCap;             /* sum of all arc capacities */
#endif

node   *sentinelNode;        /* end of the node list marker */
arc *stopA;                  /* used in forAllArcs */
long workSinceUpdate = 0;    /* the number of arc scans since last update */
float globUpdtFreq;          /* global update frequency */
long updateCnt    = 0;       /* number of updates */
float t, t2, t3;                 /* for saving times */

#ifdef STAT
long    gapCnt   = 0,           /* number of gaps */
        gNodeCnt = 0;           /* number of nodes after gap */

ullint  arcScanCntI  = 0,       /* number of initial arc scans */
        arcScanCnt1  = 0,       /* number of arc scans at stage 1*/
        arcScanCntGlbUp = 0,    /* number of arc scans during the global updating */
        arcScanCntLab = 0,      /* number of arc scans during the relabeling procedure */
        arcScanCnt2  = 0,       /* number of arc scans at stage 2 */
        nodeScanCntI  = 0,      /* number of initial node scans */
        nodeScanCntGap  = 0,    /* number of node scans during the gap heuristic */
        nodeScanCnt1  = 0,      /* number of node scans at stage 1*/
        nodeScanCntGlbUp  = 0,  /* number of node scans during the global updating */
        nodeScanCnt2  = 0,      /* number of node scans at stage 2 */
        pushCntI  = 0,          /* number of initial pushes */
        pushCnt1  = 0,          /* number of pushes at stage 1 */
        pushCnt2  = 0,          /* number of pushes at stage 2 */
        StrPushCntI =0,         /* number of initial saturated pushes */
        StrPushCnt =0,          /* number of saturated pushes */
        nStrPushCnt =0,         /* number of non-saturated pushes */
        nStrPushCnt2 =0,        /* number of non-saturated pushes at stage 2 */
        deplPush1 =0,           /* number of pushes that depleted node excesses */
        nDeplPush1 =0,          /* number of pushes that do not depleted node excesses  */
        deplPush2 =0,           /* number of pushes that depleted node excesses */
        nDeplPush2 =0,          /* number of pushes that do not depleted node excesses  */
        selfLoopPush2 =0,       /* number of pushes to remove flows from self-loops */
        loopPush2 =0,           /* number of pushes to remove flows from loops */
        relabelCntI   = 0,      /* number of relabels at the initial stage*/
        relabelCnt  = 0,        /* number of relabels */
        relabelCntGap   = 0,    /* number of relabels during the gap heuristic*/
        relabelCntGlbUp   = 0,  /* number of relabels during global updating*/
        relabelCnt2  = 0,       /* number of relabels in the second stage */

/* bucket relative operation counts */
        aAddCnt = 0,
        aRemoveCnt = 0,
        iAddCnt = 0,
        iDeleteCnt  = 0,
        allocDSCnt = 0;
#endif // STAT

/* macros */

#define forAllNodes(i) for ( i = nodes; i != sentinelNode; i++ )
#define forAllArcs(i,a) for (a = i->first, stopA = (i+1)->first; a != stopA; a++)

#define nNode( i ) ( (i) - nodes + nMin )
#define nArc( a )  ( ( a == NULL )? -1 : (a) - arcs )

#define min( a, b ) ( ( (a) < (b) ) ? a : b )

/* FIFO queue for BFS macros */
/*
#define qInit() \
{\
  qHead = qTail = queue;\
}

#define qEmpty ( qHead == qTail )

#define qEnqueue(i) \
{\
  *qTail = i;\
  if ( qTail == qLast ) qTail = queue;\
  else qTail++;\
}

#define qDequeue(i) \
{\
  i = *qHead;\
  if ( qHead == qLast ) qHead = queue;\
  else qHead++;\
}
*/

/*
   bucket macros:
   bucket's active node list is singly-linked
     operations aAdd, aRemove (from the front)
   bucket's inactive list is doubly-linked
     operations iAdd, iDelete (from arbitrary position)
*/

long i_dist;
node *i_next, *i_prev;

#define aAdd(l,i)\
{\
  i->bNext = l->firstActive;\
  l->firstActive = i;\
  i_dist = i->d;\
  if (i_dist < aMin)\
    aMin = i_dist;\
  if (i_dist > aMax)\
    aMax = i_dist;\
  if (dMax < aMax)\
    dMax = aMax;\
}

/* i must be the first element */
#define aRemove(l,i)\
{\
  l->firstActive = i->bNext;\
}

#define iAdd(l,i)\
{\
  i_next = l->firstInactive;\
  i->bNext = i_next;\
  i->bPrev = sentinelNode;\
  i_next->bPrev = i;\
  l->firstInactive = i;\
}

#define iDelete(l,i)\
{\
  i_next = i->bNext;\
  if (l->firstInactive == i) {\
    l->firstInactive = i_next;\
    i_next->bPrev = sentinelNode;\
  }\
  else {\
    i_prev = i->bPrev;\
    i_prev->bNext = i_next;\
    i_next->bPrev = i_prev;\
  }\
}

/* allocate data structures, initialize related variables */

int allocDS( )

{

  nm = ALPHA * n + m;
  /*
  queue = (node**) calloc ( n, sizeof (node*) );
  if ( queue == NULL ) return ( 1 );
  qLast = queue + n - 1;
  qInit();
  */
  buckets = (bucket*) calloc ( n+2, sizeof (bucket) );
  if ( buckets == NULL ) return ( 1 );

  sentinelNode = nodes + n;
  sentinelNode->first = arcs + 2*m;

  return ( 0 );

} /* end of allocate */


void init( )

{
  node  *i;        /* current node */
  int overflowDetected;
  bucket *l;
  arc *a;
#ifdef PROGRESS
long ni, na;
#endif // PROGRESS
#ifdef EXCESS_TYPE_LONG
  double testExcess;
#endif
#ifndef OLD_INIT
  unsigned long delta;
#endif

  // initialize excesses

  forAllNodes(i) {
#ifdef STAT
    nodeScanCntI ++;
#endif // STAT
    i->excess = 0;
    i->current = i->first;
    forAllArcs(i, a){
#ifdef STAT
      arcScanCntI++;
#endif // STAT
      a->resCap = cap[a-arcs];
    }
  }

  for (l = buckets; l <= buckets + n-1; l++) {
    l -> firstActive   = sentinelNode;
    l -> firstInactive  = sentinelNode;
  }

  overflowDetected = 0;
#ifdef EXCESS_TYPE_LONG
  testExcess = 0;
  forAllArcs(source,a) {
    if (a->head != source) {
      testExcess += a->resCap;
    }
  }
  if (testExcess > MAXLONG) {
    printf("c WARNING: excess overflow. See README for details.\nc\n");
    overflowDetected = 1;
  }
#endif
#ifdef OLD_INIT
  source -> excess = MAXLONG;
#else
  if (overflowDetected) {
    source -> excess = MAXLONG;
  }
  else {
#ifdef SIMPLE_INIT
    source->excess = 0;
    forAllArcs(source,a) {
#ifdef STAT
        arcScanCntI++;
#endif // STAT
      if (a->head != source) {
#ifdef STAT
	pushCntI++;
	StrPushCntI++;
#endif // STAT
	delta = a -> resCap;
	a -> resCap -= delta;
	(a -> rev) -> resCap += delta;
	a->head->excess += delta;
      }
    }
#elif defined SAT_ALL_INIT
    forAllNodes(i) {
        if((i != sink)){
             forAllArcs(i,a) {
#ifdef STAT
            arcScanCntI++;
#endif // STAT
                if ((a->head != source) && (cap[a-arcs]>0)) {
#ifdef STAT
            pushCntI++;
            StrPushCntI++;
#endif // STAT
                    delta = a -> resCap;
                    a -> resCap -= delta;
                    (a -> rev) -> resCap += delta;
                    a->head->excess += delta;
                    i->excess -= delta;
#ifdef PROGRESS
    ni = nNode(i);
    na = nArc(a);
            printf ( "f %7ld %7ld %12ld\n",
                    ni, nNode( a -> head ), cap[na] - ( a -> resCap ) );
            printf("excess of node %d is %d\n", ni, i->excess);
#endif // PROGRESS
                }
            }
        }
    }
#else
double avCap;                   /* the average of arc  capacities */
avCap = (double)(allCap)/(double)(m);
int b;                         /* boolean variable */

forAllNodes(i) {
        if((i != sink)){
             forAllArcs(i,a) {
#ifdef STAT
            arcScanCntI++;
#endif // STAT

#ifdef SAT_SMALL_INIT
    if ((a->head != source) && (i != sink) &&  (cap[a-arcs]>0) && (cap[a-arcs] <= 1.05 *avCap)) b = 1;
    else b = 0;
#endif // SAT_SMALL_INIT
#ifdef SAT_LARGE_INIT
    if((a->head != source) && (i != sink) && (cap[a-arcs] >= 0.95 *avCap)) b = 1;
    else b = 0;
#endif // SAT_SMALL_INIT

                if (((i == source) || (a->head == sink)) && (a->head != source) && (i != sink) && (cap[a-arcs]>0)) {
#ifdef STAT
            pushCntI++;
            StrPushCntI++;
#endif // STAT
                    delta = a -> resCap;
                    a -> resCap -= delta;
                    (a -> rev) -> resCap += delta;
                    a->head->excess += delta;
                    i->excess -= delta;
#ifdef PROGRESS
            printf ( "f %7ld %7ld %12ld\n",
                    nNode(i), nNode( a -> head ), cap[nArc(a)] - ( a -> resCap ) );
            printf("excess of node %ld is %lld\n", nNode(i), i->excess);
#endif // PROGRESS
                }

                else if( b ) {
#ifdef STAT
            pushCntI++;
            StrPushCntI++;
#endif // STAT
                    delta = a -> resCap;
                    a -> resCap -= delta;
                    (a -> rev) -> resCap += delta;
                    a->head->excess += delta;
                    i->excess -= delta;
#ifdef PROGRESS
    ni = nNode(i);
    na = nArc(a);
            printf ( "f %7ld %7ld %12ld\n",
                    ni, nNode( a -> head ), cap[na] - ( a -> resCap ) );
            printf("excess of node %ld is %lld\n", ni, i->excess);
#endif // PROGRESS
                }
            }
        }
    }
#endif // SIMPLE_INIT
  }
  source->excess = 0;

  /*  setup labels and buckets */

#ifdef SIMPLE_INIT
  aMax = 0;
  aMin = n;
  dMax = 1;
#else
  aMax = 0;
  aMin = n;
  dMax = 1;
#endif // SIMPLE_INIT

  forAllNodes(i) {
#ifdef STAT
      nodeScanCntI ++;
#endif // STAT
    if (i == sink) {
      i->d = 0;
      iAdd(buckets,i);
#ifdef STAT
      iAddCnt++;
#endif // STAT
      continue;
    }
    if ((i == source) && (!overflowDetected)) {
      i->d = n;
    }
#ifdef SIMPLE_INIT
    else
      i->d = 1;

    l = buckets + 1;

    if (i->excess > 0) {
      /* put into active list */
      aAdd(l,i);
#ifdef STAT
      aAddCnt++;
#endif // STAT
    }
    else { /* i -> excess == 0 */
      /* put into inactive list */
      if (i->d < n){
	iAdd(l,i);
#ifdef STAT
	iAddCnt++;
#endif // STAT
      }
    }
#else
     else if (i->excess > 0) {
        i->d = 2;
        l = buckets + i->d;
        aAdd(l,i);
#ifdef STAT
        aAddCnt++;
#endif // STAT
      }
      else if (i->excess == 0){
            i->d = 2;
            l = buckets + i->d;
            iAdd(l,i);
#ifdef STAT
            iAddCnt++;
#endif // STAT
      }
      else {
            i->d = 1;
          l = buckets + i->d;
            iAdd(l,i);
#ifdef STAT
        iAddCnt++;
#endif // STAT
      }
#endif // SIMPLE_INIT
  }

#endif // OLD_INIT

  //  dMax = n-1;
  //  flow = 0.0;

#ifdef PROGRESS
printf ("Initialization\n");
    forAllNodes(i) {
      ni = nNode(i);
      printf("excess of node %ld is %lld\n", ni, i->excess);
      forAllArcs(i,a) {
	na = nArc(a);
	if ( cap[na] > 0 )
	  printf ( "f %7ld %7ld %12ld\n",
		  ni, nNode( a -> head ), cap[na] - ( a -> resCap )
		  );
      }
    }

    printf("aMax: %ld\n", aMax);
    printf("sink->excess: %lld\n",sink->excess);
    printf("c\n");

#endif // PROGRESS

} /* end of init */

void checkMax()

{
  bucket *l;

  for (l = buckets + dMax + 1; l < buckets + n; l++) {
    assert(l->firstActive == sentinelNode);
    assert(l->firstInactive == sentinelNode);
  }
}

/* global update via backward breadth first search from the sink */

void globalUpdate ()

{

  node  *i, *j;       /* node pointers */
  arc   *a;           /* current arc pointers  */
  bucket *l, *jL;          /* bucket */
  long curDist, jD;
  long state;
#ifndef SIMPLE_INIT
  bucket *deficitNodes = buckets +1; // The bucket of nodes with negative excess
#endif // SIMPLE_INIT

  updateCnt ++;

  /* initialization */

  for (l = buckets; l <= buckets + dMax; l++) {
    l -> firstActive   = sentinelNode;
    l -> firstInactive  = sentinelNode;
  }

  forAllNodes(i){
#ifdef STAT
      nodeScanCntGlbUp ++;
#endif // STAT
#ifdef SIMPLE_INIT
    i -> d = n;
#ifdef STAT
    relabelCntGlbUp++;
#endif // STAT
#else
    if (i->excess < 0 ) // Since the excess of the source is set as 0 within init(), source is not regarded here!
    {
//        assert(i->d==1);
        //i->d = 1; // Since the label of deficit nodes are not have not been changed, we do not need to reallocate them.
        iAdd(deficitNodes,i);
#ifdef STAT
	      //relabelCntGlbUp++;
	      iAddCnt++;
#endif // STAT
    }
    else
    {
        i -> d = n;
#ifdef STAT
    relabelCntGlbUp++;
#endif // STAT
    }
#endif // SIMPLE_INIT
  }
  sink -> d = 0;

  dMax = aMax = 0;
  aMin = n;

  /* breadth first search */

  // add sink to bucket zero

  iAdd(buckets, sink);
#ifdef STAT
  iAddCnt++;
#endif // STAT
  for (curDist = 0; 1; curDist++) {
    state = 0;
    l = buckets + curDist;
    jD = curDist + 1;
    jL = l + 1;
    /*
    jL -> firstActive   = sentinelNode;
    jL -> firstInactive  = sentinelNode;
    */

    if ((l->firstActive == sentinelNode) &&
	(l->firstInactive == sentinelNode))
      break;

    while (1) {

      switch (state) {
      case 0:
	i = l->firstInactive;
	state = 1;
	break;
      case 1:
	i = i->bNext;
	break;
      case 2:
	i = l->firstActive;
	state = 3;
	break;
      case 3:
	i = i->bNext;
	break;
      default:
	assert(0);
	break;
      }

      if (i == sentinelNode) {
	if (state == 1) {
	  state = 2;
	  continue;
	}
	else {
	  assert(state == 3);
	  break;
	}
      }

      /* scanning arcs incident to node i */
      forAllArcs(i,a) {
#ifdef STAT
        arcScanCntGlbUp ++;
#endif // STAT
	if (a->rev->resCap > 0 ) {
	  j = a->head;
	  if (j->d == n) {
	    j->d = jD;
#ifdef STAT
	    relabelCntGlbUp++;
#endif // STAT
	    j->current = j->first;
	    if (jD > dMax) dMax = jD;

	    if (j->excess > 0) {
	      /* put into active list */
	      aAdd(jL,j);
#ifdef STAT
	      aAddCnt++;
#endif // STAT
	    }
	    else if (j->excess  == 0){
	      /* put into inactive list */
//	      assert(!(j->excess<0));
	      iAdd(jL,j);
#ifdef STAT
	      iAddCnt++;
#endif // STAT
	    }
	  }
	}
      } /* node i is scanned */
    }
  }

} /* end of global update */

/* second stage -- preflow to flow */
void stageTwo ( )
/*
   do dsf in the reverse flow graph from nodes with excess
   cancel cycles if found
   return excess flow in topological order
*/

/*
   i->d is used for dfs labels
   i->bNext is used for topological order list
   buckets[i-nodes]->firstActive is used for DSF tree
*/

{
  node *i, *j, *tos, *bos, *restart, *r;
  arc *a;
  cType delta;

  /* deal with self-loops */
  forAllNodes(i) {
#ifdef STAT
    nodeScanCnt2 ++;
#endif // STAT
    forAllArcs(i,a){
#ifdef STAT
        arcScanCnt2 ++;
#endif // STAT
      if ( a -> head == i ) {
	a -> resCap = cap[a - arcs];
#ifdef STAT
	pushCnt2 ++;
	selfLoopPush2++;
#endif // STAT
      }
    }
  }

  /* initialize */
  tos = bos = NULL;
  forAllNodes(i) {
#ifdef STAT
    nodeScanCnt2 ++;
#endif // STAT
    i -> d = WHITE;
    //    buckets[i-nodes].firstActive = NULL;
    buckets[i-nodes].firstActive = sentinelNode;
    i -> current = i -> first;
  }

  /* eliminate flow cycles, topologicaly order vertices */
  forAllNodes(i){
#ifdef STAT
      nodeScanCnt2 ++;
#endif // STAT
    if (( i -> d == WHITE ) && ( i -> excess > 0 ) &&
	( i != source ) && ( i != sink )) {
      r = i;
      r -> d = GREY;
#ifdef STAT
      relabelCnt2++;
#endif // STAT
      do {
	for ( ; i->current != (i+1)->first; i->current++) {
	  a = i -> current;
#ifdef STAT
	  arcScanCnt2 ++;
#endif // STAT
	  if (( cap[a - arcs] == 0 ) && ( a -> resCap > 0 )) {
	    j = a -> head;
	    if ( j -> d == WHITE ) {
	      /* start scanning j */
	      j -> d = GREY;
#ifdef STAT
	      relabelCnt2++;
#endif // STAT
	      buckets[j-nodes].firstActive = i;
	      i = j;
	      break;
	    }
	    else
	      if ( j -> d == GREY ) {
		/* find minimum flow on the cycle */
		delta = a -> resCap;
		while ( 1 ) {
#ifdef STAT
            arcScanCnt2 ++;
#endif // STAT
		  delta = min ( delta, j -> current -> resCap );
		  if ( j == i )
		    break;
		  else
		    j = j -> current -> head;
		}

		/* remove delta flow units */
		j = i;
		while ( 1 ) {
		  a = j -> current;
#ifdef STAT
		  pushCnt2 ++;
		  loopPush2++;
#endif // STAT
		  a -> resCap -= delta;
		  a -> rev -> resCap += delta;
#ifdef STAT
		  if (a -> resCap > 0)
          nStrPushCnt2 ++;
#endif // STAT
		  j = a -> head;
		  if ( j == i )
		    break;
		}

		/* backup DFS to the first saturated arc */
		restart = i;
		for ( j = i -> current -> head; j != i; j = a -> head ) {
#ifdef STAT
                nodeScanCnt2 ++;
#endif // STAT
		  a = j -> current;
		  if (( j -> d == WHITE ) || ( a -> resCap == 0 )) {
		    j -> current -> head -> d = WHITE;
		    if ( j -> d != WHITE )
		      restart = j;
		  }
		}

		if ( restart != i ) {
		  i = restart;
		  i->current++;
		  break;
		}
	      }
	  }
	}

	if (i->current == (i+1)->first) {
	  /* scan of i complete */
	  i -> d = BLACK;
	  if ( i != source ) {
	    if ( bos == NULL ) {
	      bos = i;
	      tos = i;
	    }
	    else {
	      i -> bNext = tos;
	      tos = i;
	    }
	  }

	  if ( i != r ) {
	    i = buckets[i-nodes].firstActive;
	    i->current++;
	  }
	  else
	    break;
	}
      } while ( 1 );
    }
  }


  /* return excesses */
  /* note that sink is not on the stack */
  if ( bos != NULL ) {
    for ( i = tos; i != bos; i = i -> bNext ) {
#ifdef STAT
            nodeScanCnt2 ++;
#endif // STAT
      a = i -> first;
      while ( i -> excess > 0 ) {
#ifdef STAT
          arcScanCnt2 ++;
#endif // STAT
	if (( cap[a - arcs] == 0 ) && ( a -> resCap > 0 )) {
	  if (a->resCap < i->excess)
	    delta = a->resCap;
	  else
	    delta = i->excess;
#ifdef STAT
	    pushCnt2 ++;
#endif // STAT
	  a -> resCap -= delta;
	  a -> rev -> resCap += delta;
	  i -> excess -= delta;
	  a -> head -> excess += delta;
#ifdef STAT
	  if (a -> resCap > 0)
          nStrPushCnt2 ++;
      if (i -> excess )
        nDeplPush2++;
      else
        deplPush2++;
#endif // STAT
	}
	a++;
      }
    }
    /* now do the bottom */
    i = bos;
    a = i -> first;
    while ( i -> excess > 0 ) {
#ifdef STAT
        arcScanCnt2 ++;
#endif // STAT
      if (( cap[a - arcs] == 0 ) && ( a -> resCap > 0 )) {
	if (a->resCap < i->excess)
	  delta = a->resCap;
	else
	  delta = i->excess;
#ifdef STAT
	  pushCnt2 ++;
#endif // STAT
	a -> resCap -= delta;
	a -> rev -> resCap += delta;
	i -> excess -= delta;
	a -> head -> excess += delta;
#ifdef STAT
	if (a -> resCap > 0)
          nStrPushCnt2 ++;
    if (i -> excess )
        nDeplPush2++;
      else
        deplPush2++;
#endif // STAT
      }
      a++;
    }
  }
}

#ifndef SIMPLE_INIT
/* second stage -- pseudoflow to flow */
void stageTwoPseudo ( )
/*
   do dsf in the reverse flow graph from nodes with excess
   cancel cycles if found
   return excess flow in topological order
*/

/*
   i->d is used for dfs labels
   i->bNext is used for topological order list
   buckets[i-nodes]->firstActive is used for DSF tree
*/

{
  node *i, *j, *tos, *bos, *restart, *r;
  arc *a;
  cType delta;

  /* dealing with self-loops is not required here
  as they have been removed in the previous part! */

  /* initialize */

  tos = bos = NULL;
  forAllNodes(i) {
#ifdef STAT
    nodeScanCnt2 ++;
#endif // STAT
    i -> d = WHITE;
    //    buckets[i-nodes].firstActive = NULL;
    buckets[i-nodes].firstActive = sentinelNode;
    i -> current = i -> first;
  }


  /* eliminate flow cycles, topologicaly order vertices */
  forAllNodes(i){
#ifdef STAT
      nodeScanCnt2 ++;
#endif // STAT
    if (( i -> d == WHITE ) && ( i -> excess < 0 ) &&
	( i != source ) && ( i != sink )) {
      r = i;
      r -> d = GREY;
#ifdef STAT
      relabelCnt2++;
#endif // STAT
      do {
	for ( ; i->current != (i+1)->first; i->current++) {
	  a = i -> current;
#ifdef STAT
	  arcScanCnt2 ++;
#endif // STAT
	  if (( cap[a - arcs] > 0 ) && ( a -> rev -> resCap > 0 )) {
	    j = a -> head;
	    if ( j -> d == WHITE ) {
	      /* start scanning j */
	      j -> d = GREY;
#ifdef STAT
	      relabelCnt2++;
#endif // STAT
	      buckets[j-nodes].firstActive = i;
	      i = j;
	      break;
	    }
	    else
	      if ( j -> d == GREY ) {
		/* find minimum flow on the cycle */
		delta = a -> rev -> resCap;
		while ( 1 ) {
#ifdef STAT
                arcScanCnt2 ++;
#endif // STAT
		  delta = min ( delta, j -> current -> rev -> resCap );
		  if ( j == i )
		    break;
		  else
		    j = j -> current -> head;
		}

		/* remove delta flow units */
		j = i;
		while ( 1 ) {
		  a = j -> current;
#ifdef STAT
		  pushCnt2 ++;
		  loopPush2++;
#endif // STAT
		  a -> resCap += delta;
		  a -> rev -> resCap -= delta;
#ifdef STAT
		  if (a -> rev -> resCap > 0)
          nStrPushCnt2 ++;
#endif // STAT
		  j = a -> head;
		  if ( j == i )
		    break;
		}

		/* backup DFS to the first saturated arc */
		restart = i;
		for ( j = i -> current -> head; j != i; j = a -> head ) {
#ifdef STAT
                nodeScanCnt2 ++;
#endif // STAT
		  a = j -> current;
		  if (( j -> d == WHITE ) || ( a -> rev -> resCap == 0 )) {
		    j -> current -> head -> d = WHITE;
		    if ( j -> d != WHITE )
		      restart = j;
		  }
		}

		if ( restart != i ) {
		  i = restart;
		  i->current++;
		  break;
		}
	      }
	  }
	}

	if (i->current == (i+1)->first) {
	  /* scan of i complete */
	  i -> d = BLACK;
	  if ( i != source ) {
	    if ( bos == NULL ) {
	      bos = i;
	      tos = i;
	    }
	    else {
	      i -> bNext = tos;
	      tos = i;
	    }
	  }

	  if ( i != r ) {
	    i = buckets[i-nodes].firstActive;
	    i->current++;
	  }
	  else
	    break;
	}
      } while ( 1 );
    }
  }


  /* return excesses */
  /* note that sink is not on the stack */
  if ( bos != NULL ) {
    for ( i = tos; i != bos; i = i -> bNext ) {
#ifdef STAT
            nodeScanCnt2 ++;
#endif // STAT
      a = i -> first;
      while ( i -> excess < 0 ) {
#ifdef STAT
          arcScanCnt2 ++;
#endif // STAT
	if (( cap[a - arcs] > 0 ) && ( a -> rev -> resCap > 0 )) {
	  if (a -> rev ->resCap < abs(i->excess))
	    delta = a -> rev ->resCap;
	  else
	    delta = abs(i->excess);
#ifdef STAT
	    pushCnt2 ++;
#endif // STAT
	  a -> resCap += delta;
	  a -> rev -> resCap -= delta;
	  i -> excess += delta;
	  a -> head -> excess -= delta;
#ifdef STAT
	  if (a -> rev -> resCap > 0)
          nStrPushCnt2 ++;
      if (abs(i -> excess) )
        nDeplPush2++;
      else
        deplPush2++;
#endif // STAT
	}
	a++;
      }
    }
    /* now do the bottom */
    i = bos;
    a = i -> first;
    while ( i -> excess < 0 ) {
#ifdef STAT
        arcScanCnt2 ++;
#endif // STAT
      if (( cap[a - arcs] > 0 ) && ( a -> rev -> resCap > 0 )) {
	if (a->rev->resCap < abs(i->excess))
	  delta = a->rev->resCap;
	else
	  delta = abs(i->excess);
#ifdef STAT
	  pushCnt2 ++;
#endif // STAT
	a -> resCap += delta;
	a -> rev -> resCap -= delta;
	i -> excess += delta;
	a -> head -> excess -= delta;
#ifdef STAT
	if (a -> resCap > 0)
          nStrPushCnt2 ++;
    if (abs(i -> excess ))
        nDeplPush2++;
      else
        deplPush2++;
#endif // STAT
      }
      a++;
    }
  }
flow = sink -> excess;
}
#endif // SIMPLE_INIT


/* gap relabeling */

int gap (emptyB)
     bucket *emptyB;

{

  bucket *l;
  node  *i;
  long  r;           /* index of the bucket before l  */
  int   cc;          /* cc = 1 if no nodes with positive excess before
		      the gap */
#ifdef STAT
  gapCnt ++;
#endif // STAT
  r = ( emptyB - buckets ) - 1;

  /* set labels of nodes beyond the gap to "infinity" */
  for ( l = emptyB + 1; l <= buckets + dMax; l ++ ) {
#ifdef STAT
    nodeScanCntGap++;
#endif // STAT
    /* this does nothing for high level selection
    for (i = l -> firstActive; i != sentinelNode; i = i -> bNext) {
      i -> d = n;
      gNodeCnt++;
    }
    l -> firstActive = sentinelNode;
    */

    for ( i = l -> firstInactive; i != sentinelNode; i = i -> bNext ) {
#ifdef STAT
      relabelCntGap++;
#endif // STAT
      i -> d = n;
#ifdef STAT
      gNodeCnt ++;
#endif // STAT
    }

    l -> firstInactive = sentinelNode;
  }

  cc = ( aMin > r ) ? 1 : 0;

  dMax = r;
  aMax = r;

  return ( cc );

}

/*--- relabelling node i */

long relabel (i)

node *i;   /* node to relabel */

{

  node  *j;
  long  minD;     /* minimum d of a node reachable from i */
  arc   *minA;    /* an arc which leads to the node with minimal d */
  arc   *a;

  assert(i->excess > 0);
#ifdef STAT
  relabelCnt++;
#endif // STAT
  workSinceUpdate += BETA;

  i->d = minD = n;
  minA = NULL;

  /* find the minimum */
  forAllArcs(i,a) {
#ifdef STAT
    workSinceUpdate++;
    arcScanCntLab++;
    arcScanCnt1++;
#endif // STAT
    if (a -> resCap > 0) {
      j = a -> head;
      if (j->d < minD) {
	minD = j->d;
	minA = a;
      }
    }
  }

  minD++;

  if (minD < n) {

    i->d = minD;
    i->current = minA;

    if (dMax < minD) dMax = minD;

  } /* end of minD < n */

#ifdef PROGRESS
    printf("label of node %ld becomes %ld\n", nNode(i), i->d);
    printf("excess is %lld\n", i-> excess);
#endif // PROGRESS

  return ( minD );
} /* end of relabel */


/* discharge: push flow out of i until i becomes inactive */

void discharge (i)

node  *i;

{

  node  *j;                 /* sucsessor of i */
  long  jD;                 /* d of the next bucket */
  bucket *lj;               /* j's bucket */
  bucket *l;                /* i's bucket */
  arc   *a;                 /* current arc (i,j) */
  cType  delta;
  arc *stopA;

  assert(i->excess > 0);
  assert(i != sink);
  do {

    jD = i->d - 1;
    l = buckets + i->d;

    /* scanning arcs outgoing from  i  */
    for (a = i->current, stopA = (i+1)->first; a != stopA; a++) {
#ifdef STAT
      arcScanCnt1 ++;
#endif // STAT
      if (a -> resCap > 0) {
	j = a -> head;

	if (j->d == jD) {
	  //arcScanCnt ++;
	  if (a->resCap < i->excess)
	    delta = a->resCap;
	  else
	    delta = i->excess;
	  a->resCap -= delta;
	  a->rev->resCap += delta;
#ifdef STAT
      pushCnt1++;
      if (a -> resCap > 0)
          nStrPushCnt ++;
#endif // STAT

#ifdef PROGRESS
    printf("pushed %ld through %ld->%ld\n", delta, nNode(i), nNode(j));
#endif // PROGRESS

      lj = buckets + jD;

	  if (j != sink) {

	    if (j->excess == 0) {
	      /* remove j from inactive list */
	      iDelete(lj,j);
#ifdef STAT
	      iDeleteCnt++;
#endif // STAT
	      /* add j to active list */
	      aAdd(lj,j);
#ifdef STAT
	      aAddCnt++;
#endif // STAT
	    }
        //long long int newExceess = j -> excess + delta;
#ifndef SIMPLE_INIT
        if ((j->excess < 0) && (j -> excess + (long long int)delta > 0) ) {
          lj = buckets + 1;
	      /* remove j from inactive list */
	      iDelete(lj,j);
#ifdef STAT
	      iDeleteCnt++;
#endif // STAT
	      /* add j to active list */
	      ++ j->d;
	      aAdd(l,j);
#ifdef STAT
	      aAddCnt++;
#endif // STAT
	    }
	     else if ((j->excess < 0) && (j -> excess + (long long int)delta == 0) ) {
	      /* remove j from inactive list */
	      iDelete(lj,j);
#ifdef STAT
	      iDeleteCnt++;
#endif // STAT
	      /* add j to active list */
	      ++ j->d;
	      iAdd(l,j);
#ifdef STAT
	      aAddCnt++;
#endif // STAT
	    }
#endif // SIMPLE_INIT

	  }

	  j -> excess += delta;
	  i -> excess -= delta;

	  if (i->excess == 0) {
#ifdef STAT
        deplPush1++;
#endif // STAT
        break;
	  }
#ifdef STAT
        nDeplPush1++;
#endif // STAT



	} /* j belongs to the next bucket */
      } /* a  is not saturated */
    } /* end of scanning arcs from  i */

    if (a == stopA) {
      /* i must be relabeled */
      relabel (i);

      if (i->d == n) break;
      if ((l -> firstActive == sentinelNode) &&
	  (l -> firstInactive == sentinelNode)
	  )
	gap (l);

      if (i->d == n) break;
    }
    else {
      /* i no longer active */
      i->current = a;
      /* put i on inactive list */
      iAdd(l,i);
#ifdef STAT
      iAddCnt++;
#endif // STAT
      break;
    }
  } while (1);
}


// go from higher to lower buckets, push flow
void wave() {

  node   *i;
  bucket  *l;

  for (l = buckets + aMax; l > buckets; l--) {
    for (i = l->firstActive; i != sentinelNode; i = l->firstActive) {
      aRemove(l,i);
#ifdef STAT
      aRemoveCnt++;
#endif // STAT

      assert(i->excess > 0);
      discharge (i);

    }
  }
}


/* first stage  -- maximum preflow*/

void stageOne ( )

{
#ifdef PROGRESS
    //printf("sink->excess: %d\n",sink->excess);
#endif // PROGRESS
  node   *i;
  bucket  *l;             /* current bucket */


#if defined(INIT_UPDATE) || defined(OLD_INIT) || defined(WAVE_INIT)
  globalUpdate ();
#endif\

  workSinceUpdate = 0;

#ifdef WAVE_INIT
  wave();
#endif

  /* main loop */
  while ( aMax >= aMin  ) {

#ifdef STAT
    nodeScanCnt1++;
    #endif // STAT
#ifdef PROGRESS
    printf("aMax: %ld\n", aMax);
#endif // PROGRESS
    l = buckets + aMax;
    i = l->firstActive;

    if (i == sentinelNode)
      aMax--;
    else {
      aRemove(l,i);
#ifdef STAT
      aRemoveCnt++;
#endif // STAT
//        if (!(i->excess > 0))
//            printf("excess of node %d is %lld\n",nNode(i), i->excess);
      assert(i->excess > 0);

#ifdef PROGRESS
    printf("Node %ld has excess %ld\n", nNode(i), i->excess);
    printf("sink->excess: %ld\n",sink->excess);
#endif // PROGRESS
          discharge (i);

      if (aMax < aMin)
	break;
#ifndef SIMPLE_INIT
        if ((buckets  + 1)->firstInactive == sentinelNode)
            break;
#endif // SIMPLE_INIT
      /* is it time for global update? */
      if (workSinceUpdate * globUpdtFreq > nm) {
	globalUpdate ();
#ifdef PROGRESS
    printf("\nlabels after Global update: \n");
    forAllNodes(i)
    printf("Node %ld gets label %ld\n", nNode(i), i->d);
    printf("\n");
#endif // PROGRESS
	workSinceUpdate = 0;
      }
    }

  } /* end of the main loop */

  flow = sink -> excess;
#ifdef PROGRESS
    printf("flow is: %f\n", flow);
#endif // PROGRESS
}


int main (argc, argv)

     int   argc;
     char *argv[];

{
#if (defined(PRINT_FLOW) || defined(CHECK_SOLUTION))
  node *i;
  arc *a;
#endif

#ifdef PRINT_FLOW
  long ni, na;
#endif
#ifdef PRINT_CUT
  node *j;
#endif
  int  cc;
#ifdef CHECK_SOLUTION
  excessType sum;
  bucket *l;
#endif


  if (argc > 2) {
    printf("Usage: %s [update frequency]\n", argv[0]);
    exit(1);
  }

  if (argc < 2)
    globUpdtFreq = GLOB_UPDT_FREQ;
  else
    globUpdtFreq = (float) atof(argv[1]);


  //parse( &n, &m, &nodes, &arcs, &cap, &source, &sink, &nMin, &arcScanCnt, &nodeScanCnt );
  #if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
  parse( &n, &m, &nodes, &arcs, &cap, &source, &sink, &nMin, &allCap);
  #else
  parse( &n, &m, &nodes, &arcs, &cap, &source, &sink, &nMin);
  #endif


  cc = allocDS();
#ifdef STAT
  allocDSCnt++;
#endif // STAT
  if ( cc ) { fprintf ( stderr, "Allocation error\n"); exit ( 1 ); }
#ifdef TIME
  t = timer();
  t3 = t;
  t2 = t;
#endif // TIME

#ifdef Test
    printf("n: %d, m: %d\n", n, m);
#endif // PROGRESS

  init();

#ifdef PROGRESS
    printf("Excesses after initialization:\n");
    forAllNodes(i)
    printf("label  of node %ld is %ld with excess %lld \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS

#ifdef TIME
t3 = timer() - t3;
#endif // TIME

#ifdef TEST
//    printf ("Init flow,         %12.01f\n", flow);
//
//    int numDefNode=0;
//    double negExcess=0;
//
//    forAllNodes(i)
//    {
//        if (i->excess<0)
//        {
//            negExcess += i->excess;
//            numDefNode++;
//        }
//    }
//    printf("The whole deficit is %12.01f\n", negExcess);
//    printf("number of remained deficits is: %d\n\n", numDefNode);
//    printf("Source is %d and sink is %d\n", nNode(source), nNode(sink));
#endif // TEST

  stageOne ( );
#ifdef PROGRESS
    printf("Excesses after Stage one:\n");
    forAllNodes(i)
    printf("label  of node %ld is %d with excess %ld \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS

#ifdef TIME
  t2 = timer() - t2;
#endif // TIME

#ifdef TEST
//    printf ("stageone flow,         %12.01f\n", flow);
//
//     numDefNode=0;
//     negExcess=0;
//
//    forAllNodes(i)
//    {
//        if (i->excess<0)
//        {
//            negExcess += i->excess;
//            numDefNode++;
//        }
//    }
//    printf("Remained deficit is %12.01f\n", negExcess);
//    printf("the final flow will be %12.01f\n", flow + negExcess);
//    printf("number of remained deficits is: %d\n\n", numDefNode);
#endif // TEST

#ifndef CUT_ONLY
  stageTwo ( );
#ifndef SIMPLE_INIT
 stageTwoPseudo ();
#endif // SIMPLE_INIT
#ifdef TIME
  t = timer() - t;
#endif // TIME
#ifdef PROGRESS
    printf("Excesses after Stage two:\n");
    forAllNodes(i)
    printf("label  of node %ld is %ld with excess %lld \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS
#endif // CUT_ONLY

#ifdef TEST
//    printf("source excess: %lld, sink excess: %lld\n", source->excess, sink->excess);
#endif // TEST

#ifdef TEST
    printf("nodes,         %10ld\narcs,          %10ld\n", n, m);
    printf ("flow,         %12.01f\n", flow);
#else
  printf("%10ld, %10ld, ", n, m);
  printf ("%12.01f, ", flow);
//  printf("%f, ", (double)(allCap)/(double)(n));
#endif // TEST

#ifdef TIME
#ifdef TEST
  printf ("c init tm:     %12.3f\n", t3);
  printf ("c cut tm:      %12.3f\n", t2);
  printf ("MaxFlow tm,    %12.3f\n", t);
#else
  printf ("%12.3f, ", t3);
  printf ("%12.3f, ", t2);
  printf ("%12.3f, ", t);
#endif // TEST
#endif // TIME

#ifdef STAT
#ifdef TEST
    printf ("\nOperation counts at the first phase of the algorithm are:\n");

    printf ("scans/n:          %10.2f\n",
	    ((double) (relabelCnt + nodeScanCntGlbUp)) / ((double) n));

    printf ("updates,       %10ld\n", updateCnt);
    printf ("nodeScansGlbUp,%10llu\n", nodeScanCntGlbUp);
    printf ("arcScansGlbUp, %10llu\n", arcScanCntGlbUp);
    printf ("RelabelsGlbUp, %10llu\n\n", relabelCntGlbUp);

    printf ("gaps,          %10ld\n", gapCnt);
    printf ("gap nodes,     %10ld\n", gNodeCnt);
    printf ("nodeScansGap,  %10llu\n", nodeScanCntGap);
    printf ("relabelGap,    %10llu\n\n", relabelCntGap);

    printf ("nodeScansI,    %10llu\n", nodeScanCntI);
    printf ("arcScansI,     %10llu\n", arcScanCntI);
    printf ("PushesI,       %10llu\n", pushCntI);
    printf ("StrPushesI,    %10llu\n", pushCntI);
    printf ("RelabelsI,     %10llu\n\n", relabelCntI);

    printf ("arcScanCntLab, %10llu\n\n", arcScanCntLab );

    printf ("nodeScans1,     %10llu\n", nodeScanCnt1);
    printf ("arcScans1,      %10llu\n", arcScanCnt1);
    printf ("StrPushes1,     %10llu\n", pushCnt1 - nStrPushCnt);
    printf ("nStrPushes1,    %10llu\n", nStrPushCnt);
    printf ("pushes1,        %10llu\n", pushCnt1);
    printf ("deplPush1,      %10llu\n", deplPush1);
    printf ("nDeplPush1,     %10llu\n", nDeplPush1);
    printf ("relabels1,      %10llu\n\n", relabelCnt);

    printf ("nodeScans_all_1,%10llu\n", nodeScanCnt1 + nodeScanCntGlbUp + nodeScanCntGap);
    printf ("arcScans_all_1, %10llu\n", arcScanCnt1 + arcScanCntGlbUp  + arcScanCntLab);
    printf ("StrPushes_all_1,%10llu\n", pushCnt1 - nStrPushCnt);
    printf ("nStrPushes_all_1,%10llu\n", nStrPushCnt);
    printf ("pushes_all_1,   %10llu\n", pushCnt1 );
    printf ("relabels_all_1, %10llu\n\n", relabelCnt +  relabelCntGap + relabelCntGlbUp);

    printf("aAddCnt,        %10llu\n", aAddCnt);
    printf("aRemoveCnt,     %10llu\n", aRemoveCnt);
    printf("iAddCnt,        %10llu\n", iAddCnt);
    printf("iDeleteCnt,     %10llu\n", iDeleteCnt);
    printf("allocDSCnt,     %10llu\n\n", allocDSCnt);
#ifndef CUTONLY
  printf ("Operation counts of the second phase of the algorithm are:\n");
  printf ("arcScans2,     %10llu\n", arcScanCnt2);
  printf ("nodeScans2,    %10llu\n", nodeScanCnt2);
  printf ("StrPushes2,    %10llu\n", pushCnt2 - nStrPushCnt2);
  printf ("nStrPushes2,   %10llu\n", nStrPushCnt2);
  printf ("pushes2,       %10llu\n", pushCnt2);
  printf ("deplPushes2,   %10llu\n", deplPush2);
  printf ("nDeplPushes2,  %10llu\n", nDeplPush2);
  printf ("selfLoopPuses2,%10llu\n", selfLoopPush2);
  printf ("loopPushes2,   %10llu\n", loopPush2);
  printf ("relabels2,     %10llu\n\n", relabelCnt2);

  printf ("arcScans,      %10llu\n", arcScanCnt1 + arcScanCnt2 + arcScanCntGlbUp + arcScanCntI + arcScanCntLab);
  printf ("nodeScans,     %10llu\n", nodeScanCnt1 + nodeScanCntGlbUp + nodeScanCntI + nodeScanCntGap + nodeScanCnt2 );
  printf ("pushes,        %10llu\n", pushCnt1 + pushCntI + pushCnt2);
  printf ("relabels,      %10llu\n\n", relabelCnt+relabelCntI+ relabelCntGap + relabelCntGlbUp+relabelCnt2);
#endif // CUT_ONLY

#else

//-----------------------------------------------------------------

    printf ("%10.2f, ", ((double) (relabelCnt + nodeScanCntGlbUp)) / ((double) n));

    printf ("%10ld, ", updateCnt);
    printf ("%10llu, ", nodeScanCntGlbUp);
    printf ("%10llu, ", arcScanCntGlbUp);
    printf ("%10llu, ", relabelCntGlbUp);

    printf ("%10ld, ", gapCnt);
    printf ("%10ld, ", gNodeCnt);
    printf ("%10llu, ", nodeScanCntGap);
    printf ("%10llu, ", relabelCntGap);

    printf ("%10llu, ", nodeScanCntI);
    printf ("%10llu, ", arcScanCntI);
    printf ("%10llu, ", pushCntI);
    printf ("%10llu, ", pushCntI);
    printf ("%10llu, ", relabelCntI);

    printf ("%10llu, ", arcScanCntLab );

    printf ("%10llu, ", nodeScanCnt1);
    printf ("%10llu, ", arcScanCnt1);
    printf ("%10llu, ", pushCnt1 - nStrPushCnt);
    printf ("%10llu, ", nStrPushCnt);
    printf ("%10llu, ", pushCnt1);
    printf ("%10llu, ", deplPush1);
    printf ("%10llu, ", nDeplPush1);
    printf ("%10llu, ", relabelCnt);

    printf ("%10llu, ", nodeScanCnt1 + nodeScanCntGlbUp + nodeScanCntGap);
    printf ("%10llu, ", arcScanCnt1 + arcScanCntGlbUp  + arcScanCntLab);
    printf ("%10llu, ", pushCnt1  - nStrPushCnt);
    printf ("%10llu, ", nStrPushCnt);
    printf ("%10llu, ", pushCnt1 );
    printf ("%10llu, ", relabelCnt  + relabelCntGap + relabelCntGlbUp);

    printf("%10llu, ", aAddCnt);
    printf("%10llu, ", aRemoveCnt);
    printf("%10llu, ", iAddCnt);
    printf("%10llu, ", iDeleteCnt);
    printf("%10llu, ", allocDSCnt);
#ifndef CUT_ONLY
    printf ("%10llu, ", arcScanCnt2);
    printf ("%10llu, ", nodeScanCnt2);
    printf ("%10llu, ", pushCnt2 - nStrPushCnt2);
    printf ("%10llu, ", nStrPushCnt2);
    printf ("%10llu, ", pushCnt2);
    printf ("%10llu, ", deplPush2);
    printf ("%10llu, ", nDeplPush2);
    printf ("%10llu, ", selfLoopPush2);
    printf ("%10llu, ", loopPush2);
    printf ("%10llu, ", relabelCnt2);

    printf ("%10llu, ", arcScanCnt1 + arcScanCnt2 + arcScanCntGlbUp + arcScanCntI + arcScanCntLab);
    printf ("%10llu, ", nodeScanCnt1 + nodeScanCntGlbUp + nodeScanCntI + nodeScanCntGap + nodeScanCnt2 );
    printf ("%10llu, ", pushCnt1 + pushCntI + pushCnt2);
    printf ("%10llu, ", relabelCnt + relabelCntI+ relabelCntGap + relabelCntGlbUp+relabelCnt2);
#endif // CUT_ONLY
#endif // TEST
//-----------------------------------------------------------------
#endif // STAT

#ifdef CHECK_SOLUTION

  /* check if you have a flow (pseudoflow) */
  /* check arc flows */
  forAllNodes(i) {
    forAllArcs(i,a) {
      if (cap[a - arcs] > 0) /* original arc */
	if ((a->resCap + a->rev->resCap != cap[a - arcs])
	    || (a->resCap < 0)
	    || (a->rev->resCap < 0)) {
	  printf("ERROR: bad arc flow\n");
	  exit(2);
	}
    }
  }

  /* check conservation */
  forAllNodes(i)
    if ((i != source) && (i != sink)) {
#ifdef CUT_ONLY
      if (i->excess < 0) {
	printf("ERROR: nonzero node excess\n");
	exit(2);
      }
#else
      if (i->excess != 0) {
	printf("ERROR: nonzero node excess\n");
	exit(2);
      }
#endif

      sum = 0;
      forAllArcs(i,a) {
	if (cap[a - arcs] > 0) /* original arc */
	  sum -= cap[a - arcs] - a->resCap;
	else
	  sum += a->resCap;
      }

      if (i->excess != sum) {
	printf("ERROR: conservation constraint violated\n");
	exit(2);
      }
    }

  /* check if mincut is saturated */
  aMax = dMax = 0;
  for (l = buckets; l < buckets + n; l++) {
    l->firstActive = sentinelNode;
    l->firstInactive = sentinelNode;
  }
  globalUpdate();
  #ifdef TEST
//    printf("source->d: %d, n: %d\n", source->d, n);
#endif // TEST
  if (source->d < n) {
    printf("ERROR: the solution is not optimal\n");
    exit(2);
  }
  //printf("Solution checks (feasible and optimal)\n");
  printf("feasible and optimal");

#endif

#ifdef PROGRESS
printf("\n\nflow is: %f\n", flow);
printf ("flow,         %12.01f\n", flow);
#endif // PROGRESS
#ifdef PRINT_FLOW
    printf ("\nflow values\n");
    forAllNodes(i) {
      ni = nNode(i);
      forAllArcs(i,a) {
	na = nArc(a);
	if ( cap[na] >0 )
	  printf ( "f %7ld %7ld %12ld\n",
		  ni, nNode( a -> head ), cap[na] - ( a -> resCap )
		  );
      }
    }
    printf("c\n");
#endif

#ifdef PRINT_CUT
  globalUpdate();
  printf ("c nodes on the sink side\n");
  forAllNodes(j)
    if (j->d < n)
      printf("c %ld\n", nNode(j));

#endif

exit(0);

}
