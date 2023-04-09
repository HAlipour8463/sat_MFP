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
#include "timer.c"          /* timing routine */

/* Values added from the header file values.h */
#define MAXLONG 1073741824
#define atoll (long long) atof

// #define EXCESS_TYPE_LONG
// #define OLD_INIT
// #define WAVE_INIT
//#define PROGRESS
//#define PRINT_FLOW
// #define PRINT_CUT
//#define CHECK_SOLUTION
// #define CUT_ONLY
//#define STAT
//#define PRINT_STAT
//#define TEST
#define TIME

//#define AVNDCAP
//#define INIT_UPDATE
//#define SIMPLE_INIT
//#define SAT_ALL_INIT
//#define SAT_SMALL_INIT
//#define SAT_LARGE_INIT


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

//#if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
//cType  allCap;             /* sum of all arc capacities */
excessType  allCap;             /* sum of all arc capacities */
//ullint  allCap;             /* sum of all arc capacities */
//#endif

node   *sentinelNode;        /* end of the node list marker */
arc *stopA;                  /* used in forAllArcs */
long workSinceUpdate = 0;    /* the number of arc scans since last update */
float globUpdtFreq;          /* global update frequency */
long updateCnt    = 0;       /* number of updates */
float t, t2, t3;                 /* for saving times */

double avCap;                   /* the average of arc capacities */
double avNdCap;                 /* the arc capacities per node */

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

ullint  StrPushL50avCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to 50% of  avCap*/
        StrPushL75avCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to 75% of  avCap*/
        StrPushL95avCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to 95% of  avCap*/
        StrPushL100avCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to avCap*/
        StrPushL105avCap_c = 0,   /* number of pushes saturating arcs with original capacities less than or equal to 105% of  avCap*/
        StrPushL125avCap_c = 0,   /* number of pushes saturating arcs with original capacities less than or equal to 125% of  avCap*/
        StrPushL150avCap_c = 0,   /* number of pushes saturating arcs with original capacities less than or equal to 150% of  avCap*/

        StrPushL50avNdCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to 50% of  avNdCap*/
        StrPushL75avNdCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to 75% of  avNdCap*/
        StrPushL95avNdCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to 95% of  avNdCap*/
        StrPushL100avNdCap_c = 0,    /* number of pushes saturating arcs with original capacities less than or equal to avNdCap*/
        StrPushL105avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities less than or equal to 105% of  avNdCap*/
        StrPushL125avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities less than or equal to 125% of  avNdCap*/
        StrPushL150avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities less than or equal to 150% of  avNdCap*/

        StrPushG50avCap_c = 0,    /* number of pushes saturating arcs with original capacities greater than or equal to 50% of  avCap*/
        StrPushG75avCap_c = 0,    /* number of pushes saturating arcs with original capacities greater than or equal to 75% of  avCap*/
        StrPushG95avCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 95% of  avCap*/
        StrPushG100avCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to avCap*/
        StrPushG105avCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 105% of  avCap*/
        StrPushG125avCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 125% of  avCap*/
        StrPushG150avCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 150% of  avCap*/

        StrPushG50avNdCap_c = 0,    /* number of pushes saturating arcs with original capacities greater than or equal to 50% of  avNdCap*/
        StrPushG75avNdCap_c = 0,    /* number of pushes saturating arcs with original capacities greater than or equal to 75% of  avNdCap*/
        StrPushG95avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 95% of  avNdCap*/
        StrPushG100avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to avNdCap*/
        StrPushG105avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 105% of  avNdCap*/
        StrPushG125avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 125% of  avNdCap*/
        StrPushG150avNdCap_c = 0,   /* number of pushes saturating arcs with original capacities greater than or equal to 150% of  avNdCap*/

        nStrPushL50avCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to 50% of  avCap*/
        nStrPushL75avCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to 75% of  avCap*/
        nStrPushL95avCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to 95% of  avCap*/
        nStrPushL100avCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to avCap*/
        nStrPushL105avCap_c = 0,   /* number of pushes not saturating arcs with original capacities less than or equal to 105% of  avCap*/
        nStrPushL125avCap_c = 0,   /* number of pushes not saturating arcs with original capacities less than or equal to 125% of  avCap*/
        nStrPushL150avCap_c = 0,   /* number of pushes not saturating arcs with original capacities less than or equal to 150% of  avCap*/

        nStrPushL50avNdCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to 50% of  avNdCap*/
        nStrPushL75avNdCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to 75% of  avNdCap*/
        nStrPushL95avNdCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to 95% of  avNdCap*/
        nStrPushL100avNdCap_c = 0,    /* number of pushes not saturating arcs with original capacities less than or equal to avNdCap*/
        nStrPushL105avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities less than or equal to 105% of  avNdCap*/
        nStrPushL125avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities less than or equal to 125% of  avNdCap*/
        nStrPushL150avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities less than or equal to 150% of  avNdCap*/

        nStrPushG50avCap_c = 0,    /* number of pushes not saturating arcs with original capacities greater than or equal to 50% of  avCap*/
        nStrPushG75avCap_c = 0,    /* number of pushes not saturating arcs with original capacities greater than or equal to 75% of  avCap*/
        nStrPushG95avCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 95% of  avCap*/
        nStrPushG100avCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to avCap*/
        nStrPushG105avCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 105% of  avCap*/
        nStrPushG125avCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 125% of  avCap*/
        nStrPushG150avCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 150% of  avCap*/

        nStrPushG50avNdCap_c = 0,    /* number of pushes not saturating arcs with original capacities greater than or equal to 50% of  avNdCap*/
        nStrPushG75avNdCap_c = 0,    /* number of pushes not saturating arcs with original capacities greater than or equal to 75% of  avNdCap*/
        nStrPushG95avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 95% of  avNdCap*/
        nStrPushG100avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to avNdCap*/
        nStrPushG105avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 105% of  avNdCap*/
        nStrPushG125avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 125% of  avNdCap*/
        nStrPushG150avNdCap_c = 0,   /* number of pushes not saturating arcs with original capacities greater than or equal to 150% of  avNdCap*/

        StrPushL50avCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to 50% of  avCap*/
        StrPushL75avCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to 75% of  avCap*/
        StrPushL95avCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to 95% of  avCap*/
        StrPushL100avCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to avCap*/
        StrPushL105avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities less than or equal to 105% of  avCap*/
        StrPushL125avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities less than or equal to 125% of  avCap*/
        StrPushL150avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities less than or equal to 150% of  avCap*/

        StrPushL50avNdCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to 50% of  avNdCap*/
        StrPushL75avNdCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to 75% of  avNdCap*/
        StrPushL95avNdCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to 95% of  avNdCap*/
        StrPushL100avNdCap_rc = 0,    /* number of pushes saturating arcs with residual capacities less than or equal to avNdCap*/
        StrPushL105avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities less than or equal to 105% of  avNdCap*/
        StrPushL125avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities less than or equal to 125% of  avNdCap*/
        StrPushL150avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities less than or equal to 150% of  avNdCap*/

        StrPushG50avCap_rc = 0,    /* number of pushes saturating arcs with residual capacities greater than or equal to 50% of  avCap*/
        StrPushG75avCap_rc = 0,    /* number of pushes saturating arcs with residual capacities greater than or equal to 75% of  avCap*/
        StrPushG95avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 95% of  avCap*/
        StrPushG100avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to avCap*/
        StrPushG105avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 105% of  avCap*/
        StrPushG125avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 125% of  avCap*/
        StrPushG150avCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 150% of  avCap*/

        StrPushG50avNdCap_rc = 0,    /* number of pushes saturating arcs with residual capacities greater than or equal to 50% of  avNdCap*/
        StrPushG75avNdCap_rc = 0,    /* number of pushes saturating arcs with residual capacities greater than or equal to 75% of  avNdCap*/
        StrPushG95avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 95% of  avNdCap*/
        StrPushG100avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to avNdCap*/
        StrPushG105avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 105% of  avNdCap*/
        StrPushG125avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 125% of  avNdCap*/
        StrPushG150avNdCap_rc = 0,   /* number of pushes saturating arcs with residual capacities greater than or equal to 150% of  avNdCap*/

        nStrPushL50avCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to 50% of  avCap*/
        nStrPushL75avCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to 75% of  avCap*/
        nStrPushL95avCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to 95% of  avCap*/
        nStrPushL100avCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to avCap*/
        nStrPushL105avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities less than or equal to 105% of  avCap*/
        nStrPushL125avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities less than or equal to 125% of  avCap*/
        nStrPushL150avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities less than or equal to 150% of  avCap*/

        nStrPushL50avNdCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to 50% of  avNdCap*/
        nStrPushL75avNdCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to 75% of  avNdCap*/
        nStrPushL95avNdCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to 95% of  avNdCap*/
        nStrPushL100avNdCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities less than or equal to avNdCap*/
        nStrPushL105avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities less than or equal to 105% of  avNdCap*/
        nStrPushL125avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities less than or equal to 125% of  avNdCap*/
        nStrPushL150avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities less than or equal to 150% of  avNdCap*/

        nStrPushG50avCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities greater than or equal to 50% of  avCap*/
        nStrPushG75avCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities greater than or equal to 75% of  avCap*/
        nStrPushG95avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 95% of  avCap*/
        nStrPushG100avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 100% of  avCap*/
        nStrPushG105avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to avCap*/
        nStrPushG125avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 125% of  avCap*/
        nStrPushG150avCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 150% of  avCap*/

        nStrPushG50avNdCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities greater than or equal to 50% of  avNdCap*/
        nStrPushG75avNdCap_rc = 0,    /* number of pushes not saturating arcs with residual capacities greater than or equal to 75% of  avNdCap*/
        nStrPushG95avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 95% of  avNdCap*/
        nStrPushG100avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to avNdCap*/
        nStrPushG105avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 105% of  avNdCap*/
        nStrPushG125avNdCap_rc = 0,   /* number of pushes not saturating arcs with residual capacities greater than or equal to 125% of  avNdCap*/
        nStrPushG150avNdCap_rc = 0;   /* number of pushes not saturating arcs with residual capacities greater than or equal to 150% of  avNdCap*/

#endif // STAT

/* macros */

#define forAllNodes(i) for ( i = nodes; i != sentinelNode; i++ )
#define forAllArcs(i,a) for (a = i->first, stopA = (i+1)->first; a != stopA; a++)

#define nNode( i ) ( (i) - nodes + nMin )
#define nArc( a )  ( ( a == NULL )? -1 : (a) - arcs )

#define min( a, b ) ( ( (a) < (b) ) ? a : b )
#define max( a, b ) ( ( (a) > (b) ) ? a : b )

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

#ifdef STAT
/* Count different types of arc saturations  */

int satCount(tstCap, tstResCap, tstDelta)
{
    long satState;
    //cType *tstCap, *tstResCap, *tstDelta;

    if (tstResCap == tstDelta)
    {
        if (tstResCap == tstCap)
            satState = 11;
        else
            satState = 12;
    }
    else
    {
        if (tstResCap == tstCap)
            satState = 21;
        else
            satState = 22;
    }

    switch (satState) {
      case 11:
	if (tstResCap >= avCap)
    {
        if (tstResCap >= 1.5 * avCap)
        {
            StrPushG50avCap_c ++;
            StrPushG75avCap_c ++;
            StrPushG95avCap_c ++;
            StrPushG100avCap_c ++;
            StrPushG105avCap_c ++;
            StrPushG125avCap_c ++;
            StrPushG150avCap_c ++;
        }
        else if (tstResCap >= 1.25 * avCap)
        {
            StrPushG50avCap_c ++;
            StrPushG75avCap_c ++;
            StrPushG95avCap_c ++;
            StrPushG100avCap_c ++;
            StrPushG105avCap_c ++;
            StrPushG125avCap_c ++;
            StrPushL150avCap_c ++;
        }
        else if (tstResCap >= 1.05 * avCap)
        {
            StrPushG50avCap_c ++;
            StrPushG75avCap_c ++;
            StrPushG95avCap_c ++;
            StrPushG100avCap_c ++;
            StrPushG105avCap_c ++;
            StrPushL125avCap_c ++;
            StrPushL150avCap_c ++;
        }
        else
        {
            StrPushG50avCap_c ++;
            StrPushG75avCap_c ++;
            StrPushG95avCap_c ++;
            StrPushG100avCap_c ++;
            StrPushL105avCap_c ++;
            StrPushL125avCap_c ++;
            StrPushL150avCap_c ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avCap)
        {
            StrPushL50avCap_c ++;
            StrPushL75avCap_c ++;
            StrPushL95avCap_c ++;
            StrPushL100avCap_c ++;
            StrPushL105avCap_c ++;
            StrPushL125avCap_c ++;
            StrPushL150avCap_c ++;
        }
        else if (tstResCap <= 0.75 * avCap)
        {
            StrPushG50avCap_c ++;
            StrPushL75avCap_c ++;
            StrPushL95avCap_c ++;
            StrPushL100avCap_c ++;
            StrPushL105avCap_c ++;
            StrPushL125avCap_c ++;
            StrPushL150avCap_c ++;
        }
        else if (tstResCap <= 0.95 * avCap)
        {
            StrPushG50avCap_c ++;
            StrPushG75avCap_c ++;
            StrPushL95avCap_c ++;
            StrPushL100avCap_c ++;
            StrPushL105avCap_c ++;
            StrPushL125avCap_c ++;
            StrPushL150avCap_c ++;
        }
        else
        {
            StrPushG50avCap_c ++;
            StrPushG75avCap_c ++;
            StrPushG95avCap_c ++;
            StrPushL100avCap_c ++;
            StrPushL105avCap_c ++;
            StrPushL125avCap_c ++;
            StrPushL150avCap_c ++;
        }
    }
    //%%%%%%%%%%%%%%%%%%%%%%%
    if (tstResCap >= avNdCap)
    {
        if (tstResCap >= 1.5 * avNdCap)
        {
            StrPushG50avNdCap_c ++;
            StrPushG75avNdCap_c ++;
            StrPushG95avNdCap_c ++;
            StrPushG100avNdCap_c ++;
            StrPushG105avNdCap_c ++;
            StrPushG125avNdCap_c ++;
            StrPushG150avNdCap_c ++;
        }
        else if (tstResCap >= 1.25 * avNdCap)
        {
            StrPushG50avNdCap_c ++;
            StrPushG75avNdCap_c ++;
            StrPushG95avNdCap_c ++;
            StrPushG100avNdCap_c ++;
            StrPushG105avNdCap_c ++;
            StrPushG125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
        else if (tstResCap >= 1.05 * avNdCap)
        {
            StrPushG50avNdCap_c ++;
            StrPushG75avNdCap_c ++;
            StrPushG95avNdCap_c ++;
            StrPushG100avNdCap_c ++;
            StrPushG105avNdCap_c ++;
            StrPushL125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
        else
        {
            StrPushG50avNdCap_c ++;
            StrPushG75avNdCap_c ++;
            StrPushG95avNdCap_c ++;
            StrPushG100avNdCap_c ++;
            StrPushL105avNdCap_c ++;
            StrPushL125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avNdCap)
        {
            StrPushL50avNdCap_c ++;
            StrPushL75avNdCap_c ++;
            StrPushL95avNdCap_c ++;
            StrPushL100avNdCap_c ++;
            StrPushL105avNdCap_c ++;
            StrPushL125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
        else if (tstResCap <= 0.75 * avNdCap)
        {
            StrPushG50avNdCap_c ++;
            StrPushL75avNdCap_c ++;
            StrPushL95avNdCap_c ++;
            StrPushL100avNdCap_c ++;
            StrPushL105avNdCap_c ++;
            StrPushL125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
        else if (tstResCap <= 0.95 * avNdCap)
        {
            StrPushG50avNdCap_c ++;
            StrPushG75avNdCap_c ++;
            StrPushL95avNdCap_c ++;
            StrPushL100avNdCap_c ++;
            StrPushL105avNdCap_c ++;
            StrPushL125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
        else
        {
            StrPushG50avNdCap_c ++;
            StrPushG75avNdCap_c ++;
            StrPushG95avNdCap_c ++;
            StrPushL100avNdCap_c ++;
            StrPushL105avNdCap_c ++;
            StrPushL125avNdCap_c ++;
            StrPushL150avNdCap_c ++;
        }
    }
	break;
      case 12:
	if (tstResCap >= avCap)
    {
        if (tstResCap >= 1.5 * avCap)
        {
            StrPushG50avCap_rc ++;
            StrPushG75avCap_rc ++;
            StrPushG95avCap_rc ++;
            StrPushG100avCap_rc ++;
            StrPushG105avCap_rc ++;
            StrPushG125avCap_rc ++;
            StrPushG150avCap_rc ++;
        }
        else if (tstResCap >= 1.25 * avCap)
        {
            StrPushG50avCap_rc ++;
            StrPushG75avCap_rc ++;
            StrPushG95avCap_rc ++;
            StrPushG100avCap_rc ++;
            StrPushG105avCap_rc ++;
            StrPushG125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
        else if (tstResCap >= 1.05 * avCap)
        {
            StrPushG50avCap_rc ++;
            StrPushG75avCap_rc ++;
            StrPushG95avCap_rc ++;
            StrPushG100avCap_rc ++;
            StrPushG105avCap_rc ++;
            StrPushL125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
        else
        {
            StrPushG50avCap_rc ++;
            StrPushG75avCap_rc ++;
            StrPushG95avCap_rc ++;
            StrPushG100avCap_rc ++;
            StrPushL105avCap_rc ++;
            StrPushL125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avCap)
        {
            StrPushL50avCap_rc ++;
            StrPushL75avCap_rc ++;
            StrPushL95avCap_rc ++;
            StrPushL100avCap_rc ++;
            StrPushL105avCap_rc ++;
            StrPushL125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
        else if (tstResCap <= 0.75 * avCap)
        {
            StrPushG50avCap_rc ++;
            StrPushL75avCap_rc ++;
            StrPushL95avCap_rc ++;
            StrPushL100avCap_rc ++;
            StrPushL105avCap_rc ++;
            StrPushL125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
        else if (tstResCap <= 0.95 * avCap)
        {
            StrPushG50avCap_rc ++;
            StrPushG75avCap_rc ++;
            StrPushL95avCap_rc ++;
            StrPushL100avCap_rc ++;
            StrPushL105avCap_rc ++;
            StrPushL125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
        else
        {
            StrPushG50avCap_rc ++;
            StrPushG75avCap_rc ++;
            StrPushG95avCap_rc ++;
            StrPushL100avCap_rc ++;
            StrPushL105avCap_rc ++;
            StrPushL125avCap_rc ++;
            StrPushL150avCap_rc ++;
        }
    }
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%
    if (tstResCap >= avNdCap)
    {
        if (tstResCap >= 1.5 * avNdCap)
        {
            StrPushG50avNdCap_rc ++;
            StrPushG75avNdCap_rc ++;
            StrPushG95avNdCap_rc ++;
            StrPushG100avNdCap_rc ++;
            StrPushG105avNdCap_rc ++;
            StrPushG125avNdCap_rc ++;
            StrPushG150avNdCap_rc ++;
        }
        else if (tstResCap >= 1.25 * avNdCap)
        {
            StrPushG50avNdCap_rc ++;
            StrPushG75avNdCap_rc ++;
            StrPushG95avNdCap_rc ++;
            StrPushG100avNdCap_rc ++;
            StrPushG105avNdCap_rc ++;
            StrPushG125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
        else if (tstResCap >= 1.05 * avNdCap)
        {
            StrPushG50avNdCap_rc ++;
            StrPushG75avNdCap_rc ++;
            StrPushG95avNdCap_rc ++;
            StrPushG100avNdCap_rc ++;
            StrPushG105avNdCap_rc ++;
            StrPushL125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
        else
        {
            StrPushG50avNdCap_rc ++;
            StrPushG75avNdCap_rc ++;
            StrPushG95avNdCap_rc ++;
            StrPushG100avNdCap_rc ++;
            StrPushL105avNdCap_rc ++;
            StrPushL125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avNdCap)
        {
            StrPushL50avNdCap_rc ++;
            StrPushL75avNdCap_rc ++;
            StrPushL95avNdCap_rc ++;
            StrPushL100avNdCap_rc ++;
            StrPushL105avNdCap_rc ++;
            StrPushL125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
        else if (tstResCap <= 0.75 * avNdCap)
        {
            StrPushG50avNdCap_rc ++;
            StrPushL75avNdCap_rc ++;
            StrPushL95avNdCap_rc ++;
            StrPushL100avNdCap_rc ++;
            StrPushL105avNdCap_rc ++;
            StrPushL125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
        else if (tstResCap <= 0.95 * avNdCap)
        {
            StrPushG50avNdCap_rc ++;
            StrPushG75avNdCap_rc ++;
            StrPushL95avNdCap_rc ++;
            StrPushL100avNdCap_rc ++;
            StrPushL105avNdCap_rc ++;
            StrPushL125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
        else
        {
            StrPushG50avNdCap_rc ++;
            StrPushG75avNdCap_rc ++;
            StrPushG95avNdCap_rc ++;
            StrPushL100avNdCap_rc ++;
            StrPushL105avNdCap_rc ++;
            StrPushL125avNdCap_rc ++;
            StrPushL150avNdCap_rc ++;
        }
    }
	break;
      case 21:
	if (tstResCap >= avCap)
    {
        if (tstResCap >= 1.5 * avCap)
        {
            nStrPushG50avCap_c ++;
            nStrPushG75avCap_c ++;
            nStrPushG95avCap_c ++;
            nStrPushG100avCap_c ++;
            nStrPushG105avCap_c ++;
            nStrPushG125avCap_c ++;
            nStrPushG150avCap_c ++;
        }
        else if (tstResCap >= 1.25 * avCap)
        {
            nStrPushG50avCap_c ++;
            nStrPushG75avCap_c ++;
            nStrPushG95avCap_c ++;
            nStrPushG100avCap_c ++;
            nStrPushG105avCap_c ++;
            nStrPushG125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
        else if (tstResCap >= 1.05 * avCap)
        {
            nStrPushG50avCap_c ++;
            nStrPushG75avCap_c ++;
            nStrPushG95avCap_c ++;
            nStrPushG100avCap_c ++;
            nStrPushG105avCap_c ++;
            nStrPushL125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
        else
        {
            nStrPushG50avCap_c ++;
            nStrPushG75avCap_c ++;
            nStrPushG95avCap_c ++;
            nStrPushG100avCap_c ++;
            nStrPushL105avCap_c ++;
            nStrPushL125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avCap)
        {
            nStrPushL50avCap_c ++;
            nStrPushL75avCap_c ++;
            nStrPushL95avCap_c ++;
            nStrPushL100avCap_c ++;
            nStrPushL105avCap_c ++;
            nStrPushL125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
        else if (tstResCap <= 0.75 * avCap)
        {
            nStrPushG50avCap_c ++;
            nStrPushL75avCap_c ++;
            nStrPushL95avCap_c ++;
            nStrPushL100avCap_c ++;
            nStrPushL105avCap_c ++;
            nStrPushL125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
        else if (tstResCap <= 0.95 * avCap)
        {
            nStrPushG50avCap_c ++;
            nStrPushG75avCap_c ++;
            nStrPushL95avCap_c ++;
            nStrPushL100avCap_c ++;
            nStrPushL105avCap_c ++;
            nStrPushL125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
        else
        {
            nStrPushG50avCap_c ++;
            nStrPushG75avCap_c ++;
            nStrPushG95avCap_c ++;
            nStrPushL100avCap_c ++;
            nStrPushL105avCap_c ++;
            nStrPushL125avCap_c ++;
            nStrPushL150avCap_c ++;
        }
    }
    //%%%%%%%%%%%%%%%%%%%%
    if (tstResCap >= avNdCap)
    {
        if (tstResCap >= 1.5 * avNdCap)
        {
            nStrPushG50avNdCap_c ++;
            nStrPushG75avNdCap_c ++;
            nStrPushG95avNdCap_c ++;
            nStrPushG100avNdCap_c ++;
            nStrPushG105avNdCap_c ++;
            nStrPushG125avNdCap_c ++;
            nStrPushG150avNdCap_c ++;
        }
        else if (tstResCap >= 1.25 * avNdCap)
        {
            nStrPushG50avNdCap_c ++;
            nStrPushG75avNdCap_c ++;
            nStrPushG95avNdCap_c ++;
            nStrPushG100avNdCap_c ++;
            nStrPushG105avNdCap_c ++;
            nStrPushG125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
        else if (tstResCap >= 1.05 * avNdCap)
        {
            nStrPushG50avNdCap_c ++;
            nStrPushG75avNdCap_c ++;
            nStrPushG95avNdCap_c ++;
            nStrPushG100avNdCap_c ++;
            nStrPushG105avNdCap_c ++;
            nStrPushL125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
        else
        {
            nStrPushG50avNdCap_c ++;
            nStrPushG75avNdCap_c ++;
            nStrPushG95avNdCap_c ++;
            nStrPushG100avNdCap_c ++;
            nStrPushL105avNdCap_c ++;
            nStrPushL125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avNdCap)
        {
            nStrPushL50avNdCap_c ++;
            nStrPushL75avNdCap_c ++;
            nStrPushL95avNdCap_c ++;
            nStrPushL100avNdCap_c ++;
            nStrPushL105avNdCap_c ++;
            nStrPushL125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
        else if (tstResCap <= 0.75 * avNdCap)
        {
            nStrPushG50avNdCap_c ++;
            nStrPushL75avNdCap_c ++;
            nStrPushL95avNdCap_c ++;
            nStrPushL100avNdCap_c ++;
            nStrPushL105avNdCap_c ++;
            nStrPushL125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
        else if (tstResCap <= 0.95 * avNdCap)
        {
            nStrPushG50avNdCap_c ++;
            nStrPushG75avNdCap_c ++;
            nStrPushL95avNdCap_c ++;
            nStrPushL100avNdCap_c ++;
            nStrPushL105avNdCap_c ++;
            nStrPushL125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
        else
        {
            nStrPushG50avNdCap_c ++;
            nStrPushG75avNdCap_c ++;
            nStrPushG95avNdCap_c ++;
            nStrPushL100avNdCap_c ++;
            nStrPushL105avNdCap_c ++;
            nStrPushL125avNdCap_c ++;
            nStrPushL150avNdCap_c ++;
        }
    }
	break;
      case 22:
	if (tstResCap >= avCap)
    {
        if (tstResCap >= 1.5 * avCap)
        {
            nStrPushG50avCap_rc ++;
            nStrPushG75avCap_rc ++;
            nStrPushG95avCap_rc ++;
            nStrPushG100avCap_rc ++;
            nStrPushG105avCap_rc ++;
            nStrPushG125avCap_rc ++;
            nStrPushG150avCap_rc ++;
        }
        else if (tstResCap >= 1.25 * avCap)
        {
            nStrPushG50avCap_rc ++;
            nStrPushG75avCap_rc ++;
            nStrPushG95avCap_rc ++;
            nStrPushG100avCap_rc ++;
            nStrPushG105avCap_rc ++;
            nStrPushG125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
        else if (tstResCap >= 1.05 * avCap)
        {
            nStrPushG50avCap_rc ++;
            nStrPushG75avCap_rc ++;
            nStrPushG95avCap_rc ++;
            nStrPushG100avCap_rc ++;
            nStrPushG105avCap_rc ++;
            nStrPushL125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
        else
        {
            nStrPushG50avCap_rc ++;
            nStrPushG75avCap_rc ++;
            nStrPushG95avCap_rc ++;
            nStrPushG100avCap_rc ++;
            nStrPushL105avCap_rc ++;
            nStrPushL125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avCap)
        {
            nStrPushL50avCap_rc ++;
            nStrPushL75avCap_rc ++;
            nStrPushL95avCap_rc ++;
            nStrPushL100avCap_rc ++;
            nStrPushL105avCap_rc ++;
            nStrPushL125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
        else if (tstResCap <= 0.75 * avCap)
        {
            nStrPushG50avCap_rc ++;
            nStrPushL75avCap_rc ++;
            nStrPushL95avCap_rc ++;
            nStrPushL100avCap_rc ++;
            nStrPushL105avCap_rc ++;
            nStrPushL125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
        else if (tstResCap <= 0.95 * avCap)
        {
            nStrPushG50avCap_rc ++;
            nStrPushG75avCap_rc ++;
            nStrPushL95avCap_rc ++;
            nStrPushL100avCap_rc ++;
            nStrPushL105avCap_rc ++;
            nStrPushL125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
        else
        {
            nStrPushG50avCap_rc ++;
            nStrPushG75avCap_rc ++;
            nStrPushG95avCap_rc ++;
            nStrPushL100avCap_rc ++;
            nStrPushL105avCap_rc ++;
            nStrPushL125avCap_rc ++;
            nStrPushL150avCap_rc ++;
        }
    }
    //%%%%%%%%%%%%%%%%%%%%%%%%%%%
    if (tstResCap >= avNdCap)
    {
        if (tstResCap >= 1.5 * avNdCap)
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushG75avNdCap_rc ++;
            nStrPushG95avNdCap_rc ++;
            nStrPushG100avNdCap_rc ++;
            nStrPushG105avNdCap_rc ++;
            nStrPushG125avNdCap_rc ++;
            nStrPushG150avNdCap_rc ++;
        }
        else if (tstResCap >= 1.25 * avNdCap)
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushG75avNdCap_rc ++;
            nStrPushG95avNdCap_rc ++;
            nStrPushG100avNdCap_rc ++;
            nStrPushG105avNdCap_rc ++;
            nStrPushG125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
        else if (tstResCap >= 1.05 * avNdCap)
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushG75avNdCap_rc ++;
            nStrPushG95avNdCap_rc ++;
            nStrPushG100avNdCap_rc ++;
            nStrPushG105avNdCap_rc ++;
            nStrPushL125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
        else
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushG75avNdCap_rc ++;
            nStrPushG95avNdCap_rc ++;
            nStrPushG100avNdCap_rc ++;
            nStrPushL105avNdCap_rc ++;
            nStrPushL125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
    }
    else
    {
        if (tstResCap <= 0.5 * avNdCap)
        {
            nStrPushL50avNdCap_rc ++;
            nStrPushL75avNdCap_rc ++;
            nStrPushL95avNdCap_rc ++;
            nStrPushL100avNdCap_rc ++;
            nStrPushL105avNdCap_rc ++;
            nStrPushL125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
        else if (tstResCap <= 0.75 * avNdCap)
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushL75avNdCap_rc ++;
            nStrPushL95avNdCap_rc ++;
            nStrPushL100avNdCap_rc ++;
            nStrPushL105avNdCap_rc ++;
            nStrPushL125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
        else if (tstResCap <= 0.95 * avNdCap)
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushG75avNdCap_rc ++;
            nStrPushL95avNdCap_rc ++;
            nStrPushL100avNdCap_rc ++;
            nStrPushL105avNdCap_rc ++;
            nStrPushL125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
        else
        {
            nStrPushG50avNdCap_rc ++;
            nStrPushG75avNdCap_rc ++;
            nStrPushG95avNdCap_rc ++;
            nStrPushL100avNdCap_rc ++;
            nStrPushL105avNdCap_rc ++;
            nStrPushL125avNdCap_rc ++;
            nStrPushL150avNdCap_rc ++;
        }
    }
	break;
      default:
	assert(0);
	break;
      }

//      return(0);
}
#endif // STAT

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
#ifdef PROGRESS
        printf("\nsentinelNode: %d ( before allocDS)\n", nNode(sentinelNode));
        printf("\n nMin: %d ( before allocDS)\n", nMin);
#endif // PROGRESS

  sentinelNode = nodes + n;
  sentinelNode->first = arcs + 2*m;

#ifdef PROGRESS
        printf("\nsentinelNode: %d (after allocDS)\n", nNode(sentinelNode));
        printf("\n sentinelNode->first: %d (after allocDS)\n", nNode(sentinelNode->first->head));
#endif // PROGRESS

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
  cType delta;
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

int b;                         /* boolean variable */



forAllNodes(i) {
        if((i != sink)){
             forAllArcs(i,a) {
#ifdef STAT
            arcScanCntI++;
#endif // STAT

#ifdef SAT_SMALL_INIT
#ifdef AVNDCAP
    if ((a->head != source) && (i != sink) &&  (cap[a-arcs]>0) && (cap[a-arcs] <= 1.05 *avNdCap)) b = 1;
    else b = 0;
#else
    if ((a->head != source) && (i != sink) &&  (cap[a-arcs]>0) && (cap[a-arcs] <= 1.05 *avCap)) b = 1;
    else b = 0;
#endif // AVNDCAP
#endif // SAT_SMALL_INIT
#ifdef SAT_LARGE_INIT
#ifdef AVNDCAP
    if((a->head != source) && (i != sink) && (cap[a-arcs] >= 0.95 *avNdCap)) b = 1;
    else b = 0;
#else
    if((a->head != source) && (i != sink) && (cap[a-arcs] >= 0.95 *avCap)) b = 1;
    else b = 0;
#endif // AVNDCAP
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

  aMax = 0;
  aMin = n;
  dMax = 0;

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
#ifdef PROGRESS
        printf("\n%d->bNext: %d (before iAdd Init)\n", nNode(i), nNode(i->bNext));
        printf("\nl->firstInactive: %d (before iAdd Init)\n",  nNode(l->firstInactive));
#endif // PROGRESS
            iAdd(l,i);
#ifdef PROGRESS
        printf("\n%d->bNext: %d (iAdd Init)\n", nNode(i), nNode(i->bNext));
    if (nNode(i) == 1023)
        printf("\n%d->bNext: %d (iAdd Init)\n", nNode(i), nNode(i->bNext));
#endif // PROGRESS
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
  long curDist, curDistStart = 0, jD;
  long state;

  updateCnt ++;

  /* initialization */

#ifdef PROGRESS
    printf("\nBefore reseting buckets through the global update, dMax: %d, aMax: %d, aMin: %d \n",
           dMax, aMax, aMin);
#endif // PROGRESS

#ifdef SIMPLE_INIT
  for (l = buckets; l <= buckets + dMax; l++) {
    l -> firstActive   = sentinelNode;
    l -> firstInactive  = sentinelNode;
  }
#else
    for (l = buckets +2; l <= buckets + max(dMax , 2); l++) {
    l -> firstActive   = sentinelNode;
    l -> firstInactive  = sentinelNode;
  }
#endif // SIMPLE_INIT

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
    if (i->excess >= 0 )
    {
        i -> d = n;
#ifdef STAT
    relabelCntGlbUp++;
#endif // STAT
    }
#endif // SIMPLE_INIT
#ifdef PROGRESS
    printf("\n%d->bNext: %d (After reseting buckets through the global update)\n", nNode(i), nNode(i->bNext));
    if (nNode(i->bNext) == 4)
        printf("\n%d->bNext: %d\n", nNode(i), nNode(i->bNext));
    if (i->bNext == sink)
        printf("\nsink->bNext: %d\n", nNode(sink->bNext));
#endif // PROGRESS
  }
  sink -> d = 0;

  dMax = 1;
  aMax = 0;
  aMin = n;

  /* breadth first search */

#ifdef SIMPLE_INIT
  // add sink to bucket zero
  iAdd(buckets, sink);
#ifdef STAT
  iAddCnt++;
#endif // STAT
#endif // SIMPLE_INIT

#ifdef PROGRESS
    printf("sink is %d\n",nNode(sink));
#endif // PROGRESS

#ifndef SIMPLE_INIT
    curDistStart =1 ;
#endif // SIMPLE_INIT

#ifdef PROGRESS
    printf("\n curDistStart: %d\n",curDistStart);
    int idx=0;
#endif // PROGRESS

  for (curDist = curDistStart; 1; curDist++) {
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

#ifdef PROGRESS
    printf("\ncurDist: %d\n",curDist);
#endif // PROGRESS

    while (1) {
#ifdef PROGRESS
    printf("\n%d->bNext: %d (while loop)\n", nNode(i), nNode(i->bNext));
    if (nNode(i->bNext) == 4)
        printf("\n%d->bNext: %d\n", nNode(i), nNode(i->bNext));
    if (i->bNext == sink)
        printf("\nsink->bNext: %d\n", nNode(sink->bNext));
#endif // PROGRESS

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
#ifdef PROGRESS
    printf("\nscanning arcs incident to node %d with label %d and excess %lld\n", nNode(i), i->d, i->excess);
#endif // PROGRESS
      forAllArcs(i,a) {
#ifdef STAT
        arcScanCntGlbUp ++;
#endif // STAT
#ifdef PROGRESS
    printf("scanning the reverse of arc %d -> %d with resCap %ld\n", nNode(i), nNode(a->head), a->rev->resCap);
    printf("label of %d is %d with excess %lld\n", nNode(a->head), a->head->d, a->head->excess);
#endif // PROGRESS
	if (a->rev->resCap > 0 ) {
	  j = a->head;
//#ifdef PROGRESS
//    printf("scanning the reverse of arc %d -> %d\n", nNode(i), nNode(a->head));
//    printf("label of %d is %d with excess %lld\n", nNode(a->head), a->head->d, a->head->excess);
//#endif // PROGRESS
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
#ifdef PROGRESS
    if (nNode(j) == 1023)
        printf("\n%d->bNext: %d (iAdd)\n", nNode(j), nNode(j->bNext));
        printf("\n%d->bNext: %d (iAdd)\n",nNode(sink), nNode(sink->bNext));
#endif // PROGRESS
#ifdef STAT
	      iAddCnt++;
#endif // STAT
	    }
	  }
	}
#ifdef PROGRESS
    printf("label of %d is %d after scanning the reverse of arc %d -> %d\n\n", nNode(a->head), a->head->d, nNode(i), nNode(a->head));
#endif // PROGRESS
      } /* node i is scanned */
    }
  }
#ifdef PROGRESS
    printf("\nAfter reseting buckets through the global update, dMax: %d, aMax: %d, aMin: %d \n\n",
           dMax, aMax, aMin);
#endif // PROGRESS
} /* end of global update */


void globalUpdate2 ()

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

#ifdef PROGRESS
    printf("\nBefore reseting buckets through the global update 2, dMax: %d, aMax: %d, aMin: %d \n",
           dMax, aMax, aMin);
#endif // PROGRESS

  for (l = buckets; l <= buckets + dMax; l++) {
    l -> firstActive   = sentinelNode;
    l -> firstInactive  = sentinelNode;
  }

  forAllNodes(i){
#ifdef STAT
      nodeScanCntGlbUp ++;
#endif // STAT
    i -> d = n;
#ifdef STAT
    relabelCntGlbUp++;
#endif // STAT
  }
  sink -> d = 0;

  dMax = 1;
  aMax = 0;
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

#ifdef PROGRESS
    printf("\ncurDist: %d\n",curDist);
    int idx=0;
#endif // PROGRESS

    while (1) {
#ifdef PROGRESS
    printf("running the while loop within global update 2 %d time\n", idx + curDist );
    ++idx;
#endif // PROGRESS

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
#ifdef PROGRESS
    printf("\nAfter reseting buckets through the global update, dMax: %d, aMax: %d, aMin: %d \n",
           dMax, aMax, aMin);
#endif // PROGRESS
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
#ifdef STAT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // STAT
	  a->resCap -= delta;
	  a->rev->resCap += delta;
#ifdef STAT
      pushCnt1++;
      if (a -> resCap > 0){
        nStrPushCnt ++;
      }

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
#ifdef PROGRESS
    printf("\nExcesses after initialization and global update:\n");
    forAllNodes(i)
    printf("label  of node %ld is %ld with excess %lld \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS
#endif // defined

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
//  #if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
  parse( &n, &m, &nodes, &arcs, &cap, &source, &sink, &nMin, &allCap);
//  #else
//  parse( &n, &m, &nodes, &arcs, &cap, &source, &sink, &nMin);
//  #endif


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

avCap = (double)(allCap)/(double)(m); // the average arc capacity
avNdCap = (double)(allCap)/(double)(n); // the capacity per node

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

  printf ("StrPushL50avCap_c,      %10llu\n", StrPushL50avCap_c);
  printf ("StrPushL75avCap_c,      %10llu\n", StrPushL75avCap_c);
  printf ("StrPushL95avCap_c,      %10llu\n", StrPushL95avCap_c);
  printf ("StrPushL100avCap_c,     %10llu\n", StrPushL100avCap_c);
  printf ("StrPushL105avCap_c,     %10llu\n", StrPushL105avCap_c);
  printf ("StrPushL125avCap_c,     %10llu\n", StrPushL125avCap_c);
  printf ("StrPushL150avCap_c,     %10llu\n\n", StrPushL150avCap_c);

  printf ("StrPushG50avCap_c,      %10llu\n", StrPushG50avCap_c);
  printf ("StrPushG75avCap_c,      %10llu\n", StrPushG75avCap_c);
  printf ("StrPushG95avCap_c,      %10llu\n", StrPushG95avCap_c);
  printf ("StrPushG100avCap_c,     %10llu\n", StrPushG100avCap_c);
  printf ("StrPushG105avCap_c,     %10llu\n", StrPushG105avCap_c);
  printf ("StrPushG125avCap_c,     %10llu\n", StrPushG125avCap_c);
  printf ("StrPushG150avCap_c,     %10llu\n\n", StrPushG150avCap_c);

  printf ("StrPushL50avNdCap_c,    %10llu\n", StrPushL50avNdCap_c);
  printf ("StrPushL75avNdCap_c,    %10llu\n", StrPushL75avNdCap_c);
  printf ("StrPushL95avNdCap_c,    %10llu\n", StrPushL95avNdCap_c);
  printf ("StrPushL100avNdCap_c,   %10llu\n", StrPushL100avNdCap_c);
  printf ("StrPushL105avNdCap_c,   %10llu\n", StrPushL105avNdCap_c);
  printf ("StrPushL125avNdCap_c,   %10llu\n", StrPushL125avNdCap_c);
  printf ("StrPushL150avNdCap_c,   %10llu\n\n", StrPushL150avNdCap_c);

  printf ("StrPushG50avNdCap_c,    %10llu\n", StrPushG50avNdCap_c);
  printf ("StrPushG75avNdCap_c,    %10llu\n", StrPushG75avNdCap_c);
  printf ("StrPushG95avNdCap_c,    %10llu\n", StrPushG95avNdCap_c);
  printf ("StrPushG100avNdCap_c,   %10llu\n", StrPushG100avNdCap_c);
  printf ("StrPushG105avNdCap_c,   %10llu\n", StrPushG105avNdCap_c);
  printf ("StrPushG125avNdCap_c,   %10llu\n", StrPushG125avNdCap_c);
  printf ("StrPushG150avNdCap_c,   %10llu\n\n", StrPushG150avNdCap_c);

  printf ("StrPushL50avCap_rc,     %10llu\n", StrPushL50avCap_rc);
  printf ("StrPushL75avCap_rc,     %10llu\n", StrPushL75avCap_rc);
  printf ("StrPushL95avCap_rc,     %10llu\n", StrPushL95avCap_rc);
  printf ("StrPushL100avCap_rc,    %10llu\n", StrPushL100avCap_rc);
  printf ("StrPushL105avCap_rc,    %10llu\n", StrPushL105avCap_rc);
  printf ("StrPushL125avCap_rc,    %10llu\n", StrPushL125avCap_rc);
  printf ("StrPushL150avCap_rc,    %10llu\n\n", StrPushL150avCap_rc);

  printf ("StrPushG50avCap_rc,     %10llu\n", StrPushG50avCap_rc);
  printf ("StrPushG75avCap_rc,     %10llu\n", StrPushG75avCap_rc);
  printf ("StrPushG95avCap_rc,     %10llu\n", StrPushG95avCap_rc);
  printf ("StrPushG100avCap_rc,    %10llu\n", StrPushG100avCap_rc);
  printf ("StrPushG105avCap_rc,    %10llu\n", StrPushG105avCap_rc);
  printf ("StrPushG125avCap_rc,    %10llu\n", StrPushG125avCap_rc);
  printf ("StrPushG150avCap_rc,    %10llu\n\n", StrPushG150avCap_rc);

  printf ("StrPushL50avNdCap_rc,   %10llu\n", StrPushL50avNdCap_rc);
  printf ("StrPushL75avNdCap_rc,   %10llu\n", StrPushL75avNdCap_rc);
  printf ("StrPushL95avNdCap_rc,   %10llu\n", StrPushL95avNdCap_rc);
  printf ("StrPushL100avNdCap_rc,  %10llu\n", StrPushL100avNdCap_rc);
  printf ("StrPushL105avNdCap_rc,  %10llu\n", StrPushL105avNdCap_rc);
  printf ("StrPushL125avNdCap_rc,  %10llu\n", StrPushL125avNdCap_rc);
  printf ("StrPushL150avNdCap_rc,  %10llu\n\n", StrPushL150avNdCap_rc);

  printf ("StrPushG50avNdCap_rc,   %10llu\n", StrPushG50avNdCap_rc);
  printf ("StrPushG75avNdCap_rc,   %10llu\n", StrPushG75avNdCap_rc);
  printf ("StrPushG95avNdCap_rc,   %10llu\n", StrPushG95avNdCap_rc);
  printf ("StrPushG100avNdCap_rc,  %10llu\n", StrPushG100avNdCap_rc);
  printf ("StrPushG105avNdCap_rc,  %10llu\n", StrPushG105avNdCap_rc);
  printf ("StrPushG125avNdCap_rc,  %10llu\n", StrPushG125avNdCap_rc);
  printf ("StrPushG150avNdCap_rc,  %10llu\n\n", StrPushG150avNdCap_rc);

  printf ("nStrPushL50avCap_c,     %10llu\n", nStrPushL50avCap_c);
  printf ("nStrPushL75avCap_c,     %10llu\n", nStrPushL75avCap_c);
  printf ("nStrPushL95avCap_c,     %10llu\n", nStrPushL95avCap_c);
  printf ("nStrPushL100avCap_c,    %10llu\n", nStrPushL100avCap_c);
  printf ("nStrPushL105avCap_c,    %10llu\n", nStrPushL105avCap_c);
  printf ("nStrPushL125avCap_c,    %10llu\n", nStrPushL125avCap_c);
  printf ("nStrPushL150avCap_c,    %10llu\n\n", nStrPushL150avCap_c);

  printf ("nStrPushG50avCap_c,     %10llu\n", nStrPushG50avCap_c);
  printf ("nStrPushG75avCap_c,     %10llu\n", nStrPushG75avCap_c);
  printf ("nStrPushG95avCap_c,     %10llu\n", nStrPushG95avCap_c);
  printf ("nStrPushG100avCap_c,    %10llu\n", nStrPushG100avCap_c);
  printf ("nStrPushG105avCap_c,    %10llu\n", nStrPushG105avCap_c);
  printf ("nStrPushG125avCap_c,    %10llu\n", nStrPushG125avCap_c);
  printf ("nStrPushG150avCap_c,    %10llu\n\n", nStrPushG150avCap_c);

  printf ("nStrPushL50avNdCap_c,   %10llu\n", nStrPushL50avNdCap_c);
  printf ("nStrPushL75avNdCap_c,   %10llu\n", nStrPushL75avNdCap_c);
  printf ("nStrPushL95avNdCap_c,   %10llu\n", nStrPushL95avNdCap_c);
  printf ("nStrPushL100avNdCap_c,  %10llu\n", nStrPushL100avNdCap_c);
  printf ("nStrPushL105avNdCap_c,  %10llu\n", nStrPushL105avNdCap_c);
  printf ("nStrPushL125avNdCap_c,  %10llu\n", nStrPushL125avNdCap_c);
  printf ("nStrPushL150avNdCap_c,  %10llu\n\n", nStrPushL150avNdCap_c);

  printf ("nStrPushG50avNdCap_c,   %10llu\n", nStrPushG50avNdCap_c);
  printf ("nStrPushG75avNdCap_c,   %10llu\n", nStrPushG75avNdCap_c);
  printf ("nStrPushG95avNdCap_c,   %10llu\n", nStrPushG95avNdCap_c);
  printf ("nStrPushG100avNdCap_c,  %10llu\n", nStrPushG100avNdCap_c);
  printf ("nStrPushG105avNdCap_c,  %10llu\n", nStrPushG105avNdCap_c);
  printf ("nStrPushG125avNdCap_c,  %10llu\n", nStrPushG125avNdCap_c);
  printf ("nStrPushG150avNdCap_c,  %10llu\n\n", nStrPushG150avNdCap_c);

  printf ("nStrPushL50avCap_rc,    %10llu\n", nStrPushL50avCap_rc);
  printf ("nStrPushL75avCap_rc,    %10llu\n", nStrPushL75avCap_rc);
  printf ("nStrPushL95avCap_rc,    %10llu\n", nStrPushL95avCap_rc);
  printf ("nStrPushL100avCap_rc,   %10llu\n", nStrPushL100avCap_rc);
  printf ("nStrPushL105avCap_rc,   %10llu\n", nStrPushL105avCap_rc);
  printf ("nStrPushL125avCap_rc,   %10llu\n", nStrPushL125avCap_rc);
  printf ("nStrPushL150avCap_rc,   %10llu\n\n", nStrPushL150avCap_rc);

  printf ("nStrPushG50avCap_rc,    %10llu\n", nStrPushG50avCap_rc);
  printf ("nStrPushG75avCap_rc,    %10llu\n", nStrPushG75avCap_rc);
  printf ("nStrPushG95avCap_rc,    %10llu\n", nStrPushG95avCap_rc);
  printf ("nStrPushG100avCap_rc,   %10llu\n", nStrPushG100avCap_rc);
  printf ("nStrPushG105avCap_rc,   %10llu\n", nStrPushG105avCap_rc);
  printf ("nStrPushG125avCap_rc,   %10llu\n", nStrPushG125avCap_rc);
  printf ("nStrPushG150avCap_rc,   %10llu\n\n", nStrPushG150avCap_rc);

  printf ("nStrPushL50avNdCap_rc,  %10llu\n", nStrPushL50avNdCap_rc);
  printf ("nStrPushL75avNdCap_rc,  %10llu\n", nStrPushL75avNdCap_rc);
  printf ("nStrPushL95avNdCap_rc,  %10llu\n", nStrPushL95avNdCap_rc);
  printf ("nStrPushL100avNdCap_rc, %10llu\n", nStrPushL100avNdCap_rc);
  printf ("nStrPushL105avNdCap_rc, %10llu\n", nStrPushL105avNdCap_rc);
  printf ("nStrPushL125avNdCap_rc, %10llu\n", nStrPushL125avNdCap_rc);
  printf ("nStrPushL150avNdCap_rc, %10llu\n\n", nStrPushL150avNdCap_rc);

  printf ("nStrPushG50avNdCap_rc,  %10llu\n", nStrPushG50avNdCap_rc);
  printf ("nStrPushG75avNdCap_rc,  %10llu\n", nStrPushG75avNdCap_rc);
  printf ("nStrPushG95avNdCap_rc,  %10llu\n", nStrPushG95avNdCap_rc);
  printf ("nStrPushG100avNdCap_rc, %10llu\n", nStrPushG100avNdCap_rc);
  printf ("nStrPushG105avNdCap_rc, %10llu\n", nStrPushG105avNdCap_rc);
  printf ("nStrPushG125avNdCap_rc, %10llu\n", nStrPushG125avNdCap_rc);
  printf ("nStrPushG150avNdCap_rc, %10llu\n\n", nStrPushG150avNdCap_rc);

  printf("allCap, %10llu\n", allCap);
  printf("avCap, %lf\n", avCap);
  printf("avNdCap, %lf\n", avNdCap);

  	int x1 = 3837191168, x2 =  2082712576, x3=1410065408, x4=145800000000, x5=20000000000;
	long long int  x6 = 145800000000, x7=20000000000;
	excessType x8 = 229526432000, x9=229526432000000;
	cType x10 = 229526432000, x11=229526432000000, x12= 5898979798;
	printf("\n x1: %d, x2: %d, x3: %d, x4: %d, x5: %d, x6: %lld, x7: %lld\n", x1, x2, x3, x4, x5, x6, x7);
	printf("sizeof(int): %d, sizeof(long long int): %d\n", sizeof(int), sizeof(long long int));
	printf("x8: %llu,   x9: %llu\n", x8, x9);
	printf("x10: %lu,   x11: %lu,   x12: %lu\n", x10, x11, x12);

	ullint x13=256, x14=66435;
	printf("x13: %llu,   x14: %llu\n", x13, x14);

	long x15=100000000000;
	unsigned long x16=100000000000;
	ullint x17=100000000000;
	printf("x15: %lu, x16: %lu, x17: %llu\n", x15, x16, x17);
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

  printf ("%10llu, ", StrPushL50avCap_c);
  printf ("%10llu, ", StrPushL75avCap_c);
  printf ("%10llu, ", StrPushL95avCap_c);
  printf ("%10llu, ", StrPushL100avCap_c);
  printf ("%10llu, ", StrPushL105avCap_c);
  printf ("%10llu, ", StrPushL125avCap_c);
  printf ("%10llu, ", StrPushL150avCap_c);

  printf ("%10llu, ", StrPushG50avCap_c);
  printf ("%10llu, ", StrPushG75avCap_c);
  printf ("%10llu, ", StrPushG95avCap_c);
  printf ("%10llu, ", StrPushG100avCap_c);
  printf ("%10llu, ", StrPushG105avCap_c);
  printf ("%10llu, ", StrPushG125avCap_c);
  printf ("%10llu, ", StrPushG150avCap_c);

  printf ("%10llu, ", StrPushL50avNdCap_c);
  printf ("%10llu, ", StrPushL75avNdCap_c);
  printf ("%10llu, ", StrPushL95avNdCap_c);
  printf ("%10llu, ", StrPushL100avNdCap_c);
  printf ("%10llu, ", StrPushL105avNdCap_c);
  printf ("%10llu, ", StrPushL125avNdCap_c);
  printf ("%10llu, ", StrPushL150avNdCap_c);

  printf ("%10llu, ", StrPushG50avNdCap_c);
  printf ("%10llu, ", StrPushG75avNdCap_c);
  printf ("%10llu, ", StrPushG95avNdCap_c);
  printf ("%10llu, ", StrPushG100avNdCap_c);
  printf ("%10llu, ", StrPushG105avNdCap_c);
  printf ("%10llu, ", StrPushG125avNdCap_c);
  printf ("%10llu, ", StrPushG150avNdCap_c);

  printf ("%10llu, ", StrPushL50avCap_rc);
  printf ("%10llu, ", StrPushL75avCap_rc);
  printf ("%10llu, ", StrPushL95avCap_rc);
  printf ("%10llu, ", StrPushL100avCap_rc);
  printf ("%10llu, ", StrPushL105avCap_rc);
  printf ("%10llu, ", StrPushL125avCap_rc);
  printf ("%10llu, ", StrPushL150avCap_rc);

  printf ("%10llu, ", StrPushG50avCap_rc);
  printf ("%10llu, ", StrPushG75avCap_rc);
  printf ("%10llu, ", StrPushG95avCap_rc);
  printf ("%10llu, ", StrPushG100avCap_rc);
  printf ("%10llu, ", StrPushG105avCap_rc);
  printf ("%10llu, ", StrPushG125avCap_rc);
  printf ("%10llu, ", StrPushG150avCap_rc);

  printf ("%10llu, ", StrPushL50avNdCap_rc);
  printf ("%10llu, ", StrPushL75avNdCap_rc);
  printf ("%10llu, ", StrPushL95avNdCap_rc);
  printf ("%10llu, ", StrPushL100avNdCap_rc);
  printf ("%10llu, ", StrPushL105avNdCap_rc);
  printf ("%10llu, ", StrPushL125avNdCap_rc);
  printf ("%10llu, ", StrPushL150avNdCap_rc);

  printf ("%10llu, ", StrPushG50avNdCap_rc);
  printf ("%10llu, ", StrPushG75avNdCap_rc);
  printf ("%10llu, ", StrPushG95avNdCap_rc);
  printf ("%10llu, ", StrPushG100avNdCap_rc);
  printf ("%10llu, ", StrPushG105avNdCap_rc);
  printf ("%10llu, ", StrPushG125avNdCap_rc);
  printf ("%10llu, ", StrPushG150avNdCap_rc);

  printf ("%10llu, ", nStrPushL50avCap_c);
  printf ("%10llu, ", nStrPushL75avCap_c);
  printf ("%10llu, ", nStrPushL95avCap_c);
  printf ("%10llu, ", nStrPushL100avCap_c);
  printf ("%10llu, ", nStrPushL105avCap_c);
  printf ("%10llu, ", nStrPushL125avCap_c);
  printf ("%10llu, ", nStrPushL150avCap_c);

  printf ("%10llu, ", nStrPushG50avCap_c);
  printf ("%10llu, ", nStrPushG75avCap_c);
  printf ("%10llu, ", nStrPushG95avCap_c);
  printf ("%10llu, ", nStrPushG100avCap_c);
  printf ("%10llu, ", nStrPushG105avCap_c);
  printf ("%10llu, ", nStrPushG125avCap_c);
  printf ("%10llu, ", nStrPushG150avCap_c);

  printf ("%10llu, ", nStrPushL50avNdCap_c);
  printf ("%10llu, ", nStrPushL75avNdCap_c);
  printf ("%10llu, ", nStrPushL95avNdCap_c);
  printf ("%10llu, ", nStrPushL100avNdCap_c);
  printf ("%10llu, ", nStrPushL105avNdCap_c);
  printf ("%10llu, ", nStrPushL125avNdCap_c);
  printf ("%10llu, ", nStrPushL150avNdCap_c);

  printf ("%10llu, ", nStrPushG50avNdCap_c);
  printf ("%10llu, ", nStrPushG75avNdCap_c);
  printf ("%10llu, ", nStrPushG95avNdCap_c);
  printf ("%10llu, ", nStrPushG100avNdCap_c);
  printf ("%10llu, ", nStrPushG105avNdCap_c);
  printf ("%10llu, ", nStrPushG125avNdCap_c);
  printf ("%10llu, ", nStrPushG150avNdCap_c);

  printf ("%10llu, ", nStrPushL50avCap_rc);
  printf ("%10llu, ", nStrPushL75avCap_rc);
  printf ("%10llu, ", nStrPushL95avCap_rc);
  printf ("%10llu, ", nStrPushL100avCap_rc);
  printf ("%10llu, ", nStrPushL105avCap_rc);
  printf ("%10llu, ", nStrPushL125avCap_rc);
  printf ("%10llu, ", nStrPushL150avCap_rc);

  printf ("%10llu, ", nStrPushG50avCap_rc);
  printf ("%10llu, ", nStrPushG75avCap_rc);
  printf ("%10llu, ", nStrPushG95avCap_rc);
  printf ("%10llu, ", nStrPushG100avCap_rc);
  printf ("%10llu, ", nStrPushG105avCap_rc);
  printf ("%10llu, ", nStrPushG125avCap_rc);
  printf ("%10llu, ", nStrPushG150avCap_rc);

  printf ("%10llu, ", nStrPushL50avNdCap_rc);
  printf ("%10llu, ", nStrPushL75avNdCap_rc);
  printf ("%10llu, ", nStrPushL95avNdCap_rc);
  printf ("%10llu, ", nStrPushL100avNdCap_rc);
  printf ("%10llu, ", nStrPushL105avNdCap_rc);
  printf ("%10llu, ", nStrPushL125avNdCap_rc);
  printf ("%10llu, ", nStrPushL150avNdCap_rc);

  printf ("%10llu, ", nStrPushG50avNdCap_rc);
  printf ("%10llu, ", nStrPushG75avNdCap_rc);
  printf ("%10llu, ", nStrPushG95avNdCap_rc);
  printf ("%10llu, ", nStrPushG100avNdCap_rc);
  printf ("%10llu, ", nStrPushG105avNdCap_rc);
  printf ("%10llu, ", nStrPushG125avNdCap_rc);
  printf ("%10llu, ", nStrPushG150avNdCap_rc);

  printf("%10llu, ", allCap);
  printf("%lf, ", avCap);
  printf("%lf, ", avNdCap);

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
  globalUpdate2();
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
  globalUpdate2();
  printf ("c nodes on the sink side\n");
  forAllNodes(j)
    if (j->d < n)
      printf("c %ld\n", nNode(j));

#endif

exit(0);

}
