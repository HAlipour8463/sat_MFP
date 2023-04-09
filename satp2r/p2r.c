/* Maximum flow - highest level p2r algorithm */
/* COPYRIGHT C 1995 -- 2008 by IG Systems, Inc., igsys@eclipse.net */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>

#include "values.h"
#include "types.h"          /* type definitions */
#include "parser.c"         /* parser */
#include "timer.c"          /* timing routine */

//#define CHECK_SOLUTION
//#define LASY_UPDATE
//#define OLD_UPDATE

#define TIME
//#define PROGRESS
//#define TEST
//#define STAT
#define SATCOUNT

//#define AVNDCAP
//#define INIT_UPDATE
//#define SIMPLE_INIT
//#define SAT_ALL_INIT
//#define SAT_SMALL_INIT
//#define SAT_LARGE_INIT

#define DELETED n
//#define GLOB_UPDT_FREQ 0.6667
//#define GLOB_UPDT_FREQ 0.23
#define GLOB_UPDT_FREQ 0.2

// how far above the last excess to update
#define STOP_H 0

#define INIT_W 4.0

#define WHITE 0
#define GREY 1
#define BLACK 2

/* global variables */

long    n,                   /* number of nodes */
        m,                   /* number of arcs */
        nLeft,               /* after deleting by gap and global update */
        mInp,                /* input num. arcs with parallel arcs */
        nMin,                /* smallest node id */
        dMax,                /* maximum label */
        aMax,                /* maximum active node label */
        eMax;                /* maximum guaranteed correct bucket */
double flow;                 /* flow value */

node   *nodes;               /* array of nodes */
arc    *arcs;                /* array of arcs */
bucket *buckets;             /* array of buckets */
cType  *cap;                 /* array of capacities */
node   *source;              /* source node pointer */
node   *sink;                /* sink node pointer */
//node   **stack;            /* for DFS */
//node   **sBot, **sTop;     /* stack pointers */

excessType  allCap;             /* sum of all arc capacities */

#ifdef STAT
long  int  upScanCnt =0,
        gapCnt   = 0,        /* number of gaps */
        updateCnt =0,        /* number of updates */
        gNodeCnt = 0,        /* number of nodes after gap */
        dNodeCnt = 0,
        globUpdtCnt =0;      /*  number of global updates */
#endif // STAT
float t, t2, t3;             /* for saving times */

double avCap;                   /* the average of arc capacities */
double avNdCap;                 /* the arc capacities per node */

node   *sentinelNode;        /* end of the node list marker */
arc *stop__A;                /* used in forAllArcs */
double workSinceUpdate=0;    /* the number of arc scans since last update */
double globUpdtFreq;         /* global update frequency */
double globUpdtFreqOrig;
double updThresh;
long scanN=0;

#ifdef STAT
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
        pushCnt  = 0,           /* number of pushes */
        pushCntI = 0,           /* Initial pushes */
        pushCnt1  = 0,          /* number of pushes at stage 1 */
        pushCnt2  = 0,          /* number of pushes at stage 2 */
        StrPushCntI =0,         /* number of initial saturated pushes */
        StrPushCnt =0,          /* number of saturated pushes */
        nStrPushCnt =0,         /* number of non-saturated pushes */
        nStrPushCnt2 =0,        /* number of non-saturated pushes at stage 2*/
        deplPush1 =0,           /* number of pushes that depleted node excesses */
        nDeplPush1 =0,          /* number of pushes that do not depleted node excesses  */
        deplPush2 =0,           /* number of pushes that depleted node excesses */
        nDeplPush2 =0,          /* number of pushes that do not depleted node excesses  */
        selfLoopPush2 =0,       /* number of pushes to remove flows from self-loops */
        loopPush2 =0,           /* number of pushes to remove flows from loops */
        augCnt = 0,             /* number of augmentations */
        relabelCntI   = 0,      /* number of relabels at the initial stage*/
        relabelCnt   = 0,       /* number of relabels */
        relabelCntGap   = 0,    /* number of relabels during the gap heuristic */
        relabelCntGlbUp   = 0,  /* number of relabels during global updating*/
        relabelCnt2   = 0,      /* number of relabels in the second stage */

/* bucket relative operation counts */
        aAddCnt = 0,
        aDeleteCnt = 0,
        iAddCnt = 0,
        iDeleteCnt  = 0,
        allocDSCnt = 0,
        checkDsCnt = 0;
#ifdef SATCOUNT
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
#endif // SATCOUNT
#endif // STAT

/* macros */

#define forAllNodes(i) for ( i = nodes; i != sentinelNode; i++ )
#define forAllArcs(i,a) for (a = i->first, stop__A = (i+1)->first; a != stop__A; a++)

#define nNode( i ) ( (i) - nodes + nMin )
#define nArc( a )  ( ( a == NULL )? -1 : (a) - arcs )

#define isCurrent(i) ((i->current->resCap > 0) && (i->current->head->d < i->d))

#define min(a, b) (((a) < (b)) ? a : b)

#define max(a, b) (((a) > (b)) ? a : b)

#define sReset() (sTop = sBot)

#define sPush(i) {*sTop = i; sTop++;}

#define sPop(i) {sTop--; i = *sTop;}


#define qInit() \
{\
  qHead = qTail = sentinelNode;\
}

#define qEmpty (qHead == sentinelNode)

#define qEnqueue(i) \
{\
  i->bNext = sentinelNode;\
  i->bPrev = qTail;\
  qTail->bNext = i;\
  qTail = i;\
  if (qHead == sentinelNode) qHead = i;\
}

#define qDequeue(i) \
{\
  i = qHead;\
  qHead = i->bNext;\
  qHead->bPrev = sentinelNode;\
  if (qHead == sentinelNode) qTail = sentinelNode;\
}

/*
   bucket macros:
   bucket's active node list is singly-linked
     operations aAdd, aRemove (from the front)
   bucket's inactive list is doubly-linked
     operations iAdd, iDelete (from arbitrary position)
*/


#ifdef STAT
/* Count different types of arc saturations  */
#ifdef SATCOUNT
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
#endif // SATCOUNT
#endif // STAT

//long i_dist;
//node *i_next, *i_prev;


void aAdd(bucket *l, node *i)
{
  i->bNext = l->firstActive;
  i->bNext->bPrev = i;
  i->bPrev = sentinelNode;
  l->firstActive = i;
  if (i->d > aMax) {
    aMax = i->d;
    if (i->d > dMax)
      dMax = i->d;
  }
}

void aDelete(bucket *l, node *i)
{
  if (l->firstActive == i) {
    l->firstActive = i->bNext;
    i->bNext->bPrev = sentinelNode;
  }
  else {
    i->bPrev->bNext = i->bNext;
    i->bNext->bPrev = i->bPrev;
  }
}


void iAdd(bucket *l, node *i)
{
  i->bNext = l->firstInactive;
  i->bPrev = sentinelNode;
  i->bNext->bPrev = i;
  l->firstInactive = i;
  if (i->d > dMax)
    dMax = i->d;
}

void iDelete(bucket *l, node *i)
{
  if (l->firstInactive == i) {
    l->firstInactive = i->bNext;
    i->bNext->bPrev = sentinelNode;
  }
  else {
    i->bPrev->bNext = i->bNext;
    i->bNext->bPrev = i->bPrev;
  }
}

/* allocate datastructures, initialize related variables */

int allocDS( )

{
  bucket *l;

  buckets = (bucket*) calloc ( n+2, sizeof (bucket) );
  if ( buckets == NULL ) return ( 1 );

  sentinelNode = nodes + n;
  sentinelNode->first = arcs + 2*m;

  for (l = buckets; l <= buckets + n; l++) {
    l->firstActive = sentinelNode;
    l->firstInactive = sentinelNode;
  }

  return (0);

} /* end of allocate */


void printGraph()
{
  node *i;
  arc *a;
  arc *stop__A;

  printf("n %ld mInp %ld m %ld sent %d\n", n, mInp, m, sentinelNode - nodes + 1);

  forAllNodes(i) {
    printf("node %d\n", i-nodes+1);
    forAllArcs(i, a) {
      printf("  arc %d (%d %d) res cap %ld cap %ld rev %d\n", a - arcs,
	     i-nodes+1, a->head-nodes+1,
	     a->resCap, cap[a-arcs],
	     a->rev - arcs);
    }
  }


}


void initBFS()

{

  node *i, *j;       /* node pointers */
  arc *a;           /* current arc pointers  */
  arc *stop__A;
  bucket *l;
  node *qHead, *qTail;
  /*
  for (l = buckets; l <= buckets + dMax; l++) {
    l->firstActive = sentinelNode;
    l->firstInactive = sentinelNode;
  }
  */
#ifdef STAT
  updateCnt++;
#endif // STAT
  scanN = 0;


  //  printf(">>> init update (%ld) relCnt %ld\n", updateCnt, relabelCnt);

  qInit();

  /* initialization */

  forAllNodes(i) {
#ifdef STAT
    nodeScanCntI ++;
#endif // STAT
#ifdef SIMPLE_INIT
    i->d = DELETED;
#else
    if (i->excess < 0) // Since the excess of the source is set as 0 within init(), source is not regarded here!
    {
        i->d = 1; // At the initialisation stage, all deficit nodes must take label 1
        qEnqueue(i);
    }
    else
    {
     i->d = DELETED;
#ifdef STAT
    relabelCntI++;
#endif // STAT
    }
#endif // SIMPLE_INIT
  }

  sink->d = 0;
  aMax = 0;
  /* breadth first search */

  qEnqueue(sink);

  while (!qEmpty) {

    qDequeue(i);
#ifdef STAT
    nodeScanCntI++;
#endif // STAT

    //    printf(">>> scanning %d (%ld)\n", i-nodes+1, i->d);

    dMax = i->d;
    l = buckets + dMax;
    // Adopted for SAT_ALL_ININ : (i->excess == 0) is changed as follows;
    if ((i == sink) || (i->excess <= 0)){
      iAdd(l, i);
#ifdef STAT
      iAddCnt++;
#endif // STAT
      }
    else{
      aAdd(l, i);
#ifdef STAT
      aAddCnt++;
#endif // STAT
    }

    /* scanning arcs incident to node i */

    scanN++;
#ifdef STAT
    upScanCnt++;
#endif // STAT
    forAllArcs(i, a) {
#ifdef STAT
      arcScanCntI++;
#endif // STAT
      if (a->rev->resCap > 0 ) {
	j = a->head;
	if (j->d == DELETED) {
	    j->d = i->d + 1;
	    j->current = j->first;
	    qEnqueue(j);
#ifdef STAT
        relabelCntI++;
#endif // STAT
	}
      } /* node i is scanned */
    }
  }

  nLeft = scanN;

  eMax = dMax;

  workSinceUpdate = 0;

  updThresh = scanN + 500;

}

// return 0 if s or t have no adjacent arcs
int init()

{
  node *i;
  arc *stop__A;

  bucket *l;
  arc *a;
  cType delta;

  nLeft = n;
  //  updThresh = n + (long) pow(m, 0.75) - (long) (INIT_W * (double) n);
  if (m <= pow(n, 1.5))
    //    updThresh = 0;
    updThresh = 0;
  else
    updThresh = 4*n;


  // initialize excesses

  forAllNodes(i) {
#ifdef STAT
    nodeScanCntI++;
#endif // STAT
    i->excess = 0;
    i->current = i->first;
#ifdef SIMPLE_INIT
    i->d = 1;
#endif
  }

  // iterate over all arcs
  for (a = arcs, stop__A = arcs + m; a != stop__A; a++) {
#ifdef STAT
    arcScanCntI++;
#endif // STAT
    a->resCap = cap[a-arcs];
  }

  if ((source->first == NULL) || (sink->first == NULL))
    return 0;
  /*
  for (l = buckets; l <= buckets + n; l++) {
    l->firstActive = sentinelNode;
    l->firstInactive = sentinelNode;
  }
  */
#ifdef SIMPLE_INIT
  source->excess = 0;
  // saturate source arcs
  forAllArcs(source,a) {
#ifdef STAT
    arcScanCntI ++;
#endif // STAT
    if (a->head != source) {
#ifdef STAT
      pushCntI++;
      StrPushCntI++;
#endif // STAT
      delta = a->resCap;
      a->resCap -= delta;
      (a->rev)->resCap += delta;
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
            printf ( "f %7ld %7ld %12ld\n",
                    nNode(i), nNode( a -> head ), cap[nArc(a)] - ( a -> resCap ) );
            printf("excess of node %d is %d\n", nNode(i), i->excess);
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
//    ni = nNode(i);
//    na = nArc(a);
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
//    ni = nNode(i);
//    na = nArc(a);
            printf ( "f %7ld %7ld %12ld\n",
                    nNode(i), nNode( a -> head ), cap[nArc(a)] - ( a -> resCap ) );
            printf("excess of node %ld is %lld\n", nNode(i), i->excess);
#endif // PROGRESS
                }
            }
        }
    }
#endif // SIMPLE_INIT

source->excess = 0;

  /*  setup labels and buckets */
  l = buckets + 1;

  aMax = 0;
  dMax = 0;
#ifdef SIMPLE_INIT
  eMax = 0;
#else
  eMax = 1;
#endif // SIMPLE_INIT

  if (updThresh == 0) {
    initBFS();
    return (1);
  }
  else {
    source->d = DELETED;
    nLeft--;

    sink->d = 0;

    forAllNodes(i) {
#ifdef STAT
      nodeScanCntI++;
#endif // STAT
      if (i == sink) {
      iAdd(buckets,i);
#ifdef STAT
      iAddCnt++;
#endif // STAT
      continue;
      }

 #ifdef SIMPLE_INIT
      if (i->d < DELETED) {
	l = buckets + i->d;
	if (i->excess > 0) {
//#ifdef SAT_ALL_INIT
//    assert(i->excess > 0);
//#endif // SAT_ALL_INIT
	  aAdd(l,i);
#ifdef STAT
	  aAddCnt++;
#endif // STAT
	}
	else {
	  iAdd(l,i);
#ifdef STAT
	  iAddCnt++;
#endif // STAT
	}
      }
#else
        if (i != source) {
      if (i->excess > 0) {
        i->d = 2;
//        l = buckets + i->d;
        aAdd(buckets+2,i);
#ifdef STAT
        aAddCnt++;
#endif // STAT
      }
      else if (i->excess == 0){
            i->d = 2;
//            l = buckets + i->d;
            iAdd(buckets+2,i);
#ifdef STAT
            iAddCnt++;
#endif // STAT
      }
      else {
            i->d = 1;
//          l = buckets + i->d;
            iAdd(buckets+1,i);
#ifdef STAT
        iAddCnt++;
#endif // STAT
      }
    }
#endif //SIMPLE_INIT
    }
  }
  return (1);
} /* end of init */

void checkDs()

{
  bucket *l;
  node *i;

  for (l = buckets ; l < buckets + dMax; l++) {
    for (i = l->firstActive; i != sentinelNode; i = i->bNext)
      assert(i->d == l - buckets);
    for (i = l->firstInactive; i != sentinelNode; i = i->bNext)
      assert(i->d == l - buckets);
  }
}

/* global update via breadth first search backward */
/* assume sink is the only node at level 0 */

void globalUpdate ()

{
#ifdef STAT
  globUpdtCnt++;
#endif // STAT
  node  *i, *j;       /* node pointers */
  arc   *a;           /* current arc pointers  */
  bucket *l, *jL;          /* bucket */
  long curDist, jD;
  long state;
  arc *stop__A;
  //  excessType remEx;
  bucket B, *remNodes;
  long aMaxOld, dMaxOld;
  int tType=0; // reason for termination
#ifdef LASY_UPDATE
  node *lastN;
#endif


  remNodes = &B;
  remNodes->firstActive = sentinelNode;
  remNodes->firstInactive = sentinelNode;

#ifdef STAT
  updateCnt++;
#endif // STAT
  scanN = 0;

  //  printf(">>> global update (%ld) relCnt %ld\n", updateCnt, relabelCnt);

  /* breadth first search */

  //  remEx = 0;
  aMaxOld = aMax;
  dMaxOld = dMax;

#ifdef OLD_UPDATE
#ifdef SIMPLE_INIT
    eMax = 0;
#else
    eMax = 1;
#endif // SIMPLE_INIT
#endif // OLD_UPDATE

  for (curDist = eMax; 1; curDist++) {

    state = 0;
    l = buckets + curDist;
    jD = curDist + 1;
    jL = l + 1;

    // first case
    if ((l->firstActive == sentinelNode) &&
	(l->firstInactive == sentinelNode)) {
      // stop after scanning all reachable vertices
      tType = 1;
      break;
    }
#ifdef LASY_UPDATE
    if ((curDist > aMaxOld + STOP_H) &&
	(remNodes->firstActive == sentinelNode)) {
      // all nodes with excess have current distances
      tType = 2;
      break;
    }
#endif
    // clean up the next level
#ifdef LASY_UPDATE
    lastN = NULL;
#endif
    for (j = jL->firstInactive; j != sentinelNode; j = j->bNext) {
      j->d = DELETED;
#ifdef STAT
      relabelCntGlbUp++;
#endif // STAT
#ifdef LASY_UPDATE
      lastN = j;
#endif
    }

#ifdef LASY_UPDATE
    // concatenate and clean
    if (jL->firstInactive != sentinelNode) {
      // lastN points to the last real node
      lastN->bNext = remNodes->firstInactive;
      lastN->bNext->bPrev = lastN;
      remNodes->firstInactive = jL->firstInactive;
      jL->firstInactive = sentinelNode;
    }
#else
    jL->firstInactive = sentinelNode;
#endif

#ifdef LASY_UPDATE
    lastN = NULL;
#endif
    for (j = jL->firstActive; j != sentinelNode; j = j->bNext) {
      j->d = DELETED;
#ifdef STAT
      relabelCntGlbUp++;
#endif // STAT
#ifdef LASY_UPDATE
      lastN = j;
#endif
    }

#ifdef LASY_UPDATE
    // concatenate and clean
    if (jL->firstActive != sentinelNode) {
      // lastN points to the last real node
      lastN->bNext = remNodes->firstActive;
      lastN->bNext->bPrev = lastN;
      remNodes->firstActive = jL->firstActive;
      jL->firstActive = sentinelNode;
    }
#else
    jL->firstActive = sentinelNode;
#endif

    i = NULL;
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

      //assert(i != NULL);

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

      scanN++;
#ifdef STAT
      upScanCnt++;
#endif // STAT

      /* scanning arcs incident to node i */
#ifdef STAT
      nodeScanCntGlbUp++;
#endif // STAT
      forAllArcs(i,a) {
#ifdef STAT
        arcScanCntGlbUp ++;
#endif // STAT
	if (a->rev->resCap > 0 ) {
	  j = a->head;
	  if (j->d == DELETED) {
	    if (j->excess > 0) {
	      aDelete(remNodes, j);
	      j->d = jD;
	      aAdd(jL,j);
#ifdef STAT
	      aDeleteCnt++;
	      relabelCntGlbUp++;
	      aAddCnt++;
#endif // STAT
	    }
        else {
          //assert(j->excess  == 0);
	      iDelete(remNodes, j);
	      j->d = jD;
	      iAdd(jL,j);
#ifdef STAT
	      iDeleteCnt++;
	      relabelCntGlbUp++;
	      iAddCnt++;
#endif // STAT
	    }
	    j->current = j->first;
	  }
	}
      } /* node i is scanned */
    }
  }

  if (((buckets+curDist)->firstActive == sentinelNode) &&
      ((buckets+curDist)->firstInactive == sentinelNode))
    curDist--;

  if (tType == 1) {
    // all reachable nodes scanned
    // clean up higher levels containing unreachable nodes
    for (l = buckets + curDist + 1; l <= buckets + dMaxOld; l++) {
#ifdef STAT
      nodeScanCntGlbUp++;
#endif // STAT
      for (i = l->firstInactive; i != sentinelNode; i = i->bNext) {
	i->d = DELETED;
	nLeft--;
#ifdef STAT
	relabelCntGlbUp++;
#endif // STAT
      }
      l->firstInactive = sentinelNode;

      for (i = l->firstActive; i != sentinelNode; i = i->bNext) {
	i->d = DELETED;
	nLeft--;
#ifdef STAT
	relabelCntGlbUp++;
#endif // STAT
      }
      l->firstActive = sentinelNode;

      //      aMax = dMax = curDist;
    }
  }
#ifdef LASY_UPDATE
  else {
    // stopped because all nodes with excess have current distances

    //assert(tType == 2);
    //assert(remNodes->firstActive == sentinelNode);

    // concervatively update removed node d's
    if (remNodes->firstInactive != sentinelNode) {
      curDist++;
      jD = curDist;
      jL = buckets + jD;
      lastN = NULL;
      for (j = remNodes->firstInactive; j != sentinelNode; j = j->bNext) {
	lastN = j;
	j->d = jD;
	j->current = j->first;
      }

      // place nodes on remNodes list into jL
      lastN->bNext = jL->firstInactive;
      lastN->bNext->bPrev = lastN;
      jL->firstInactive = remNodes->firstInactive;
    }

    if (dMaxOld > curDist)
      dMax = dMaxOld;
    else
      dMax = curDist;
  }
#endif

  eMax = curDist;
  aMax = curDist;

  workSinceUpdate = 0;

  updThresh = 500 +
    //    ((double) n)/100.0 +
    //    ((double) nLeft)/50 +
    scanN;
  /*
  updThresh = ((double) n)/100.0 +
    (double) (nLeft + 1) *
    (
     pow(4.0, (((float) (scanN + 1))/(float) (nLeft + 1)))
     );
  */
  //  printf(">>> tr %f    sc %ld    left %ld\n", (float) updThresh, scanN, nLeft);

  //  printf(">>> after update check is %d\n", checkGap());

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
   buckets[i-nodes].firstActive is used for DSF tree
*/

{
  node *i, *j, *tos, *bos, *restart, *r;
  arc *a;
  cType delta;

  /* assume self-loops have been removed

  // deal with self-loops

  forAllNodes(i) {
    forAllArcs(i,a)
    if ( a -> head == i ) {
      a -> resCap = cap[a - arcs];
    }
  }
  */

  // Since we deactivated the relevant pre-process, we activate it here
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
	if (a -> resCap > 0)
          nStrPushCnt2 ++;
#endif
      }
    }
  }

  /* initialize */
  tos = bos = NULL;
  forAllNodes(i) {
#ifdef STAT
      nodeScanCnt2++;
#endif // STAT
    i->d = WHITE;
    //    buckets[i-nodes].firstActive = NULL;
    buckets[i-nodes].firstActive = sentinelNode;
    i->current = i->first;
  }

  /* eliminate flow cycles, topologicaly order vertices */
  forAllNodes(i){
#ifdef STAT
      nodeScanCnt2++;
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
#ifdef STAT
      arcScanCnt2++;
#endif // STAT
	  a = i -> current;
	  if (cap[a - arcs] < a->resCap) {
	  // a->rev has positive flow
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
	      if (j->d == GREY) {
		/* find minimum flow on the cycle */
		delta = a->resCap - cap[a-arcs];
		while ( 1 ) {
#ifdef STAT
          arcScanCnt2++;
#endif // STAT
		  delta = min(delta,
			      j->current->resCap - cap[j->current - arcs]);
		  if ( j == i )
		    break;
		  else
		    j = j -> current -> head;
		}

		/* remove delta flow units */
		j = i;
		while ( 1 ) {
		  a = j -> current;
		  a -> resCap -= delta;
		  a -> rev -> resCap += delta;
#ifdef STAT
		  pushCnt2++;
		  if (a -> resCap > 0)
          nStrPushCnt2 ++;
          loopPush2++;
#endif // STAT
		  j = a -> head;
		  if ( j == i )
		    break;
		}

		/* backup DFS to the first saturated arc */
		restart = i;
		for ( j = i -> current -> head; j != i; j = a -> head ) {
#ifdef STAT
          arcScanCnt2++;
#endif // STAT
		  a = j -> current;
		  if (( j -> d == WHITE ) ||
		      (a->resCap == cap[a - arcs])) {
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
      a = i -> first;
      while ( i -> excess > 0 ) {
#ifdef STAT
        arcScanCnt2++;
#endif // STAT
	if (cap[a - arcs] < a->resCap) {
	  // a->rev has positive flow
	  if (a->resCap - cap[a - arcs] < i->excess)
	    delta = a->resCap - cap[a - arcs];
	  else
	    delta = i->excess;
	  a -> resCap -= delta;
	  a -> rev -> resCap += delta;
	  i -> excess -= delta;
	  a -> head -> excess += delta;
#ifdef STAT
	    pushCnt2++;
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
      if (cap[a - arcs] < a->resCap) {
	  // a->rev has positive flow
	if (a->resCap - cap[a - arcs] < i->excess)
	  delta = a->resCap - cap[a - arcs];
	else
	  delta = i->excess;
	a -> resCap -= delta;
	a -> rev -> resCap += delta;
	i -> excess -= delta;
	a -> head -> excess += delta;
#ifdef STAT
	pushCnt2++;

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


/* borrowed from hipr to test some bugs */
/* second stage -- preflow to flow */
void stageTwo_hipr ( )
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
	if (a -> resCap > 0)
          nStrPushCnt2 ++;
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
#ifdef STAT
      arcScanCnt2 ++;
#endif // STAT
      a = i -> current;
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
		  a -> resCap -= delta;
		  a -> rev -> resCap += delta;
#ifdef STAT
		  pushCnt2 ++;
		  loopPush2++;
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
	  a -> resCap -= delta;
	  a -> rev -> resCap += delta;
	  i -> excess -= delta;
	  a -> head -> excess += delta;
#ifdef STAT
	    pushCnt2 ++;
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
	a -> resCap -= delta;
	a -> rev -> resCap += delta;
	i -> excess -= delta;
	a -> head -> excess += delta;
#ifdef STAT
	  pushCnt2 ++;
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
  flow = sink->excess;
}

/* This is the same as that of hipr implementation.
some parameters are a little different from void stageTwo ( )
presented above, but they are the same essentially.*/
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
		  a -> resCap += delta;
		  a -> rev -> resCap -= delta;
#ifdef STAT
		  pushCnt2 ++;
		  loopPush2++;
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
	a -> resCap += delta;
	a -> rev -> resCap -= delta;
	i -> excess += delta;
	a -> head -> excess -= delta;
#ifdef STAT
	  pushCnt2 ++;
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
#ifdef PROGRESS
    printf("flow is : %f", flow);
#endif // PROGRESS
}
#endif // SIMPLE_INIT


/* gap relabeling */

void gap(bucket *emptyB)

{

  bucket *l;
  node  *i;
  long  r;           /* index of the bucket before l  */

  //  printf(">>> gap %d\n", emptyB - buckets);
#ifdef STAT
  gapCnt++;
#endif // STAT
  r = (emptyB - buckets) - 1;

  /* set labels of nodes beyond the gap to "infinity" */
  for (l = emptyB; l <= buckets + dMax; l ++) {
#ifdef STAT
    nodeScanCntGap++;
#endif // STAT
    for (i = l -> firstActive; i != sentinelNode; i = i -> bNext) {
      i->d = DELETED;
      nLeft--;
#ifdef STAT
      relabelCntGap++;
      gNodeCnt++;
#endif // STAT
    }
    l -> firstActive = sentinelNode;

    for (i = l -> firstInactive; i != sentinelNode; i = i -> bNext) {
      i->d = DELETED;
      nLeft--;
#ifdef STAT
      relabelCntGap++;
      gNodeCnt++;
#endif // STAT
    }
    l -> firstInactive = sentinelNode;
  }

  dMax = r;
  aMax = r;
  if (r < eMax)
    eMax = r;

}

/*--- relabelling node i */
// find the best label
void relabel (node *i)

{

  node  *j;
  long  minD;     /* minimum d of a node reachable from i */
  arc   *minA;    /* an arc which leads to the node with minimal d */
  arc   *a;
  arc *stop__A;
  bucket *l;

  //  printf(">>>relabeling %d (%ld)\n", i-nodes+1, i->d);
#ifdef STAT
  relabelCnt++;
#endif // STAT
  workSinceUpdate++;

  if (eMax > i->d)
    eMax = i->d;

  // check for gap
  l = buckets + i->d;
  if (((i->bNext == sentinelNode) && (i->bPrev == sentinelNode)) &&
      (((i->excess > 0) &&
	(l->firstInactive == sentinelNode)) ||
       ((i->excess == 0) && (l->firstActive == sentinelNode)))
      ) {
    gap(l);
    return;
  }

  minD = DELETED;
  minA = NULL;

  /* find the minimum */
  forAllArcs(i,a) {
#ifdef STAT
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

  if (minD < DELETED)
    minD++;
  else
    minD = DELETED;

  if (i->excess > 0) {
    aDelete(l,i);
#ifdef STAT
    aDeleteCnt++;
#endif // STAT
  }
  else {
    iDelete(l,i);
#ifdef STAT
    iDeleteCnt++;
#endif // STAT
  }

  if (minD < DELETED) {
    i->current = minA;
    //assert(i->d < minD);
    i->d = minD;
    l = buckets + i->d;
    if (i->excess > 0) {
      aAdd(l, i);
#ifdef STAT
      aAddCnt++;
#endif // STAT
    }
    else {
      iAdd(l, i);
#ifdef STAT
      iAddCnt++;
#endif // STAT
    }
  }
  else {
    i->d = DELETED;
    nLeft--;
#ifdef STAT
    dNodeCnt++;
#endif // STAT
  }

} /* end of relabel */

// return 1 if found a current arc out of i or 0 otherwise
int makeCurrent(node *i)

{
  arc *a;
  arc *stopA;

  // assume i->current is not current
  //assert((i->current->resCap == 0) || (i->current->head->d >= i->d));
  //assert(i->current < (i+1)->first);

  for (a = (i->current)+1, stopA = (i+1)->first; a != stopA; a++) {
#ifdef STAT
        arcScanCnt1++;
#endif // STAT
    if ((a->resCap > 0) && (a->head->d < i->d)) {
      i->current = a;
      return(1);
    }
  }

  return(0);

}

// push flow to the sink or 2 steps
// avoid node activation
void twoLevPush(node *i)

{
  node  *j, *k;
  bucket *l;                /* i's bucket */
  arc   *a;                 /* current arc (i,j) */
  cType  delta;
  excessType jCap;
  long long int prevEx; // Adopted for pseudo flows
  arc *b, *stopB;
  int relabelJ;

  //assert(i->excess > 0);
  a = i->current;
  j = a->head;
  //assert(j != sink);
  prevEx = j->excess;
//#ifdef SAT_ALL_INIT
//	assert(! (prevEx < 0));
//#endif // SAT_ALL_INIT

  delta = min(a->resCap, i->excess);
#ifdef STAT
  nodeScanCnt1++;
#endif // STAT

#ifdef STAT
#ifdef SATCOUNT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // SATCOUNT
#endif // STAT

  if (prevEx > 0) {
    // push delta to j
    a->resCap -= delta;
    a->rev->resCap += delta;
#ifdef STAT
    pushCnt++;
    pushCnt1++;
    if (a->resCap >0)
        nStrPushCnt++;
#endif // STAT

    if ((a->resCap == 0) && (eMax > j->d))
      eMax = j->d;

    j->excess += delta;
    i->excess -= delta;
#ifdef STAT
    if (i->excess == 0)
        deplPush1++;
	else
        nDeplPush1++;
#endif // STAT

//    assert(j->excess > 0);

    // if i was active but no longer is
    if (i->excess == 0) {
      l = buckets + i->d;
      aDelete(l, i);
      iAdd(l, i);
#ifdef STAT
      aDeleteCnt++;
      iAddCnt++;
#endif // STAT
    }

    stopB = (j+1)->first;
    for (b = j->current; b < stopB; b++) {
#ifdef STAT
      arcScanCnt1++;
#endif // STAT
      if ((b->resCap > 0) && (b->head->d < j->d)) {
	k = b->head;
	delta = min(b->resCap, j->excess);

#ifdef STAT
#ifdef SATCOUNT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // SATCOUNT
#endif // STAT

	b->resCap -= delta;
	b->rev->resCap += delta;
#ifdef STAT
	pushCnt++;
	pushCnt1++;
    if (b->resCap >0)
        nStrPushCnt++;
#endif // STAT

	if ((b->resCap == 0) && (eMax > k->d))
	  eMax = k->d;

	k->excess += delta;
	j->excess -= delta;
#ifdef STAT
	if (j->excess == 0)
        deplPush1++;
	else
        nDeplPush1++;
#endif // STAT

//#ifndef SAT_ALL_INIT
//	assert(k->excess > 0);
//#endif // SAT_ALL_INIT

	// did k become active?
	if ((k->excess == delta) && (k != sink)) {
	  l = buckets + k->d;
	  iDelete(l, k);
	  aAdd(l, k);
#ifdef STAT
	  iDeleteCnt++;
	  aAddCnt++;
#endif // STAT
	}
#ifndef SIMPLE_INIT
    if ((k->excess>0) && (k->excess < delta)) {
	  l = buckets + k->d;
	  eMax = 1;
	  iDelete(l, k);
	  ++k->d;
	  aAdd(l+1, k);
#ifdef STAT
	  iDeleteCnt++;
	  aAddCnt++;
	  relabelCnt++;
#endif // STAT
	}

    // did k become neutral?
    if ((k->excess==0) && (k->excess < delta)) {
	  l = buckets + k->d;
	  eMax = 1;
	  iDelete(l, k);
	  ++k->d;
	  iAdd(l+1, k);
#ifdef STAT
	  iDeleteCnt++;
	  iAddCnt++;
	  relabelCnt++;
#endif // STAT
	}
#endif // SIMPLE_INIT

	if (j->excess == 0) {
	  j->current = b;
	  break;
	}
      }
    }

    if (j->excess == 0) {
      l = buckets + j->d;
      aDelete(l, j);
      iAdd(l, j);
#ifdef STAT
	  aDeleteCnt++;
	  iAddCnt++;
#endif // STAT
    }
    else
      relabel(j);
  }
  else {
    // j's excess is zero, maintain it at zero
//#ifdef SAT_ALL_INIT
//	assert(j->excess == 0);
//#endif // SAT_ALL_INIT
    jCap = 0;
    stopB = (j+1)->first;
    for (b = j->current; b < stopB; b++) {
#ifdef STAT
      arcScanCnt1++;
#endif // STAT
      if ((b->resCap > 0) && (b->head->d < j->d)) {
	jCap += b->resCap;
	if (jCap > j->excess + delta)
	  break;
      }
    }

//    assert(jCap > 0);

    //    if (jCap <= delta)
    if (jCap < delta)
      relabelJ = 1;
    else
      relabelJ = 0;

    delta = min(delta, jCap);

#ifdef STAT
#ifdef SATCOUNT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // SATCOUNT
#endif // STAT

    // push delta to j
    a->resCap -= delta;
    a->rev->resCap += delta;
#ifdef STAT
    pushCnt++;
    pushCnt1++;
    if (a->resCap >0)
        nStrPushCnt++;
#endif // STAT

    if ((a->resCap == 0) && (eMax > j->d))
      eMax = j->d;

    j->excess += delta;
    i->excess -= delta;
#ifdef STAT
    if (i->excess == 0)
        deplPush1++;
	else
        nDeplPush1++;
#endif // STAT
//    assert(j->excess > 0);

    // if i was active but no longer is
    if (i->excess == 0) {
      l = buckets + i->d;
      aDelete(l, i);
      iAdd(l, i);
#ifdef STAT
      aDeleteCnt++;
      iAddCnt++;
#endif // STAT
    }

    stopB = (j+1)->first;
    for (b = j->current; b < stopB; b++) {
#ifdef STAT
      arcScanCnt1++;
#endif // STAT
      if ((b->resCap > 0) && (b->head->d < j->d)) {
	k = b->head;
	delta = min(b->resCap, j->excess);
//	assert(delta > 0);

#ifdef STAT
#ifdef SATCOUNT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // SATCOUNT
#endif // STAT

	b->resCap -= delta;
	b->rev->resCap += delta;
#ifdef STAT
	pushCnt++;
	pushCnt1++;
    if (b->resCap >0)
        nStrPushCnt++;
#endif // STAT

	if ((b->resCap == 0) && (eMax > k->d))
	  eMax = k->d;

	k->excess += delta;
	j->excess -= delta;
#ifdef STAT
	if (j->excess == 0)
        deplPush1++;
	else
        nDeplPush1++;
#endif // STAT

//#ifndef SAT_ALL_INIT
//	assert(k->excess > 0);
//#endif // SAT_ALL_INIT

	// did k become active?
	if ((k->excess == delta) && (k != sink)) {
	  l = buckets + k->d;
	  iDelete(l, k);
	  aAdd(l, k);
#ifdef STAT
	  iDeleteCnt++;
	  aAddCnt++;
#endif // STAT
	}
#ifndef SIMPLE_INIT
    if ((k->excess>0) && (k->excess < delta)) {
	  l = buckets + k->d;
	  eMax = 1;
	  iDelete(l, k);
	  ++k->d;
	  aAdd(l+1, k);
#ifdef STAT
	  iDeleteCnt++;
	  aAddCnt++;
	  relabelCnt++;
#endif // STAT
	}

    // did k become neutral?
    if ((k->excess==0) && (k->excess < delta)) {
	  l = buckets + k->d;
	  eMax = 1;
	  iDelete(l, k);
	  ++k->d;
	  iAdd(l+1, k);
#ifdef STAT
	  iDeleteCnt++;
	  iAddCnt++;
	  relabelCnt++;
#endif // STAT
	}
#endif // SIMPLE_INIT

	if (j->excess == 0) {
	  j->current = b;
	  break;
	}
      }
    }

//    assert(j->excess == 0);
    if (relabelJ)
      relabel(j);
  }
}


void sinkPush(node *i)

{
  arc *a;
  cType delta;
  bucket *l;

//  assert(i->current->head == sink);
//  assert(i->d == 1);

  a = i->current;
  delta = min(a->resCap, i->excess);
//  assert(delta > 0);

#ifdef STAT
#ifdef SATCOUNT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // SATCOUNT
#endif // STAT

  a->resCap -= delta;
  a->rev->resCap += delta;
#ifdef STAT
  pushCnt++;
  pushCnt1++;
  if (a->resCap >0)
        nStrPushCnt++;
#endif // STAT

  if (a->resCap == 0)
    eMax = 0;

  sink->excess += delta;
  i->excess -= delta;
#ifdef STAT
  if (i->excess == 0)
        deplPush1++;
	else
        nDeplPush1++;
#endif // STAT

  // if i no longer active
  if (i->excess == 0) {
    l = buckets + i->d;
    aDelete(l, i);
    iAdd(l, i);
#ifdef STAT
    aDeleteCnt++;
    iAddCnt++;
#endif // STAT
  }
}

void deficitPush(node *i)

{
  arc *a;
  cType delta;
  bucket *l;
  node *j;

  j = i -> current -> head;

//  assert(i->excess > 0);
//  assert(j->excess < 0);
//  assert(j->d < i ->d );

  a = i->current;

  delta = min(a->resCap, i->excess);
//  assert(delta > 0);

#ifdef STAT
#ifdef SATCOUNT
      satCount(cap[a-arcs], a ->resCap, delta);
#endif // SATCOUNT
#endif // STAT

  a->resCap -= delta;
  a->rev->resCap += delta;
#ifdef STAT
  pushCnt++;
  pushCnt1++;
  if (a->resCap >0)
        nStrPushCnt++;
#endif // STAT

  if (a->resCap == 0)
    eMax = 1;

  j->excess += delta;
  i->excess -= delta;
#ifdef STAT
  if (i->excess == 0)
        deplPush1++;
	else
        nDeplPush1++;
#endif // STAT

  // if i no longer active
  if (i->excess == 0) {
    l = buckets + i->d;
    aDelete(l, i);
    iAdd(l, i);
#ifdef STAT
    aDeleteCnt++;
    iAddCnt++;
#endif // STAT
  }

  // if j becomes active
  if (j->excess > 0) {
    l = buckets + j->d;
    eMax = 1;
    iDelete(l,j);
    ++ j->d;        // Only deficit nodes have label 1 in the stage one
    aAdd(l+1, j);
#ifdef STAT
    iDeleteCnt++;
    aAddCnt++;
    relabelCnt++;
#endif // STAT
  }

  // if j becomes neutral
  if (j->excess == 0) {
    l = buckets + j->d;
    eMax = 1;
    iDelete(l,j);
    ++ j->d;        // Only deficit nodes have label 1 in the stage one
    iAdd(l+1, j);
#ifdef STAT
    iDeleteCnt++;
    iAddCnt++;
    relabelCnt++;
#endif // STAT
  }
}

/* first stage  -- maximum preflow*/
void stageOne ( )

{

  node *i;
  bucket *l;
  node *j;
  arc *a, *stopA;
  arc *b, *stopB;

#if defined(INIT_UPDATE)
  globalUpdate ();
#else
  workSinceUpdate = 0;
#endif

  //  printf(">>> init %ld n %ld updThresh %ld\n", workSinceUpdate, n, updThresh);


  /* main loop */
  while (aMax >= 0) {
#ifdef STAT
    nodeScanCnt1++;
#endif // STAT
    /*
    // is it time for global update?
    if (workSinceUpdate * globUpdtFreq > updThresh) {
      globalUpdate ();
    }
    */

    l = buckets + aMax;
    i = l->firstActive;

    if (i == sentinelNode)
      aMax--;
    else {
      //!!!
//      assert (i->d == aMax);
//      assert(i->excess > 0);

      // make sure i has an admissible neighbour j which is current
      stopA = (i+1)->first;
      j = NULL;

      for (a = i->current; a < stopA; a++) {
#ifdef STAT
      arcScanCnt1++;
#endif // STAT
	if ((a->resCap > 0) && (a->head->d < i->d)) {
	  j = a->head;
#ifdef SIMPLE_INIT
	  if (j == sink) {
	    i->current = a;
	    break;
	  }
#else
      if (j -> excess < 0) {
	    i->current = a;
	    break;
	  }
#endif // SIMPLE_INIT
	  stopB = (j+1)->first;
	  for (b = j->current; b != stopB; b++) {
#ifdef STAT
        arcScanCnt1++;
#endif // STAT
	    if ((b->resCap > 0) && (b->head->d < j->d)) {
	      j->current = b;
	      break;
	    }
	  }

	  if (b == stopB) {
	    relabel(j);
	    if (i->d == DELETED) break;
	  }
	  else {
	    i->current = a;
	    break;
	  }
	}
      }

      if (i->d == DELETED) continue;

      if (a == stopA) {
	relabel(i);
	// is it time for global update?
	if (workSinceUpdate * globUpdtFreq > updThresh) {
	  globalUpdate ();
	}
      }
      else {
//	assert(j != NULL);

#ifdef SIMPLE_INIT
	if (j == sink)
	  sinkPush(i);
#else
    if (j -> excess <0)
    {
//        assert(i->excess >0);
        deficitPush(i);

        if ((buckets  + 1)->firstInactive == sentinelNode)
            break;
//#ifdef TEST
//    if (nNode(i)==558)
//        printf("The excess of nod %d after deficitPush is %d\n", nNode(i), i->excess);
//#endif // TEST
    }

#endif // SIMPLE_INIT
	else
    {
	  twoLevPush(i);
#ifdef PROGRESS
    if (nNode(i)==558)
        printf("The excess of nod %d after twoLevPush is %d\n", nNode(i), i->excess);
#endif // PROGRESS
    }
      }
    }
  } /* end of the main loop */

  flow = sink->excess;

}


int main (int argc, char *argv[])


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
  long long sum;
  bucket *l;
#endif
  arc *stop__A;

  int nonTriv;


  if (argc > 2) {
    printf("Usage: %s [update frequency]\n", argv[0]);
    exit(1);
  }

  if (argc < 2)
    globUpdtFreq = GLOB_UPDT_FREQ;
  else
    globUpdtFreq = (float) atof(argv[1]);
  globUpdtFreqOrig = globUpdtFreq;

  // printf("c\nc P2R version 0.45 \n");

//  #if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
  parse( &n, &m, &mInp, &nodes, &arcs, &cap, &source, &sink, &nMin, &allCap);
//  #else
//  parse( &n, &m, &mInp, &nodes, &arcs, &cap, &source, &sink, &nMin );
//  #endif

  //printf("c nodes:       %10ld\nc arcs:        %10ld (%ld)\nc\n", n, mInp, m*2);
  //printf("%10ld, %10ld, ", n, m);


  // printf("c (freq %.4f)\nc \nc\n", globUpdtFreq);
  //printf("%.4f, ", globUpdtFreq);

  cc = allocDS();
#ifdef STAT
  allocDSCnt++;
#endif // STAT
  if ( cc ) { fprintf ( stderr, "Allocation error\n"); exit ( 1 ); }

  //  printGraph();
#ifdef TIME
  t = timer();
  t3 = t;
  t2 = t;
#endif // TIME

#ifdef PROGRESS
forAllNodes(i)
    forAllArcs(i,a)
        if(cap[nArc(a)]>0)
            printf ( "%2ld -> %2ld: %2ld\n",
                    nNode(i), nNode( a -> head ), cap[nArc(a)] );
#endif // PROGRESS

  avCap = (double)(allCap)/(double)(m); // the average arc capacity
  avNdCap = (double)(allCap)/(double)(n); // the capacity per node

  nonTriv = init();
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
#endif // TEST

#ifdef PROGRESS
    forAllNodes(i)
    if (nNode(i)==558)
        printf("The excess of nod %d after initialization is %d\n", nNode(i), i->excess);

    printf("\nResidual network after initialization:\n");
    forAllNodes(i)
        forAllArcs(i, a)
            if(a->resCap>0)
                printf("%d -> %d: %d \n", nNode(i), nNode(a->head), a->resCap);

    printf("\nExcesses after Initialization:\n");
    forAllNodes(i)
    printf("label  of node %d is %d with excess %d \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS
  if (nonTriv)
    stageOne();
  else
    flow = 0;

#ifdef PROGRESS
    forAllNodes(i)
    if (nNode(i)==558)
        printf("The excess of nod %d after stage one is %d\n", nNode(i), i->excess);

    printf("\nResidual network after stage one:\n");
    forAllNodes(i)
        forAllArcs(i, a)
            if(a->resCap>0)
                printf("%d -> %d: %d \n", nNode(i), nNode(a->head), a->resCap);

    printf("\nExcesses after stage one:\n");
    forAllNodes(i)
    printf("label  of node %d is %d with excess %d \n", nNode(i), i-> d, i->excess);
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
   //stageTwo ( );
  stageTwo_hipr ();
  #ifdef TEST
//    printf ("stage2 flow,         %12.01f\n", flow);
#endif // TEST
#ifdef PROGRESS
    printf("\nExcesses after stage two:\n");
    forAllNodes(i)
    printf("label  of node %d is %d with excess %d \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS
#ifndef SIMPLE_INIT
 stageTwoPseudo ();
   #ifdef TEST
//    printf ("final flow,         %12.01f\n", flow);
#endif // TEST
#ifdef PROGRESS
    printf("\nExcesses after Stage two for deficits:\n");
    forAllNodes(i)
    printf("label  of node %d is %d with excess %d \n", nNode(i), i-> d, i->excess);
#endif // PROGRESS
#endif // SIMPLE_INIT

#ifdef TIME
  t = timer() - t;
#endif // TIME
#endif // CUT_ONLY

//------------------------ Outputs ------------------------------------

#ifdef TEST
    printf("nodes,         %10ld\narcs,          %10ld\n", n, m);
    printf ("flow,         %12.01f\n", flow);
#else
  printf("%10ld, %10ld, ", n, m);
  printf ("%12.01f, ", flow);
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
    printf("c (freq %.4f)\n", globUpdtFreq);
    //printf ("c relabels:    %10ld\n", relabelCnt);
    printf ("c upd. scans:  %10d\n", upScanCnt);
    printf ("c scans/n:     %10.2f\n",
	    ((double) (relabelCnt + upScanCnt)) / ((double) n));
    //printf ("c pushes:      %10ld\n", pushCnt);
    //printf ("c updates:     %10ld\n", updateCnt);
    //printf ("c gaps:        %10ld\n", gapCnt);
    //printf ("c gap nodes:   %10llu\n", gNodeCnt);
    //printf ("c del nodes:   %10llu\n", dNodeCnt);
    //printf ("c\n");

    printf ("Operation counts at the first phase of the algorithm are:\n");

    printf ("c scans/n:     %10.2f\n",
	    ((double) (relabelCnt + nodeScanCntGlbUp)) / ((double) n));
    printf ("c\n");

    printf ("updates,       %10d\n", updateCnt);
    printf ("globUpdtCnt,   %10d\n", globUpdtCnt);
    printf ("nodeScansGlbUp,%10llu\n", nodeScanCntGlbUp);
    printf ("arcScansGlbUp, %10llu\n", arcScanCntGlbUp);
    printf ("RelabelsGlbUp, %10llu\n\n", relabelCntGlbUp);

    printf ("gaps,          %10ld\n", gapCnt);
    printf ("gap nodes,     %10ld\n", gNodeCnt);
    printf ("c del nodes:   %10ld\n", dNodeCnt);
    printf ("nodeScansGap,  %10llu\n", nodeScanCntGap);
    printf ("relabelGap,    %10llu\n\n", relabelCntGap);

    printf ("nodeScansI,    %10llu\n", nodeScanCntI);
    printf ("arcScansI,     %10llu\n", arcScanCntI);
    printf ("PushesI,       %10llu\n", pushCntI);
    printf ("StrPushesI,    %10llu\n", pushCntI);
    printf ("relabelsI,     %10llu\n\n", relabelCntI);

    printf ("arcScanCntLab, %10llu\n\n", arcScanCntLab );

    printf ("nodeScans1,    %10llu\n", nodeScanCnt1);
    printf ("arcScans1,     %10llu\n", arcScanCnt1);
    printf ("StrPushes1,    %10llu\n", pushCnt1 - nStrPushCnt);
    printf ("nStrPushes1,   %10llu\n", nStrPushCnt);
    printf ("pushes1,       %10llu\n", pushCnt1);
    printf ("deplPush1,     %10llu\n", deplPush1);
    printf ("nDeplPush1,    %10llu\n", nDeplPush1);
    printf ("relabels1,     %10llu\n\n", relabelCnt);

    printf ("nodeScans_all_1, %10llu\n", nodeScanCnt1 + nodeScanCntGlbUp + nodeScanCntGap);
    printf ("arcScans_all_1,  %10u\n", arcScanCnt1 + arcScanCntGlbUp +  arcScanCntLab);
    printf ("StrPushes_all_1, %10llu\n", pushCnt1 - nStrPushCnt);
    printf ("nStrPushes_all_1,%10llu\n", nStrPushCnt);
    printf ("pushes_all_1,    %10llu\n", pushCnt1 );
    printf ("relabels_all_1,  %10llu\n\n", relabelCnt + relabelCntGap + relabelCntGlbUp);

    printf("aAddCnt,        %10llu\n", aAddCnt);
    printf("aDeleteCnt,     %10llu\n", aDeleteCnt);
    printf("iAddCnt,        %10llu\n", iAddCnt);
    printf("iDeleteCnt,     %10llu\n", iDeleteCnt);
    printf("allocDSCnt,     %10llu\n", allocDSCnt);
    printf("checkDsCnt,     %10llu\n\n", checkDsCnt);
#ifndef CUTONLY
  printf ("\nOperation counts of the second phase of the algorithm are:\n");
  printf ("nodeScans2,      %10llu\n", nodeScanCnt2);
  printf ("arcScans2,       %10llu\n", arcScanCnt2);
  printf ("StrPushes2,      %10llu\n", pushCnt2 - nStrPushCnt2);
  printf ("nStrPushes2,     %10llu\n", nStrPushCnt2);
  printf ("pushes2,         %10llu\n", pushCnt2);
  printf ("deplPushes2,     %10llu\n", deplPush2);
  printf ("nDeplPushes2,    %10llu\n", nDeplPush2);
  printf ("selfLoopPuses2,  %10llu\n", selfLoopPush2);
  printf ("loopPushes2,     %10llu\n", loopPush2);
  printf ("relabels2,       %10llu\n\n", relabelCnt2);

  printf ("MaxFlow tm,      %10.2f\n", t);
  printf ("arcScans,        %10llu\n", arcScanCnt1 + arcScanCntGlbUp + arcScanCntI + arcScanCntLab + arcScanCnt2 );
  printf ("nodeScans,       %10llu\n", nodeScanCnt1 + nodeScanCntGlbUp + nodeScanCntI + nodeScanCntGap + nodeScanCnt2 );
  printf ("pushes,          %10llu\n", pushCnt1 + pushCntI + pushCnt2);
  printf ("relabels,        %10llu\n\n", relabelCnt + relabelCntI + relabelCntGap + relabelCntGlbUp + relabelCnt2);
#endif // CUTONLY

#ifdef SATCOUNT
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
#endif // SATCOUNT

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
    printf("%.4f, ", globUpdtFreq);
    printf ("%10ld, ", upScanCnt);
    printf ("%10.2f, ", ((float) (relabelCnt + upScanCnt)) / ((float) n));
    //printf ("%10ld, ", dNodeCnt);
    printf ("%10.2f, ", ((float) (relabelCnt + nodeScanCntGlbUp)) / ((float) n));

    printf ("%10ld, ", updateCnt);
    printf ("%10ld, ", globUpdtCnt);
    printf ("%10llu, ", nodeScanCntGlbUp);
    printf ("%10llu, ", arcScanCntGlbUp);
    printf ("%10llu, ", relabelCntGlbUp);

    printf ("%10ld, ", gapCnt);
    printf ("%10ld, ", gNodeCnt);
    printf ("%10ld, ", dNodeCnt);
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
    printf("%10llu, ", aDeleteCnt);
    printf("%10llu, ", iAddCnt);
    printf("%10llu, ", iDeleteCnt);
    printf("%10llu, ", allocDSCnt);
    printf("%10llu, ", checkDsCnt);
#ifndef CUT_ONLY
    printf ("%10llu, ", nodeScanCnt2);
    printf ("%10llu, ", arcScanCnt2);
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

#ifdef SATCOUNT
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
#endif // SATCOUNT

  printf("%10llu, ", allCap);
  printf("%lf, ", avCap);
  printf("%lf, ", avNdCap);

#endif // TEST
//-----------------------------------------------------------------
#endif // STAT

  //  printGraph();
#ifdef CHECK_SOLUTION

  /* check if you have a flow (pseudoflow) */
  /* check arc flows */
  if (nonTriv) {
    forAllNodes(i) {
      forAllArcs(i,a) {
	if ((a->resCap + a->rev->resCap !=
	     cap[a-arcs] + cap[a->rev - arcs])
	    || (a->resCap < 0)
	    || (a->rev->resCap < 0)) {
	  printf("ERROR: bad arc flow\n");
	  //	  exit(2);
	}
      }
    }

    /* check conservation */
    forAllNodes(i)
      if ((i != source) && (i != sink)) {
#ifdef CUT_ONLY
	if (i->excess < 0) {
	  printf("ERROR: nonzero node excess\n");
	  //	exit(2);
	}
#else
	if (i->excess != 0) {
	  printf("ERROR: nonzero node excess\n");
	  //	exit(2);
	}
#endif

	sum = 0;
	forAllArcs(i,a) {
	  sum += ((long long) cap[a - arcs]) -
	    ((long long) a->resCap);
	}

	if (i->excess != sum) {
	  printf("ERROR: conservation constraint violated\n");
	  //	exit(2);
	}
      }

    /* check if mincut is saturated */
    aMax = dMax = 0;
    forAllNodes(i) {
      i->d = DELETED;
    }
    for (l = buckets; l <= buckets + n; l++) {
      l->firstActive = sentinelNode;
      l->firstInactive = sentinelNode;
    }
    sink->d = 0;
    iAdd(buckets, sink);
#ifdef STAT
    long saveUp = upScanCnt;
#endif // STAT
    globalUpdate();
#ifdef STAT
    updateCnt--; // this one does not count
    upScanCnt = saveUp;
#endif // STAT
    if (source->d < n) {
      printf("ERROR: the solution is not optimal");
      //    exit(2);
    }

    //printf("c\nc Solution checks (feasible and optimal)\nc\n");
    printf("feasible and optimal");
  }
  else
    //printf("c\nc trivial cut, zero flow\nc\n");
    printf("trivial cut- zero flow ");
#endif

  //  printf(">>> init pushes: %ld\n", pushCntI);

#ifdef PRINT_FLOW
    printf ("c flow values\n");
    forAllNodes(i) {
      ni = nNode(i);
      forAllArcs(i,a) {
	na = nArc(a);
	if ( cap[na] > 0 )
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
    if (j->d < DELETED)
      printf("c %ld\n", nNode(j));

#endif

exit(0);

}
