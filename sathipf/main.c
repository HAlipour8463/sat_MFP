#include <stdio.h>
#include <sys/time.h>
//#include <sys/resource.h>
#include <stdlib.h>
#include<assert.h>

//#define TIMER
#define STATS
//#define PROGRESS
//#define DISPLAY_FLOW
//#define STDIN
//#define TEST
#define SATCOUNT

//#define Alloc
//#define FIFO_BUCKET
//#define LOWEST_LABEL
#define SIMPLE_INIT
//#define SAT_ALL_INIT
//#define SAT_SMALL_INIT
//#define SAT_LARGE_INIT
/* Active SAT_SMALL&LARGE_INIT  to saturate arcs with capacities >= (1+ satThreshold) times of avCap (or avNdCap) and  arcs with
capacities <= (1- satThreshold) times of avCap (or avNdCap) or greater than or equal to the given satThreshold */
//#define SAT_SMALL&LARGE_INIT
//#define AVNDCAP
//#define SAT125 /* Defines the threshold for which the type of arcs that will be saturated is determined */


#ifdef SAT25
    float satThreshold = 0.25;
#elif defined  SAT50
    float satThreshold = 0.50;
#elif defined SAT75
    float satThreshold = 0.75;
#elif defined SAT95
    float satThreshold = 0.95;
#elif defined SAT100
    float satThreshold = 1;
#elif defined SAT105
    float satThreshold = 1.05;
#elif defined SAT125
    float satThreshold = 1.25;
#elif defined SAT150
    float satThreshold = 1.5;
#elif defined SAT175
    float satThreshold = 1.75;
#elif defined SAT200
    float satThreshold = 2;
#else
    float satThreshold = 0;
#endif


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
//	uint flow;
	ullint flow;
//	uint capacity;
	ullint capacity;
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

ullint  allCap;             /* sum of all arc capacities */
double avCap;               /* the average of arc capacities */
double avNdCap;             /* the arc capacities per node */

#if (defined(SAT_SMALL_INIT) || defined(SAT_LARGE_INIT))
ullint allCap = 0;
double avCap = 0;
double avNdCap = 0;
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
#endif // STATS

#define min(a, b) (((a) < (b)) ? a : b)

#define max(a, b) (((a) > (b)) ? a : b)

#ifdef STATS
/* Count different types of arc saturations  */
#ifdef SATCOUNT
int satCount(ullint tstCap, ullint tstResCap, ullint tstDelta)
{
#ifdef PROGRESS
    printf("\nsatCount is called\n");
    printf("tstCap: %llu,\n", tstCap);
    printf("tstResCap: %llu,\n", tstResCap);
    printf("tstDelta: %llu,\n\n", tstDelta);
#endif // PROGRESS
    long satState;

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
#endif // STATS

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
	FILE *fp = fopen("ak_1022.txt", "r");
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

			sscanf (line, "%c %d %d %llu", &ch, &from, &to, &capacity);

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

            allCap += capacity;

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
	uint i, size;
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
        for (int j=0; j< size; ++j)
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
#ifdef AVNDCAP
        if ((tempArc->to->number != source) && (tempNode->number != sink) &&  ( ((tempArc->capacity>0) && (tempArc->capacity <= satThreshold *avNdCap)) ||
                (tempNode->number == source) || (tempArc->to->number == sink)) ) b = 1;
        else b = 0;
#else
        if ((tempArc->to->number != source) && (tempNode->number != sink) &&  ( ((tempArc->capacity>0) && (tempArc->capacity <= satThreshold *avCap)) ||
                (tempNode->number == source) || (tempArc->to->number == sink)) ) b = 1;
        else b = 0;
#endif // AVNDCAP
#elif defined SAT_LARGE_INIT
#ifdef AVNDCAP
        if ((tempArc->to->number != source) && (tempNode->number != sink) &&  ( (tempArc->capacity >= satThreshold *avNdCap) ||
                (tempNode->number == source) || (tempArc->to->number == sink)) ) b = 1;
        else b = 0;
#else
        if ((tempArc->to->number != source) && (tempNode->number != sink) &&  ( (tempArc->capacity >= satThreshold *avCap) ||
                (tempNode->number == source) || (tempArc->to->number == sink)) ) b = 1;
        else b = 0;
#endif // AVNDCAP
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

#ifdef PROGRESS
    printf("\nwithin pushUpward we have:\n");
    printf("currentArc->capacity: %llu,\n", currentArc->capacity);
    printf("resCap: %llu,\n", resCap);
    printf("child->excess: %llu\n", child->excess);
    printf("delta: %llu,\n\n", min(child->excess, resCap));
#endif // PROGRESS
	if (resCap >= child->excess)
	{
	    if (resCap == child->excess)
        {
#ifdef STATS
        strPushCnt1++;
#ifdef SATCOUNT
      satCount(currentArc->capacity, resCap, min(resCap, child->excess));
#endif // SATCOUNT
#endif // STATS
        }
		else
        {
#ifdef STATS
            nStrPushCnt1++;
#ifdef SATCOUNT
      satCount(currentArc->capacity, resCap, min(resCap, child->excess));
#endif // SATCOUNT
#endif // STATS
        }

#ifdef PROGRESS
        printf("pushUpward from child: %lu with label %lu and excess %lli to parent: %lu with label %lu and excess %lld, pushed flow: %llu \n",
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
        printf("pushUpward from child: %lu with label %lu and excess %lli to parent: %lu with label %lu and excess %lld, pushed flow: %llu \n",
           child->number, child->label, child->excess, parent->number, parent->label, parent->excess, resCap);
#endif // PROGRESS

#ifdef STATS
	strPushCnt1++;
#ifdef SATCOUNT
      satCount(currentArc->capacity, resCap, min(resCap, child->excess));
#endif // SATCOUNT
#endif // STATS

	currentArc->direction = 0;
//	parent->excess += (llint) resCap;
//	child->excess -= (llint) resCap;
	parent->excess +=  resCap;
	child->excess -=  resCap;
#ifdef STATS
	nDeplPush1++;
#endif // STAT
	currentArc->flow = currentArc->capacity;
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
#ifdef SATCOUNT
      /* Since the capacity of the reverse arc is not fixed, we use the
      capacity of the original arc instead so that the push operation on
      the reverse arc is considered as the operation on the residual capacity
      instead of the original capacity in the satCount if the flow does not
      equal to the original arc capacity*/
      satCount(currentArc->capacity, flow, min(flow, child->excess));
#endif // SATCOUNT
#endif // STATS
        }
		else
        {
#ifdef STATS
            nStrPushCnt1++;
#ifdef SATCOUNT
      satCount(currentArc->capacity, flow, min(flow, child->excess));
#endif // SATCOUNT
#endif // STATS
        }

#ifdef PROGRESS
        printf("pushDownward from child: %lu with label %lu and excess %lli to parent: %lu with label %lu and excess %lld, pushed flow: %llu \n",
               child->number, child->label, child->excess, parent->number, parent->label, parent->excess, child->excess);
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
        printf("pushDownward from child: %lu with label %lu and excess %lli to parent: %lu with label %lu and excess %lld, pushed flow: %llu \n",
        child->number, child->label, child->excess, parent->number, parent->label, parent->excess, flow);
#endif // PROGRESS

#ifdef STATS
	strPushCnt1++;
#ifdef SATCOUNT
      satCount(currentArc->capacity, flow, min(flow, child->excess));
#endif // SATCOUNT
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
#ifdef STATS
	    nodeScanCnt1++;
#endif // STAT
		parent = current->parent;
		prevEx = parent->excess;

		arcToParent = current->arcToParent;

		if (arcToParent->direction)
		{
#ifdef PROGRESS
    printf("\nwithin pushExcess we have:\n");
    printf("arcToParent->capacity: %llu,\n", arcToParent->capacity);
    printf("resCap: %llu,\n", arcToParent->capacity - arcToParent->flow);
    printf("current->excess: %lli\n", current->excess);
    printf("delta: %llu,\n", min(current->excess, (arcToParent->capacity - arcToParent->flow)));
#endif // PROGRESS
			pushUpward (arcToParent, current, parent, (arcToParent->capacity - arcToParent->flow));
		}
		else
		{
			pushDownward (arcToParent, current, parent, arcToParent->flow);
		}
	}

#ifdef PROGRESS
    printf("after pushing within pushExcess function we have:\n\n");

   	printf ("strPushes1 , %lld\n", strPushCnt1);
	printf ("nStrPushes1, %lld\n", nStrPushCnt1);
	printf ("pushes1    , %lld\n\n", pushCnt1);

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
#endif // PROGRESS

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
#ifdef STATS
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
#ifdef STATS
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
#ifdef STATS
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
#ifdef STATS
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
#ifdef STATS
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
#ifdef STATS
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
#ifdef STATS
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

#ifdef STATS
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
#ifdef STATS
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

    avCap = (double)(allCap)/(double)(numArcs);
    avNdCap = (double)(allCap)/(double)(numNodes); // the capacity per node


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
	printf ("relabel2    , %lld\n\n", relabelCnt2);

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
  printf("satThreshold, %f\n", satThreshold);

  	int x1 = 3837191168, x2 =  2082712576, x3=1410065408, x4=145800000000, x5=20000000000;
	long long int  x6 = 145800000000, x7=20000000000;
	ullint x8 = 229526432000, x9=229526432000000;
	uint x10 = 229526432000, x11=229526432000000, x12= 5898979798;
	printf("\n x1: %d, x2: %d, x3: %d, x4: %d, x5: %d, x6: %lld, x7: %lld\n", x1, x2, x3, x4, x5, x6, x7);
	printf("sizeof(int): %d, sizeof(long long int): %d\n", sizeof(int), sizeof(long long int));
	printf("x8: %llu,   x9: %llu\n", x8, x9);
	printf("x10: %lu,   x11: %lu,   x12: %lu\n", x10, x11, x12);

    ullint x13=256, x14=66435;
	printf("x13: %llu,   x14: %llu\n", x13, x14);

	long x15=100000000000;
	unsigned long x16=100000000000;
	ullint x17=100000000000;
	printf("x15: %lu, x16: %lu, x17: %llu\n\n", x15, x16, x17);

	double x18 = 1111111111111.11;
	float x19=2.0;
	double x20=2.0;
	printf("x18: %lf\n  x19: %f\n  x18*x19: %lf\n  x20: %lf\n  x18*x20: %lf\n\n", x18, x19, x18*x20);

#endif // STATS
#else

    printf ("%u, ", numNodes);
	printf ("%u, ", numArcs);
#ifdef TIMER
	printf ("%.3f, ", (readEnd-readStart));
	printf ("%.3f, ", (initEnd-initStart));
	printf ("%.3f, ", (solveEnd-initStart));
	printf ("%.3f, ", (flowEnd-initStart));
#endif // TIMER
#ifdef STATS
	//printf ("%lld, ", numArcScans);
	printf ("%u, ", numMergers);
	//printf ("%lld, ", numPushes);
	//printf ("%d, ", numRelabels);
	printf ("%u, ", numGaps);
	printf ("%llu, ", arcScanCntI);
	printf ("%llu, ", nodeScanCntI);
	printf ("%llu, ", pushCntI);

    printf ("%llu, ", arcScanCnt1);
	printf ("%llu, ",   nodeScanCnt1);
	printf ("%llu, ", strPushCnt1);
	printf ("%llu, ", nStrPushCnt1);
	printf ("%llu, ", pushCnt1);
	printf ("%llu, ", deplPush1);
	printf ("%llu, ",nDeplPush1);
	printf ("%llu, ", relabelCnt1);
	printf ("%llu, ", rootScanCnt1);
	printf ("%llu, ", numBreakRelationship);
	printf ("%llu, ", numAddRelationship);

	printf ("%llu, ", arcScanCnt2);
	printf ("%llu, ", nodeScanCnt2);
	printf ("%llu, ", strPushCnt2);
	printf ("%llu, ", nStrPushCnt2);
	printf ("%llu, ", pushCnt2);
    printf ("%llu, ", deplPush2);
	printf ("%llu, ",nDeplPush2);
	printf ("%llu, ", relabelCnt2);

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
printf("%.2f, ", satThreshold);
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
