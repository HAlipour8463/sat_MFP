# makefile for programs and generator

# compiler flags:
#
# CHECK_SOLUTION     check if at the end the sink is unreachable 
#                    from the source
# CUT_ONLY           define to compute min-cut but not max-flow
# STAT         	     define to print detailed operation statistics
# PRINT_FLOW         define to print out flow value
# PRINT_CUT          define to print out the sink size of the cut
# INIT_UPDATE        perform initial global update
# FULL_RELABEL       increase distance label as much as possible
#                    instead of adding 1
# LASY_UPDATE        stop when all vertices with excess have been reached
# NO_REALLLOC        do not call realloc to free up some memory
# SIMPLE_INIT	     simple initialisation
# SAT_ALL_INIT	     saturating all initialisation	
# SAT_SMALL_INIT     saturating small initialisation	
# SAT_LARGE_INIT     saturating large initialisation	
# AVNDCAP 	     the average capacity per node	

CCOMP = gcc
#CCOMP = g++
CFLAGS = -O4 -DNDEBUG -DSTAT -DCHECK_SOLUTION -Wall -lm -DLASY_UPDATE -DNO_REALLOC
#CFLAGS = -g -DPRINT_STAT -DCHECK_SOLUTION -Wall -lm -DLASY_UPDATE


all: hipr sa_hipr  ss_hipr  sl_hipr  sag_hipr  ssg_hipr  slg_hipr  ss2_hipr  sl2_hipr ss2g_hipr  sl2g_hipr

hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSIMPLE_INIT -o hipr hipr.c

sa_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_ALL_INIT -o sa_hipr hipr.c
ss_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -o ss_hipr hipr.c
sl_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -o sl_hipr hipr.c
ss2_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DAVNDCAP -o ss2_hipr hipr.c
sl2_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DAVNDCAP -o sl2_hipr hipr.c


sag_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_ALL_INIT -DINIT_UPDATE -o sag_hipr hipr.c
ssg_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DINIT_UPDATE -o ssg_hipr hipr.c
slg_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DINIT_UPDATE -o slg_hipr hipr.c
ss2g_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DAVNDCAP -DINIT_UPDATE -o ss2g_hipr hipr.c
sl2g_hipr: hipr.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DAVNDCAP -DINIT_UPDATE -o sl2g_hipr hipr.c




clean: 
	rm -f hipr sa_hipr ss_hipr sl_hipr sag_hipr ssg_hipr slg_hipr ss2_hipr  sl2_hipr ss2g_hipr  sl2g_hipr *~
