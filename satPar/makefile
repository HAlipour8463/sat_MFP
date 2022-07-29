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
# AVNDCAP	     average arc cpacity per node

CCOMP = gcc
#CCOMP = g++
CFLAGS = -O4 -DNDEBUG -DSTAT -DCHECK_SOLUTION -Wall -lm -DLASY_UPDATE -DNO_REALLOC
#CFLAGS = -g -DPRINT_STAT -DCHECK_SOLUTION -Wall -lm -DLASY_UPDATE


all: par sa_par ss_par sl_par sag_par ssg_par slg_par ss2_par sl2_par ss2g_par sl2g_par

par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSIMPLE_INIT -o par par.c

sa_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_ALL_INIT -o sa_par par.c
ss_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -o ss_par par.c
sl_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -o sl_par par.c
ss2_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DAVNDCAP -o ss2_par par.c
sl2_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DAVNDCAP -o sl2_par par.c


sag_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_ALL_INIT -DINIT_UPDATE -o sag_par par.c
ssg_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DINIT_UPDATE -o ssg_par par.c
slg_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DINIT_UPDATE -o slg_par par.c
ss2g_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DAVNDCAP -DINIT_UPDATE -o ss2g_par par.c
sl2g_par: par.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DAVNDCAP -DINIT_UPDATE -o sl2g_par par.c




clean: 
	rm -f par sa_par ss_par sl_par sag_par ssg_par slg_par ss2_par sl2_par ss2g_par sl2g_par *~
