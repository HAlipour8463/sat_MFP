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

CCOMP = gcc
#CCOMP = g++
CFLAGS = -O4 -DNDEBUG -DSTAT -DCHECK_SOLUTION -Wall -lm -DLASY_UPDATE -DNO_REALLOC
#CFLAGS = -g -DPRINT_STAT -DCHECK_SOLUTION -Wall -lm -DLASY_UPDATE


all: p2r sa_p2r ss_p2r sl_p2r sag_p2r ssg_p2r slg_p2r

p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSIMPLE_INIT -o p2r p2r.c

sa_p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_ALL_INIT -o sa_p2r p2r.c
ss_p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -o ss_p2r p2r.c
sl_p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -o sl_p2r p2r.c

sag_p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_ALL_INIT -DINIT_UPDATE -o sag_p2r p2r.c
ssg_p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_SMALL_INIT -DINIT_UPDATE -o ssg_p2r p2r.c
slg_p2r: p2r.c parser.c types.h timer.c
	$(CCOMP) $(CFLAGS) -DSAT_LARGE_INIT -DINIT_UPDATE -o slg_p2r p2r.c




clean: 
	rm -f p2r sa_p2r ss_p2r sl_p2r sag_p2r ssg_p2r slg_p2r *~
