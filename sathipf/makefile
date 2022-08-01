###############################################################################################
#                                COMPILER FLAGS                                    	      #
###############################################################################################
#                                                                                  	      #
# -DSTATS          : Display operation counts.                                       	      #
# -DDISPLAY_CUT    : Output includes the nodes in the source set of the minimum cut. 	      #
# -DDISPLAY_FLOW   : Displays flow values for each arc.					      #
# -DSIMPLE_INIT	   : Simple initialisation						      #
# -DSAT_ALL_INIT   : Initialisation with saturating all arcs				      #
# -DSAT_SMALL_INIT : Initialisation with saturating small arcs (<= 1.05 average arc capacity) #
# -DSAT_LARGE_INIT  : Initialisation with saturating large arcs (>= 1.05 average arc capacity) #
# -DAVNDCAP        : Repalcing average arc capacity with average capacity per node            #         
#                                                                                  	      #
###############################################################################################



CFLAGS=-O4 -Wall -DSTATS -DSTDIN
BINDIR=bin
CC=gcc

all: ${BINDIR}/pseudo_lifo ${BINDIR}/pseudo_fifo ${BINDIR}/pseudo_lo_fifo ${BINDIR}/pseudo_lo_lifo \
     ${BINDIR}/sa_pseudo_lifo ${BINDIR}/sa_pseudo_fifo ${BINDIR}/sa_pseudo_lo_fifo ${BINDIR}/sa_pseudo_lo_lifo \
     ${BINDIR}/ss_pseudo_lifo ${BINDIR}/ss_pseudo_fifo ${BINDIR}/ss_pseudo_lo_fifo ${BINDIR}/ss_pseudo_lo_lifo \
     ${BINDIR}/ss2_pseudo_lifo ${BINDIR}/ss2_pseudo_fifo ${BINDIR}/ss2_pseudo_lo_fifo ${BINDIR}/ss2_pseudo_lo_lifo \
     ${BINDIR}/sl_pseudo_lifo ${BINDIR}/sl_pseudo_fifo ${BINDIR}/sl_pseudo_lo_fifo ${BINDIR}/sl_pseudo_lo_lifo \
     ${BINDIR}/sl2_pseudo_lifo ${BINDIR}/sl2_pseudo_fifo ${BINDIR}/sl2_pseudo_lo_fifo ${BINDIR}/sl2_pseudo_lo_lifo

pseudo_lifo: ${BINDIR}/pseudo_lifo

pseudo_fifo: ${BINDIR}/pseudo_fifo

pseudo_lo_fifo: ${BINDIR}/pseudo_lo_fifo

pseudo_lo_lifo: ${BINDIR}/pseudo_lo_lifo


sa_pseudo_lifo: ${BINDIR}/sa_pseudo_lifo

sa_pseudo_fifo: ${BINDIR}/sa_pseudo_fifo

sa_pseudo_lo_fifo: ${BINDIR}/sa_pseudo_lo_fifo

sa_pseudo_lo_lifo: ${BINDIR}/sa_pseudo_lo_lifo


ss_pseudo_lifo: ${BINDIR}/ss_pseudo_lifo

ss_pseudo_fifo: ${BINDIR}/ss_pseudo_fifo

ss_pseudo_lo_fifo: ${BINDIR}/ss_pseudo_lo_fifo

ss_pseudo_lo_lifo: ${BINDIR}/ss_pseudo_lo_lifo


ss2_pseudo_lifo: ${BINDIR}/ss2_pseudo_lifo

ss2_pseudo_fifo: ${BINDIR}/ss2_pseudo_fifo

ss2_pseudo_lo_fifo: ${BINDIR}/ss2_pseudo_lo_fifo

ss2_pseudo_lo_lifo: ${BINDIR}/ss2_pseudo_lo_lifo


sl_pseudo_lifo: ${BINDIR}/sl_pseudo_lifo

sl_pseudo_fifo: ${BINDIR}/sl_pseudo_fifo

sl_pseudo_lo_fifo: ${BINDIR}/sl_pseudo_lo_fifo

sl_pseudo_lo_lifo: ${BINDIR}/sl_pseudo_lo_lifo


sl2_pseudo_lifo: ${BINDIR}/sl2_pseudo_lifo

sl2_pseudo_fifo: ${BINDIR}/sl2_pseudo_fifo

sl2_pseudo_lo_fifo: ${BINDIR}/sl2_pseudo_lo_fifo

sl2_pseudo_lo_lifo: ${BINDIR}/sl2_pseudo_lo_lifo


${BINDIR}/pseudo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSIMPLE_INIT pseudo.c -o bin/pseudo_lifo

${BINDIR}/pseudo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSIMPLE_INIT pseudo.c -o bin/pseudo_fifo

${BINDIR}/pseudo_lo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSIMPLE_INIT -DLOWEST_LABEL pseudo.c -o bin/pseudo_lo_fifo

${BINDIR}/pseudo_lo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSIMPLE_INIT -DLOWEST_LABEL pseudo.c -o bin/pseudo_lo_lifo


${BINDIR}/sa_pseudo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_ALL_INIT pseudo.c -o bin/sa_pseudo_lifo

${BINDIR}/sa_pseudo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_ALL_INIT pseudo.c -o bin/sa_pseudo_fifo

${BINDIR}/sa_pseudo_lo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_ALL_INIT -DLOWEST_LABEL pseudo.c -o bin/sa_pseudo_lo_fifo

${BINDIR}/sa_pseudo_lo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_ALL_INIT -DLOWEST_LABEL pseudo.c -o bin/sa_pseudo_lo_lifo


${BINDIR}/ss_pseudo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_SMALL_INIT pseudo.c -o bin/ss_pseudo_lifo

${BINDIR}/ss_pseudo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_SMALL_INIT pseudo.c -o bin/ss_pseudo_fifo

${BINDIR}/ss_pseudo_lo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_SMALL_INIT -DLOWEST_LABEL pseudo.c -o bin/ss_pseudo_lo_fifo

${BINDIR}/ss_pseudo_lo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_SMALL_INIT -DLOWEST_LABEL pseudo.c -o bin/ss_pseudo_lo_lifo


${BINDIR}/ss2_pseudo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_SMALL_INIT -DAVNDCAP pseudo.c -o bin/ss2_pseudo_lifo

${BINDIR}/ss2_pseudo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_SMALL_INIT -DAVNDCAP pseudo.c -o bin/ss2_pseudo_fifo

${BINDIR}/ss2_pseudo_lo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_SMALL_INIT -DAVNDCAP -DLOWEST_LABEL pseudo.c -o bin/ss2_pseudo_lo_fifo

${BINDIR}/ss2_pseudo_lo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_SMALL_INIT -DAVNDCAP -DLOWEST_LABEL pseudo.c -o bin/ss2_pseudo_lo_lifo


${BINDIR}/sl_pseudo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_LARGE_INIT pseudo.c -o bin/sl_pseudo_lifo

${BINDIR}/sl_pseudo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_LARGE_INIT pseudo.c -o bin/sl_pseudo_fifo

${BINDIR}/sl_pseudo_lo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_LARGE_INIT -DLOWEST_LABEL pseudo.c -o bin/sl_pseudo_lo_fifo

${BINDIR}/sl_pseudo_lo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_LARGE_INIT -DLOWEST_LABEL pseudo.c -o bin/sl_pseudo_lo_lifo


${BINDIR}/sl2_pseudo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_LARGE_INIT -DAVNDCAP pseudo.c -o bin/sl2_pseudo_lifo

${BINDIR}/sl2_pseudo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_LARGE_INIT -DAVNDCAP pseudo.c -o bin/sl2_pseudo_fifo

${BINDIR}/sl2_pseudo_lo_fifo:
	${CC} ${CFLAGS} -DFIFO_BUCKET -DSAT_LARGE_INIT -DAVNDCAP -DLOWEST_LABEL pseudo.c -o bin/sl2_pseudo_lo_fifo

${BINDIR}/sl2_pseudo_lo_lifo:
	${CC} ${CFLAGS} -DLIFO_BUCKET -DSAT_LARGE_INIT -DAVNDCAP -DLOWEST_LABEL pseudo.c -o bin/sl2_pseudo_lo_lifo



clean:
	rm -f ${BINDIR}/*