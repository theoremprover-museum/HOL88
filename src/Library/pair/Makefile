# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: pair
#
# $Id: Makefile,v 3.1 1993/12/07 14:42:10 jg Exp $
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : check out the source code,
#                     create theories and compile code
#
#    make clean	    : remove only compiled code
#	
#    make clobber   : remove both theories and compiled code
#
#    make decimate  : remove theories, compiled code and source code
#                     that isn't different to that in REVISION.
#
#    make destroy   : remove theories, compiled code and source code.
#                     HANDLE WITH CARE
#
#    make source    : check out the source code (see REVISION)
#
# ---------------------------------------------------------------------
# MACROS:
#
#    HOL            : the pathname of the version of hol used
#    SOURCE         : all the source files
#    REVISION       : The rcs revision of the source code to get
# =====================================================================

HOL= ../../hol

SOURCE= all.ml basic.ml both1.ml both2.ml conv.ml exi.ml pair.ml syn.ml

REVISION=

# =====================================================================
# Basic functions.
# =====================================================================

all: pair_ml.o
	@echo "===> library pair built"

source: ${SOURCE}

clean:
	rm -f *.l *.c *.o *.h *.data *.i *.s *.ir
	@echo "===> library pair: all object code deleted"

clobber:
	rm -f *.l *.c *.o *.th *.h *.data *.i *.s *.ir
	@echo "===> library pair: all object code and theory files deleted"

# decimate:
# 	rm -f *.l *.c *.o *.th *.h *.data *.i *.s *.ir
# 	rcsclean -r${REVISION} ${SOURCE}
# 	@echo "===> library pair: all source, object code and theories deleted"
# 
# destroy:
# 	rm -f *.l *.c *.o *.th *.h *.data *.i *.s *.ir
# 	rm -f ${SOURCE}
# 	@echo "===> library pair: all source, object code and theories deleted"

.FAILED:
	@echo "===> library pair build failed"

.DEFAULT:
	co -r${REVISION} $@

# =====================================================================
# Entries for individual files.
# =====================================================================

syn_ml.o: syn.ml
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'compilet `syn`;;'				\
        'quit();;' | ${HOL}

basic_ml.o: basic.ml syn_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `syn`;;'					\
        'compilet `basic`;;'				\
        'quit();;' | ${HOL}

both1_ml.o: both1.ml syn_ml.o basic_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `syn`;;'					\
        'loadf `basic`;;'				\
        'compilet `both1`;;'				\
        'quit();;' | ${HOL}

all_ml.o: all.ml syn_ml.o basic_ml.o both1_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `syn`;;'					\
        'loadf `basic`;;'				\
        'loadf `both1`;;'				\
        'compilet `all`;;'				\
        'quit();;' | ${HOL}

exi_ml.o: exi.ml syn_ml.o basic_ml.o both1_ml.o all_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `syn`;;'					\
        'loadf `basic`;;'				\
        'loadf `both1`;;'				\
        'loadf `all`;;'					\
        'compilet `exi`;;'				\
        'quit();;' | ${HOL}

both2_ml.o: both2.ml syn_ml.o basic_ml.o both1_ml.o all_ml.o exi_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `syn`;;'					\
        'loadf `basic`;;'				\
        'loadf `both1`;;'				\
        'loadf `all`;;'					\
        'loadf `exi`;;'					\
        'compilet `both2`;;'				\
        'quit();;' | ${HOL}

conv_ml.o: conv.ml syn_ml.o basic_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `syn`;;'					\
        'loadf `basic`;;'				\
        'compilet `conv`;;'				\
        'quit();;' | ${HOL}

pair_ml.o: pair.ml syn_ml.o basic_ml.o both1_ml.o all_ml.o exi_ml.o	\
		both2_ml.o conv_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'compilet `pair`;;'				\
        'quit();;' | ${HOL}
