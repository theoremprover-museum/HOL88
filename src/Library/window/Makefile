# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: window
#
# $Id: Makefile,v 3.1 1993/12/07 14:15:19 jg Exp $
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : create theories and compile code
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

HOL=../../hol

SOURCE=basic_close.ml imp_close.ml mk_win_th.ml thms.ml eq_close.ml	\
	inter.ml ml_ext.ml win.ml load_code.ml tables.ml window.ml	\
	hol_ext.ml load_window.ml tactic.ml xlabel.ml

REVISION=

# =====================================================================
# Basic functions.
# =====================================================================

all: window_ml.o xlabel_ml.o tactic_ml.o
	@echo "===> library window built"

source: ${SOURCE}

clean:
	rm -f *.l *.c *.o *.h *.data
	@echo "===> library window: all object code deleted"

clobber:
	rm -f *.l *.c *.o *.th *.h *.data
	@echo "===> library window: all object code and theory files deleted"

#decimate:
#	rm -f *.l *.c *.o *.th *.h *.data
#	rcsclean -r${REVISION} ${SOURCE}
#	@echo "===> library window: all source object code and theories deleted"
#
#destroy:
#	rm -f *.l *.c *.o *.th *.h *.data *.i *.s *.ir
#	rm -f ${SOURCE}
#	@echo "===> library pair: all source, object code and theories deleted"

.FAILED:
	@echo "===> library window build failed"

.DEFAULT:
	co -r${REVISION} $@

# =====================================================================
# Entries for individual files.
# =====================================================================


win.th: mk_win_th.ml
	rm -f win.th
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'loadt `mk_win_th`;;'				\
	'quit ();;' | ${HOL}

thms_ml.o: thms.ml win.th
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'load_theory `win`;;'				\
        'compilet `thms`;;'				\
        'quit();;' | ${HOL}

ml_ext_ml.o: ml_ext.ml
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'compilet `ml_ext`;;'				\
        'quit();;' | ${HOL}

hol_ext_ml.o: hol_ext.ml win.th thms_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'compilet `hol_ext`;;'				\
        'quit();;' | ${HOL}

tables_ml.o: tables.ml win.th thms_ml.o hol_ext_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'compilet `tables`;;'				\
        'quit();;' | ${HOL}

win_ml.o: win.ml ml_ext_ml.o win.th thms_ml.o hol_ext_ml.o tables_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `ml_ext`;;'				\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'compilet `win`;;'				\
        'quit();;' | ${HOL}

basic_close_ml.o: basic_close.ml win.th thms_ml.o hol_ext_ml.o tables_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'compilet `basic_close`;;'			\
        'quit();;' | ${HOL}

eq_close_ml.o: eq_close.ml win.th thms_ml.o hol_ext_ml.o tables_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'compilet `eq_close`;;'				\
        'quit();;' | ${HOL}

imp_close_ml.o: imp_close.ml win.th thms_ml.o hol_ext_ml.o tables_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'compilet `imp_close`;;'			\
        'quit();;' | ${HOL}

inter_ml.o: inter.ml ml_ext_ml.o win.th thms_ml.o	\
		hol_ext_ml.o tables_ml.o win_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `ml_ext`;;'				\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'loadf `win`;;'					\
        'compilet `inter`;;'				\
        'quit();;' | ${HOL}

load_code_ml.o: load_code.ml ml_ext_ml.o win.th thms_ml.o hol_ext_ml.o	\
			tables_ml.o basic_close_ml.o eq_close_ml.o	\
			imp_close_ml.o win_ml.o inter_ml.o 
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'load_theory `win`;;'				\
        'compilet `load_code`;;'			\
        'quit();;' | ${HOL}

load_window_ml.o: load_window.ml load_code_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'compilet `load_window`;;'			\
        'quit();;' | ${HOL}

window_ml.o: window.ml win.th load_code_ml.o load_window_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'compilet `window`;;'				\
        'quit();;' | ${HOL}

xlabel_ml.o: xlabel.ml ml_ext_ml.o win.th thms_ml.o	\
		hol_ext_ml.o tables_ml.o win_ml.o inter_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `ml_ext`;;'				\
	'load_theory `win`;;'				\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'loadf `win`;;'					\
        'loadf `inter`;;'				\
        'compilet `xlabel`;;'				\
        'quit();;' | ${HOL}

tactic_ml.o: tactic.ml ml_ext_ml.o win.th thms_ml.o	\
		hol_ext_ml.o tables_ml.o win_ml.o inter_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'	\
        'loadf `ml_ext`;;'				\
		'load_theory `win`;;'			\
        'loadf `thms`;;'				\
        'loadf `hol_ext`;;'				\
        'loadf `tables`;;'				\
        'loadf `win`;;'					\
        'loadf `inter`;;'				\
        'compilet `tactic`;;'				\
        'quit();;' | ${HOL}
