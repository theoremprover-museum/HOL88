# =====================================================================
#
# 		 MAKEFILE FOR EXECUTION SEQUENCE SEMANTICS
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : create theories and compile code
#
#    make clean	    : remove only compiled code
#	
#    make clobber   : remove both theories and compiled code
# ---------------------------------------------------------------------
#
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o
	@echo "===> execution sequences: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th  
	@echo "===> execution sequences: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

temporal.th: temporal.ml inv.th 
	rm -f temporal.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `temporal.ml`;;\
		quit();;' | ${Hol}

inv.th: inv.ml hoare.th 
	rm -f inv.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `inv.ml`;;\
		quit();;' | ${Hol}

hoare.th: hoare.ml wp.th 
	rm -f hoare.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `hoare.ml`;;\
		quit();;' | ${Hol}

wp.th: wp.ml sem.th 
	rm -f wp.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `wp.ml`;;\
		quit();;' | ${Hol}

sem.th: sem.ml pred.th 
	rm -f sem.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `sem.ml`;;\
		quit();;' | ${Hol}

pred.th: exseq.th lnum.th
	rm -f pred.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `pred.ml`;;\
		quit();;' | ${Hol}

exseq.th: exseq.ml lnum.th
	rm -f exseq.th
	echo	'set_flag(`abort_when_fail`,true);;\
		loadt `exseq.ml`;;\
		quit();;' | ${Hol}

lnum.th: lnum.ml cpo.th
	rm -f lnum.th
	echo    'set_flag(`abort_when_fail`,true);;\
		loadt `lnum.ml`;;\
		quit();;' | ${Hol}

cpo.th: cpo.ml arith_hack.th
	rm -f cpo.th
	echo    'set_flag(`abort_when_fail`,true);;\
		loadt `cpo.ml`;;\
		quit();;' | ${Hol}

arith_hack.th: arith_hack.ml mytactics_ml.o
	rm -f arith_hack.th
	echo    'set_flag(`abort_when_fail`,true);;\
		loadt `arith_hack.ml`;;\
		quit();;' | ${Hol}

mytactics_ml.o: mytactics.ml
	echo    'set_flag(`abort_when_fail`,true);;\
		compilet `mytactics`;;\
		quit();;' | ${Hol}
  
# =====================================================================
# Main entries
# ===================================================================== 

all: mytactics_ml.o arith_hack.th cpo.th lnum.th exseq.th pred.th sem.th wp.th hoare.th inv.th
	@echo "===> execution sequence semantics rebuilt"

