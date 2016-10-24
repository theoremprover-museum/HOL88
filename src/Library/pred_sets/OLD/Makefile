# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: pred_sets
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
#
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
	rm -f *_ml.o *_ml.l
	@echo "===> library pred_sets: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library pred_sets: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

pred_sets.th: mk_pred_set_defs.ml mk_pred_sets.ml
	rm -f pred_sets.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_pred_set_defs`;;'\
	     'loadt `mk_pred_sets`;;'\
	     'quit();;' | ${Hol}

all: pred_sets.th
	@echo "===> library pred_sets rebuilt"
