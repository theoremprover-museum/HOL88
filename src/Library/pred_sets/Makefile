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
	rm -f *_ml.o
	@echo "===> library pred_sets: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library pred_sets: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

pred_sets.th: mk_pred_sets.ml 
	rm -f pred_sets.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_pred_sets`;;' | ${Hol} 

gspec_ml.o: pred_sets.th gspec.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `pred_sets`;;'\
	     'compilet `gspec`;;'\
	     'quit();;' | ${Hol}

set_ind_ml.o: pred_sets.th set_ind.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `pred_sets`;;'\
	     'compilet `set_ind`;;'\
	     'quit();;' | ${Hol}

fset_conv_ml.o: pred_sets.th fset_conv.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `pred_sets`;;'\
	     'compilet `fset_conv`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: pred_sets.th set_ind_ml.o gspec_ml.o fset_conv_ml.o 
	@echo "===> library pred_sets rebuilt"
