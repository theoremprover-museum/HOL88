# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: finite_sets
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
	@echo "===> library finite_sets: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library finite_sets: object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

finite_sets.th: mk_finite_sets.ml 
	rm -f finite_sets.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_finite_sets`;;' | ${Hol} 

set_ind_ml.o: finite_sets.th set_ind.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `finite_sets`;;'\
	     'compilet `set_ind`;;'\
	     'quit();;' | ${Hol}

fset_conv_ml.o: finite_sets.th fset_conv.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `finite_sets`;;'\
	     'compilet `fset_conv`;;'\
	     'quit();;' | ${Hol}


# =====================================================================
# Main entry
# =====================================================================

all: finite_sets.th set_ind_ml.o fset_conv_ml.o 
	@echo "===> library finite_sets rebuilt"
