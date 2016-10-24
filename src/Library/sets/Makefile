# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: sets
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
	@echo "===> library sets: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library sets: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

sets.th: mk_sets.ml 
	rm -f sets.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_sets`;;' | ${Hol} 

gspec_ml.o: sets.th gspec.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `sets`;;'\
	     'compilet `gspec`;;'\
	     'quit();;' | ${Hol}

set_ind_ml.o: sets.th set_ind.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `sets`;;'\
	     'compilet `set_ind`;;'\
	     'quit();;' | ${Hol}

fset_conv_ml.o: sets.th fset_conv.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `sets`;;'\
	     'compilet `fset_conv`;;'\
	     'quit();;' | ${Hol}


# =====================================================================
# Main entry
# =====================================================================

all: sets.th set_ind_ml.o gspec_ml.o fset_conv_ml.o 
	@echo "===> library sets rebuilt"
