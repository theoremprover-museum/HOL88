# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: fixpoints
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
	@echo "===> library fixpoints: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library fixpoints: all object code and theory files deleted"


# =====================================================================
# Entries for individual files.
# =====================================================================

fixpoints.th: mk_fixpoints.ml
	      rm -f fixpoints.th
	      echo 'set_flag(`abort_when_fail`,true);;'\
	      'loadt `mk_fixpoints`;;' | ${Hol} 

fixpoints_ml.o: fixpoints.ml fixpoints.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `fixpoints`;;'\
	     'compilet `fixpoints`;;'\
	     'quit();;' | ${Hol}


# =====================================================================
# Main entry
# =====================================================================

all:    fixpoints.th fixpoints_ml.o\
        fixpoints_ml.o
	@echo "===> library fixpoints rebuilt"
