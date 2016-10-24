# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: bags
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
	@echo "===> library bags: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library bags: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

more_arithmetic.th: mk_more_arithmetic.ml 
	rm -f more_arithmetic.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_more_arithmetic`;;' | ${Hol} 

bags.th: more_arithmetic.th mk_bags.ml 
	rm -f bags.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_bags`;;' | ${Hol} 

# =====================================================================
# Main entry
# =====================================================================

all: more_arithmetic.th bags.th
	@echo "===> library bags rebuilt"
