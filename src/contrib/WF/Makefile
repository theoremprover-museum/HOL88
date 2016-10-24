# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: WF
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
	@echo "===> library WF: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library WF: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

WF.th: mk_WF.ml 
	rm -f sets.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_WF`;;' | ${Hol} 

predicate.th: predicate.ml 
	rm -f predicate.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `predicate`;;' | ${Hol} 

# =====================================================================
# Main entry
# =====================================================================

all: predicate.th WF.th 
	@echo "===> library WF rebuilt"
