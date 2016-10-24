# =====================================================================
#
# 		           Makefile for icl-taut
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
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f taut_rules_ml.o taut_rules_ml.l
	@echo "===> icl-taut: all object code deleted"

clobber:
	rm -f taut_rules_ml.o taut_rules_ml.l
	@echo "===> icl-taut: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

taut_rules_ml.o: taut_rules.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `taut_rules`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: taut_rules_ml.o
	@echo "===> icl-taut rebuilt"
