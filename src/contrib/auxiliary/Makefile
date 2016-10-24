# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: AUXILIARY
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
	@echo "===> library auxiliary: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library auxiliary: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

functions_ml.o: functions.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `functions`;;'\
	     'quit();;' | ${Hol}

tactics_ml.o: tactics.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
             'compilet `tactics`;;'\
             'quit();;' | ${Hol}

rules_ml.o: rules.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
             'compilet `rules`;;'\
	     'quit();;' | ${Hol}

auxiliary.th: functions.ml tactics.ml rules.ml theorems.ml
	rm -f auxiliary.th
	echo 'set_flag(`abort_when_fail`,true);;'\
             'loadt `theorems`;;'\
	     'quit();;' | ${Hol}

conversions_ml.o: functions_ml.o auxiliary.th conversions.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `auxiliary`;;'\
	     'loadf `functions`;;'\
	     'autoload_defs_and_thms `auxiliary`;;'\
 	     'compilet `conversions`;;'\
	     'quit();;' | ${Hol}  

# =====================================================================
# Main entry
# =====================================================================
                                 
all:    functions_ml.o tactics_ml.o rules_ml.o auxiliary.th conversions_ml.o
	@echo "===> library auxiliary rebuilt"
