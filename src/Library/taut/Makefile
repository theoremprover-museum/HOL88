# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: taut
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
	rm -f taut_check_ml.o taut_check_ml.l
	@echo "===> library taut: all object code deleted"

clobber:
	rm -f taut_check_ml.o taut_check_ml.l
	@echo "===> library taut: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

taut_check_ml.o: taut_check.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `taut_check`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: taut_check_ml.o
	@echo "===> library taut rebuilt"
