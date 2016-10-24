# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: unwind
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
	rm -f *_ml.o *_ml.l
	@echo "===> library unwind: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l
	@echo "===> library unwind: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

unwinding_ml.o: unwinding.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `unwinding`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: unwinding_ml.o
	@echo "===> library unwind rebuilt"
