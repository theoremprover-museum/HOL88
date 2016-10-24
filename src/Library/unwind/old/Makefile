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

mjcg-unwind_ml.o: mjcg-unwind.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `mjcg-unwind`;;'\
	     'quit();;' | ${Hol}

des-unwind_ml.o: des-unwind.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `des-unwind`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: mjcg-unwind_ml.o des-unwind_ml.o
	@echo "===> library unwind rebuilt"
