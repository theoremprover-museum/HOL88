# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: ind_defs
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : compile code
#
#    make clean	    : remove compiled code
#	
#    make clobber   : remove compiled code
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
	@echo "===> library ind_defs: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l 
	@echo "===> library ind_defs: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

ind-defs_ml.o: ind-defs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `ind-defs`;;'\
	     'quit();;' | ${Hol}

ind_defs_ml.o: ind-defs_ml.o ind_defs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `ind_defs`;;'\
	     'quit();;' | ${Hol}


# =====================================================================
# Main entry
# =====================================================================

all: ind_defs_ml.o
	@echo "===> library ind_defs rebuilt"

