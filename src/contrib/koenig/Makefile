# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: koenig
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

Hol=hol

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o *_ml.l
	@echo "===> library koenig: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library koenig: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

koenig.th: mk_koenig.ml
	rm -f koenig.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_koenig`;;'\
	     'quit();;' | ${Hol}

all: koenig.th
	@echo "===> library koenig rebuilt"
