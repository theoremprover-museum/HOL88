# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: CARD
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : create theories and compile code
#
# make clean	    : remove theories and compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library card: all object code and theory files deleted"
                      
card.th: mk_card.ml
	     rm -f card.th
	     echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_card`;;'\
             'quit();;' | ${Hol}

all:    card.th 
	@echo "===> library card rebuilt"
