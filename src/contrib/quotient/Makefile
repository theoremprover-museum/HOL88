# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: quotient
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
	rm -f *_ml.o *_ml.l 
	@echo "===> library quotient: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th
	@echo "===> library quotient: all object code and theory files deleted"
          
quotient.th: mk_quotient.ml 
	      rm -f quotient.th
	      echo 'set_flag(`abort_when_fail`,true);;'\
	      'loadt `mk_quotient`;;'\
	      'quit();;' | ${Hol}

quotientfns_ml.o: quotientfns.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `auxiliary`;;'\
             'autoload_defs_and_thms `bool`;;'\
	     'load_theory `quotient`;;'\
             'autoload_defs_and_thms `quotient`;;'\
	     'compilet `quotientfns`;;'\
	     'quit();;' | ${Hol}


all:   	quotient.th quotientfns_ml.o
	@echo "===> library quotient rebuilt"
