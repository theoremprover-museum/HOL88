# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: WELL-ORDER
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
	@echo "===> library well_order: all object code and theory files deleted"
                      
well_order.th: mk_well_order.ml
	     rm -f well_order.th
	     echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_well_order`;;'\
             'quit();;' | ${Hol}

transfinite.th: well_order.th mk_transfinite.ml
	     rm -f transfinite.th
	     echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_transfinite`;;'\
             'quit();;' | ${Hol}

wo_fns_ml.o: transfinite.th wo_fns.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	      'load_library `auxiliary`;;'\
	      'load_theory `transfinite`;;'\
	      'autoload_defs_and_thms `transfinite`;;'\
              'compilet `wo_fns`;;'\
              'quit();;' | ${Hol}


all:    well_order.th transfinite.th wo_fns_ml.o
	@echo "===> library well_order rebuilt"
