#=================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: more_arithmetic
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : create theories
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
	rm -f *_ml.o
	@echo "===> library more_arithmetic: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library more_arithmetic: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

more_arithmetic.th: mk_more_arithmetic.ml pre.th sub.th  mult.th odd_even.th min_max.th div_mod.th
	rm -f more_arithmetic.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_more_arithmetic`;;'\
	     'quit();;' | ${Hol} 

ineq.th: ineq.ml
	rm -f ineq.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `ineq`;;'\
	     'quit();;' | ${Hol} 


zero_ineq.th: zero.ml ineq.th
	rm -f zero_ineq.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `zero`;;'\
	     'quit();;' | ${Hol} 

suc.th: suc.ml ineq.th
	rm -f suc.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `suc`;;'\
	     'quit();;' | ${Hol} 


add.th: add.ml suc.th
	rm -f add.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `add`;;'\
	     'quit();;' | ${Hol} 


pre.th: pre.ml ineq.th
	rm -f pre.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `pre`;;'\
	     'quit();;' | ${Hol} 


sub.th: sub.ml add.th zero_ineq.th
	rm -f sub.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `sub`;;'\
	     'quit();;' | ${Hol} 


mult.th: mult.ml ineq.th
	rm -f mult.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mult`;;'\
	     'quit();;' | ${Hol} 

min_max.th: minmax.ml 
	rm -f min_max.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `minmax`;;'\
	     'quit();;' | ${Hol} 

odd_even.th: odd_even.ml 
	rm -f odd_even.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `odd_even`;;'\
	     'quit();;' | ${Hol} 

div_mod.th: div_mod.ml 
	rm -f div_mod.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `div_mod`;;'\
	     'quit();;' | ${Hol} 

num_convs_ml.o: num_convs.ml more_arithmetic.th more_arithmetic.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `num_convs`;;'\
	     'quit();;' | ${Hol}


num_tac_ml.o: num_tac.ml more_arithmetic.th more_arithmetic.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `num_tac`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: more_arithmetic.th num_convs_ml.o num_tac_ml.o
	@echo "===> library more_arithmetic rebuilt"
