# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: ZET
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
	@echo "===> library zet: all object code and theory files deleted"
                      
zet.th: mk_zet.ml
	rm -f zet.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_zet`;;'\
             'quit();;' | ${Hol}

zet_tactics_ml.o: zet.th zet_tactics.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `zet`;;'\
	     'load_from_lib false `auxiliary` `functions`;;'\
	     'autoload_defs_and_thms `zet`;;'\
	     'compilet `zet_tactics`;;'\
	     'quit();;' | ${Hol}

zet_ind_ml.o: zet.th zet_ind.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `zet`;;'\
	     'load_from_lib false `auxiliary` `functions`;;'\
	     'autoload_defs_and_thms `zet`;;'\
	     'compilet `zet_ind`;;'\
	     'quit();;' | ${Hol}

all:    zet.th zet_tactics_ml.o zet_ind_ml.o 
	@echo "===> library zet rebuilt"
