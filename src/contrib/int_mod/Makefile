# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: int_mod
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
	rm -f *_ml.o 
	@echo "===> library: int_mod. All object code deleted"

clobber:
	rm -f *_ml.o *.th 
	@echo "===> library: int_mod. All object code and theory files deleted"

int_sbgp.th: mk_int_sbgp.ml
	rm -f int_sbgp.th
	echo  'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_int_sbgp`;;'\
	     'quit();;' | ${Hol}

int_mod.th: mk_int_mod.ml int_sbgp.th
	rm -f int_mod.th
	echo  'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_int_mod`;;'\
	     'quit();;' | ${Hol}

int_mod_ml.o: int_mod.ml int_sbgp.th int_mod.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `int_mod`;;'\
	     'quit();;' | ${Hol}

inst_int_mod_ml.o: inst_int_mod.ml int_mod.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `integer`;;'\
	     'load_theory `int_mod`;;'\
	     'compilet `inst_int_mod`;;'\
	     'quit();;' | ${Hol}

all: int_sbgp.th int_mod.th int_mod_ml.o inst_int_mod_ml.o
	@echo "===> library: int_mod rebuilt"
