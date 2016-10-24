
Hol=/usr/groups/hol/HOL22/hol


theory:	
	make clean
	make LIB=record_proof:disable all

proof:	
	make clobber
	make LIB=record_proof all

all:	MULT_VER.th
	@echo 'Multiplier verified in HOL22'

MULT_VER.th:	MULT_FUN.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`$(LIB)`;;'\
	     'loadt `HOL_MULT`;;'\
             'quit();;' | ${Hol} 

MULT_FUN.th:	MULT_FUN_CURRY.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`$(LIB)`;;'\
	     'loadt `MULT_FUN`;;'\
             'quit();;' | ${Hol} 

MULT_FUN_CURRY.th:	NEXT.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`$(LIB)`;;'\
	     'loadt `MULT_FUN_CURRY`;;'\
             'quit();;' | ${Hol} 

NEXT.th:	mk_NEXT.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`$(LIB)`;;'\
	     'loadt `mk_NEXT`;;'\
             'quit();;' | ${Hol} 

	
# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *.th
	@echo "===> library word: all theory files deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th *.prf*
	@echo "===> benchmark: all proof files and theory files deleted"
