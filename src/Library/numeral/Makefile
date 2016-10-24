# =====================================================================
#
#                MAKEFILE FOR THE HOL LIBRARY: numeral
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all       : create theories and compile code
#
#    make clean     : remove only compiled code
#
#    make clobber   : remove both theories and compiled code
# ---------------------------------------------------------------------
#
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

all: numeral_rules_ml.o

clean:; rm -f numeral_rules_ml.o

clobber: clean; rm -f numeral.th

numeral.th: numeral_theory.ml
	echo 'set_flag(`abort_when_fail`,true);;'	\
	     'loadt `numeral_theory`;;'			\
	     'quit();;' | ${Hol}

numeral_rules_ml.o: numeral_rules.ml numeral.th
	rm -f dummy.th
	echo 'set_flag(`abort_when_fail`,true);;'				\
	     'new_theory `dummy`;;'						\
	     'load_library `reduce`;;'						\
	     'new_parent `numeral`;;'						\
	     'let t = `numeral` in do'						\
	     'map (\s. autoload_theory(`definition`,t,fst s)) (definitions t);' \
	     'map (\s. autoload_theory(`theorem`,t,fst s)) (theorems t);;'	\
	     'compilet `numeral_rules`;;'					\
	     'quit();;' | ${Hol}
	rm -f dummy.th

