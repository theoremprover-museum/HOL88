# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: integer
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

Hol=../../hol

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o *_ml.l
	@echo "===> library integer: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library integer: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

more_arith.th: mk_more_arith.ml num_tac.ml
	rm -f more_arith.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_more_arith`;;'\
	     'quit();;' | ${Hol}

num_tac_ml.o: num_tac.ml more_arith.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `more_arith`;;'\
	     'compilet `num_tac`;;'\
	     'quit();;' | ${Hol}

load_more_arith_ml.o: load_more_arith.ml more_arith.th num_tac_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `more_arith`;;'\
	     'compilet `load_more_arith`;;'\
	     'quit();;' | ${Hol}	

integer.th: mk_integer.ml more_arith.th num_tac_ml.o
	rm -f integer.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_integer`;;'\
	     'quit();;' | ${Hol}

integer_tac_ml.o: integer_tac.ml integer.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'let path = library_pathname() ^ `/group/`'\
	     'in set_search_path(search_path() @ [path]);;'\
	     'load_theory `integer`;;'\
	     'compilet `integer_tac`;;'\
	     'quit();;' | ${Hol}

integer_ml.o: integer.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `integer`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: integer.th integer_tac_ml.o integer_ml.o
	@echo "===> library integer rebuilt"
