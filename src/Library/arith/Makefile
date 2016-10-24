# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: arith
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
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.l *_ml.o
	@echo "===> library arith: all object code deleted"

clobber:
	rm -f *_ml.l *_ml.o
	@echo "===> library arith: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

int_extra_ml.o: int_extra.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `int_extra`;;'\
	     'quit();;' | ${Hol}

string_extra_ml.o: string_extra.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `string_extra`;;'\
	     'quit();;' | ${Hol}

arith_cons_ml.o: int_extra_ml.o arith_cons.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'compilet `arith_cons`;;'\
	     'quit();;' | ${Hol}

term_coeffs_ml.o: arith_cons_ml.o string_extra_ml.o term_coeffs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'compilet `term_coeffs`;;'\
	     'quit();;' | ${Hol}

qconv_ml.o: qconv.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `qconv`;;'\
	     'quit();;' | ${Hol}

decls_ml.o: decls.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `decls`;;'\
	     'quit();;' | ${Hol}

norm_bool_ml.o: term_coeffs_ml.o qconv_ml.o decls_ml.o norm_bool.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'compilet `norm_bool`;;'\
	     'quit();;' | ${Hol}

norm_arith_ml.o: norm_bool_ml.o norm_arith.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'loadf `norm_bool`;;'\
	     'compilet `norm_arith`;;'\
	     'quit();;' | ${Hol}

norm_ineqs_ml.o: norm_arith_ml.o norm_ineqs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'loadf `norm_bool`;;'\
	     'loadf `norm_arith`;;'\
	     'compilet `norm_ineqs`;;'\
	     'quit();;' | ${Hol}

solve_ineqs_ml.o: norm_ineqs_ml.o solve_ineqs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'loadf `norm_bool`;;'\
	     'loadf `norm_arith`;;'\
	     'loadf `norm_ineqs`;;'\
	     'compilet `solve_ineqs`;;'\
	     'quit();;' | ${Hol}

solve_ml.o: solve_ineqs_ml.o solve.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'loadf `norm_bool`;;'\
	     'loadf `norm_arith`;;'\
	     'loadf `norm_ineqs`;;'\
	     'loadf `solve_ineqs`;;'\
	     'compilet `solve`;;'\
	     'quit();;' | ${Hol}

rationals_ml.o: int_extra_ml.o rationals.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'compilet `rationals`;;'\
	     'quit();;' | ${Hol}

sup-inf_ml.o: rationals_ml.o string_extra_ml.o sup-inf.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `rationals`;;'\
	     'loadf `string_extra`;;'\
	     'compilet `sup-inf`;;'\
	     'quit();;' | ${Hol}

streams_ml.o: streams.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `streams`;;'\
	     'quit();;' | ${Hol}

sol_ranges_ml.o: sup-inf_ml.o streams_ml.o sol_ranges.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `int_extra`;;'\
	     'loadf `rationals`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `sup-inf`;;'\
	     'loadf `streams`;;'\
	     'compilet `sol_ranges`;;'\
	     'quit();;' | ${Hol}

exists_arith_ml.o: sol_ranges_ml.o norm_ineqs_ml.o exists_arith.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `reduce`;;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'loadf `norm_bool`;;'\
	     'loadf `norm_arith`;;'\
	     'loadf `norm_ineqs`;;'\
	     'loadf `rationals`;;'\
	     'loadf `sup-inf`;;'\
	     'loadf `streams`;;'\
	     'loadf `sol_ranges`;;'\
	     'compilet `exists_arith`;;'\
	     'quit();;' | ${Hol}

sub_and_cond_ml.o: decls_ml.o sub_and_cond.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `decls`;;'\
	     'compilet `sub_and_cond`;;'\
	     'quit();;' | ${Hol}

prenex_ml.o: decls_ml.o prenex.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `decls`;;'\
	     'compilet `prenex`;;'\
	     'quit();;' | ${Hol}

instance_ml.o: instance.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `instance`;;'\
	     'quit();;' | ${Hol}

gen_arith_ml.o: solve_ml.o exists_arith_ml.o\
                sub_and_cond_ml.o prenex_ml.o instance_ml.o\
                gen_arith.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `reduce`;;'\
	     'loadf `int_extra`;;'\
	     'loadf `arith_cons`;;'\
	     'loadf `string_extra`;;'\
	     'loadf `term_coeffs`;;'\
	     'loadf `qconv`;;'\
	     'loadf `decls`;;'\
	     'loadf `norm_bool`;;'\
	     'loadf `norm_arith`;;'\
	     'loadf `norm_ineqs`;;'\
	     'loadf `solve_ineqs`;;'\
	     'loadf `solve`;;'\
	     'loadf `rationals`;;'\
	     'loadf `sup-inf`;;'\
	     'loadf `streams`;;'\
	     'loadf `sol_ranges`;;'\
	     'loadf `exists_arith`;;'\
	     'loadf `sub_and_cond`;;'\
	     'loadf `prenex`;;'\
	     'loadf `instance`;;'\
	     'compilet `gen_arith`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: gen_arith_ml.o
	@echo "===> library arith rebuilt"
