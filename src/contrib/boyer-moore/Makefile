# =====================================================================
#
#                MAKEFILE FOR BOYER-MOORE-STYLE PROVER
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : compile code
#
# make clean	    : remove compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

clean:
	rm -f *_ml.l *_ml.o
	@echo "===> Boyer-Moore-style prover: all object code deleted"

support_ml.o: support.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `support`;;'\
	     'quit();;' | ${Hol} 

struct_equal_ml.o: struct_equal.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `struct_equal`;;'\
	     'quit();;' | ${Hol} 

shells_ml.o: support_ml.o struct_equal_ml.o shells.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'compilet `shells`;;'\
	     'quit();;' | ${Hol} 

environment_ml.o: shells_ml.o environment.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'compilet `environment`;;'\
	     'quit();;' | ${Hol} 

clausal_form_ml.o: environment_ml.o clausal_form.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'compilet `clausal_form`;;'\
	     'quit();;' | ${Hol} 

waterfall_ml.o: clausal_form_ml.o waterfall.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'compilet `waterfall`;;'\
	     'quit();;' | ${Hol} 

rewrite_rules_ml.o: waterfall_ml.o rewrite_rules.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'compilet `rewrite_rules`;;'\
	     'quit();;' | ${Hol} 

definitions_ml.o: rewrite_rules_ml.o definitions.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'compilet `definitions`;;'\
	     'quit();;' | ${Hol} 

terms_and_clauses_ml.o: definitions_ml.o terms_and_clauses.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'loadf `definitions`;;'\
	     'compilet `terms_and_clauses`;;'\
	     'quit();;' | ${Hol} 

equalities_ml.o: terms_and_clauses_ml.o equalities.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'loadf `definitions`;;'\
	     'loadf `terms_and_clauses`;;'\
	     'compilet `equalities`;;'\
	     'quit();;' | ${Hol} 

generalize_ml.o: equalities_ml.o generalize.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'loadf `definitions`;;'\
	     'loadf `terms_and_clauses`;;'\
	     'loadf `equalities`;;'\
	     'compilet `generalize`;;'\
	     'quit();;' | ${Hol} 

irrelevance_ml.o: generalize_ml.o irrelevance.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'loadf `definitions`;;'\
	     'loadf `terms_and_clauses`;;'\
	     'loadf `equalities`;;'\
	     'loadf `generalize`;;'\
	     'compilet `irrelevance`;;'\
	     'quit();;' | ${Hol} 

induction_ml.o: irrelevance_ml.o induction.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'loadf `definitions`;;'\
	     'loadf `terms_and_clauses`;;'\
	     'loadf `equalities`;;'\
	     'loadf `generalize`;;'\
	     'loadf `irrelevance`;;'\
	     'compilet `induction`;;'\
	     'quit();;' | ${Hol} 

main_ml.o: induction_ml.o main.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `support`;;'\
	     'loadf `struct_equal`;;'\
	     'loadf `shells`;;'\
	     'loadf `environment`;;'\
	     'loadf `clausal_form`;;'\
	     'loadf `waterfall`;;'\
	     'loadf `rewrite_rules`;;'\
	     'loadf `definitions`;;'\
	     'loadf `terms_and_clauses`;;'\
	     'loadf `equalities`;;'\
	     'loadf `generalize`;;'\
	     'loadf `irrelevance`;;'\
	     'loadf `induction`;;'\
	     'compilet `main`;;'\
	     'quit();;' | ${Hol} 

all: main_ml.o
	@echo "===> Boyer-Moore-style prover rebuilt"
