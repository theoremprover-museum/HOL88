# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: UNITY
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
#    make all	    : create theories and compile code
#
#    make clean	    : remove only compiled code
#	
#    make clobber   : remove both theories and compiled code
#
# For the moment no compilation files have been made
#	
# ---------------------------------------------------------------------
#
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

dummy:
	@echo "*** UNITY library: make parameter missing ***"

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o
	@echo "===> library UNITY: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library UNITY: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

state_logic.th: mk_state_logic.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `aux_definitions`;;'\
	     'loadt `mk_state_logic`;;'\
             'quit();;' | ${Hol}

unless.th: state_logic.th mk_unless.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `aux_definitions`;;'\
             'autoload_defs_and_thms `state_logic`;;'\
	     'loadt `mk_unless`;;'\
             'quit();;' | ${Hol}

ensures.th: unless.th mk_ensures.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `aux_definitions`;;'\
             'autoload_defs_and_thms `state_logic`;;'\
             'autoload_defs_and_thms `unless`;;'\
	     'loadt `mk_ensures`;;'\
             'quit();;' | ${Hol}

gen_induct.th: ensures.th mk_gen_induct.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `aux_definitions`;;'\
             'autoload_defs_and_thms `state_logic`;;'\
             'autoload_defs_and_thms `unless`;;'\
             'autoload_defs_and_thms `ensures`;;'\
	     'loadt `mk_gen_induct`;;'\
             'quit();;' | ${Hol}

leadsto.th: gen_induct.th mk_leadsto.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `aux_definitions`;;'\
             'autoload_defs_and_thms `state_logic`;;'\
             'autoload_defs_and_thms `unless`;;'\
             'autoload_defs_and_thms `ensures`;;'\
             'autoload_defs_and_thms `gen_induct`;;'\
	     'loadt `mk_leadsto`;;'\
             'quit();;' | ${Hol}

comp_unity.th: leadsto.th mk_comp_unity.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `aux_definitions`;;'\
             'autoload_defs_and_thms `state_logic`;;'\
             'autoload_defs_and_thms `unless`;;'\
             'autoload_defs_and_thms `ensures`;;'\
             'autoload_defs_and_thms `gen_induct`;;'\
             'autoload_defs_and_thms `leadsto`;;'\
	     'loadt `mk_comp_unity`;;'\
             'quit();;' | ${Hol}

all:    state_logic.th unless.th ensures.th gen_induct.th leadsto.th\
        comp_unity.th
	@echo "===> library UNITY rebuilt"
