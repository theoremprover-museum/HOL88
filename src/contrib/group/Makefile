# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: group
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
	@echo "===> library group: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library group: all object code and theory files deleted"


# =====================================================================
# Entries for individual files.
# =====================================================================

#Not needed for HOL88.1.05 (MJCG 14 April, 1989)
#add_lib_path_ml.o: add_lib_path.ml
#	echo 'set_flag(`abort_when_fail`,true);;'\
#	     'compilet `add_lib_path`;;'\
#	     'quit();;' | ${Hol}

start_groups_ml.o: start_groups.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `start_groups`;;'\
	     'quit();;' | ${Hol}

elt_gp.th: mk_elt_gp.ml group_tac.ml start_groups_ml.o
	rm -f elt_gp.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_elt_gp`;;'\
	     'quit();;' | ${Hol}

group_tac_ml.o: group_tac.ml start_groups_ml.o elt_gp.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `elt_gp`;;'\
	     'compilet `group_tac`;;'\
	     'quit();;' | ${Hol}

inst_gp_ml.o: inst_gp.ml start_groups_ml.o elt_gp.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `elt_gp`;;'\
	     'compilet `inst_gp`;;'\
	     'quit();;' | ${Hol}

load_elt_gp_ml.o: load_elt_gp.ml start_groups_ml.o elt_gp.th group_tac_ml.o \
     inst_gp_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `elt_gp`;;'\
	     'compilet `load_elt_gp`;;'\
	     'quit();;' | ${Hol}

more_gp.th: mk_more_gp.ml elt_gp.th group_tac_ml.o start_groups_ml.o
	rm -f more_gp.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_more_gp`;;'\
	     'quit();;' | ${Hol}

load_more_gp_ml.o: load_more_gp.ml start_groups_ml.o elt_gp.th group_tac_ml.o \
     inst_gp_ml.o more_gp.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `more_gp`;;'\
	     'compilet `load_more_gp`;;'\
	     'quit();;' | ${Hol}

group_ml.o: group.ml start_groups_ml.o elt_gp.th group_tac_ml.o inst_gp_ml.o \
     more_gp.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `more_gp`;;'\
	     'compilet `group`;;'\
	     'quit();;' | ${Hol}


# =====================================================================
# Main entry
# =====================================================================

all: start_groups_ml.o elt_gp.th group_tac_ml.o \
     inst_gp_ml.o load_elt_gp_ml.o more_gp.th load_more_gp_ml.o group_ml.o
	@echo "===> library group rebuilt"
