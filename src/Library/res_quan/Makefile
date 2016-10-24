# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: res_quan
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
	@echo "===> library res_quan: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library res_quan: all object code and theory files deleted"

# =====================================================================
# Macros
# =====================================================================
THY=res_quan.th
THY_SRC= mk_res_quan.ml
OBJ_SRC= res_quan.ml res_rules.ml cond_rewr.ml

OBJ= res_rules_ml.o cond_rewr_ml.o

# =====================================================================
# Entries for individual files.
# =====================================================================

res_quan.th: mk_res_quan.ml 
	rm -f res_quan.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_res_quan`;;'\
             'quit();;' | ${Hol} 

cond_rewr_ml.o:	cond_rewr.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `cond_rewr`;;'\
             'quit();;' | ${Hol} 

res_rules_ml.o: res_quan.th res_rules.ml cond_rewr_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `res_quan`;;'\
	     'loadf `cond_rewr`;;'\
	     'compilet `res_rules`;;'\
             'quit();;' | ${Hol} 

all: res_quan.th $(OBJ)
	@echo "===> library res_quan rebuilt"


