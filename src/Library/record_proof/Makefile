# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: record_proof
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
#Hol=/usr/groups/hol/HOL22/hol


# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o
	@echo "===> library record_proof: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library record_proof: all object code and theory files deleted"

# =====================================================================
# Macros
# =====================================================================

OBJ_SRC= proof_rec.ml dummy_funs.ml
OBJ= proof_rec_ml.o dummy_funs_ml.o

THMDIR=./help/thms/
MAKEDOC=../create-doc-files2

# =====================================================================
# Entries for individual files.
# =====================================================================


proof_rec_ml.o:  proof_rec.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `proof_rec`;;'\
             'quit();;' | ${Hol} 

dummy_funs_ml.o:  dummy_funs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `dummy_funs`;;'\
             'quit();;' | ${Hol} 

all:	$(OBJ)
	@echo "===> library record_proof rebuilt"
