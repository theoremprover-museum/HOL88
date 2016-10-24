# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: word
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : create theories and compile code
#
#    make doc	    : create .doc files for all theorems
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

#Hol=../../hol
#Hol=/usr/groups/hol/HOL21/bin/hol
Hol=/usr/groups/hol/HOL22/hol


# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o
	@echo "===> library word: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library word: all object code and theory files deleted"

# =====================================================================
# Macros
# =====================================================================
THY= word_base.th word_bitop.th word_num.th\
   bword_bitop.th bword_num.th bword_arith.th
THY_NAMES= word_base word_bitop word_num\
   bword_bitop bword_num bword_arith
THY_SRC= mk_word_base.ml mk_word_bitop.ml mk_word_num.ml\
    mk_bword_bitop.ml mk_bword_num.ml mk_bword_arith.ml
# mk_word_ints.ml  more_integers.ml
OBJ_SRC= word_funs.ml word_convs.ml
OBJ= word_convs_ml.o

THMDIR=./help/thms/
MAKEDOC=../create-doc-files2

# =====================================================================
# Entries for individual files.
# =====================================================================

word.th: mk_word.ml $(THY)
	rm -f word.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_word`;;'\
             'quit();;' | ${Hol} 

word_base.th: mk_word_base.ml word_funs.ml
	rm -f word_base.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_word_base`;;'\
             'quit();;' | ${Hol} 

word_bitop.th: mk_word_bitop.ml word_base.th word_funs.ml
	rm -f word_bitop.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_word_bitop`;;'\
             'quit();;' | ${Hol} 

word_num.th: mk_word_num.ml word_bitop.th word_base.th word_funs.ml
	rm -f word_num.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_word_num`;;'\
             'quit();;' | ${Hol} 

bword_bitop.th: mk_bword_bitop.ml word_bitop.th word_funs.ml
	rm -f bword_bitop.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_bword_bitop`;;'\
             'quit();;' | ${Hol} 

bword_num.th: mk_bword_num.ml word_bitop.th word_funs.ml
	rm -f bword_num.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_bword_num`;;'\
             'quit();;' | ${Hol} 

bword_arith.th: mk_bword_arith.ml bword_num.th
	rm -f bword_arith.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_bword_arith`;;'\
             'quit();;' | ${Hol} 

word_convs_ml.o: word.th word_convs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`res_quan`;;'\
	     'load_theory `word`;;'\
	     'compilet `word_convs`;;'\
             'quit();;' | ${Hol} 

all: word.th $(OBJ)
	@echo "===> library word rebuilt"


doc:	
	for thy in ${THY_NAMES} ; \
	    do (cd $(THMDIR)$$thy; $(MAKEDOC) $$thy) ; \
	done
	@echo "===> .doc files for theorems created"
