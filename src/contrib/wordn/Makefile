# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: wordn
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

#Hol=../../hol
Hol=/usr/groups/hol/HOL21/hol


# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o
	@echo "===> library wordn: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library wordn: all object code and theory files deleted"

# =====================================================================
# Macros
# =====================================================================
THY= wordn_base.th wordn_bitops.th wordn_num.th
# wordn_ints.th more_integers.th
THY_SRC= mk_wordn_base.ml mk_wordn_bitops.ml mk_wordn_num.ml
# mk_wordn_ints.ml  more_integers.ml
OBJ_SRC= wordn_rules.ml wordn_conv.ml wordn_bit_op.ml wordn_num.ml\
  wordn_bits.ml wordn_tacs.ml oconv.ml genfuns.ml
OBJ= wordn_rules_ml.o wordn_conv_ml.o wordn_bit_op_ml.o wordn_num_ml.o\
  wordn_bits_ml.o wordn_tacs_ml.o oconv_ml.o genfuns_ml.o

# =====================================================================
# Entries for individual files.
# =====================================================================

wordn.th: mk_wordn.ml $(THY)
	rm -f wordn.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'loadt `mk_wordn`;;'\
             'quit();;' | ${Hol} 

wordn_base.th: mk_wordn_base.ml 
	rm -f wordn_base.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_wordn_base`;;'\
             'quit();;' | ${Hol} 

wordn_bitops.th: mk_wordn_bitops.ml 
	rm -f wordn_bitops.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_wordn_bitops`;;'\
             'quit();;' | ${Hol} 

wordn_num.th: mk_wordn_num.ml 
	rm -f wordn_num.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_wordn_num`;;'\
             'quit();;' | ${Hol} 

more_integers.th: more_integers.ml 
	rm -f more_integers.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `more_integers`;;'\
             'quit();;' | ${Hol} 

wordn_ints.th: mk_wordn_ints.ml wordn_num.th more_integers.th
	rm -f wordn_ints.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_wordn_ints`;;'\
             'quit();;' | ${Hol} 

oconv_ml.o:  oconv.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'compilet `oconv`;;'\
             'quit();;' | ${Hol} 

genfuns_ml.o:  genfuns.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `genfuns`;;'\
             'quit();;' | ${Hol} 

wordn_tacs_ml.o:  wordn_tacs.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `wordn_tacs`;;'\
             'quit();;' | ${Hol} 

wordn_conv_ml.o:  wordn_conv.ml wordn_rules_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'load_theory `wordn`;;'\
	     'loadf `wordn_rules`;;'\
	     'compilet `wordn_conv`;;'\
             'quit();;' | ${Hol} 

wordn_rules_ml.o: wordn.th wordn_rules.ml genfuns_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'loadf `genfuns`;;'\
	     'load_theory `wordn`;;'\
	     'compilet `wordn_rules`;;'\
             'quit();;' | ${Hol} 

wordn_bit_op_ml.o: wordn.th oconv_ml.o genfuns_ml.o wordn_tacs_ml.o wordn_bit_op.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'load_theory `wordn`;;'\
	     'loadf `oconv`;;'\
	     'loadf `genfuns`;;'\
	     'loadf `wordn_rules`;;'\
	     'loadf `wordn_tacs`;;'\
	     'compilet `wordn_bit_op`;;'\
             'quit();;' | ${Hol} 

wordn_bits_ml.o: wordn.th oconv_ml.o genfuns_ml.o wordn_tacs_ml.o wordn_bits.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'load_theory `wordn`;;'\
	     'loadf `oconv`;;'\
	     'loadf `genfuns`;;'\
	     'loadf `wordn_tacs`;;'\
	     'compilet `wordn_bits`;;'\
             'quit();;' | ${Hol} 

wordn_num_ml.o: wordn.th wordn_num.ml oconv_ml.o genfuns_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library`more_lists`;;'\
	     'load_theory `wordn`;;'\
	     'loadf `oconv`;;'\
	     'loadf `genfuns`;;'\
	     'loadf `wordn_rules`;;'\
	     'loadf `wordn_conv`;;'\
	     'loadf `wordn_bit_op`;;'\
	     'compilet `wordn_num`;;'\
             'quit();;' | ${Hol} 

all: wordn.th $(OBJ)
	chmod go+r *
	@echo "===> library wordn rebuilt"


