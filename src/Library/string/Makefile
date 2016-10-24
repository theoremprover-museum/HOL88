# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: string
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
	@echo "===> library string: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library string: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

ascii.th: mk_ascii.ml
	rm -f ascii.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_ascii`;;' | ${Hol} 

string.th: mk_string.ml ascii.th
	rm -f string.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_string`;;' | ${Hol} 

ascii_ml.o: ascii.ml ascii.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `ascii`;;'\
	     'compilet `ascii`;;'\
	     'quit();;' | ${Hol}

stringconv_ml.o: stringconv.ml string.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `string`;;'\
	     'compilet `stringconv`;;'\
	     'quit();;' | ${Hol}

string_rules_ml.o: string_rules.ml stringconv_ml.o ascii_ml.o string.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `string`;;'\
	     'loadf `stringconv`;;'\
	     'loadf `ascii`;;'\
	     'compilet `string_rules`;;'\
	     'quit();;' | ${Hol}

string_ml.o: string.ml string_rules_ml.o string.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `string`;;'\
	     'compilet `string`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: ascii.th string.th ascii_ml.o stringconv_ml.o string_rules_ml.o \
     string_ml.o
	@echo "===> library string rebuilt"

