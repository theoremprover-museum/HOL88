# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: parser
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
#    Hol         : the pathname of the version of hol used
#
#    Obj         : the default filename extension for compiled lisp files,
#		   for franz it is o, for common lisp it depends on the 
#		   implementation
# =====================================================================

Hol=../../hol
Obj=o

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o *_ml.l *.$(Obj)
	@echo "===> library parser: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.$(Obj)
	@echo "===> library parser: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

general_ml.o: general.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `general`;;'\
	     'quit();;' | ${Hol}

parser_ml.o: parser.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `parser`;;' \
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: general_ml.o parser_ml.o
	@echo "===> library parser rebuilt"
