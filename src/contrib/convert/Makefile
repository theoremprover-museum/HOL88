# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: convert
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
#
#    OBJECTS        : the things to make 
# =====================================================================

Hol=../../hol
OBJECTS = unwind_ml.o unfold_ml.o prune_ml.o conv_package_ml.o more_conv_ml.o

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f $(OBJECTS)
	@echo "===> library convert: all object code deleted"

clobber:
	rm -f $(OBJECTS)
	@echo "===> library convert: all object code deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

unwind_ml.o: unwind.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `unwind`;;'\
	     'quit();;' | ${Hol}

more_conv_ml.o: more_conv.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `more_conv`;;'\
	     'quit();;' | ${Hol}

unfold_ml.o: unfold.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `unfold`;;'\
	     'quit();;' | ${Hol}

prune_ml.o: prune.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `prune`;;'\
	     'quit();;' | ${Hol}

conv_package_ml.o: conv_package.ml 
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `conv_package`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry.
# =====================================================================

all: $(OBJECTS)
	@echo "===> library convert rebuilt"


