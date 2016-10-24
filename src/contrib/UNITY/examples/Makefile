# =====================================================================
#
# 	 MAKEFILE FOR EXAMPLES USING HOL-UNITY
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : all examples
#
# make clean	    : remove theories and compiled code
#
#
# For the moment no compilation files have been made
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the name of the version of hol used (currently 2.0)
# =====================================================================

Hol=hol

dummy:
	@echo "*** UNITY Examples: make parameter missing ***"

example01.th: mk_example01.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `mk_example01`;;'\
             'quit();;' | ${Hol}

example02.th: mk_example02.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `mk_example02`;;'\
             'quit();;' | ${Hol}

example03.th: mk_example03.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `mk_example03`;;'\
             'quit();;' | ${Hol}

clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "*** UNITY Examples: all object code and theories deleted***"
                      
all:    example01.th example02.th example03.th
	@echo "===> UNITY examples rebuilt"

