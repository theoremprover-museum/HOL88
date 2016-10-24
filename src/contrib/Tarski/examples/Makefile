# =====================================================================
#
# 	 MAKEFILE FOR EXAMPLES USING Tarski
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
	@echo "*** Tarski Examples: make parameter missing ***"

UNITY01.th: mk_UNITY01.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `mk_UNITY01`;;'\
             'quit();;' | ${Hol}

CTL01.th: mk_CTL01.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `mk_CTL01`;;'\
             'quit();;' | ${Hol}

clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "*** Tarski Examples: all object code and theories deleted***"
                      
all:    UNITY01.th CTL01.th
	@echo "===> Tarski examples rebuilt"

