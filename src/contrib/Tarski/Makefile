# =====================================================================
#
# 	 MAKEFILE FOR Tarski
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : Tarski theory
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
	@echo "*** Tarski: make parameter missing ***"

tarski.th: mk_tarski.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `mk_tarski`;;'\
             'quit();;' | ${Hol}

clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "*** Tarski: all object code and theories deleted***"
                      
all:    tarski.th
	@echo "===> Tarski rebuilt"
