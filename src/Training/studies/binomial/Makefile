# =====================================================================
#
#		MAKEFILE FOR THE BINOMIAL THEOREM CASE STUDY
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : create theories
# make tidy	    : remove temporary files
# make clean	    : remove theories and dvi files
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

Hol=/usr/groups/hol/HOL2/bin/hol

all: BINOMIAL.th BINOMIAL_integer.th
	@echo "===> Theories BINOMIAL and BINOMIAL_integer rebuilt"

tidy:
	rm -f ,* *~ core *.aux *.log *.blg *.toc *.bbl
	@echo "===> Temporary files removed"

clean: tidy
	rm -f *.th *.dvi
	@echo "===> Theory and dvi files removed"

BINOMIAL.th: mk_BINOMIAL.ml
	rm -f BINOMIAL.th
	echo 'loadt `mk_BINOMIAL.ml`;;' | ${Hol} > BINOMIAL.log

BINOMIAL_integer.th: BINOMIAL.th mk_BINOMIAL_integer.ml
	rm -f BINOMIAL_integer.th
	echo 'loadt `mk_BINOMIAL_integer.ml`;;' | ${Hol} > BINOMIAL_integer.log
