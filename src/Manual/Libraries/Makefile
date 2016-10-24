# =====================================================================
# Makefile for the hol LIBRARIES documentation
# =====================================================================

# ---------------------------------------------------------------------
# List of libraries that have documentation
# ---------------------------------------------------------------------
Libraries = abs_theory arith finite_sets more_arithmetic \
            numeral pair parser pred_sets prettyp reals record_proof reduce \
            res_quan sets string taut trs unwind wellorder window word

# ---------------------------------------------------------------------
# Pathname to libraries directory
# ---------------------------------------------------------------------
Libp=../../Library

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make LIBRARIES"

clean:
	rm -f *.dvi *.aux *.toc *.log 

individual-libraries:
	for lib in ${Libraries} ; \
	    do (cd ${Libp}/$$lib/Manual; make all) ; \
	done
	@echo "===> all library documentation typeset"

libraries:
	latex libraries.tex

all: 
	make clean; make individual-libraries; make libraries


