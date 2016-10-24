# =====================================================================
# Makefile for the more_arithmetic library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the more_arithmetic help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make the documentation"

# ---------------------------------------------------------------------
# Remove all trace of previous LaTeX jobs
# ---------------------------------------------------------------------
clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg
	@echo "\begin{theindex}" > index.tex
	@echo "\mbox{}" >> index.tex
	@echo "\end{theindex}" >> index.tex

tex: ids theorems
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the more\_arithmetic Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}\label{thms}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{Theorems about Inequalities}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/ineq theorems.tex
	@echo "\section{Theorems about {\tt 0}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/zero_ineq theorems.tex
	@echo "\section{Theorems about {\tt SUC}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/suc theorems.tex
	@echo "\section{Theorems about {\tt PRE}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/pre theorems.tex
	@echo "\section{Theorems about Addition}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/add theorems.tex
	@echo "\section{Theorems about Subtraction}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/sub theorems.tex
	@echo "\section{Theorems about Multiplication and Exponential Functions}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/mult theorems.tex
	@echo "\section{Theorems about Division}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/div_mod theorems.tex
	@echo "\section{Theorems about Maximum and Minimum}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/min_max theorems.tex
	@echo "\section{Theorems about Odd and Even Numbers}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/odd_even theorems.tex

index: 
	${MAKEINDEX} more_arithmetic.idx index.tex 

more_arithmetic: 
	latex more_arithmetic.tex 

all: 
	make clean; make tex; make more_arithmetic; make index; make more_arithmetic
