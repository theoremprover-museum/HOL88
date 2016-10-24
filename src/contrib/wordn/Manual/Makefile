# =====================================================================
# Makefile for the wordn library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the wordn help files
# ---------------------------------------------------------------------
Help=../help

# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex program
# ---------------------------------------------------------------------
MAKEINDEX=../../Manual/Reference/bin/makeindex

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

tex:	entries theorems
	@echo "TeX files made"

entries:
	@echo "\chapter{ML Functions in the wordn Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/ENTRIES entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{The theory {\tt wordn\_base}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/THEOREMS/base theorems.tex
	@echo "\section{The theory {\tt wordn\_bitops}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/THEOREMS/bitops theorems.tex
	@echo "\section{The theory {\tt wordn\_num}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/THEOREMS/num theorems.tex

index: 
	${MAKEINDEX} -o index.tex wordn

wordn: 
	latex wordn.tex 

all: 
	make clean; make tex; make wordn; make index; make wordn

