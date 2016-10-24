# =====================================================================
# Makefile for the record_proof library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the record_proof help files
# ---------------------------------------------------------------------
Help=../help
LATEX=latex
# ---------------------------------------------------------------------
# Pathname to the doc-to-tex script and doc-to-tex.sed file 
# ---------------------------------------------------------------------
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
#MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../
MAKEINDEX=makeindex

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

tex:	 functions
	@echo "TeX files made"

functions:
	@echo "\chapter{ML Functions in the {\tt record\_proof} Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help} entries.tex

index: 
	${MAKEINDEX} record_proof.idx

record_proof: 
	$(LATEX) record_proof.tex 

all: 
	make clean; make tex; make record_proof; make index; make record_proof

