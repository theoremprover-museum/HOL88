# =====================================================================
# Makefile for the latex-hol library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the latex-hol help files
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

LATEX=latex

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

tex: ids 
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the {\tt latex-hol} Library}">entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex


index: 
	${MAKEINDEX} latex-hol.idx index.tex

latex-hol: 
	$(LATEX) latex-hol.tex 

all: 
	make clean; make tex
	@echo "edit the entries.tex file"
	make latex-hol; make index; make latex-hol
