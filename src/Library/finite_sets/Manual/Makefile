# =====================================================================
# Makefile for the finite_sets library documentation 
# =====================================================================

# ---------------------------------------------------------------------
# Pathname to the finite_sets help files
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

tex: theorems ids
	@echo "TeX files made"

ids:
	@echo "\chapter{ML Functions in the Library}">entries.tex
	@echo "\label{entries}">>entries.tex
	@echo "\input{entries-intro}" >> entries.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:
	@echo "\chapter{Pre-proved Theorems}" > theorems.tex
	@echo "\input{theorems-intro}" >> theorems.tex
	@echo "\section{The type definition}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/sdef theorems.tex
	@echo "\section{Basic properties of {\tt EMPTY}, {\tt INSERT}, and {\tt IN}}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/basic theorems.tex
	@echo "\section{Set inclusion}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/subs theorems.tex
	@echo "\section{Intersection and union}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/unin theorems.tex
	@echo "\section{Set difference}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/diff theorems.tex
	@echo "\section{Deletion of an element}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/del theorems.tex
	@echo "\section{Disjoint sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/disj theorems.tex
	@echo "\section{The {\tt CHOICE} and {\tt REST} functions}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/chre theorems.tex
	@echo "\section{Image of a function on a set}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/image theorems.tex
	@echo "\section{Mappings between sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/fun theorems.tex
	@echo "\section{Singleton sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/sing theorems.tex
	@echo "\section{Cardinality of sets}">>theorems.tex
	/bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/card theorems.tex

index: 
	${MAKEINDEX} finite_sets.idx index.tex 

finite_sets: 
	latex finite_sets.tex 

all: 
	make clean; make tex; make finite_sets; make index; make finite_sets

