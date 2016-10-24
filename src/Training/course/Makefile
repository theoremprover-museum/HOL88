#=====================================================================
# Makefile for typesetting the HOL course slides.
# =====================================================================

default: 
	@echo "Type \"make all\" to typeset the HOL course slides"

intro.dvi: intro.tex
	latex intro.tex

logicA.dvi: logicA.tex
	latex logicA.tex

logicB.dvi: logicB.tex
	latex logicB.tex

macros.dvi: macros.tex
	latex macros.tex

ml.dvi: ml.tex
	latex ml.tex

primrec.dvi: primrec.tex
	latex primrec.tex

systemA.dvi: systemA.tex
	latex systemA.tex

systemB.dvi: systemB.tex
	latex systemB.tex

thmproveA.dvi: thmproveA.tex
	latex thmproveA.tex

thmproveB.dvi: thmproveB.tex
	latex thmproveB.tex

tydefs.dvi: tydefs.tex
	latex tydefs.tex

all: intro.dvi logicA.dvi logicB.dvi ml.dvi primrec.dvi systemA.dvi\
     systemB.dvi thmproveA.dvi thmproveB.dvi tydefs.dvi
	echo "course made"
