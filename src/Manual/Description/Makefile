# =====================================================================
# Makefile for the hol DESCRIPTION
# =====================================================================

# ---------------------------------------------------------------------
# Pathnames: MAKEINDEX = makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../LaTeX/makeindex  ../../ 

default:
	@echo "INSTRUCTIONS: Type \"make all\" to make DESCRIPTION"

clean:
	rm -f *.dvi *.aux *.toc *.log *.idx *.ilg

index: 
	${MAKEINDEX} description.idx index.tex

description: 
	latex description.tex 

all: 
	make clean; make description; make index; make description
