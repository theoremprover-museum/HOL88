# =====================================================================
# Makefile for mweb  documentation 
# =====================================================================

LATEX = latex2e

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

mweb: 
	$(LATEX) mweb.tex 

index:	
	$(MAKEINDEX) mweb
all: 
	make clean; make mweb; bibtex mweb; make mweb

