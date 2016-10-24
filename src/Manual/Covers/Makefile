# Makefile for HOL Manual title and end pages.  This is separate from the main
# manual stuff because of the heavy PostScript hacking involved.

# The following variables are needed:
#
#   LATEX -- The name of the LaTeX command normally used at this site.
#   DVI2PS -- The name of the dvi -> ps converter.
#   DVI2PSOPTS -- Options for the converter named in DVI2PS.

LATEX = latex
DVI2PS = dvips
DVI2PSOPTS =
RM = rm -f

default:
	@echo "$(DIR)"
	@echo "INSTRUCTIONS: Type \"make all\" to make the fancy covers."
	@echo -n "  NB - psfig macros required.  See Covers/psfig/"
	@echo " if you don't have them."

endpages.dvi: CRC.ps DESCRIPTION.ps LANTERN.ps REFERENCE.ps TUTORIAL.ps \
              arms.ps endpages.tex endpages.sty
	$(LATEX) endpages
	@echo "===> endpages.dvi created"

titlepages.dvi: CRC.ps DESCRIPTION.ps LANTERN.ps REFERENCE.ps TUTORIAL.ps \
                arms.ps titlepages.tex titlepages.sty
	$(LATEX) titlepages
	@echo "===> titlepages.dvi created"

dvi: endpages.dvi titlepages.dvi

endpages.ps: endpages.dvi
	-$(DVI2PS) $(DVI2PSOPTS) endpages > endpages.ps
	@echo "===> endpages.ps created"

titlepages.ps: titlepages.dvi
	-$(DVI2PS) $(DVI2PSOPTS) titlepages > titlepages.ps
	@echo "===> titlepages.ps created"

all: clobber endpages.ps titlepages.ps

clean:
	$(RM) *.log core *.aux *~ #* LOG
	@echo "===> Fancy end and title pages cleaned up"

clobber: clean
	$(RM) endpages.ps titlepages.ps *.dvi 
	@echo "===> Fancy end and title pages clobbered"


