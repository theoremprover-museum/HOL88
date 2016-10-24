LATEX	=	latex
RM	=	/bin/rm -f

all:	ind.dvi

ind.dvi:	ind.tex fig1.tex
	$(LATEX) ind

clean:
	$(RM) core
	$(RM) *~
	$(RM) \#*
	$(RM) ind.dvi
	$(RM) ind.log

clobber:	clean
