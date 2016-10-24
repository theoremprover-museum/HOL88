#=======================================================================
# Make auxiliary documentation using nroff and LaTeX.  makeindex.l is
# the nroff/troff input file for the UNIX manual pages.  From it, we
# produce:
#	makeindex.hlp (printable ASCII help file),
#	makeindex.info (GNU Emacs INFO node file),
#	makeindex.ps (PostScript version of typeset manual pages), and
#	makeindex.vms (VAX VMS hierarchical help file),
#	manpages.dvi (.dvi file of manual pages)
#
# Targets:
#	all
#	clean
#	clobber
#	install
#	makeindex.dvi
#	makeindex.hlp
#	makeindex.ps
#	makeindex.info
#	makeindex.vms
#	manpages.dvi
#	uninstall
#
# [15-Aug-1991]
#=======================================================================

CATDIR	=	$(MANTOP)/cat1
LATEX	=	latex
MANTOP	=	/usr/local/man
MANDIR	=	$(MANTOP)/man1
RM	=	/bin/rm -f

all:	makeindex.dvi makeindex.hlp makeindex.info makeindex.ps \
	makeindex.vms manpages.dvi

clean:
	$(RM) *~
	$(RM) \#*
	$(RM) core
	$(RM) makeindex.aux
	$(RM) makeindex.dvi
	$(RM) makeindex.log

clobber:	clean
	$(RM) makeindex.hlp
	$(RM) makeindex.info
	$(RM) makeindex.ps
	$(RM) makeindex.vms
	$(RM) manpages.dvi

install:	uninstall
	cp makeindex.l $(MANDIR)/makeindex.1
	chmod 774 $(MANDIR)/makeindex.1

makeindex.dvi:	makeindex.tex
	$(LATEX) makeindex.tex
	$(LATEX) makeindex.tex

makeindex.hlp:	makeindex.l
	nroff -man makeindex.l | col -b >makeindex.hlp

# ======================================================================
# NB: The vmshelp* and uhelp* convertors are available for anonymous ftp
# on math.utah.edu from ~ftp/pub/tex/pub/info or via e-mail from the
# tuglib server with requests "help" and "send index from
# ftp/pub/tex/pub/info"
# ======================================================================
makeindex.info:	makeindex.vms
	vmshelp2 makeindex.vms >makeindex.info

makeindex.ps:	makeindex.l
# To convert a manual page to PostScript:
#	on BSD: tbl | eqn | ditroff -man | psdit | psrev
#	on AIX: tbl | eqn | psroff -t -man | psrev
# Omit psrev if your printer stacks pages face down.
# tbl and eqn are not required for makeindex.l.
# This pipeline is hidden in a private script:
	man2ps <makeindex.l >makeindex.ps

# Reduce makeindex.hlp to makeindex.vms with the help of sed and awk.
# Alas, the output of nroff recorded in makeindex.hlp is somewhat
# system dependent.  The sed patterns here suffice for SunOS 4.1.1
# and IBM RS/6000 AIX 3.1, but may require modifications on other
# UNIX systems.

makeindex.vms:	makeindex.hlp
	echo '1 MAKEINDEX' >makeindex.vms
	expand < makeindex.hlp | \
	sed	-e '/^ *MAKEINDEX(1L).*MAKEINDEX(1L)/d' \
		-e '/^ *Page.*(printed.*)/d' \
		-e '/^Sun Release [0-9]/d' \
		-e 's/^ *INPUT STYLE SPECIFIERS/3 INPUT STYLE SPECIFIERS/' \
		-e 's/^ *OUTPUT STYLE SPECIFIERS/3 OUTPUT STYLE SPECIFIERS/' \
		-e 's/^ *TeX EXAMPLE/3 TeX EXAMPLE/' \
		-e 's/^ *TROFF EXAMPLE/3 TROFF EXAMPLE/' \
		-e 's/^ *CREATING THE INDEX FILE/3 CREATING THE INDEX FILE/' \
		-e 's/^ *COMPLETING THE INDEX/3 COMPLETING THE INDEX/' \
		-e 's/^     / /' \
		-e 's/^ \([A-Z]\)/2 \1/' \
		-e 's/^\([A-Z]\)/2 \1/' |\
	awk -f deblank.awk >> makeindex.vms

# We create a .dvi file for the manual pages under a different name to
# avoid a collision with makeindex.dvi.  GNU groff works quite nicely,
# and gives us a .dvi file that anyone can process, even if they do not
# have a PostScript printer.  groff's font selection is a bit unusual;
# it wants a few Computer Modern fonts in magnifications 0.8 and 0.9.
# For manpages.dvi, it needs these additional font files: cmbx10.240pk
# cmbx10.270pk cmcsc10.240pk cmcsc10.270pk cmr10.240pk cmr10.270pk
# cmti10.240pk cmti10.270pk.  If your DVI driver can substitute a nearby
# size, you should be able to manage without them.
manpages.dvi:	makeindex.l
	groff -Tdvi -man makeindex.l >manpages.dvi

uninstall:
	if [ -f $(CATDIR)/makeindex.1 ] ; then $(RM) $(CATDIR)/makeindex.1 ; fi
	if [ -f $(MANDIR)/makeindex.1 ] ; then $(RM) $(MANDIR)/makeindex.1 ; fi

