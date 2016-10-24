# Copyright 1991 by Norman Ramsey.  All rights reserved.
# See file COPYRIGHT for more information.
#
# Adjust these two lines for your ANSI C compiler
CC=gcc -O
CFLAGS=-g

# BIN is where the commands (notangle, noweave, nountangle, noroots) land
# LIB is where the pieces of the pipes (nt, markup, unmarkup) are stored
# MAN is the root of your local man pages directory
# MANEXT is the extension for your commands' man pages (usually 1 or l)
# TEXINPUTS is the directory for TeX macro files
HOST=
BIN=
LIB=
MAN=
MANEXT=
TEXINPUTS=

# Stop editing.  No user-serviceable parts below.

TANGLEOBJS=notangle.o getline.o modules.o modtrees.o strsave.o \
	main.o errors.o columns.o
MARKUPOBJS=markmain.o strsave.o markup.o errors.o getline.o columns.o
FILES=columns.nw errors.nw getline.nw main.nw markmain.nw markup.nw \
	modtrees.nw modules.nw notangle.nw readme.nw strsave.nw
SHELLS=notangle.sh nountangle.sh noweave.sh noroots.sh unmarkup
SRCS=columns.h errors.h getline.h markup.h modtrees.h \
	modules.h notangle.h strsave.h \
	columns.c errors.c getline.c main.c markmain.c markup.c \
	modtrees.c modules.c notangle.c readme.c strsave.c
NAME='name of RCS version'

NOTANGLE=notangle

.SUFFIXES: .nw .tex .dvi .h
.nw.tex: ;	noweave $*.nw >$*.tex
.nw.c: ;	$(NOTANGLE) -L $*.nw >$*.c
.nw.o: ;	$(NOTANGLE) -L $*.nw >$*.c
		$(CC) $(CFLAGS) -c $*.c
.nw.h: ;	$(NOTANGLE) -Rheader $*.nw >x$*.h
		-cmp -s x$*.h $*.h || cp x$*.h $*.h

all:	nt markup

nt:	$(TANGLEOBJS)
	$(CC) $(CFLAGS) -o nt $(TANGLEOBJS)

markup:	$(MARKUPOBJS)
	$(CC) $(CFLAGS) -o markup $(MARKUPOBJS)

install:	nt markup notangle.sh noweave.sh nountangle.sh noroots.sh noxref
		sed "s@|LIBDIR|@$(LIB)@" notangle.sh > $(BIN)/notangle
		sed "s@|LIBDIR|@$(LIB)@" noweave.sh  > $(BIN)/noweave
		sed "s@|LIBDIR|@$(LIB)@" nountangle.sh  > $(BIN)/nountangle
		sed "s@|LIBDIR|@$(LIB)@" noroots.sh  > $(BIN)/noroots
		chmod +x $(BIN)/notangle $(BIN)/noweave $(BIN)/nountangle $(BIN)/noroots
		strip nt markup
		cp nt markup unmarkup noxref $(LIB)
		chmod +x $(LIB)/unmarkup $(LIB)/noxref
		cp nwkernel.tex nwmac.tex noweb.sty $(TEXINPUTS)
		sed  -e "s@|LIBDIR|@$(LIB)@" -e "s@|TEXINPUTS|@$(TEXINPUTS)@" notangle.1 > $(MAN)/man$(MANEXT)/notangle.$(MANEXT)
		cd $(MAN)/man$(MANEXT); /bin/rm -f noweave.$(MANEXT) noweb.$(MANEXT) nountangle.$(MANEXT) noroots.$(MANEXT)
		cd $(MAN)/man$(MANEXT); ln notangle.$(MANEXT) noweave.$(MANEXT); ln notangle.$(MANEXT) noweb.$(MANEXT) ; ln notangle.$(MANEXT) nountangle.$(MANEXT) ; ln notangle.$(MANEXT) noroots.$(MANEXT)

clean: ;	rm -f *.makelog *.log *.blg *.dvi *.o *.toc *~ nt markup x*.h *.st *.lt

boot: ;		touch *.c *.h

veryclean:	clean
		rm -f $(SRCS)

bundle:		clean
		bundle COPYRIGHT README Makefile [a-z]* > ../nwbundle

checkin:	$(FILES) $(SHELLS) notangle.1 Makefile README COPYRIGHT
		ci -n'$(NAME)' -l -f -m'checked in as version named $(NAME)' $(FILES) $(SHELLS) notangle.1 Makefile README COPYRIGHT

columns.o:	columns.h
errors.o:	errors.h
getline.o:	getline.h errors.h columns.h
main.o:		notangle.h
markmain.o:	markup.h errors.h getline.h columns.h
markup.o:	markup.h strsave.h errors.h
modtrees.o:	strsave.h modules.h modtrees.h errors.h
modules.o:	modules.h modtrees.h errors.h columns.h strsave.h
notangle.o:	strsave.h getline.h modules.h modtrees.h errors.h
strsave.o:	strsave.h errors.h
