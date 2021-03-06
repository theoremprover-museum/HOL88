#  Makefile modified for IBM PC DOS (Turbo C 2.0) [11-Dec-89] (only major
#  targets supported)
#
#  Makefile for the program `makeindex'
#
#  Copyright (C) 1987	Pehong Chen	(phc@renoir.berkeley.edu)
#  Computer Science Division
#  University of California, Berkeley
#

CC = tcc
O = .obj
X = .exe
INCLUDE = /usr/include
INCLUDE = c:/sys/tc/include

DEST	      = /usr/local/bin
DEST	      = c:/usr/bin

MANDIR	      = /usr/local/man/manl
MANDIR	      = nul

MANUAL	      = makeindex.l

DOC	      = makeindex.tex

EXTHDRS	      = ${INCLUDE}\ctype.h \
		${INCLUDE}\stdio.h

HDRS	      = genind.h \
		mkind.h \
		scanid.h \
		scanst.h

XCFLAGS=

LDFLAGS	      = -A -N -ml -v -y $(XCFLAGS)

CFLAGS	      = -DOS_PCDOS=1 -DIBM_PC_TURBO=1 $(LDFLAGS)

LIBS	      =

LINKER	      = link

MAKEFILE      = Makefile

OBJS	      = genind${O} mkind${O} qsort${O} scanid${O} scanst${O} sortid${O}

PRINT	      = psgrind

SRCS	      = genind.c \
		mkind.c \
		qsort.c \
		scanid.c \
		scanst.c \
		sortid.c

PROGRAM	      = makeindx

TAR	      = $(PROGRAM).tar

SHAR	      = $(PROGRAM).shar

ALL	      = $(MAKEFILE) $(DOC) $(MANUAL) $(HDRS) $(SRCS)

# Default stack is too small--increase
STACKSIZE=8000

LINKFLAGS=/MAP/LINE/ST:$(STACKSIZE)

# Rules...

.SUFFIXES:
.SUFFIXES:	.obj .c .sym .map

.c.obj:
		$(CC) -c $(CFLAGS) $*.c
#		$(CC) -c $(CFLAGS) $*.c >$*.clg
#		errshow <$*.clg >$*.cer
#		del $*.clg

.map.sym:
		mapsym $*
		del $*.map

RM = del

$(PROGRAM):	$(PROGRAM)$(X)

$(PROGRAM)$(X):	$(OBJS)
#		@rm -f $(PROGRAM)
		$(CC) $(LDFLAGS) -e$(PROGRAM)$(X) $(OBJS)
#		@size $(PROGRAM)

install:	$(PROGRAM)
		install -c -s -m 0755 $(PROGRAM) $(DEST)
		@ls -lgs $(DEST)/$(PROGRAM)

tar:
		@rm -f $(TAR)
		tar -cf $(TAR) $(ALL)

shar:
		@rm -f $(SHAR)
		shar $(SHAR) $(ALL)

dist:
		cp $(PROGRAM) $(DEST)
		rcp $(PROGRAM) monet:$(DEST)
		rcp $(PROGRAM) arpa:$(DEST)
		rcp $(PROGRAM) harrison@vangogh:bin

clean:
		@rm -f $(OBJS) core $(PROGRAM) *${O}ut

depend:
		@rm -f .#*.[chly]
		mkmf -f $(MAKEFILE) PROGRAM=$(PROGRAM) DEST=$(DEST)

index:
		@ctags -wx $(HDRS) $(SRCS)

print:
		@$(PRINT) $(HDRS) $(SRCS)

man:
		ptroff -man $(MANUAL)

program:	$(PROGRAM)

tags:		$(HDRS) $(SRCS)
		@ctags $(HDRS) $(SRCS)

# update:		$(DEST)/$(PROGRAM)

# $(DEST)/$(PROGRAM):	$(SRCS) $(HDRS) $(EXTHDRS)
#		@make -f $(MAKEFILE) DEST=$(DEST) install

# .DEFAULT:;	co $@
###
genind${O}:	mkind.h	genind.h
mkind${O}:	mkind.h
qsort${O}:	mkind.h
scanid${O}:	mkind.h scanid.h
scanst${O}:	mkind.h scanst.h
sortid${O}:	mkind.h
