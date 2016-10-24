# 
# Makefile for mweb
#

# Change the following two directories to suit your site.
BINDIR=/usr/local/bin
TEXMACDIR=/usr/local/lib/tex

# Do not change anything below.

HEADER=mweb.h patchlevel.h
SRC=common.c mtangle.c mweave.c winnow.c mmerge.c
OBJ=common.o mtangle.o mweave.o winnow.o
PROGRAMS=mtangle mweave winnow mmerge
TEXMAC=mwebmac.tex

all:	$(PROGRAMS)

mweave:	common.o mweave.o
	$(CC) $(CFLAGS) -o mweave common.o mweave.o

mtangle:	common.o mtangle.o
	$(CC) $(CFLAGS) -o mtangle common.o mtangle.o

winnow:	common.o winnow.o
	$(CC) $(CFLAGS) -o winnow common.o winnow.o

mmerge:	mmerge.c
	$(CC) $(CFLAGS) -o mmerge mmerge.c

common.o:	common.c $(HEADER)

mweave.o:	mweave.c $(HEADER)

mtangle.o:	mtangle.c $(HEADER)

winnow.o: 	winnow.c $(HEADER)

install:
	$(INSTALL) $(PROGRAMS) $(BINDIR)
	$(INSTALL) $(TEXMAC) $(TAXMACDIR)

clean:
	rm -f *.o $(PROGRAMS)
