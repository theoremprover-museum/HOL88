#----------------------------------------------------------------------------#
# Makefile for integers theory.                                              #
#----------------------------------------------------------------------------#

Hol=/usr/groups/hol/HOL22/sun4/hol

all: INT.th

INT.th: useful.ml equiv.ml int.ml;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `int.ml`;;'\
         'quit();;' | ${Hol}

clean:; rm -f *_ml.o

clobber: clean; rm -f *.th
