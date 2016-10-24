#----------------------------------------------------------------------------#
# Makefile for the underlying theories in the "reals" library.               #
#----------------------------------------------------------------------------#

Hol=../../../hol

all: TRANSC.th

TRANSC.th: useful.ml transc.ml POWSER.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `transc.ml`;;'\
         'quit();;' | ${Hol}

POWSER.th: useful.ml powser.ml LIM.th SEQ.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `powser.ml`;;'\
         'quit();;' | ${Hol}

LIM.th: useful.ml lim.ml REAL.th TOPOLOGY.th NETS.th SEQ.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `lim.ml`;;'\
         'quit();;' | ${Hol}

SEQ.th: useful.ml seq.ml REAL.th TOPOLOGY.th NETS.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `seq.ml`;;'\
         'quit();;' | ${Hol}

NETS.th: useful.ml nets.ml REAL.th TOPOLOGY.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `nets.ml`;;'\
         'quit();;' | ${Hol}

TOPOLOGY.th: useful.ml topology.ml REAL.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `topology.ml`;;'\
         'quit();;' | ${Hol}

REAL.th: useful.ml real.ml REALAX.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `real.ml`;;'\
         'quit();;' | ${Hol}

REALAX.th: useful.ml equiv.ml realax.ml HREAL.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `realax.ml`;;'\
         'quit();;' | ${Hol}

HREAL.th: useful.ml hreal.ml HRAT.th;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `hreal.ml`;;'\
         'quit();;' | ${Hol}

HRAT.th: useful.ml equiv.ml hrat.ml;\
    echo 'set_flag(`abort_when_fail`,true);;'\
         'loadt `hrat.ml`;;'\
         'quit();;' | ${Hol}

clean:; rm -f *_ml.o

clobber: clean; rm -f *.th
