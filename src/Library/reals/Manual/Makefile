#============================================================================#
# Make the manual for the "reals" library                                    #
#============================================================================#

Help=../help
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

all:; make clean; make tex; make reals; make index; make reals

clean:;                                                                    \
    rm -f *.dvi *.aux *.toc *.log *.idx *.ilg;                             \
    echo "\begin{theindex}" >index.tex;                                    \
    echo "\mbox{}" >>index.tex;                                            \
    echo "\end{theindex}" >>index.tex

tex: theorems

theorems:;                                                                 \
    echo "\chapter{Pre-proved Theorems}" >theorems.tex;                    \
    echo "\input{theorems-intro}" >>theorems.tex;                          \
    echo "\section{HRAT}" >>theorems.tex;                                  \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/HRAT theorems.tex;     \
    echo "\section{HREAL}" >>theorems.tex;                                 \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/HREAL theorems.tex;    \
    echo "\section{REALAX}" >>theorems.tex;                                \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/REALAX theorems.tex;   \
    echo "\section{REAL}" >>theorems.tex;                                  \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/REAL theorems.tex;     \
    echo "\section{TOPOLOGY}" >>theorems.tex;                              \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/TOPOLOGY theorems.tex; \
    echo "\section{NETS}" >>theorems.tex;                                  \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/NETS theorems.tex;     \
    echo "\section{LIM}" >>theorems.tex;                                   \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/LIM theorems.tex;      \
    echo "\section{SEQ}" >>theorems.tex;                                   \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/SEQ theorems.tex;      \
    echo "\section{POWSER}" >>theorems.tex;                                \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/POWSER theorems.tex;   \
    echo "\section{TRANSC}" >>theorems.tex;                                \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/TRANSC theorems.tex

reals:;                                                                    \
    latex reals.tex

index:;                                                                    \
    ${MAKEINDEX} reals.idx index.tex
