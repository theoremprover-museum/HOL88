#============================================================================#
# Make the manual for the "wellorder" library                                #
#============================================================================#

Help=../help
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed
# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

all:; make clean; make tex; make wellorder; make index; make wellorder

clean:;                                                                 \
    rm -f *.dvi *.aux *.toc *.log *.idx *.ilg entries.tex;              \
    echo "\begin{theindex}" >index.tex;                                 \
    echo "\mbox{}" >>index.tex;                                         \
    echo "\end{theindex}" >>index.tex

tex: theorems ids

ids:;                                                                   \
    echo "\chapter{ML Functions in the wellorder Library}" >entries.tex;\
    echo "\label{entries}" >>entries.tex;                               \
    echo "\input{entries-intro}" >>entries.tex;                         \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

theorems:;                                                              \
    echo "\chapter{Pre-proved Theorems}" >theorems.tex;                 \
    echo "\input{theorems-intro}" >>theorems.tex;                       \
    echo "\section{Basic definitions}" >>theorems.tex;                  \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/defs theorems.tex;  \
    echo "\section{Miscellaneous lemmas}" >>theorems.tex;               \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/lemmas theorems.tex;\
    echo "\section{Main theorems}"  >>theorems.tex;                     \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/main theorems.tex

wellorder:;                                                             \
    latex wellorder.tex

index:;                                                                 \
    ${MAKEINDEX} wellorder.idx index.tex
