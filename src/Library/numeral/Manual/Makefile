#===========================================#
# Make the manual for the "numeral" library #
#===========================================#

Help=../help
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

all:; make clean; make thms; make ids; make numeral; make index; make numeral

clean:;                                                                 \
    rm -f *.dvi *.aux *.toc *.log *.idx *.ilg entries.tex;              \
    echo "\begin{theindex}" >index.tex;                                 \
    echo "\mbox{}" >>index.tex;                                         \
    echo "\end{theindex}" >>index.tex

ids:;                                                                   \
    echo "\chapter{ML Functions in the numeral Library}" >entries.tex;  \
    echo "\input{entries-intro}" >>entries.tex;                         \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

thms:;                                                                  \
    echo "\chapter{Pre-proved Theorems}" > theorems.tex;                \
    echo "\input{theorems-intro}" >> theorems.tex;                      \
    echo "\section{Numeral theory}" >> theorems.tex;                    \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/thms/numeral theorems.tex

index:;                                                                 \
    ${MAKEINDEX} numeral.idx index.tex

numeral:;                                                               \
    latex numeral.tex
