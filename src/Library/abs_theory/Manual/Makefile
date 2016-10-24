#==============================================#
# Make the manual for the "abs_theory" library #
#==============================================#

Help=../help
DOCTOTEX=../../../Manual/Reference/bin/doc-to-tex
DOCTOTEXSED=../../../Manual/Reference/bin/doc-to-tex.sed

# ---------------------------------------------------------------------
# Pathname to the makeindex script
# ---------------------------------------------------------------------
MAKEINDEX=../../../Manual/LaTeX/makeindex ../../../

all:; make clean; make ids; make abs_theory; make index; make abs_theory

clean:;                                                                 \
    rm -f *.dvi *.aux *.toc *.log *.idx *.ilg entries.tex;              \
    echo "\begin{theindex}" >index.tex;                                 \
    echo "\mbox{}" >>index.tex;                                         \
    echo "\end{theindex}" >>index.tex

ids:;                                                                   \
    echo "\chapter{ML Functions in the {\tt abs\_theory} Library}" >entries.tex;   \
    echo "\input{entries-intro}" >>entries.tex;                         \
    /bin/sh ${DOCTOTEX} ${DOCTOTEXSED} ${Help}/entries entries.tex

index:;                                                                 \
    ${MAKEINDEX} abs_theory.idx index.tex

abs_theory:;                                                            \
    latex abs_theory.tex
