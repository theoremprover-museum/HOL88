# =====================================================================
#
#                MAKEFILE FOR THE HOL LIBRARY: reduce
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all       : create theories and compile code
#
#    make clean     : remove only compiled code
#
#    make clobber   : remove both theories and compiled code
#
#    [In fact there are no theories in this library]
# ---------------------------------------------------------------------
#
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

all: reduce_ml.o;

clean:; rm -f boolconv_ml.o arithconv_ml.o reduce_ml.o

clobber: clean;

reduce_ml.o: arithconv_ml.o boolconv_ml.o reduce.ml;    \
    echo 'set_flag(`abort_when_fail`,true);;'           \
         'compilet `reduce`;;'                          \
         'quit();;' | ${Hol}

arithconv_ml.o: arithconv.ml;                           \
    echo 'set_flag(`abort_when_fail`,true);;'           \
         'compilet `arithconv`;;'                       \
         'quit();;' | ${Hol}

boolconv_ml.o: boolconv.ml;                             \
    echo 'set_flag(`abort_when_fail`,true);;'           \
         'compilet `boolconv`;;'                        \
         'quit();;' | ${Hol}
