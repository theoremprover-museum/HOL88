# =====================================================================
#
#                MAKEFILE FOR THE HOL LIBRARY: wellorder
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all       : create theories and compile code[*]
#
#    make clean     : remove only compiled code[*]
#
#    make clobber   : remove both theories and compiled code[*]
#
# [*] In fact this library contains no compiled code
# ---------------------------------------------------------------------
#
# MACROS:
#
#    Hol            : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

all: WELLORDER.th

clean:;

clobber: clean; rm -f WELLORDER.th

WELLORDER.th:  mk_wellorder.ml;                         \
    echo 'set_flag(`abort_when_fail`,true);;'           \
         'loadt `mk_wellorder`;;'                       \
         'quit();;' | ${Hol}
