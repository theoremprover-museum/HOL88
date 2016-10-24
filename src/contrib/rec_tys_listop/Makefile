# =====================================================================
#
# 	 MAKEFILE FOR rec_tys_listop
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : compile all files
#
# make clean	    : remove compiled code
#
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the name of the version of hol used (currently 2.1)?
# =====================================================================

Hol=/usr/groups/hol/HOL21/sun4/hol

.SUFFIXES: _ml.o .ml


.ml_ml.o:  /bin/rm -f $*_ml.o
	echo    'set_flag(`abort_when_fail`,true);;\
                compilet `$*`;;\
                quit();;' | ${Hol}

clean:
	rm -f *_ml.o 
	@echo "*** rec_tys_listop: all object code deleted ***"

rt_lop_tyfns_ml.o: rt_lop_prim_rec_ml.o

all:    rt_lop_tydefs_ml.o rt_lop_prim_rec_ml.o rt_lop_tyfns_ml.o 
	@echo "===> rec_tys_listop object code rebuilt"
