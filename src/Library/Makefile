# =====================================================================
#
# 		 MAKEFILE FOR THE HOL SYSTEM LIBRARY
#
# =====================================================================

# =====================================================================
# SUMMARY OF MAIN ENTRIES:
#
# make library	   : rebuilds the library, compiling sources whenever 
#
# make clean	   : removes all object code
#
# make clobber	   : removes all object code, and theories
#
# =====================================================================

# =====================================================================
# MACROS:
#
# Libraries = a list of all libraries to be made
#
# Hol	    = the pathname of the version of hol that will be used to 
#	      rebuild the library.
#
# LispType  = the type of the lisp system, cl or franz
#
# Obj       = the default filename extension for compiled lisp files.
#
# Lisp      = the pathname of the common lisp system (not used for franz)
# 
# Liszt     = the pathname of the franz lisp compiler (not used for cl)
#
# LispDir   = the directory where the Lisp sources are
# =====================================================================

Libraries = unwind taut sets reduce arith pred_sets string finite_sets\
	    res_quan wellorder abs_theory reals window pair word\
	    record_proof parser prettyp trs latex-hol more_arithmetic\
	    numeral ind_defs

# NB: UNITY, auxiliary, bags, convert, eval, fixpoints, group, int_mod,
#     integer, prog_logic88, and quotient moved to contrib, 1 Mar. 94 by RJB
# NB: more_lists has been moved to contrib from the library 9 Feb. 94 by WW
# NB: card, well_order, zet, csp temporarily removed from the library

Hol=../hol
LispType=cl
Obj=fasl
Lisp=cl
Liszt=
LispDir=/usr/local/hol/lisp

clean:
	for lib in ${Libraries} ; \
	    do (cd $$lib; $(MAKE) Obj=${Obj} clean; cd ..) ; \
	done
	@echo "===> all library object code deleted"

clobber:
	for lib in ${Libraries} ; \
	    do (cd $$lib; $(MAKE) Obj=${Obj} clobber; cd ..) ; \
	done
	@echo "===> all library object code and theory files deleted"

library:
	for lib in ${Libraries} ; \
	    do (cd $$lib; $(MAKE)  LispType=${LispType}\
                                   Obj=${Obj}\
                                   Lisp=${Lisp}\
                                   Liszt=${Liszt}\
                                   LispDir=${LispDir}\
                                   Hol=${Hol} all; cd ..) ; \
	done
	@echo "=======> library rebuilt"

