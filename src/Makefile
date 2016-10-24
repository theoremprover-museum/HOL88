#=====================================================================
#
# 		  MAKEFILE FOR THE HOL SYSTEM
#
# =====================================================================

# =====================================================================
# INSTRUCTIONS:
#
# (1) Site dependent macros:
#
#     There are two flags and four site-dependent pathnames used in
#     this makefile which you may have to change to rebuild hol at
#     your site.
#
#     They are given by the six macros:
#
#           LispType, Obj, Lisp, Liszt, LisztComm and HOLdir
#
#     To use this makefile at your site, you may have to edit these
#     macros to reflect local lisp setups and local pathnames. See the
#     note below under MACROS for a description of these macros.
#     
# (2) To build hol.
#
#     To build hol, just type: "make hol".  This will build the hol
#     system, and create an executable version of hol in the form
#     of a file called "hol" in this directory.
#
#     Typing "make hol" will recompile any source code that needs
#     to be recompiled.  So if you make changes to any of the system's
#     source code files, just type "make hol" to recompile and 
#     rebuild the system.  Only the code that needs to be recompiled
#     to reflect the changes will be compiled.
#
#     Note: typing "make hol" will NOT, in general, rebuild any of the 
#     built-in theories.  In particular, a theory <file>.th will
#     be recreated only if:
#
#	     a) the corresponding ml source: mk_<file>.ml has 
#	        been changed, or
#
#	     b) a parent of the theory <file>.th has been changed.
#
#     This means that  if the executable code used to create a
#     theory changes (e.g. hol-lcf), the theory will not be rebuilt.
#     This is done to avoid unnecessary and time-consuming rebuilding 
#     of the built-in theories.
#
#     To force a theory to be rebuilt, remove the theory file.  
#     Or "touch" the corresponding file: mk_<file>.ml.  This is worth
#     doing, to check if the built-in theories can be rebuilt.
#
# (3) To completely rebuild hol from scratch.
#
#     To do a total rebuild of the system, including theory files, 
#     type "make clobber" before rebuilding hol.  This will remove all
#     object code and all theory files.  It is worth trying this at some
#     point to make sure that it's possible to do a total rebuild.
# =====================================================================

# =====================================================================
# SUMMARY OF MAIN ENTRIES:
#
# make all	      : builds hol and all libraries
#
# make hol	      : builds hol, compiling sources whenever necessary
#
# make clean          : removes object code from hol system and lisp
#
# make clobber	      : removes all object code and theories (incl. libraries)
#
# make library	      : rebuilds the library
#
# make clean-library  : removes object code and theories in the library
# =====================================================================

# =====================================================================
# MACROS:
#
# LispType     = the type of the lisp system used to build HOL. 
#                Possibilities are cl (for Common Lisp) or franz 
#                (for Franz Lisp).
#
# Obj          = the default filename extension for compiled lisp files.
#                for Franz Lisp this is o; for Common Lisp this depends on
#                the implementation. Some implementations and values are:
#
#                   Lucid CL     lbin
#                   KCL, AKCL    o
#                   Allegro CL   fasl
#
# Lisp         = the lisp system used to build HOL.  This can be 
# 		 an absolute pathname, a relative pathname, or simply
#		 the name of the appropriate shell command (e.g. "lisp")
#                provided this can be found by following the builder's 
#                unix search path.
# 
# Liszt        = the franz lisp complier used to build HOL.  This can be 
#	 	 an absolute pathname, a relative pathname, or simply
#		 the name of the appropriate shell command (e.g. "liszt")
#                provided this can be found by following the builder's 
#                unix search path. This macro is relevant only for
#	         building a Franz Lisp version of HOL.
#
# LisztComm    = the command issued (internally) by HOL to call the 
#		 lisp compiler when compiling ML.  This can be just 
#		 "liszt", if liszt will be found by following the HOL 
#		 user's search path. An absolute pathname can also be 
#		 nused for LisztComm. This macro is relevant onlt
#                for building a Franz Lisp version of HOL.
#
# Allegro      = Option for case-sensitivity in any version of Allegro
#                common lisp.
#
# AllegroV4.0  =  Allegro 4.0 specials
#
# AllegroV4.1  = Allegro 4.1 specials
#
#
# AllegroStuff = Combinations of options for any given version of
#                Allegro common lisp.
#
# HOLdir       = the absolute pathname of the top-level HOL directory
#
# Theory       = the directory where built-in .th files will be put.
#
# Library      = the absolute pathname of the library directory
#
# Help 	       = the absolute pathnames to the HOL help directories
#
# Hol          = the HOL system to be used for building libraries
#               (normally hol)
#
# LispDir      = the directory where the Lisp sources are
#               (used for Library/eval and Library/prog_logic88)
#
# Version      = the version number of HOL.  This is incremented by 
#		 0.01 whenever a change is made, and incremented by 
#		 1.0 for a major new release.
# ExeName      = the executable file name to be built
# =====================================================================

# *********************************************************************
# To install HOL, edit the following definitions of:
#     LispType, Obj, Lisp, Liszt, LisztComm, and HOLdir 
# *********************************************************************

SHELL=/bin/sh

LispType=cl
Obj=o
Lisp=akcl
Liszt=
LisztComm=
Allegro=(set-case-mode :case-insensitive-upper)
AllegroV4.0= $(Allegro) (setq *cltl1-in-package-compatibility-p* t) (setq comp:*cltl1-compile-file-toplevel-compatibility-p* t)

AllegroV4.1= $(AllegroV4.0) (setq *enable-package-locked-errors* nil)
AllegroStuff= (progn () $(AllegroV4.1))

HOLdir=/usr/local/hol
Theory=$(HOLdir)/theories
Library=$(HOLdir)/Library
Help=$(HOLdir)/help/ENTRIES/

Hol=hol
LispDir=${HOLdir}/lisp

ExeName = hol
Version = 2.02 (SUN4/AKCL)

# =====================================================================
# Default (from Phil Windley)
# =====================================================================

default:
	@echo "Type \"make all\" to make hol and the Library,
	@echo "\"make hol\" to just make hol, or \"make clean\"
	@echo "to delete object files."

# =====================================================================
# Cleaning functions
# =====================================================================

clean:
	/bin/rm -f ml/*_ml.o ml/*_ml.l ml/site.ml lisp/*.$(Obj)
	/bin/rm -f hol-lcf basic-hol hol
	$(MAKE) clean-library
	@echo "=======> all hol and lisp object code deleted"

clobber:
	/bin/rm -f ml/*_ml.o ml/*_ml.l ml/site.ml lisp/*.$(Obj)
	/bin/rm -f ${Theory}/*.th hol-lcf basic-hol hol
	$(MAKE) clobber-library
	@echo "=======> all object code and theory files deleted"

clean-library:
	(cd ${Library}; $(MAKE) Obj=${Obj} clean; cd ..)

clobber-library:
	(cd ${Library}; $(MAKE) Obj=${Obj} clobber; cd ..)


# =====================================================================
# MAKEFILE ENTRIES FOR HOL
# =====================================================================

# ---------------------------------------------------------------------
# Macros: 
#
#   HolMl = the ml object code that hol depends on
# ---------------------------------------------------------------------

HolMl=ml/load_thms.ml ml/numconv_ml.o ml/tydefs_ml.o ml/ind_ml.o\
      ml/prim_rec_ml.o ml/tyfns_ml.o ml/num_ml.o ml/list_ml.o\
      ml/lib_loader_ml.o

# ---------------------------------------------------------------------
# main entry for hol
# ---------------------------------------------------------------------

hol: basic-hol ${Theory}/HOL.th $(HolMl) lisp/banner.$(Obj) lisp/akcl.l
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `HOL`;;'\
	     'loadf `ml/load_thms`;;'\
	     'loadf `ml/lib_loader`;;'\
	     'loadf `ml/numconv`;;'\
	     'loadf `ml/tydefs`;;'\
	     'loadf `ml/ind`;;'\
	     'loadf `ml/prim_rec`;;'\
	     'loadf `ml/tyfns`;;'\
	     'loadf `ml/num`;;'\
	     'loadf `ml/list`;;'\
	     'map delete_cache [`arithmetic`;`sum`;`list`];;'\
	     'map delete_cache [`tree`;`ltree`;`prim_rec`];;'\
	     'lisp `(load "lisp/banner")`;;'\
	     'lisp `(setq %system-name "HOL")`;;'\
	     'lisp `(setq %hol-dir "$(HOLdir)")`;;'\
	     'lisp `(setq %lib-dir "$(Library)")`;;'\
	     'lisp `(setq %liszt "$(LisztComm)")`;;'\
	     'lisp `(setq %version "$(Version)")`;;'\
	     'set_flag(`abort_when_fail`,false);;'\
	     'set_search_path[``; `~/`; `${Theory}/`];;'\
	     'set_help_search_path (words `$(Help)`);;'\
	     'set_library_search_path [`${Library}/`];;'\
	     'lisp `(load "lisp/akcl.l")`;;'\
	     'lisp `(setup)`;;'\
	     'save `${ExeName}`;;'\
	     'set_thm_count 0;;'\
	     'quit();;'\
	     | basic-hol
	make permissions
	@echo "=======> hol88 version $(Version) made"

library: $(ExeName) 
	date
	(cd ${Library}; $(MAKE) LispType=${LispType}\
                             Obj=${Obj}\
                             Lisp=${Lisp}\
                             Liszt=${Liszt}\
                             LispDir=${LispDir}\
                             Hol=${HOLdir}/${ExeName} library; cd ..)
	date

all:
	(date; $(MAKE) hol; date; $(MAKE) library; date)
	make permissions
	@echo "=======> hol Version $(Version) and libraries made"


# ---------------------------------------------------------------------
# Entry for changing permissions.
#
# Macros:
#
#  directories:          Dperm  =  drwxrwxr-x  = 775
#  text files:           Tperm  =  -rw-rw-r--  = 664
#  executable files:     Eperm  =  -rwxrwxr-x  = 775
#
#                        Exec = those files to be "executable"
#
# ---------------------------------------------------------------------

Dperm=775
Tperm=664
Eperm=775

Exec=hol hol-lcf basic-hol Manual/LaTeX/makeindex\
     Manual/LaTeX/makeindex.bin/*/makeindex\
     Manual/Reference/bin/mktex Manual/Reference/bin/typecheck

permissions:
	find . \( -type d -user $(USER) -exec chmod $(Dperm) {} \; \) -o\
	       \( -type f -user $(USER) -exec chmod $(Tperm) {} \; \)
	@for f in $(Exec) ; do\
	  ( if [ -f $$f ]; then\
	    find $$f \( -user $(USER) \) -exec chmod $(Eperm) {} \; ;fi) ; \
	done


# ---------------------------------------------------------------------
# makefile entries for hol system ml code
# ---------------------------------------------------------------------

ml/numconv_ml.o: basic-hol ${Theory}/num.th ml/numconv.ml 
	echo 'load_theory `num`;;'\
	     'compilet `ml/numconv`;;'\
	     'quit();;'\
	| basic-hol

ml/lib_loader_ml.o: basic-hol ml/lib_loader.ml 
	echo 'compilet `ml/lib_loader`;;'\
	     'quit();;'\
	| basic-hol

ml/tydefs_ml.o: basic-hol ${Theory}/HOL.th ml/load_thms.ml ml/tydefs.ml 
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `HOL`;;'\
	     'compilet `ml/tydefs`;;'\
	     'quit();;'\
	| basic-hol

ml/ind_ml.o: basic-hol ml/ind.ml 
	echo 'compilet `ml/ind`;;'\
	     'quit();;'\
	| basic-hol

ml/prim_rec_ml.o: basic-hol ml/prim_rec.ml 
	echo 'compilet `ml/prim_rec`;;'\
	     'quit();;'\
	| basic-hol

ml/tyfns_ml.o: basic-hol ${Theory}/HOL.th ml/prim_rec_ml.o ml/load_thms.ml ml/tyfns.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `HOL`;;'\
	     'compilet `ml/tyfns`;;'\
	     'quit();;'\
	| basic-hol

ml/num_ml.o: basic-hol ${Theory}/HOL.th ml/ind_ml.o ml/prim_rec_ml.o\
	     ml/num.ml ml/numconv_ml.o
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `HOL`;;'\
	     'compilet `ml/num`;;'\
	     'quit();;'\
	| basic-hol

ml/list_ml.o: basic-hol ${Theory}/HOL.th ml/ind_ml.o ml/prim_rec_ml.o\
	      ml/numconv_ml.o ml/list.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `HOL`;;'\
	     'compilet `ml/list`;;'\
	     'quit();;'\
	| basic-hol

# ---------------------------------------------------------------------
# HOL built-in theories
#
# Note: the theory files really depend on the code used to make them.
# E.g. basic-hol, and various ml code.  But these dependencies are not 
# reflected in the entries below.  And only uncompiled ML is used.
# ---------------------------------------------------------------------

${Theory}/one.th: theories/mk_one.ml 
	cd ${Theory}; rm -f one.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_one.ml;\
	cd ${HOLdir}
	@echo "=======> theory one built"

${Theory}/combin.th: theories/mk_combin.ml 
	cd ${Theory}; rm -f combin.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_combin.ml;\
	cd ${HOLdir}
	@echo "=======> theory combin built"

${Theory}/fun.th:	theories/mk_fun.ml 
	cd ${Theory}; rm -f fun.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_fun.ml;\
	cd ${HOLdir}
	@echo "=======> theory fun built"

${Theory}/sum.th: theories/mk_sum.ml ${Theory}/combin.th
	cd ${Theory}; rm -f sum.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_sum.ml;\
	cd ${HOLdir}
	@echo "=======> theory sum built"

${Theory}/num.th: theories/mk_num.ml 
	cd ${Theory}; rm -f num.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_num.ml;\
	cd ${HOLdir}
	@echo "=======> theory num built"

${Theory}/prim_rec.th: theories/mk_prim_rec.ml ${Theory}/num.th
	cd ${Theory}; rm -f prim_rec.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_prim_rec.ml;\
	cd ${HOLdir}
	@echo "=======> theory prim_rec built"

${Theory}/arithmetic.th: ${Theory}/mk_arith.ml ${Theory}/mk_arith_thms.ml\
	  		 ${Theory}/prim_rec.th ${Theory}/fun.th
	cd ${Theory}; rm -f arithmetic.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_arith.ml;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_arith_thms.ml;\
	cd ${HOLdir}
	@echo "=======> theory arithmetic built"

${Theory}/list.th: ${Theory}/mk_list.ml ${Theory}/mk_list_defs.ml \
		${Theory}/mk_list_thms.ml ${Theory}/mk_list_thm2.ml\
		${Theory}/combin.th ${Theory}/arithmetic.th
	cd ${Theory}; rm -f list.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_list.ml;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_list_defs.ml;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_list_thms.ml;\
	cd ${HOLdir}
	@echo "=======> theory list built"

${Theory}/tree.th: theories/mk_tree.ml ${Theory}/list.th
	cd ${Theory}; rm -f tree.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_tree.ml;\
	cd ${HOLdir}
	@echo "=======> theory tree built"

${Theory}/ltree.th: theories/mk_ltree.ml ${Theory}/tree.th ${Theory}/combin.th
	cd ${Theory}; rm -f ltree.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_ltree.ml;\
	cd ${HOLdir}
	@echo "=======> theory ltree built"

${Theory}/tydefs.th: theories/mk_tydefs.ml ${Theory}/ltree.th 
	cd ${Theory}; rm -f tydefs.th;\
	${HOLdir}/basic-hol < ${HOLdir}/theories/mk_tydefs.ml;\
	cd ${HOLdir}
	@echo "=======> theory tydefs built"

${Theory}/HOL.th: ${Theory}/tydefs.th ${Theory}/sum.th ${Theory}/one.th 
	cd ${Theory}; rm -f HOL.th;\
	echo 'new_theory `HOL`;;'\
	     'map new_parent [`one`;`sum`;`tydefs`];;'\
	     'close_theory();;'\
	     'quit();;'\
	     | ${HOLdir}/basic-hol;\
	cd ${HOLdir}
	@echo "=======> theory HOL built"


# =====================================================================
# MAKEFILE ENTRIES FOR BASIC-HOL
# =====================================================================

# ---------------------------------------------------------------------
# Macros: 
#
#   BasicHolLisp = all the lisp object code that hol-lcf depends on
#
#   BasicHolMl = the ml object (and source) code that hol-lcf depends on
# ---------------------------------------------------------------------


#    parse_as_binder removed from this list [TFM 92.10.01]

BasicHolLisp=lisp/genfns.$(Obj) lisp/gnt.$(Obj)\
	     lisp/hol-pars.$(Obj) lisp/parslist.$(Obj)\
	     lisp/parslet.$(Obj) lisp/constp.$(Obj)\
	     lisp/hol-writ.$(Obj) lisp/mk_pp_thm.$(Obj)

BasicHolMl=ml/genfns_ml.o ml/hol-syn_ml.o ml/hol-rule_ml.o\
	   ml/hol-drule_ml.o ml/drul_ml.o ml/hol-thyfn_ml.o\
	   ml/tacticals_ml.o ml/tacont_ml.o ml/tactics_ml.o\
	   ml/conv_ml.o ml/hol-net_ml.o ml/rewrite_ml.o\
	   ml/resolve_ml.o ml/goals_ml.o ml/stack_ml.o\
	   ml/abs-rep_ml.o

# ---------------------------------------------------------------------
# main entry for basic-hol
#
# NOTE: the order of dependencies here is important.  BasicHolLisp must
# be compiled before rebuilding BASIC-HOL.th.  This is because the 
# basic-hol theories are not stated in the Makefile made to depend on 
# code.  See the note below about the basic-hol theories.
# ---------------------------------------------------------------------

basic-hol: hol-lcf $(BasicHolLisp) ${Theory}/BASIC-HOL.th $(BasicHolMl)
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `BASIC-HOL`;;'\
	     'loadf `ml/hol-in-out`;;'\
	     'loadf `ml/hol-rule`;;'\
	     'loadf `ml/hol-drule`;;'\
	     'loadf `ml/drul`;;'\
	     'loadf `ml/tacticals`;;'\
	     'loadf `ml/tacont`;;'\
	     'loadf `ml/tactics`;;'\
	     'loadf `ml/conv`;;'\
	     'loadf `ml/hol-net`;;'\
	     'loadf `ml/rewrite`;;'\
	     'loadf `ml/resolve`;;'\
	     'loadf `ml/hol-thyfn`;;'\
	     'loadf `ml/goals`;;'\
	     'loadf `ml/stack`;;'\
	     'loadf `ml/abs-rep`;;'\
             'activate_binders `bool`;;'\
	     'lisp `(setq %liszt "$(LisztComm)")`;;'\
	     'lisp `(setq %version "$(Version)")`;;'\
	     'lisp `(setq %system-name "BASIC-HOL")`;;'\
	     'lisp `(setup)`;;'\
	     'save `basic-hol`;;'\
	     'quit();;'\
	     | hol-lcf
	@echo "=======> basic-hol88 made"

# ---------------------------------------------------------------------
# makefile entries for compiling the ML code of basic-hol.
# ---------------------------------------------------------------------

ml/hol-in-out_ml.o: hol-lcf
	echo 'compilet `ml/hol-in-out`;;'\
	     'quit();;'\
	     | hol-lcf

ml/genfns_ml.o: hol-lcf ml/genfns.ml 
	echo 'compilet `ml/genfns`;;'\
	     'quit();;'\
	     | hol-lcf

ml/hol-syn_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
		 ml/hol-syn.ml 
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'lisp `(load "lisp/genfns")`;;'\
	     'lisp `(load "lisp/gnt")`;;'\
	     'lisp `(load "lisp/hol-pars")`;;'\
	     'lisp `(load "lisp/parslist")`;;'\
	     'lisp `(load "lisp/parslet")`;;'\
	     'lisp `(load "lisp/constp")`;;'\
	     'lisp `(load "lisp/hol-writ")`;;'\
	     'lisp `(load "lisp/mk_pp_thm")`;;'\
	     'compilet `ml/hol-syn`;;'\
	     'quit();;'\
	     | hol-lcf

ml/hol-rule_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
		  ml/hol-syn_ml.o ml/hol-rule.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/hol-rule`;;'\
	     'quit();;'\
	     | hol-lcf

ml/hol-drule_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
		   ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule.ml 
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/hol-drule`;;'\
	     'quit();;'\
	     | hol-lcf

ml/drul_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	      ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	      ml/drul.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/drul`;;'\
	     'quit();;'\
	     | hol-lcf

ml/hol-thyfn_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	           ml/hol-syn_ml.o ml/hol-thyfn.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/hol-thyfn`;;'\
	     'quit();;'\
	     | hol-lcf

ml/tacticals_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	           ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	           ml/drul_ml.o ml/tacticals.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/tacticals`;;'\
	     'quit();;'\
	     | hol-lcf

ml/tacont_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	        ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	        ml/drul_ml.o ml/tacticals_ml.o ml/tacont.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/tacont`;;'\
	     'quit();;'\
	     | hol-lcf

ml/tactics_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	         ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	         ml/drul_ml.o ml/tacticals_ml.o ml/tacont_ml.o\
		 ml/tactics.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/tactics`;;'\
	     'quit();;'\
	     | hol-lcf

ml/conv_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	      ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	      ml/drul_ml.o ml/tacticals_ml.o ml/conv.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/conv`;;'\
	     'quit();;'\
	     | hol-lcf


ml/hol-net_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	         ml/hol-syn_ml.o ml/hol-net.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/hol-net`;;'\
	     'quit();;'\
	     | hol-lcf

ml/rewrite_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	         ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	         ml/drul_ml.o ml/tacticals_ml.o ml/conv_ml.o\
	         ml/hol-net_ml.o ml/rewrite.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/rewrite`;;'\
	     'quit();;'\
	     | hol-lcf

ml/resolve_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	         ml/hol-syn_ml.o ml/hol-rule_ml.o ml/hol-drule_ml.o\
	         ml/drul_ml.o ml/tacticals_ml.o ml/tacont_ml.o\
		 ml/tactics_ml.o ml/conv_ml.o ml/resolve.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/resolve`;;'\
	     'quit();;'\
	     | hol-lcf

ml/goals_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	         ml/hol-syn_ml.o ml/hol-thyfn_ml.o ml/hol-rule_ml.o\
		 ml/hol-drule_ml.o ml/drul_ml.o ml/tacticals_ml.o ml/goals.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/goals`;;'\
	     'quit();;'\
	     | hol-lcf

ml/stack_ml.o: hol-lcf ${Theory}/bool.th $(BasicHolLisp) ml/genfns_ml.o\
	         ml/hol-syn_ml.o ml/hol-thyfn_ml.o ml/hol-rule_ml.o\
		 ml/hol-drule_ml.o ml/drul_ml.o ml/tacticals_ml.o\
		 ml/goals_ml.o ml/stack.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `bool`;;'\
	     'compilet `ml/stack`;;'\
	     'quit();;'\
	     | hol-lcf

ml/abs-rep_ml.o: hol-lcf ${Theory}/BASIC-HOL.th $(BasicHolLisp)\
		 ml/genfns_ml.o ml/hol-syn_ml.o ml/hol-rule_ml.o\
		 ml/hol-drule_ml.o ml/drul_ml.o ml/abs-rep.ml
	echo 'set_search_path[``; `${Theory}/`];;'\
	     'load_theory `BASIC-HOL`;;'\
	     'compilet `ml/abs-rep`;;'\
	     'quit();;'\
	     | hol-lcf

# ---------------------------------------------------------------------
# Makefile entries for the built-in theories of basic-hol.
#
# NOTE: Strictly speaking, these theories depend on the code that is 
# used to create them.  Thus, for example, they all depend on hol-lcf.
# In addition, they depend on BasicHolLisp and (sometimes) BasicHolMl.
# But these dependencies are not reflected in the entries below.  
# This means the theories will not get rebuilt if only hol-lcf
# changes, or some BasicHolLisp or BasicHolMl code changes.
# But the theories will be recreated if they are missing, or the 
# files that create the theories are changed, or the parent 
# theories are changed.  Note that BasicHolLisp must be compiled
# before these theories are made.
#
# The entries below ensure that if a BasicHolMl file is used to create
# a theory, the SOURCE is loaded rather than the OBJECT.  This guards
# against the case where one (but not all) object files are missing.
# ---------------------------------------------------------------------

${Theory}/PPLAMB.th: theories/mk_PPLAMB.ml 
	cd ${Theory}; rm -f PPLAMB.th;\
	${HOLdir}/hol-lcf < ${HOLdir}/theories/mk_PPLAMB.ml;\
	cd ${HOLdir}
	@echo "=======> theory PPLAMB built"

${Theory}/bool.th: theories/mk_bool.ml ${Theory}/PPLAMB.th 
	-@if [ -f ml/genfns_ml.o ]; then\
	    mv -f ml/genfns_ml.o ml/genfns_ml.o.save;fi
	-@if [ -f ml/hol-syn_ml.o ]; then\
	    mv -f ml/hol-syn_ml.o ml/hol-syn_ml.o.save;fi
	cd ${Theory}; rm -f bool.th;\
	${HOLdir}/hol-lcf < ${HOLdir}/theories/mk_bool.ml;\
	cd ${HOLdir}
	-@if [ -f ml/genfns_ml.o.save ]; then\
	    mv -f ml/genfns_ml.o.save ml/genfns_ml.o;fi
	-@if [ -f ml/hol-syn_ml.o.save ]; then\
	    mv -f ml/hol-syn_ml.o.save ml/hol-syn_ml.o;fi
	@echo "=======> theory bool built"

${Theory}/ind.th: theories/mk_ind.ml ${Theory}/bool.th 
	-@if [ -f ml/genfns_ml.o ]; then\
	    mv -f ml/genfns_ml.o ml/genfns_ml.o.save;fi
	-@if [ -f ml/hol-syn_ml.o ]; then\
	    mv -f ml/hol-syn_ml.o ml/hol-syn_ml.o.save;fi
	cd ${Theory}; rm -f ind.th;\
	${HOLdir}/hol-lcf < ${HOLdir}/theories/mk_ind.ml;\
	cd ${HOLdir}
	-@if [ -f ml/genfns_ml.o.save ]; then\
	    mv -f ml/genfns_ml.o.save ml/genfns_ml.o;fi
	-@if [ -f ml/hol-syn_ml.o.save ]; then\
	    mv -f ml/hol-syn_ml.o.save ml/hol-syn_ml.o;fi
	@echo "=======> theory ind built"

${Theory}/BASIC-HOL.th: theories/mk_BASIC-HOL.ml ${Theory}/ind.th 
	-@if [ -f ml/genfns_ml.o ]; then\
	    mv -f ml/genfns_ml.o ml/genfns_ml.o.save;fi
	-@if [ -f ml/hol-syn_ml.o ]; then\
	    mv -f ml/hol-syn_ml.o ml/hol-syn_ml.o.save;fi
	-@if [ -f ml/hol-rule_ml.o ]; then\
	    mv -f ml/hol-rule_ml.o ml/hol-rule_ml.o.save;fi
	-@if [ -f ml/hol-drule_ml.o ]; then\
	    mv -f ml/hol-drule_ml.o ml/hol-drule_ml.o.save;fi
	-@if [ -f ml/hol-thyfn_ml.o ]; then\
	    mv -f ml/hol-thyfn_ml.o ml/hol-thyfn_ml.o.save;fi
	cd ${Theory}; rm -f BASIC-HOL.th;\
	${HOLdir}/hol-lcf < ${HOLdir}/theories/mk_BASIC-HOL.ml;\
	cd ${HOLdir}
	-@if [ -f ml/genfns_ml.o.save ]; then\
	    mv -f ml/genfns_ml.o.save ml/genfns_ml.o;fi
	-@if [ -f ml/hol-syn_ml.o.save ]; then\
	    mv -f ml/hol-syn_ml.o.save ml/hol-syn_ml.o;fi
	-@if [ -f ml/hol-rule_ml.o.save ]; then\
	    mv -f ml/hol-rule_ml.o.save ml/hol-rule_ml.o;fi
	-@if [ -f ml/hol-drule_ml.o.save ]; then\
	    mv -f ml/hol-drule_ml.o.save ml/hol-drule_ml.o;fi
	-@if [ -f ml/hol-thyfn_ml.o.save ]; then\
	    mv -f ml/hol-thyfn_ml.o.save ml/hol-thyfn_ml.o;fi
	@echo "=======> theory BASIC-HOL built"

# =====================================================================
# MAKEFILE ENTRIES FOR HOL-LCF
# =====================================================================

# ---------------------------------------------------------------------
# Macros: 
#
#   HolLcfLisp = all the lisp object code that hol-lcf depends on
#
#   HolLcfMl = the ml object (and source) code that hol-lcf depends on
# ---------------------------------------------------------------------

HolLcfLisp=lisp/f-$(LispType).$(Obj) lisp/f-system.$(Obj)\
	   lisp/mk-ml.$(Obj) lisp/mk-hol-lcf.$(Obj)\
	   lisp/f-site.$(Obj) lisp/f-gp.$(Obj)\
	   lisp/f-parser.$(Obj) lisp/f-parsml.$(Obj)\
	   lisp/f-mlprin.$(Obj) lisp/f-typeml.$(Obj)\
	   lisp/f-dml.$(Obj) lisp/f-format.$(Obj)\
	   lisp/f-tran.$(Obj) lisp/f-iox-stand.$(Obj)\
	   lisp/f-writml.$(Obj) lisp/f-tml.$(Obj)\
	   lisp/f-lis.$(Obj)\
	   lisp/f-ol-rec.$(Obj) lisp/f-parsol.$(Obj)\
	   lisp/f-typeol.$(Obj) lisp/f-help.$(Obj)\
	   lisp/f-writol.$(Obj) lisp/f-thyfns.$(Obj)\
	   lisp/f-freadth.$(Obj) \
	   lisp/f-ol-syntax.$(Obj) lisp/f-subst.$(Obj)\
	   lisp/f-inst.$(Obj) lisp/f-simpl.$(Obj) lisp/f-ol-net.$(Obj)

HolLcfMl=ml/ml-curry_ml.o ml/lis_ml.o ml/gen_ml.o ml/site_ml.o ml/killpp.ml

# ---------------------------------------------------------------------
# main entry for hol-lcf
# ---------------------------------------------------------------------

hol-lcf: $(HolLcfLisp) $(HolLcfMl)
	echo '#+allegro $(AllegroStuff)'\
	     '(load "lisp/mk-ml")'\
	     '(load "lisp/mk-hol-lcf")'\
	     '(setq %version "$(Version)")'\
	     '(set-make)'\
	     '(tml)'\
	     'load(`ml/site`,false);;'\
	     'load(`ml/ml-curry`,false);;'\
	     'load(`ml/lis`,false);;'\
	     'load(`ml/gen`,false);;'\
	     'load(`ml/killpp`,false);;'\
	     'lisp `(setq %system-name "HOL-LCF")`;;'\
	     'lisp `(setq %liszt "$(LisztComm)")`;;'\
	     'lisp `(setup)`;;'\
	     'save `hol-lcf`;;'\
	     'quit();;'\
	     | $(Lisp)
	@echo "=======> hol-lcf made"

# =====================================================================
# Makefile entries for compiled ml code that is part of hol-lcf
#
# These depend on the hol-lcf lisp object codes.
# =====================================================================

ml/ml-curry_ml.o: ml/ml-curry.ml $(HolLcfLisp)
	echo '#+allegro $(AllegroStuff)'\
	     '(load "lisp/mk-ml")'\
	     '(load "lisp/mk-hol-lcf")'\
	     '(setq %system-name "HOL-LCF")'\
	     '(setq %liszt "$(LisztComm)")'\
	     '(setq %version "$(Version)")'\
	     '(set-make)'\
	     '(tml)'\
	     'compile(`ml/ml-curry`,true);;'\
	     'quit();;'\
	     | $(Lisp)

ml/lis_ml.o: ml/lis.ml ml/ml-curry_ml.o $(HolLcfLisp)
	echo '#+allegro $(AllegroStuff)'\
	     '(load "lisp/mk-ml")'\
	     '(load "lisp/mk-hol-lcf")'\
	     '(setq %system-name "HOL-LCF")'\
	     '(setq %liszt "$(LisztComm)")'\
	     '(setq %version "$(Version)")'\
	     '(set-make)'\
	     '(tml)'\
	     'load(`ml/ml-curry`,false);;'\
	     'compile(`ml/lis`,true);;'\
	     'quit();;'\
	     | $(Lisp)

ml/gen_ml.o: ml/gen.ml ml/ml-curry_ml.o ml/lis_ml.o $(HolLcfLisp)
	echo '#+allegro $(AllegroStuff)'\
	     '(load "lisp/mk-ml")'\
	     '(load "lisp/mk-hol-lcf")'\
	     '(setq %system-name "HOL-LCF")'\
	     '(setq %liszt "$(LisztComm)")'\
	     '(setq %version "$(Version)")'\
	     '(set-make)'\
	     '(tml)'\
	     'load(`ml/ml-curry`,false);;'\
	     'load(`ml/lis`,false);;'\
	     'compile(`ml/gen`,true);;'\
	     'quit();;'\
	     | $(Lisp)

ml/site_ml.o: ml/site.ml $(HolLcfLisp)
	echo '#+allegro $(AllegroStuff)'\
	     '(load "lisp/mk-ml")'\
	     '(load "lisp/mk-hol-lcf")'\
	     '(setq %system-name "HOL-LCF")'\
	     '(setq %liszt "$(LisztComm)")'\
	     '(setq %version "$(Version)")'\
	     '(set-make)'\
	     '(tml)'\
	     'compile(`ml/site`,true);;'\
	     'quit();;'\
	     | $(Lisp)

# note that this is new.  ml/site.ml.orig *must* exist
# sed substitution for theories_dir_pathname removed [TFM 91.02.24]
ml/site.ml: ml/site.ml.orig
	sed -e "s;ml/;${HOLdir}/ml/;g" \
	    -e "s;lisp/;${HOLdir}/lisp/;g" ml/site.ml.orig > ml/site.ml

# =====================================================================
# MAKEFILE ENTRIES FOR ALL THE LISP CODE 
# =====================================================================

HolLispBasic=lisp/f-$(LispType).$(Obj)


lisp/f-$(LispType).$(Obj): lisp/f-$(LispType).l
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(compile-file "lisp/f-cl.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-franz; fi
 
lisp/f-constants.$(Obj): lisp/f-constants.l $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-constants.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-constants; fi

lisp/f-dml.$(Obj): lisp/f-dml.l lisp/f-macro.$(Obj) lisp/f-constants.$(Obj)\
	           $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-dml.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-dml; fi

lisp/f-format.$(Obj): lisp/f-format.l lisp/f-macro.$(Obj)\
	              lisp/f-constants.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-format.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-format; fi

lisp/f-gp.$(Obj): lisp/f-gp.l lisp/f-constants.$(Obj) lisp/f-macro.$(Obj)\
	          $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-gp.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-gp; fi

lisp/f-help.$(Obj): lisp/f-help.l lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-help.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-help; fi

lisp/f-inst.$(Obj): lisp/f-inst.l lisp/f-constants.$(Obj)\
	            lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-inst.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-inst; fi

lisp/f-iox-stand.$(Obj): lisp/f-iox-stand.l lisp/f-constants.$(Obj)\
	                 lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-iox-stand.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-iox-stand; fi

lisp/f-lis.$(Obj): lisp/f-lis.l lisp/f-constants.$(Obj)\
	           lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-lis.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-lis; fi

lisp/f-macro.$(Obj): lisp/f-macro.l $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-macro.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-macro; fi

lisp/f-mlprin.$(Obj): lisp/f-mlprin.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-mlprin.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-mlprin; fi

# ---------------------------------------------------------------------
#lisp/f-obj.$(Obj): lisp/f-obj.l lisp/f-macro.$(Obj) $(HolLispBasic)
#	if [ $(LispType) = cl ]; then\
#	  echo '#+allegro $(AllegroStuff)'\
#	       '(load "lisp/f-cl") (compile-file "lisp/f-obj.l") (quit)'\
#	       | $(Lisp); else\
#	  $(Liszt) lisp/f-obj; fi
# ---------------------------------------------------------------------

lisp/f-ol-net.$(Obj): lisp/f-ol-net.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-ol-net.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-ol-net; fi

lisp/f-ol-rec.$(Obj): lisp/f-ol-rec.l $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-ol-rec.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-ol-rec; fi

lisp/f-ol-syntax.$(Obj): lisp/f-ol-syntax.l lisp/f-constants.$(Obj)\
	                 lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj)\
	                 $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-ol-syntax.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-ol-syntax; fi

lisp/f-parser.$(Obj): lisp/f-parser.l lisp/f-constants.$(Obj)\
                      lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-parser.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-parser; fi

lisp/f-parsml.$(Obj): lisp/f-parsml.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-parsml.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-parsml; fi

lisp/f-parsol.$(Obj): lisp/f-parsol.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-parsol.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-parsol; fi

lisp/f-simpl.$(Obj): lisp/f-simpl.l lisp/f-constants.$(Obj)\
	             lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-simpl.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-simpl; fi

lisp/f-site.$(Obj): lisp/f-site.l lisp/f-constants.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-site.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-site; fi

lisp/f-subst.$(Obj): lisp/f-subst.l lisp/f-constants.$(Obj)\
	             lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-subst.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-subst; fi

lisp/f-thyfns.$(Obj): lisp/f-thyfns.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-thyfns.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-thyfns; fi

lisp/f-freadth.$(Obj): lisp/f-freadth.l lisp/f-macro.$(Obj)\
	               $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-freadth.l") (quit)'\
	       | $(Lisp); else\
	  touch lisp/f-freadth.$(Obj); fi

lisp/f-tml.$(Obj): lisp/f-tml.l lisp/f-constants.$(Obj)\
	           lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-tml.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-tml; fi

lisp/f-tran.$(Obj): lisp/f-tran.l lisp/f-constants.$(Obj)\
	            lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-tran.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-tran; fi

lisp/f-typeml.$(Obj): lisp/f-typeml.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-typeml.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-typeml; fi

lisp/f-typeol.$(Obj): lisp/f-typeol.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-typeol.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-typeol; fi

lisp/f-system.$(Obj): lisp/f-system.l lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-system.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-system; fi

lisp/f-writml.$(Obj): lisp/f-writml.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-writml.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-writml; fi

lisp/f-writol.$(Obj): lisp/f-writol.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj)\
	              lisp/genmacs.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/f-writol.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/f-writol; fi

lisp/constp.$(Obj): lisp/constp.l $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/constp.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/constp; fi

lisp/genfns.$(Obj): lisp/genfns.l lisp/f-macro.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/genfns.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/genfns; fi

lisp/genmacs.$(Obj): lisp/genmacs.l lisp/f-macro.$(Obj)\
	             lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/genmacs.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/genmacs; fi

lisp/gnt.$(Obj): lisp/gnt.l lisp/f-constants.$(Obj) lisp/f-macro.$(Obj)\
	         lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/gnt.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/gnt; fi

lisp/hol-pars.$(Obj): lisp/hol-pars.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj)\
	              lisp/genmacs.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/hol-pars.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/hol-pars; fi

lisp/hol-writ.$(Obj): lisp/hol-writ.l lisp/f-constants.$(Obj)\
	              lisp/f-macro.$(Obj) lisp/f-ol-rec.$(Obj)\
	              lisp/genmacs.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/hol-writ.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/hol-writ; fi

lisp/mk-hol-lcf.$(Obj): lisp/mk-hol-lcf.l $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/mk-hol-lcf.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/mk-hol-lcf; fi

lisp/mk-ml.$(Obj): lisp/mk-ml.l lisp/f-macro.$(Obj) lisp/f-help.$(Obj)\
	           lisp/f-ol-rec.$(Obj) lisp/genmacs.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/mk-ml.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/mk-ml; fi

lisp/mk_pp_thm.$(Obj): lisp/mk_pp_thm.l lisp/f-macro.$(Obj)\
	               lisp/f-ol-rec.$(Obj) lisp/genmacs.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/mk_pp_thm.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/mk_pp_thm; fi

# No longer used. [TFM 91.10.01 for HOL88 2.01]
# lisp/parse_as_binder.$(Obj): lisp/parse_as_binder.l lisp/f-macro.$(Obj)\
#	                     $(HolLispBasic)
#	if [ $(LispType) = cl ]; then\
#	  echo '#+allegro $(AllegroStuff)'\
#	       '(load "lisp/f-cl") (compile-file "lisp/parse_as_binder.l") (quit)'\
#	       | $(Lisp); else\
#	  $(Liszt) lisp/parse_as_binder; fi

lisp/parslet.$(Obj): lisp/parslet.l lisp/f-constants.$(Obj) lisp/f-macro.$(Obj)\
	             lisp/f-ol-rec.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/parslet.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/parslet; fi

lisp/parslist.$(Obj): lisp/parslist.l lisp/f-constants.$(Obj) $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/parslist.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/parslist; fi

lisp/banner.$(Obj): $(HolLispBasic)
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro $(AllegroStuff)'\
	       '(load "lisp/f-cl") (compile-file "lisp/banner.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) lisp/banner; fi


