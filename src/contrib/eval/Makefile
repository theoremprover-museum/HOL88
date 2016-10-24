# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: eval
#
# =====================================================================

# =====================================================================
# MAIN ENTRIES:
#
#    make all	    : create theories and compile code
#
#    make clean	    : remove only compiled code
#	
#    make clobber   : remove both theories and compiled code
#
# ---------------------------------------------------------------------
# MACROS:
#
#    Hol         : the pathname of the version of hol used
#
#    LispType    : the type of the lisp system, cl or franz
#
#    Obj         : the default filename extension for compiled lisp files,
#		   for franz it is o, for common lisp it depends on the 
#		   implementation
#
#    Lisp        : the pathname of the common lisp system (not used for franz)
#
#    Liszt       : the pathname of the franz lisp compiler (not used for cl)
#
#    LispDir     : the pathname of the hol lisp directory
# =====================================================================

Hol=../../hol
LispType=franz
Obj=o
Lisp=../../../akcl/saved_kcl_sun3
Liszt=/usr/groups/hol/franz/bin/liszt
LispDir=../../lisp

Allegro_Case=:case-insensitive-upper

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o *_ml.l *.${Obj}
	@echo "===> library eval: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.${Obj}
	@echo "===> library eval: all object code deleted"


# =====================================================================
# Entries for individual files.
# =====================================================================

eval.$(Obj): eval.l
	rm -f f-macro.$(Obj); ln -s $(LispDir)/f-macro.$(Obj) .
	rm -f f-ol-rec.$(Obj); ln -s $(LispDir)/f-ol-rec.$(Obj) .
	rm -f genmacs.$(Obj); ln -s $(LispDir)/genmacs.$(Obj) .
	rm -f f-$(LispType).$(Obj); ln -s $(LispDir)/f-$(LispType).$(Obj) .
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro (set-case-mode $(Allegro_Case))'\
	       '(load "f-cl") (compile-file "eval.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) eval.l; fi

dml-eval.$(Obj): dml-eval.l
	rm -f f-macro.$(Obj); ln -s $(LispDir)/f-macro.$(Obj) .
	rm -f f-ol-rec.$(Obj); ln -s $(LispDir)/f-ol-rec.$(Obj) .
	rm -f genmacs.$(Obj); ln -s $(LispDir)/genmacs.$(Obj) .
	rm -f f-$(LispType).$(Obj); ln -s $(LispDir)/f-$(LispType).$(Obj) .
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro (set-case-mode $(Allegro_Case))'\
	       '(load "f-cl") (compile-file "dml-eval.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) dml-eval.l; fi

wordn_ml.o: wordn.ml eval.$(Obj) dml-eval.$(Obj)
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'lisp `(load "eval")`;;'\
	     'lisp `(load "dml-eval")`;;'\
	     'compilet `wordn`;;'\
	     'quit();;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: eval.$(Obj) dml-eval.$(Obj) wordn_ml.o
	@echo "===> library eval rebuilt"
