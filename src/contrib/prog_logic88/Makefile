# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: prog_logic88
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : create theories and compile code
#
# make clean	    : remove theories and compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# LispType  : the type of the lisp system, cl or franz
#
# Obj       : the default filename extension for compiled lisp files, for
#             franz is o, for common lisp depends on the implementation
#
# Lisp      : the pathname of the common lisp system (not used for franz)
#
# Liszt	    : the pathname of the franz lisp compiler (not used for cl)
#
#
# LispDir   : the pathname of the hol lisp directory
#
# Hol	    : the pathname of the hol system
# =====================================================================

Allegro_Case=:case-insensitive-upper
LispType=franz
#LispType=${LispType}

Obj=o
#Obj=${Obj}

#Lisp=../../akcl
Lisp=/usr/groups/hol/franz/bin/lisp

Liszt=/usr/groups/hol/franz/bin/liszt
#Liszt=${Liszt}

LisztComm=/usr/groups/hol/franz/bin/liszt
#LisztComm=${LisztComm}

#LispDir=../../lisp
LispDir=/usr/groups/hol/HOL13/lisp

Hol=../../hol
#Hol=${Hol}

HOLdir=/usr/groups/hol/HOL21
#HOLdir=${HOLdir}

LispDir=${HOLdir}/lisp
#LispDir=${Lispdir}

# =====================================================================

clean:
	rm -f *_ml.o *_ml.l *.$(Obj)
	@echo "===> library prog_logic88: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th *.$(Obj)
	@echo "===> library prog_logic88: all object code and theory files deleted"


parse_hacks.$(Obj): parse_hacks.l
	rm -f f-constants.$(Obj); ln -s $(LispDir)/f-constants.$(Obj) .
	rm -f f-macro.$(Obj); ln -s $(LispDir)/f-macro.$(Obj) .
	rm -f f-ol-rec.$(Obj); ln -s $(LispDir)/f-ol-rec.$(Obj) .
	rm -f f-$(LispType).$(Obj); ln -s $(LispDir)/f-$(LispType).$(Obj) .
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro (set-case-mode $(Allegro_Case))'\
	       '(load "f-cl") (compile-file "parse_hacks.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) parse_hacks.l; fi

print_hacks.$(Obj): print_hacks.l
	rm -f f-constants.$(Obj); ln -s $(LispDir)/f-constants.$(Obj) .
	rm -f f-macro.$(Obj); ln -s $(LispDir)/f-macro.$(Obj) .
	rm -f f-ol-rec.$(Obj); ln -s $(LispDir)/f-ol-rec.$(Obj) .
	rm -f genmacs.$(Obj); ln -s $(LispDir)/genmacs.$(Obj) .
	rm -f f-$(LispType).$(Obj); ln -s $(LispDir)/f-$(LispType).$(Obj) .
	if [ $(LispType) = cl ]; then\
	  echo '#+allegro (set-case-mode $(Allegro_Case))'\
	       '(load "f-cl") (compile-file "print_hacks.l") (quit)'\
	       | $(Lisp); else\
	  $(Liszt) print_hacks.l; fi

semantics.th: mk_semantics.ml
	rm -f semantics.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_semantics`;;'\
	     'quit();;' | ${Hol} 

hoare_thms.th: mk_hoare_thms.ml semantics.th
	rm -f hoare_thms.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_hoare_thms`;;'\
	     'quit();;' | ${Hol} 

halts.th: mk_halts.ml hoare_thms.th semantics.th
	rm -f halts.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_halts`;;'\
	     'quit();;' | ${Hol} 

halts_thms.th: mk_halts_thms.ml halts.th hoare_thms.th semantics.th
	rm -f halts_thms.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_halts_thms`;;'\
	     'quit();;' | ${Hol} 

halts_logic.th: mk_halts_logic.ml halts.th hoare_thms.th semantics.th
	rm -f halts_logic.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_halts_logic`;;'\
	     'quit();;' | ${Hol} 

dijkstra.th: mk_dijkstra.ml halts_thms.th
	rm -f dijkstra.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_dijkstra`;;'\
	     'quit();;' | ${Hol} 

dynamic_logic.th: mk_dynamic_logic.ml dijkstra.th halts_logic.th
	rm -f dynamic_logic.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_dynamic_logic`;;'\
	     'quit();;' | ${Hol} 

prog_logic88.th: mk_prog_logic88.ml dynamic_logic.th dijkstra.th\
        halts_logic.th halts_thms.th halts.th hoare_thms.th semantics.th
	rm -f prog_logic88.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_prog_logic88`;;'\
	     'quit();;' | ${Hol} 

syntax_functions_ml.o: syntax_functions.ml parse_hacks.l print_hacks.l
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `string`;;'\
	     'load_theory `prog_logic88`;;'\
	     'loadt `autoload`;;'\
	     'compilet `syntax_functions`;;'\
	     'quit();;' | ${Hol}

hol_match_ml.o: hol_match.ml syntax_functions_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `string`;;'\
	     'load_theory `prog_logic88`;;'\
	     'loadt `autoload`;;'\
	     'loadt `syntax_functions`;;'\
	     'compilet `hol_match`;;'\
	     'quit();;' | ${Hol}

hoare_logic_ml.o: hoare_logic.ml prog_logic88.th hol_match_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `string`;;'\
	     'load_theory `prog_logic88`;;'\
	     'loadt `autoload`;;'\
	     'loadt `syntax_functions`;;'\
	     'loadt `hol_match`;;'\
	     'compilet `hoare_logic`;;'\
	     'quit();;' | ${Hol}

vc_gen_ml.o: vc_gen.ml hoare_logic_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `string`;;'\
	     'load_theory `prog_logic88`;;'\
	     'loadt `autoload`;;'\
	     'loadt `syntax_functions`;;'\
	     'loadt `hol_match`;;'\
	     'loadt `hoare_logic`;;'\
	     'compilet `vc_gen`;;'\
	     'quit();;' | ${Hol}

halts_logic_ml.o: halts_logic.ml hoare_logic_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `string`;;'\
	     'load_theory `prog_logic88`;;'\
	     'loadt `autoload`;;'\
	     'loadt `syntax_functions`;;'\
	     'loadt `hol_match`;;'\
	     'loadt `hoare_logic`;;'\
	     'loadt `vc_gen`;;'\
	     'compilet `halts_logic`;;'\
	     'quit();;' | ${Hol}

halts_vc_gen_ml.o: halts_vc_gen.ml halts_logic_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_library `string`;;'\
	     'load_theory `prog_logic88`;;'\
	     'loadt `autoload`;;'\
	     'loadt `syntax_functions`;;'\
	     'loadt `hol_match`;;'\
	     'loadt `hoare_logic`;;'\
	     'loadt `vc_gen`;;'\
	     'loadt `halts_logic`;;'\
	     'compilet `halts_vc_gen`;;'\
	     'quit();;' | ${Hol}

all: parse_hacks.$(Obj) print_hacks.$(Obj)\
     semantics.th hoare_thms.th halts.th halts_thms.th dijkstra.th\
     dynamic_logic.th prog_logic88.th\
     syntax_functions_ml.o hol_match_ml.o hoare_logic_ml.o vc_gen_ml.o\
     halts_logic_ml.o halts_vc_gen_ml.o
	@echo "===> library prog_logic88 rebuilt"
