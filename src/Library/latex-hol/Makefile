# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: latex-hol
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : compile code
#
# make clean	    : remove compiled code
#	
# make clobber	    : remove pp code and compiled code
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

#Hol=../../hol
Hol=/usr/groups/hol/HOL21/bin/hol

clean:
	rm -f *.o
	@echo "===> library latex-hol: all object code deleted"
clobber:
	rm -f latex_*_pp.ml  *.o
	@echo "===> library latex-hol: all object code and _pp.ml file deleted"


latex_type_pp.ml:	latex_type.pp
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'PP_to_ML false `latex_type` ``;;'\
	        'quit();;' | ${Hol}

latex_type_pp_ml.o:	latex_type_pp.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'loadf `filters`;;'\
		'loadf `hol_trees`;;'\
		'loadf `precedence`;;'\
		'compilet `latex_type_pp`;;'\
		'quit();;' | ${Hol}

latex_term_pp.ml:	latex_term.pp
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'PP_to_ML false `latex_term` ``;;'\
	        'quit();;' | ${Hol}

latex_term_pp_ml.o:	latex_term_pp.ml latex_type_pp_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'loadf `filters`;;'\
		'loadf `hol_trees`;;'\
		'loadf `precedence`;;'\
		'loadf `latex_type_pp`;;'\
		'compilet `latex_term_pp`;;'\
		'quit();;' | ${Hol}

latex_thm_pp.ml:	latex_thm.pp
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'PP_to_ML false `latex_thm` ``;;'\
	        'quit();;' | ${Hol}
latex_thm_pp_ml.o:	latex_thm_pp.ml latex_term_pp_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'loadf `filters`;;'\
		'loadf `hol_trees`;;'\
		'loadf `precedence`;;'\
		'loadf `latex_type_pp`;;'\
		'loadf `latex_term_pp`;;'\
		'compilet `latex_thm_pp`;;'\
		'quit();;' | ${Hol}

latex_sets_pp.ml:	latex_sets.pp
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'PP_to_ML false `latex_sets` ``;;'\
	        'quit();;' | ${Hol}

latex_sets_pp_ml.o:	latex_sets_pp.ml latex_thm_pp_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'loadf `filters`;;'\
		'loadf `hol_trees`;;'\
		'loadf `precedence`;;'\
		'loadf `latex_type_pp`;;'\
		'loadf `latex_term_pp`;;'\
		'loadf `latex_thm_pp`;;'\
		'compilet `latex_sets_pp`;;'\
		'quit();;' | ${Hol}

filters_ml.o:	filters.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
		'compilet `filters`;;'\
		'quit();;' | ${Hol}

hol_trees_ml.o: hol_trees.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
	     'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
	     'compilet `hol_trees`;;'\
	     'quit();;' | ${Hol} 

precedence_ml.o: hol_trees_ml.o precedence.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
	     'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
	     'loadf `hol_trees`;;'\
	     'compilet `precedence`;;'\
	     'quit();;' | ${Hol} 

formaters_ml.o:	formaters.ml filters_ml.o hol_trees_ml.o precedence_ml.o\
	latex_type_pp_ml.o latex_thm_pp_ml.o latex_term_pp_ml.o\
	latex_sets_pp_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_printer`);;'\
		'loadf(library_pathname() ^ `/prettyp/PP_parser`);;'\
		'loadf `filters`;;'\
		'loadf `hol_trees`;;'\
		'loadf `precedence`;;'\
		'loadf `latex_sets_pp`;;'\
		'loadf `latex_thm_pp`;;'\
		'loadf `latex_term_pp`;;'\
		'loadf `latex_type_pp`;;'\
		'compilet `formaters`;;'\
		'quit();;' | ${Hol}

all:	formaters_ml.o
	@echo "===>Library latex-hol rebuilt"
