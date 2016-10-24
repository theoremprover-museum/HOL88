# =====================================================================
#
# 		 MAKEFILE FOR abs_theory Library.
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
# Name      : name of library
#
# Hol	    : the pathname of the version of hol used
#
# Root	    : root directory for the directory holding this file
#
# Home      : directory (relative to Root) that contains this file
#
# Library   : root directory for library
#
# ML        : list of ML sources
#
# =====================================================================

Name=abs_theory

Hol=hol

Root=../..

Home=${Root}/Library/abs_theory

Lib=${Root}/Library

default:
	@echo "===> ${Name}. Type \"make example,\" \"make abs_theory_ml.o,\" or \"make clean\""

all:	example abs_theory_ml.o

clean:
	-/bin/rm -f *_ml.o 
	@echo "===> ${Name}. All object code deleted"

clobber:
	-/bin/rm -f *_ml.o *.th print
	@echo "===> ${Name}: All object code and theory files deleted"

# =====================================================================
# Add new suffixes for ML and theory files
# =====================================================================
.SUFFIXES: .ml .th 

# =====================================================================
# Default action for creating a .th file from a .ml file.
# =====================================================================
.ml.th: 
	@ echo Making ${Home}/$*.th...;\
	  echo 'set_flag(`abort_when_fail`,true);;'\
             'set_flag(`prompt`,false);;'\
             'set_flag(`sticky`,true);;'\
             'set_flag(`timing`,true);;'\
             'set_search_path (search_path() @ '\
             '   [`${Root}/ml/`;'\
             '   ]);;'\
	     'loadt `${Home}/$*.ml`;;'\
	     'quit();;' | ${Hol} || ${RM} $*.th


# =====================================================================
# List of ML source texts 
# =====================================================================
ML= monoid_def.ml group_def.ml example.ml

example: example.th
	@echo "===> ${Name} rebuilt on `date`"


abs_theory_ml.o: abs_theory.ml
	@ echo Making abs_theory.ml;\
	  echo 'set_flag(`abort_when_fail`,true);;'\
             'set_flag(`prompt`,false);;'\
             'set_flag(`sticky`,true);;'\
             'set_flag(`timing`,true);;'\
             'set_search_path (search_path() @ '\
             '   [`${Root}/ml/`;'\
             '   ]);;'\
	     'compilet `abs_theory`;;'\
	     'quit();;' | ${Hol} || ${RM} $*.th



# =====================================================================    
# Print recently changed files
# =====================================================================
print:	${ML}
	-@for f in $?; \
	  do 2up $$f | lpr -x; \
	     echo "Printing $$f" ;\
	  done
	 @touch print 


# =====================================================================    
# information below this line is generated automatically by depgen
# =====================================================================    
example.th: example.ml group_def.th
group_def.th: group_def.ml monoid_def.th
monoid_def.th: monoid_def.ml
