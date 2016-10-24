# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: trs
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
# make clobber	    : remove compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

Hol=../../hol

clean:
	rm -f *_ml.l *_ml.o
	@echo "===> library trs: all object code deleted"

clobber: clean

extents_ml.o: extents.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `extents`;;'\
	     'quit();;' | ${Hol} 

sets_ml.o: extents_ml.o sets.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'compilet `sets`;;'\
	     'quit();;' | ${Hol} 

extract_ml.o: sets_ml.o extract.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'compilet `extract`;;'\
	     'quit();;' | ${Hol} 

struct_ml.o: extract_ml.o struct.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'compilet `struct`;;'\
	     'quit();;' | ${Hol} 

name_ml.o: struct_ml.o name.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'loadf `struct`;;'\
	     'compilet `name`;;'\
	     'quit();;' | ${Hol} 

thmkind_ml.o: name_ml.o thmkind.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'loadf `struct`;;'\
	     'loadf `name`;;'\
	     'compilet `thmkind`;;'\
	     'quit();;' | ${Hol} 

matching_ml.o: thmkind_ml.o matching.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'loadf `struct`;;'\
	     'loadf `name`;;'\
	     'loadf `thmkind`;;'\
	     'compilet `matching`;;'\
	     'quit();;' | ${Hol} 

sidecond_ml.o: matching_ml.o sidecond.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'loadf `struct`;;'\
	     'loadf `name`;;'\
	     'loadf `thmkind`;;'\
	     'loadf `matching`;;'\
	     'compilet `sidecond`;;'\
	     'quit();;' | ${Hol} 

search_ml.o: sidecond_ml.o search.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'loadf `struct`;;'\
	     'loadf `name`;;'\
	     'loadf `thmkind`;;'\
	     'loadf `matching`;;'\
	     'loadf `sidecond`;;'\
	     'compilet `search`;;'\
	     'quit();;' | ${Hol} 

user_ml.o: search_ml.o user.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `extents`;;'\
	     'loadf `sets`;;'\
	     'loadf `extract`;;'\
	     'loadf `struct`;;'\
	     'loadf `name`;;'\
	     'loadf `thmkind`;;'\
	     'loadf `matching`;;'\
	     'loadf `sidecond`;;'\
	     'loadf `search`;;'\
	     'compilet `user`;;'\
	     'quit();;' | ${Hol} 

all: user_ml.o
	@echo "===> library trs rebuilt"
