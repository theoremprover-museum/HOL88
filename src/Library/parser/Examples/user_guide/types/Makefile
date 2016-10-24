# Generated parser Makefile

# Version of HOL to be used:
HOL=/usr/groups/hol/hol_12/hol

# General definitions for all generated parsers:
GENERAL=/usr/users/jvt/HOL/CHEOPS/Parser/ml/general

# Insert entries for user-defined stuff here:
# Remember to insert the appropriate dependencies and "load"'s below.
types_help_ml.o: types_help.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'compilet `types_help`;;'\
	     'quit();;' | $(HOL)

# Now compile the declarations:
types_decls_ml.o: types_decls.ml types_help_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `types_help`;;'\
	     'compilet `types_decls`;;'\
	     'quit();;' | $(HOL)

# Finally do the actual functions
types_ml.o: types.ml types_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `types_help`;;'\
	     'loadf `types_decls`;;'\
	     'compilet `types`;;'\
	     'quit();;' | $(HOL)

all: types_ml.o
	@echo '===> Parser "types" built.'

