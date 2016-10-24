# Generated parser Makefile

# Version of HOL to be used:
HOL=/usr/groups/hol/hol_12/hol

# General definitions for all generated parsers:
GENERAL=/usr/users/jvt/HOL/CHEOPS/Parser/ml/general

# Insert entries for user-defined stuff here:
# Remember to insert the appropriate dependencies and "load"'s below.

# Now compile the declarations:
bool_decls_ml.o: bool_decls.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'compilet `bool_decls`;;'\
	     'quit();;' | $(HOL)

# Finally do the actual functions
bool_ml.o: bool.ml bool_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `bool_decls`;;'\
	     'compilet `bool`;;'\
	     'quit();;' | $(HOL)

all: bool_ml.o
	@echo '===> Parser "bool" built.'

