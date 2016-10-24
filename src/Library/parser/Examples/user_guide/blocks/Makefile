# Generated parser Makefile

# Version of HOL to be used:
HOL=/usr/groups/hol/hol_12/hol

# General definitions for all generated parsers:
GENERAL=/usr/users/jvt/HOL/CHEOPS/Parser/ml/general

# Insert entries for user-defined stuff here:
# Remember to insert the appropriate dependencies and "load"'s below.

# Now compile the declarations:
blocks_decls_ml.o: blocks_decls.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'compilet `blocks_decls`;;'\
	     'quit();;' | $(HOL)

# Finally do the actual functions
blocks_ml.o: blocks.ml blocks_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `blocks_decls`;;'\
	     'compilet `blocks`;;'\
	     'quit();;' | $(HOL)

all: blocks_ml.o
	@echo '===> Parser "blocks" built.'

