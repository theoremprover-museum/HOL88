# Generated parser Makefile

# Version of HOL to be used:
HOL=/usr/groups/hol/hol_12/hol

# General definitions for all generated parsers:
GENERAL=/usr/groups/hol/hol_12/Library/parser/general

# Insert entries for user-defined stuff here:
# Remember to insert the appropriate dependencies and "load"'s below.
tiny_help_ml.o: tiny_help.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'compilet `tiny_help`;;'\
	     'quit();;' | $(HOL)

# Now compile the declarations:
tiny_decls_ml.o: tiny_decls.ml tiny_help_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `tiny_help`;;'\
	     'compilet `tiny_decls`;;'\
	     'quit();;' | $(HOL)

# Finally do the actual functions
tiny_ml.o: tiny.ml tiny_decls_ml.o tiny_help_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `tiny_help`;;'\
	     'loadf `tiny_decls`;;'\
	     'compilet `tiny`;;'\
	     'quit();;' | $(HOL)

all: tiny_ml.o
	@echo '===> Parser "tiny" built.

