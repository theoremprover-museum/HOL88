# Generated parser Makefile

# Version of HOL to be used:
HOL=/usr/groups/hol/hol_12/hol

# General definitions for all generated parsers:
GENERAL=/usr/groups/hol/hol_12/Library/parser/general

# Insert entries for user-defined stuff here:
# Remember to insert the appropriate dependencies and "load"'s below.
term_help_ml.o: term_help.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'compilet `term_help`;;'\
	     'quit();;' | $(HOL)

# Now compile the declarations:
type_decls_ml.o: term_help_ml.o type_decls.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `term_help`;;'\
	     'compilet `type_decls`;;'\
	     'quit();;' | $(HOL)

term_decls_ml.o: type_decls_ml.o term_decls.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `term_help`;;'\
	     'loadf `type_decls`;;'\
	     'compilet `term_decls`;;'\
	     'quit();;' | $(HOL)

# Finally do the actual functions
type_ml.o: term_decls_ml.o type.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `term_help`;;'\
	     'loadf `type_decls`;;'\
	     'loadf `term_decls`;;'\
	     'compilet `type`;;'\
	     'quit();;' | $(HOL)

term_ml.o: term.ml type_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `term_help`;;'\
	     'loadf `type_decls`;;'\
	     'loadf `term_decls`;;'\
	     'loadf `type`;;'\
	     'compilet `term`;;'\
	     'quit();;' | $(HOL)

all:: term_ml.o
	@echo '===> Parser "term" built.'

