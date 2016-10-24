# Generated parser Makefile

# Version of HOL to be used:
HOL=/usr/groups/hol/hol_12/hol

# General definitions for all generated parsers:
GENERAL=/usr/groups/hol/hol_12/Library/parser/general

# Insert entries for user-defined stuff here:
# Remember to insert the appropriate dependencies and "load"'s below.
PP_printer_ml.o: PP_printer.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'compilet `PP_printer`;;'\
	     'quit();;' | $(HOL)

full-ella_ml.o: full-ella.ml PP_printer_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'compilet `full-ella`;;'\
	     'quit();;' | $(HOL)

PP_command_ml.o: PP_command.ml full-ella_ml.o PP_printer_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'compilet `PP_command`;;'\
	     'quit();;' | $(HOL)

PP_v0: PP_printer_ml.o full-ella_ml.o PP_command_ml.o

v1_help_ml.o: v1_help.ml PP_printer_ml.o full-ella_ml.o PP_command_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'compilet `v1_help`;;'\
	     'quit();;' | $(HOL)

# Now compile the declarations:
A1_1_decls_ml.o: A1_1_decls.ml v1_help_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'compilet `A1_1_decls`;;'\
	     'quit();;' | $(HOL)

A1_2_decls_ml.o: A1_2_decls.ml A1_1_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'compilet `A1_2_decls`;;'\
	     'quit();;' | $(HOL)

A1_3_decls_ml.o: A1_3_decls.ml A1_2_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'compilet `A1_3_decls`;;'\
	     'quit();;' | $(HOL)

A1_4_decls_ml.o: A1_4_decls.ml A1_3_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'compilet `A1_4_decls`;;'\
	     'quit();;' | $(HOL)

A1_5_decls_ml.o: A1_5_decls.ml A1_4_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'compilet `A1_5_decls`;;'\
	     'quit();;' | $(HOL)

A1_6_decls_ml.o: A1_6_decls.ml A1_5_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'compilet `A1_6_decls`;;'\
	     'quit();;' | $(HOL)

A1_7_decls_ml.o: A1_7_decls.ml A1_6_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'compilet `A1_7_decls`;;'\
	     'quit();;' | $(HOL)

A1_8_decls_ml.o: A1_8_decls.ml A1_7_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'compilet `A1_8_decls`;;'\
	     'quit();;' | $(HOL)

A1_9_decls_ml.o: A1_9_decls.ml A1_8_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'compilet `A1_9_decls`;;'\
	     'quit();;' | $(HOL)

A1_10_decls_ml.o: A1_10_decls.ml A1_9_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'compilet `A1_10_decls`;;'\
	     'quit();;' | $(HOL)

A1_11_decls_ml.o: A1_11_decls.ml A1_10_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'compilet `A1_11_decls`;;'\
	     'quit();;' | $(HOL)

decls: A1_1_decls_ml.o A1_2_decls_ml.o A1_3_decls_ml.o A1_4_decls_ml.o \
	A1_5_decls_ml.o A1_6_decls_ml.o A1_7_decls_ml.o A1_8_decls_ml.o \
	A1_9_decls_ml.o A1_10_decls_ml.o A1_11_decls_ml.o

# Finally do the actual functions
A1_1_ml.o: A1_1.ml A1_11_decls_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'compilet `A1_1`;;'\
	     'quit();;' | $(HOL)

A1_2_ml.o: A1_2.ml A1_1_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'compilet `A1_2`;;'\
	     'quit();;' | $(HOL)

A1_3_ml.o: A1_3.ml A1_2_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'compilet `A1_3`;;'\
	     'quit();;' | $(HOL)

A1_4_ml.o: A1_4.ml A1_3_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'compilet `A1_4`;;'\
	     'quit();;' | $(HOL)

A1_5_ml.o: A1_5.ml A1_4_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'compilet `A1_5`;;'\
	     'quit();;' | $(HOL)

A1_6_ml.o: A1_6.ml A1_5_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'loadf `A1_5`;;'\
	     'compilet `A1_6`;;'\
	     'quit();;' | $(HOL)

A1_7_ml.o: A1_7.ml A1_6_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'loadf `A1_5`;;'\
	     'loadf `A1_6`;;'\
	     'compilet `A1_7`;;'\
	     'quit();;' | $(HOL)

A1_8_ml.o: A1_8.ml A1_7_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'loadf `A1_5`;;'\
	     'loadf `A1_6`;;'\
	     'loadf `A1_7`;;'\
	     'compilet `A1_8`;;'\
	     'quit();;' | $(HOL)

A1_9_ml.o: A1_9.ml A1_8_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'loadf `A1_5`;;'\
	     'loadf `A1_6`;;'\
	     'loadf `A1_7`;;'\
	     'loadf `A1_8`;;'\
	     'compilet `A1_9`;;'\
	     'quit();;' | $(HOL)

A1_10_ml.o: A1_10.ml A1_9_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'loadf `A1_5`;;'\
	     'loadf `A1_6`;;'\
	     'loadf `A1_7`;;'\
	     'loadf `A1_8`;;'\
	     'loadf `A1_9`;;'\
	     'compilet `A1_10`;;'\
	     'quit();;' | $(HOL)

A1_11_ml.o: A1_11.ml A1_10_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `$(GENERAL)`;;'\
	     'loadf `PP_printer`;;'\
	     'loadf `full-ella`;;'\
	     'loadf `PP_command`;;'\
	     'loadf `v1_help`;;'\
	     'loadf `A1_1_decls`;;'\
	     'loadf `A1_2_decls`;;'\
	     'loadf `A1_3_decls`;;'\
	     'loadf `A1_4_decls`;;'\
	     'loadf `A1_5_decls`;;'\
	     'loadf `A1_6_decls`;;'\
	     'loadf `A1_7_decls`;;'\
	     'loadf `A1_8_decls`;;'\
	     'loadf `A1_9_decls`;;'\
	     'loadf `A1_10_decls`;;'\
	     'loadf `A1_11_decls`;;'\
	     'loadf `A1_1`;;'\
	     'loadf `A1_2`;;'\
	     'loadf `A1_3`;;'\
	     'loadf `A1_4`;;'\
	     'loadf `A1_5`;;'\
	     'loadf `A1_6`;;'\
	     'loadf `A1_7`;;'\
	     'loadf `A1_8`;;'\
	     'loadf `A1_9`;;'\
	     'loadf `A1_10`;;'\
	     'compilet `A1_11`;;'\
	     'quit();;' | $(HOL)

parser: A1_1_ml.o A1_2_ml.o A1_3_ml.o A1_4_ml.o A1_5_ml.o A1_6_ml.o \
	A1_7_ml.o A1_8_ml.o A1_9_ml.o A1_10_ml.o A1_11_ml.o

all: decls parser
	@echo '===> Parser "ella" built'.
