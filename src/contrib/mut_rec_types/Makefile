
HOL = ../../hol

all: mut_rec_tools.th mut_eu_ml.o tools_ml.o mut_conv_ml.o microc_ml.o\
     mut_def_ml.o

mut_rec_tools.th: mut_thms.ml tools_ml.o
	/bin/rm -f mut_rec_tools.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `tools`;;'\
	     'loadt `mut_thms`;;'\
	     'quit();;' | ${HOL}

mut_eu_ml.o: mut_eu.ml mut_rec_tools.th tools_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `tools`;;'\
	     'load_theory `mut_rec_tools`;;'\
	     'compilet `mut_eu`;;'\
	     'quit();;' | ${HOL}

 
tools_ml.o: tools.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `tools`;;'\
	     'quit();;' | ${HOL}

mut_conv_ml.o: mut_conv.ml mut_rec_tools.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `mut_rec_tools`;;'\
	     'compilet `mut_conv`;;'\
	     'quit();;' | ${HOL}

microc_ml.o: microc.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `microc`;;'\
	     'quit();;' | ${HOL}

mut_def_ml.o: mut_def.ml mut_rec_tools.th tools_ml.o microc_ml.o\
              mut_conv_ml.o mut_eu_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'new_theory `dummy`;;'\
	     'new_parent `mut_rec_tools`;;'\
	     'compilet `mut_def`;;'\
	     'quit();;' | ${HOL}
	/bin/rm -f dummy.th

