HOL = /usr/groups/hol/hol_12/hol

quant.th: quant.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `quant`;;'\
	     'quit();;' | $(HOL)

prenex_ml.o: prenex.ml quant.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `prenex`;;'\
	     'quit();;' | $(HOL)

all: prenex_ml.o quant.th
