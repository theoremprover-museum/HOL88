Hol=/usr/groups/hol/HOL12/bin/hol

lib_ml.o: lib.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'compilet `lib`;;'\
	     'quit();;' | $(Hol)

rewrite_ml.o: rewrite.ml lib_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `lib`;;'\
	     'compilet `rewrite`;;'\
	     'quit();;' | $(Hol)

kb_ml.o: kb.ml rewrite_ml.o lib_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `lib`;;'\
	     'loadf `rewrite`;;'\
	     'compilet `kb`;;'\
	     'quit();;' | $(Hol)

order_ml.o: order.ml kb_ml.o rewrite_ml.o lib_ml.o
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadf `lib`;;'\
	     'loadf `rewrite`;;'\
	     'loadf `kb`;;'\
	     'compilet `order`;;'\
	     'quit();;' | $(Hol)

all: lib_ml.o rewrite_ml.o kb_ml.o order_ml.o
	@echo "===> Knuth-Bendix contrib rebuilt"

clean:
	/bin/rm -f *.o *.th
	@echo "===> Knuth-Bendix contrib cleaned up"

clobber:
	/bin/rm -f *.o *.th
	@echo "===> Knuth-Bendix contrib clobbered"

