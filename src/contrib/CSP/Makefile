# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: CSP
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : create theories and compile code
#
# make clean	    : remove theories and compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

Hol=/usr/groups/hol/HOL12/sun4_sos/hol

clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library csp: all object code and theory files deleted"  

boolarith1.th: boolarith1.ml
	rm -f boolarith1.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `boolarith1`;;'\
	     'quit();;' | ${Hol}

boolarith2.th: boolarith2.ml boolarith1.th
	rm -f boolarith2.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `boolarith2`;;'\
	     'quit();;' | ${Hol}

list_lib1.th: list_lib1.ml
	rm -f list_lib1.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `list_lib1`;;'\
	     'quit();;' | ${Hol}

traces.th: traces.ml list_lib1.th
	rm -f traces.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `traces`;;'\
	     'quit();;' | ${Hol}

restrict.th: restrict.ml traces.th boolarith2.th
	rm -f restrict.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `restrict`;;'\
	     'quit();;' | ${Hol}

star.th: star.ml restrict.th
	rm -f star.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `star`;;'\
	     'quit();;' | ${Hol}

order.th: order.ml restrict.th
	rm -f order.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `order`;;'\
	     'quit();;' | ${Hol}

process_ty.th: process_ty.ml star.th
	rm -f process_ty.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `process_ty`;;'\
	     'quit();;' | ${Hol}
 
stop.th: stop.ml process_ty.th
	rm -f stop.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `stop`;;'\
	     'quit();;' | ${Hol}
 
run.th: run.ml process_ty.th
	rm -f run.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `run`;;'\
	     'quit();;' | ${Hol}
 
prefix.th: prefix.ml process_ty.th
	rm -f prefix.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `prefix`;;'\
	     'quit();;' | ${Hol}
 
after.th: after.ml process_ty.th
	rm -f after.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `after`;;'\
	     'quit();;' | ${Hol}
 
choice.th: choice.ml process_ty.th
	rm -f choice.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `choice`;;'\
	     'quit();;' | ${Hol}

parallel.th: parallel.ml process_ty.th
	rm -f parallel.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `parallel`;;'\
	     'quit();;' | ${Hol}

process_fix.th: process_fix.ml stop.th
	rm -f process_fix.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `process_fix`;;'\
	     'quit();;' | ${Hol}

mu.th: mu.ml process_fix.th
	rm -f mu.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mu`;;'\
	     'quit();;' | ${Hol}

process.th: process.ml run.th prefix.th choice.th after.th parallel.th mu.th
	rm -f process.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `process`;;'\
	     'quit();;' | ${Hol}

after_laws.th: after_laws.ml process.th
	rm -f after_laws.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `after_laws`;;'\
	     'quit();;' | ${Hol}

par_laws.th: par_laws.ml process.th
	rm -f par_laws.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `par_laws`;;'\
	     'quit();;' | ${Hol}

csp_syntax.th: csp_syntax.ml process.th
	rm -f csp_syntax.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `csp_syntax`;;'\
	     'quit();;' | ${Hol}

all:	boolarith1.th boolarith2.th list_lib1.th\
	traces.th restrict.th star.th order.th\
	process_ty.th\
	stop.th run.th prefix.th after.th choice.th parallel.th\
	process_fix.th mu.th process.th\
	after_laws.th par_laws.th\
	csp_syntax.th
	@echo "===> library csp rebuilt"
