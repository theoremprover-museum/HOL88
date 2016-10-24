# =====================================================================
#
# 		 MAKEFILE FOR: pred
#
# =====================================================================

Hol=hol

# =====================================================================
# Default entry.
# =====================================================================

default:
	@echo 'MAKEFILE FOR: pred'

# =====================================================================
# Cleaning functions.
# =====================================================================

clean:
	rm -f *_ml.o
	@echo "===> library pred: all object code deleted"

clobber:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library pred: all object code and theory files deleted"

# =====================================================================
# Entries for individual files.
# =====================================================================

pred.th: mk_pred.ml
	rm -f pred.th
	echo 'set_flag (`abort_when_fail`, true) ;;'\
	     'loadt `mk_pred` ;;'\
	     'if (draft_mode ()) then (close_theory ()) ;;'\
 	     'quit () ;;' | ${Hol}

# =====================================================================
# Main entry
# =====================================================================

all: pred.th
	@echo "===> library pred rebuilt"
