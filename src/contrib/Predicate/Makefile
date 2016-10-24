Hol=/usr/groups/hol/HOL21/bin/hol
noweave=NOWEB/bin/noweave
notangle=NOWEB/bin/notangle

TexPred: predicate.nw
	rm -f predicate.tex predicate.log predicate.aux predicate.dvi
	${noweave} -l predicate.nw > predicate.tex
	@echo "DCG predicate>: LATEX source produced"

LPred: predicate.nw
	rm -f predicate.ml
	${notangle} -Rmyloader predicate.nw > predicate.ml
	@echo "DCG predicate>: personal loader source produced"

PubLPred: predicate.nw
	rm -f predicate.ml
	${notangle} -Rloader predicate.nw > predicate.ml
	@echo "DCG predicate>: public loader source produced"

Pred: predicate.nw
	rm -f mk_predicate.ml
	${notangle} -Rpredicate predicate.nw > mk_predicate.ml
	@echo "DCG predicate>: HOL source produced"

SPred: predicate.nw
	rm -f predicate_SUP.ml
	${notangle} -RCYAN-and-JADE-tactics predicate.nw > predicate_SUP.ml
	@echo "DCG predicate>: support file produced"

SPredMisc: predicate.nw
	rm -f my_misc.ml
	${notangle} -Rmymisc predicate.nw > my_misc.ml
	@echo "DCG predicate>: my_misc source produced"

TPred: mk_predicate.ml
	rm -f predicate.th
	echo ' set_flag(`abort_when_fail`,true);;'\
	' loadt `mk_predicate`;;' | ${Hol}

PackPred:
	make PubLPred
	rm -f PACKPred
	shar NOWEB.dir predicate.nw predicate.tex predicate.ml mk_predicate.ml my_misc.ml OLD_RES.ml predicate_SUP.ml UNITYsty.tex noweb.sty Pred_README Makefile > PACKPred
	make LPred
