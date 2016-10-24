%----- -*- Emacs Mode: fundamental -*- -------------------------------

  File:		tarski.ml

  Author:	Kim Dam Petersen.
  Date:		26/7-1991.

  Description:

	This theory loads the theory which derives the existence of a
	minimal and maximal fixpoint of a predicate transformer.  The
	theory is based on Alfred Tarski's article ``A
	lattice-theoretical fixpoint theorem and its application'' in
	[Pacific Journal of Mathematics, Vol. 5, 1955.pp. 255-309]. The
	theory given here is restricted to consider predicate transformers,
	which order by inclusion makes up a complete lattice.

  Make:		The theory is created by executing:
			# loadt`mk_tarski`;;

  Usage:	The theory is loaded by executing:
			# load_theory`tarski`;;

---------------------------------------------------------------------%

load_theory`tarski`;;
load_definitions`tarski`;;
load_theorems`tarski`;;
