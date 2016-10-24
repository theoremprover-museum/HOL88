% Extends The Basic Theory For TRACES In CSP                    	 %
% 									 %
% FILE		: star.ml     					         %
% DESCRIPTION	: Defines the * operator for finite traces and infinite  %
%                 alphabets.                                             %
% 									 %
% READS FILES	: restrict.th, rules_and_tacs.ml                       	 %
% WRITES FILES  : star.th						 %
%									 %
% AUTHOR	: Albert John Camilleri					 %
% AFFILIATION   : Hewlett-Packard Laboratories, Bristol			 %
% DATE		: 89.02.07						 %
% REVISED	: 91.10.01						 %


new_theory `star`;;

new_parent `restrict`;;

let trace = ":(*)list";;
loadf `rules_and_tacs`;;

load_definition `restrict` `RESTRICT`;;
load_theorem `restrict` `REST_CONS_THM`;;
load_definition `sets` `SUBSET_DEF`;;
load_theorem `sets` `EXTENSION`;;
load_theorem `list_lib1` `NOT_LENGTH_EQ`;;

let STAR =
    new_definition
       (`STAR`, "STAR (A:(*)set) = {s | RESTRICT s A = s}");;

let NIL_IN_STAR =
    prove_thm
       (`NIL_IN_STAR`,
	"! A:(*)set. [] IN (STAR A)",
	REWRITE_TAC [STAR] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [RESTRICT]);;

let SINGLE_STAR =
    prove_thm
       (`SINGLE_STAR`,
	"! x (A:(*)set). [x] IN (STAR A) = x IN A",
	REWRITE_TAC [STAR] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [RESTRICT] THEN
	REPEAT GEN_TAC THEN
	DISJ_CASES_TAC (SPEC "(x:*) IN A" EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC[NOT_NIL_CONS]);;

let CONS_STAR =
    prove_thm
       (`CONS_STAR`,
	"! a t (A:(*)set).
           (CONS a t) IN (STAR A) = (a IN A) /\ (t IN (STAR A))",
	REWRITE_TAC [STAR] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [RESTRICT] THEN
	REPEAT GEN_TAC THEN
	DISJ_CASES_TAC (SPEC "(a:*) IN A" EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC [CONS_11; REST_CONS_THM]);;

let APPEND_STAR =
    prove_thm
       (`APPEND_STAR`,
	"! s t (A:(*)set).
           (APPEND s t) IN (STAR A) = (s IN (STAR A) /\ t IN (STAR A))",
	LIST_INDUCT_TAC THEN
	ASM_REWRITE_TAC [APPEND; NIL_IN_STAR; CONS_STAR; CONJ_ASSOC]);;

let STAR_INDUCT =
    prove_thm
       (`STAR_INDUCT`,
	"!A:(*)set.
          STAR A = {t | (t = []) \/ ((HD t) IN A /\ (TL t) IN (STAR A))}",
	GEN_TAC THEN
	REWRITE_TAC [EXTENSION] THEN
	SET_SPEC_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [NIL_IN_STAR; CONS_STAR; NOT_CONS_NIL; HD; TL]);;

let SUBSET_STAR =
    prove_thm
       (`SUBSET_STAR`,
	"! A B: (*)set. (A SUBSET B) ==> ((STAR A) SUBSET (STAR B))",
	REWRITE_TAC [SUBSET_DEF] THEN
	REPEAT GEN_TAC THEN
	DISCH_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [NIL_IN_STAR; CONS_STAR] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC);;

close_theory();;
