% Trace Semantics for the process AFTER.				%
% 									%
% FILE		  : after.ml 						%
% 									%
% READS FILES	  : process_ty.th, rules_and_tacs.ml          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : after.th						%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%

load_library `sets`;;
load_library `string`;;
loadf `rules_and_tacs`;;

new_theory `after`;;

new_parent `process_ty`;;

map (load_theorem `process_ty`)
    [`PROCESS_LEMMA6`; `APPEND_IN_TRACES`; `TRACES_IN_STAR`];;
map (load_definition `process_ty`) [`IS_PROCESS`; `ALPHA_DEF`; `TRACES_DEF`];;
map (load_theorem `star`) [`NIL_IN_STAR`; `CONS_STAR`; `APPEND_STAR`];;
load_theorem `list_lib1` `APPEND_NIL`;;

let IS_PROCESS_AFTER =
    prove_thm
       (`IS_PROCESS_AFTER`,
	"! P s.
           s IN (TRACES P) ==>
           IS_PROCESS (ALPHA P, {t | (APPEND s t) IN (TRACES P)})",
	REWRITE_TAC [IS_PROCESS; SUBSET_DEF] THEN
	SET_SPEC_TAC THEN
	REPEAT STRIP_TAC THENL
	[IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
	 UNDISCH_TAC "(APPEND s x) IN (STAR(ALPHA P))" THEN
	 REWRITE_TAC [APPEND_STAR] THEN
	 REPEAT STRIP_TAC;
	 ASM_REWRITE_TAC [APPEND_NIL];
	 UNDISCH_TAC "(APPEND s(APPEND s' t)) IN (TRACES P)" THEN
	 REWRITE_TAC [APPEND_ASSOC; APPEND_IN_TRACES]]);;

let AFTER_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_AFTER;;

let DEST_PROCESS =
    TAC_PROOF
       (([],
	 "?f. !P s.
           s IN (TRACES P) ==>
           ((ALPHA (f P s) = (ALPHA P)) /\
            (TRACES (f P s) = {t | (APPEND s t) IN (TRACES P)}))"),
	EXISTS_TAC
	 "\P s. ABS_process (ALPHA P, {t | (APPEND s t) IN (TRACES P)})" THEN
        BETA_TAC THEN
	PURE_ONCE_REWRITE_TAC
	 [GEN_ALL (SPEC "ABS_process r" ALPHA_DEF);
	  GEN_ALL (SPEC "ABS_process r" TRACES_DEF)] THEN
	REPEAT GEN_TAC THEN
	DISCH_THEN (SUBST1_TAC o (MATCH_MP AFTER_LEMMA1)) THEN
	REWRITE_TAC []);;

let AFTER = new_specification `AFTER` [(`infix`,`/`)] DEST_PROCESS;;

map2 (\(x,y). save_thm (x, y))
     ([`ALPHA_AFTER`; `TRACES_AFTER`],
      map (GEN_ALL o DISCH_ALL) (CONJUNCTS (UNDISCH (SPEC_ALL AFTER))));;

close_theory();;
