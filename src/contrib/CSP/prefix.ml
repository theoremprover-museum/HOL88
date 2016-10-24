% Trace Semantics for the process PREFIX.				%
% 									%
% FILE		  : prefix.ml 						%
% 									%
% READS FILES	  : process_ty.th, rules_and_tacs.ml          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : prefix.th						%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%


load_library `sets`;;
load_library `string`;;
loadf `rules_and_tacs`;;

new_theory `prefix`;;

new_parent `process_ty`;;

load_theorems `list_lib1`;;
map (load_theorem `star`) [`NIL_IN_STAR`; `CONS_STAR`];;
map (load_theorem `process_ty`)
    [`PROCESS_LEMMA6`; `APPEND_IN_TRACES`; `TRACES_IN_STAR`];;
map (load_definition `process_ty`) [`IS_PROCESS`; `ALPHA_DEF`; `TRACES_DEF`];;

let IS_PROCESS_PREFIX =
    prove_thm
       (`IS_PROCESS_PREFIX`,
	"! a P.
           (a IN (ALPHA P)) ==>
           IS_PROCESS ((ALPHA P), {[]} UNION {CONS a t | t IN (TRACES P)})",
        REWRITE_TAC [IS_PROCESS; SUBSET_DEF; UNION_DEF] THEN
        SET_SPEC_TAC THEN
	REWRITE_TAC [IN_SING; APPEND_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [NIL_IN_STAR; CONS_STAR] THEN
	IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
	IMP_RES_TAC CONS_MEMBER_LIST THEN
	ASM_REWRITE_TAC [] THEN
	DISJ2_TAC THEN
	EXISTS_TAC "r:trace" THEN
	UNDISCH_TAC "t' IN (TRACES P)" THEN
	ASM_REWRITE_TAC [APPEND_IN_TRACES]);;

let PREFIX_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_PREFIX;;

let DEST_PROCESS =
    TAC_PROOF
       (([],
	 "?f. !a P.
           a IN (ALPHA P) ==>
           ((ALPHA (f a P) = (ALPHA P)) /\
            (TRACES (f a P) = {[]} UNION {CONS a t | t IN (TRACES P)}))"),
	EXISTS_TAC
	 "\a P.
	  ABS_process (ALPHA P, {[]} UNION {CONS a t | t IN (TRACES P)})" THEN
        BETA_TAC THEN
	PURE_ONCE_REWRITE_TAC
	 [GEN_ALL (SPEC "ABS_process r" ALPHA_DEF);
	  GEN_ALL (SPEC "ABS_process r" TRACES_DEF)] THEN
	REPEAT GEN_TAC THEN
	DISCH_THEN (SUBST1_TAC o (MATCH_MP PREFIX_LEMMA1)) THEN
	REWRITE_TAC []);;

let PREFIX = new_specification `PREFIX` [(`infix`,`-->`)] DEST_PROCESS;;

map2 (\(x,y). save_thm (x, y))
     ([`ALPHA_PREFIX`; `TRACES_PREFIX`],
      map (GEN_ALL o DISCH_ALL) (CONJUNCTS (UNDISCH (SPEC_ALL PREFIX))));;

close_theory ();;
