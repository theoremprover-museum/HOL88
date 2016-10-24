% Trace Semantics for the process PARALLEL.				%
% 									%
% FILE		  : parallel.ml 					%
% 									%
% READS FILES	  : process_ty.th, rules_and_tacs.ml          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : parallel.th						%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%


load_library `sets`;;
load_library `string`;;
loadf `rules_and_tacs`;;

new_theory `parallel`;;

new_parent `process_ty`;;

load_definition `restrict` `RESTRICT`;;
load_theorem `restrict` `DISTRIB_REST`;;
map (load_theorem `star`) [`NIL_IN_STAR`; `APPEND_STAR`];;
map (load_definition `process_ty`) [`IS_PROCESS`; `ALPHA_DEF`; `TRACES_DEF`];;
map (load_theorem `process_ty`)
    [`PROCESS_LEMMA6`; `APPEND_IN_TRACES`; `TRACES_IN_STAR`; `NIL_IN_TRACES`];;

let IS_PROCESS_PAR =
    prove_thm
       (`IS_PROCESS_PAR`,
	"! P Q.
          IS_PROCESS
           ((ALPHA P) UNION (ALPHA Q),
	    {s | (s IN (STAR ((ALPHA P) UNION (ALPHA Q)))) /\
                 ((RESTRICT s (ALPHA P)) IN (TRACES P)) /\
                 ((RESTRICT s (ALPHA Q)) IN (TRACES Q))})",
        REWRITE_TAC [IS_PROCESS; SUBSET_DEF] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC
	 [RESTRICT; NIL_IN_STAR; DISTRIB_REST; APPEND_STAR; NIL_IN_TRACES] THEN
        REPEAT STRIP_TAC THEN
	IMP_RES_TAC APPEND_IN_TRACES THEN
	ASM_REWRITE_TAC []);;

let PAR_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_PAR;;

let DEST_PROCESS =
    TAC_PROOF
       (([],
	 "?f. !P Q.
           ((ALPHA (f P Q) = ((ALPHA P) UNION (ALPHA Q))) /\
            (TRACES (f P Q) =
  	     {s | (s IN (STAR ((ALPHA P) UNION (ALPHA Q)))) /\
                  ((RESTRICT s (ALPHA P)) IN (TRACES P)) /\
                  ((RESTRICT s (ALPHA Q)) IN (TRACES Q))}))"),
	EXISTS_TAC
	 "\P Q.
	   ABS_process
	    ((ALPHA P) UNION (ALPHA Q),
	     {s | (s IN (STAR ((ALPHA P) UNION (ALPHA Q)))) /\
                  ((RESTRICT s (ALPHA P)) IN (TRACES P)) /\
                  ((RESTRICT s (ALPHA Q)) IN (TRACES Q))})" THEN
        BETA_TAC THEN
	REWRITE_TAC [ALPHA_DEF; TRACES_DEF; PAR_LEMMA1]);;

let PAR = new_specification `PAR` [(`infix`,`PAR`)] DEST_PROCESS;;

map2 (\(x,y). save_thm (x, y))
     ([`ALPHA_PAR`; `TRACES_PAR`],
      map GEN_ALL (CONJUNCTS (SPEC_ALL PAR)));;

close_theory();;
