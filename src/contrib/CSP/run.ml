% Trace Semantics for the process RUN.					%
% 									%
% FILE		  : run.ml 						%
% 									%
% READS FILES	  : process_ty.th			          	%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : run.th						%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%

load_library `sets`;;
load_library `string`;;

new_theory `run`;;

new_parent `process_ty`;;

map (load_theorem `star`) [`NIL_IN_STAR`; `APPEND_STAR`];;
map (load_definition `process_ty`) [`IS_PROCESS`; `ALPHA_DEF`; `TRACES_DEF`];;
load_theorem `process_ty` `PROCESS_LEMMA6`;;

let IS_PROCESS_RUN =
    prove_thm
       (`IS_PROCESS_RUN`,
	"! A. IS_PROCESS(A, STAR A)",
        REWRITE_TAC [IS_PROCESS; SUBSET_DEF; APPEND_STAR; NIL_IN_STAR] THEN
        REPEAT STRIP_TAC);;

let RUN_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_RUN;;

let DEST_PROCESS =
    TAC_PROOF
       (([],
	 "?f. !A. ((ALPHA (f A)) = A) /\
                  ((TRACES (f A)) = (STAR A))"),
	EXISTS_TAC "\x. ABS_process (x, STAR x)" THEN
        BETA_TAC THEN
	REWRITE_TAC [ALPHA_DEF; TRACES_DEF; RUN_LEMMA1]);;

let RUN = new_specification `RUN` [(`constant`,`RUN`)] DEST_PROCESS;;

map2 (\(x,y). save_thm (x, y))
     ([`ALPHA_RUN`; `TRACES_RUN`],
      map GEN_ALL (CONJUNCTS (SPEC_ALL RUN)));;

close_theory ();;
