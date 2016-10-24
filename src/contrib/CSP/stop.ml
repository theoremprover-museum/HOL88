% Trace Semantics for the process STOP.					%
% 									%
% FILE		  : stop.ml 						%
% 									%
% READS FILES	  : process_ty.th		          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : stop.th						%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%

load_library `sets`;;
load_library `string`;;

new_theory `stop`;;

new_parent `process_ty`;;

load_theorem `list_lib1` `APPEND_EQ_NIL`;;
load_theorem `star` `NIL_IN_STAR`;;
map (load_definition `process_ty`) [`IS_PROCESS`; `ALPHA_DEF`; `TRACES_DEF`];;
load_theorem `process_ty` `PROCESS_LEMMA6`;;

loadf `rules_and_tacs`;;

let IS_PROCESS_STOP =
    prove_thm
       (`IS_PROCESS_STOP`,
	"! A. IS_PROCESS (A, {[]})",
        REWRITE_TAC [IS_PROCESS; SUBSET_DEF; IN_SING; APPEND_EQ_NIL] THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC [NIL_IN_STAR]);;

let STOP_LEMMA1 = REWRITE_RULE [PROCESS_LEMMA6] IS_PROCESS_STOP;;

let DEST_PROCESS =
    TAC_PROOF
       (([],
	 "?f. !x. ((ALPHA (f x)) = x) /\ ((TRACES (f x)) = {[]})"),
	EXISTS_TAC "\x.ABS_process (x, {[]})" THEN
        BETA_TAC THEN
	REWRITE_TAC [ALPHA_DEF; TRACES_DEF; STOP_LEMMA1]);;

let STOP = new_specification `STOP` [(`constant`,`STOP`)] DEST_PROCESS;;

map2 (\(x,y). save_thm (x, y))
     ([`ALPHA_STOP`; `TRACES_STOP`],
      map GEN_ALL (CONJUNCTS (SPEC_ALL STOP)));;

close_theory ();;
