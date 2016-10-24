% Theory containing the type definition of a process and some basic	%
% theorems about processes in general.					%
% 									%
% FILE		  : process_ty.ml 					%
% 									%
% READS FILES	  : star.th                               		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : process_ty.th					%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%


load_library `sets`;;

new_theory `process_ty`;;

load_library `string`;;
new_parent `star`;;

new_type_abbrev (`event`, ":string");;
new_type_abbrev (`trace`, ":event list");;
new_type_abbrev (`alphabet`, ":event set");;

load_definition `bool` `UNCURRY_DEF`;;
let STAR = definition `star` `STAR`;;
let RESTRICT = definition `restrict` `RESTRICT`;;
let APPEND_EQ_NIL = theorem `list_lib1` `APPEND_EQ_NIL`;;
loadf `rules_and_tacs`;;

let IS_PROCESS =
    new_definition
      (`IS_PROCESS`,
       "IS_PROCESS (A:alphabet, TR:(trace)set) =
        (TR SUBSET (STAR A)) /\
        ([] IN TR) /\
        (!s t:trace. ((APPEND s t) IN TR) ==> (s IN TR))");;

let EXISTS_PROCESS =
    prove_thm
       (`EXISTS_PROCESS`,
	"? P. (\(A, TR). IS_PROCESS(A,TR)) P",
        EXISTS_TAC "(EMPTY:alphabet, {[]:trace})" THEN
	REWRITE_TAC [UNCURRY_DEF] THEN
	BETA_TAC THEN
	REWRITE_TAC [IS_PROCESS; SUBSET_DEF; STAR; IN_SING] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [APPEND_EQ_NIL] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [RESTRICT]);;

let PROCESS_TYPE =
    new_type_definition
       (`process`, "\(A,TR). IS_PROCESS(A,TR)", EXISTS_PROCESS);;

let [PROCESS_LEMMA1; PROCESS_LEMMA2; PROCESS_LEMMA3;
     PROCESS_LEMMA4; PROCESS_LEMMA5; PROCESS_LEMMA6] =
    map2 (\(x,y).
           save_thm
            (`PROCESS_LEMMA`^x,
	      (REWRITE_RULE []
	       (BETA_RULE
	       (REWRITE_RULE
	        [UNCURRY_DEF]
	        (ONCE_REWRITE_RULE [SYM (SPEC_ALL PAIR)] y))))))
    ([`1`; `2`; `3`; `4`; `5`; `6`],
     (let th = 
          define_new_type_bijections
          `process_ISO_DEF` `ABS_process` `REP_process` PROCESS_TYPE in
     [prove_rep_fn_one_one th;
      prove_rep_fn_onto th;
      prove_abs_fn_one_one th;
      prove_abs_fn_onto th;
      CONJUNCT1 th;
      CONJUNCT2 th]));;

let ALPHA_DEF =
    new_definition
       (`ALPHA_DEF`,
	"ALPHA P = FST (REP_process P)");;

let TRACES_DEF =
    new_definition
       (`TRACES_DEF`,
	"TRACES P = SND (REP_process P)");;

let ID_PROCESS =
    prove_thm
       (`ID_PROCESS`,
        "!P. ABS_process(ALPHA P,TRACES P) = P",
	REWRITE_TAC [ALPHA_DEF; TRACES_DEF; PROCESS_LEMMA5]);;

let ID_PROCESS' =
    prove_thm
       (`ID_PROCESS'`,
        "!P. (ALPHA P,TRACES P) = (REP_process P)",
	REWRITE_TAC [ALPHA_DEF; TRACES_DEF; PAIR]);;

let SPLIT_PROCESS =
    REWRITE_RULE
     [IS_PROCESS]
     (AP_TERM
       "IS_PROCESS"
       (SYM
        (SPEC "v:alphabet#(trace set)"
              (INST_TYPE [(":alphabet",":*");(":(trace set)",":**")] PAIR))));;

let PROC_TAC =
    (REWRITE_TAC [SPLIT_PROCESS; ALPHA_DEF; TRACES_DEF] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC lemma THEN
     (UNDISCH_TAC "(APPEND s t) IN (SND(REP_process P))" ORELSE ALL_TAC) THEN
     ASM_REWRITE_TAC [])
    where
     lemma =
     (fst
      (EQ_IMP_RULE (SPEC_ALL (REWRITE_RULE [SPLIT_PROCESS] PROCESS_LEMMA6))));;

let proc_LEMMA1 =
    prove_thm
       (`proc_LEMMA1`,
	"!(P:process) (v:alphabet#((trace)set)).
	  ((P = ABS_process v) /\ (IS_PROCESS v))
          ==>
          [] IN (TRACES P)",
          PROC_TAC);;

let proc_LEMMA2 =
    prove_thm
       (`proc_LEMMA2`,
	"!(P:process) (v:alphabet#((trace)set)).
	  ((P = ABS_process v) /\ (IS_PROCESS v))
          ==>
          (!s t. ((APPEND s t) IN (TRACES P)) ==> (s IN (TRACES P)))",
	PROC_TAC);;

let proc_LEMMA3 =
    prove_thm
       (`proc_LEMMA3`,
	"!(P:process) (v:alphabet#((trace)set)).
	  ((P = ABS_process v) /\ (IS_PROCESS v))
          ==>
          ((TRACES P) SUBSET (STAR (ALPHA P)))",
	PROC_TAC);;

let [NIL_IN_TRACES; APPEND_IN_TRACES; TRACES_IN_STAR] =
    map
     (\(x,y). 
      let th1 = REWRITE_RULE [PAIR] (SPEC "P:process" PROCESS_LEMMA4)
      and th2 = UNDISCH_ALL (SPEC_ALL y)
      in
      save_thm (x, GEN_ALL (CHOOSE ("v:(alphabet#((trace)set))", th1) th2)))
     [(`NIL_IN_TRACES`, proc_LEMMA1);
      (`APPEND_IN_TRACES`, proc_LEMMA2);
      (`TRACES_IN_STAR`, proc_LEMMA3)];;

let ALPHA_FST =
    prove_thm
       (`ALPHA_FST`,
	"! x y. IS_PROCESS(x,y) ==> (ALPHA (ABS_process (x, y)) = x)",
	REWRITE_TAC [PROCESS_LEMMA6; ALPHA_DEF] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);;

let TRACES_SND =
    prove_thm
       (`TRACES_SND`,
	"! x y. IS_PROCESS(x,y) ==> (TRACES (ABS_process (x, y)) = y)",
	REWRITE_TAC [PROCESS_LEMMA6; TRACES_DEF] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);;

let PROCESS_EQ_SPLIT =
    prove_thm
       (`PROCESS_EQ_SPLIT`,
	"! P Q.
	   (P = Q) =
	   (((ALPHA P) = (ALPHA Q)) /\ ((TRACES P) = (TRACES Q)))",
	REWRITE_TAC
	 [ALPHA_DEF; TRACES_DEF; SYM (SPEC_ALL PAIR_EQ); PROCESS_LEMMA1]);;

close_theory ();;
