% Some laws proved about the process AFTER.				%
% 									%
% FILE		  : after_laws.ml					%
% 									%
% READS FILES	  : process.th, rules_and_tacs.ml          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : after_laws.th					%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%

load_library `sets`;;
load_library `string`;;
loadf `rules_and_tacs`;;

new_theory `after_laws`;;

new_parent `process`;;

map (load_theorem `list_lib1`) [`CONS_EQ_APPEND`; `APPEND_EQ_NIL`];;

map (load_theorem `process_ty`)
    [`ALPHA_FST`; `TRACES_SND`; `APPEND_IN_TRACES`;
     `NIL_IN_TRACES`; `PROCESS_EQ_SPLIT`];;

map (load_theorem `prefix`) [`ALPHA_PREFIX`; `TRACES_PREFIX`];;

load_definition `after` `AFTER`;;
load_theorem `after` `TRACES_AFTER`;;

map (load_theorem `choice`) [`TRACES_choice`; `ALPHA_choice_SPEC`];;

let SET_ABBREV =
    prove_thm
       (`SET_ABBREV`,
	"! A. {x:* | x IN A} = A",
	REWRITE_TAC [EXTENSION] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC []);;

let AFTER_NIL =
    save_thm
       (`AFTER_NIL`,
	REWRITE_RULE [NIL_IN_TRACES; APPEND; SET_ABBREV;
                      SYM (SPEC_ALL PROCESS_EQ_SPLIT)]
	             (SPECL ["P:process"; "[]:trace"] AFTER));;

let TRACES_AFTER_THM =
    prove_thm
       (`TRACES_AFTER_THM`,
	"! s t P.
           ((APPEND s t) IN (TRACES P)) ==>
           ((s IN (TRACES P)) /\ (t IN (TRACES (P / s))))",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC APPEND_IN_TRACES THEN
	IMP_RES_TAC TRACES_AFTER THEN
	ASM_REWRITE_TAC [] THEN
	SET_SPEC_TAC THEN
	ASM_REWRITE_TAC []);;

let AFTER_APPEND =
    prove_thm
       (`AFTER_APPEND`,
	"! s t P.
           (APPEND s t) IN (TRACES P) ==>
           ((P / (APPEND s t)) = ((P / s) / t))",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC TRACES_AFTER_THM THEN
	IMP_RES_TAC AFTER THEN
	ASM_REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
	SET_SPEC_TAC THEN
	REWRITE_TAC [APPEND_ASSOC]);;

let simplify_lemma =
    TAC_PROOF
       (([],
	 "! t c. (?t'. (APPEND[c]t = CONS c t') /\ t' IN (TRACES P)) =
	 	 t IN (TRACES P)"),
	REPEAT GEN_TAC THEN EQ_TAC THEN
	REWRITE_TAC [SYM (SPEC_ALL CONS_EQ_APPEND); CONS_11] THEN
	REPEAT STRIP_TAC THEN
	(EXISTS_TAC "t:trace" ORELSE ALL_TAC) THEN
	ASM_REWRITE_TAC []);;

let AFTER_PREFIX =
    prove_thm
       (`AFTER_PREFIX`,
        "! c P. (c IN (ALPHA P)) ==> (((c --> P) / [c]) = P)",
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC ALPHA_PREFIX THEN
        IMP_RES_THEN
         (ASSUME_TAC o SET_SPEC_RULE o
          (\x. REWRITE_RULE [x; IN_UNION; IN_SING]
	   		    (SPECL ["c --> P"; "[c:event]"] AFTER)))
        TRACES_PREFIX THEN
        POP_ASSUM
         (STRIP_ASSUME_TAC o
	  (REWRITE_RULE [NIL_IN_TRACES; simplify_lemma; SET_ABBREV]) o
	  (SPEC "[]:trace") o
	  (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)) o
          REWRITE_RULE [APPEND_EQ_NIL; NOT_CONS_NIL; CONS_11]) THEN
        ASM_REWRITE_TAC [PROCESS_EQ_SPLIT]);;

let simplify_lemma2 =
    TAC_PROOF
       (([],
	 "(?a t'. (APPEND[c]t = CONS a t') /\ a IN B /\ t' IN (TRACES(P a))) =
	  (c IN B /\ t IN (TRACES (P c)))"),
	EQ_TAC THEN
	REWRITE_TAC [SYM (SPEC_ALL CONS_EQ_APPEND); CONS_11] THEN
	REPEAT STRIP_TAC THEN
	(EXISTS_TAC "c:event" ORELSE ALL_TAC) THEN
	(EXISTS_TAC "t:trace" ORELSE ALL_TAC) THEN
	ASM_REWRITE_TAC []);;

let simplify_lemma3 =
    TAC_PROOF
       (([],
	 "(?(a:event)t.((c = a) /\ ([] = t)) /\ a IN B /\ t IN (TRACES(P a))) =
	  c IN B"),
	EQ_TAC THEN
	REWRITE_TAC [SYM (SPEC_ALL CONS_EQ_APPEND); CONS_11] THEN
	REPEAT STRIP_TAC THEN
	(EXISTS_TAC "c:event" ORELSE ALL_TAC) THEN
	(EXISTS_TAC "[]:trace" ORELSE ALL_TAC) THEN
	ASM_REWRITE_TAC [NIL_IN_TRACES]);;

let AFTER_CHOICE_LEMMA =
    DISCH_ALL
     (ASM_REWRITE_RULE
      [SET_ABBREV]
      (UNDISCH
       (REWRITE_RULE
        [APPEND_EQ_NIL; NOT_CONS_NIL;CONS_11; simplify_lemma2; simplify_lemma3]
        (SET_SPEC_RULE
         (REWRITE_RULE [IN_UNION; IN_SING]
	 (SUBS
	  [UNDISCH_ALL
	   (SPECL ["B:alphabet"; "P:event->process"] TRACES_choice)]
	  (ADD_ASSUM "WELL_DEF_ALPHA B P"
		     (SPECL ["choice B P"; "[c:event]"] AFTER))))))));;

let AFTER_CHOICE =
    prove_thm
       (`AFTER_CHOICE`,
	"! c P B. (WELL_DEF_ALPHA B P) /\ (c IN B) ==>
                  (((choice B P) / [c]) = (P c))",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC AFTER_CHOICE_LEMMA THEN
	IMP_RES_TAC ALPHA_choice_SPEC THEN
	ASM_REWRITE_TAC [PROCESS_EQ_SPLIT]);;

close_theory();;
