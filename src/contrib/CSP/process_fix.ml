% Fix point theory for CSP processes (traces semantics).		%
% 									%
% FILE		  : process_fix.ml 					%
% 									%
% READS FILES	  : stop.th, rules_and_tacs.ml	          		%
% LOADS LIBRARIES : sets, string		          		%
% WRITES FILES    : process_fix.th					%
%									%
% AUTHOR	  : Albert J Camilleri					%
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol		%
% DATE		  : 89.03.15						%
% REVISED	  : 91.10.01						%

load_library `sets`;;
load_library `string`;;
loadf `rules_and_tacs`;;

new_theory `process_fix`;;

new_parent `stop`;;

map (load_definition `process_ty`) [`IS_PROCESS`];;
map (load_theorem `process_ty`)
    [`PROCESS_EQ_SPLIT`; `NIL_IN_TRACES`; `ALPHA_FST`; `TRACES_SND`;
     `APPEND_IN_TRACES`; `TRACES_IN_STAR`];;

load_theorems `stop`;;


let EQ_SUB_THM =
    prove_thm
       (`EQ_SUB_THM`,
	"! A B:(*)set. (A = B) = (A SUBSET B /\ B SUBSET A)",
	REPEAT GEN_TAC THEN
	EQ_TAC THENL
	[DISCH_THEN SUBST1_TAC;
	 DISCH_THEN (SUBST1_TAC o (MATCH_MP SUBSET_ANTISYM))] THEN
	REWRITE_TAC [SUBSET_REFL]);;

let PROCESS_ORDER =
    new_infix_definition
       (`PROCESS_ORDER`,
	"$<< P Q =
         ((ALPHA P) = (ALPHA Q)) /\ ((TRACES P) SUBSET (TRACES Q))");;

let REFL_PROCESS_ORDER =
    prove_thm
       (`REFL_PROCESS_ORDER`,
	"!P. P << P",
	REWRITE_TAC [PROCESS_ORDER; SUBSET_REFL]);;

let TRANS_PROCESS_ORDER =
    prove_thm
       (`TRANS_PROCESS_ORDER`,
	"!P Q R. ((P << Q) /\ (Q << R)) ==> (P << R)",
	REWRITE_TAC [PROCESS_ORDER] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC SUBSET_TRANS THEN
	ASM_REWRITE_TAC []);;

let ANTISYM_PROCESS_ORDER =
    prove_thm
       (`ANTISYM_PROCESS_ORDER`,
	"!P Q. ((P << Q) /\ (Q << P)) ==> (P = Q)",
	REWRITE_TAC [PROCESS_ORDER; PROCESS_EQ_SPLIT; EQ_SUB_THM] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);;

let PROCESS_FIX =
    new_definition
       (`PROCESS_FIX`,
	"FIX_PROC fun = @P. (fun P = P) /\ !Q. (fun Q = Q) ==> (P << Q)");;

let ITER =
    new_prim_rec_definition
       (`ITER`,
        "(ITER 0       f x = (x:*)) /\
         (ITER (SUC n) f x = f(ITER n f x))");;

let IT_UNION =
    new_definition
      (`IT_UNION`,
       "IT_UNION c = {x:* | ?n:num. x IN (c n)}");;

let CHAIN =
    new_definition
       (`CHAIN`,
        "CHAIN (P:num->process) = !n. (P n) << (P(SUC n))");;

let CHAIN_EQ_ALPHA =
    prove_thm
       (`CHAIN_EQ_ALPHA`,
	"!P. CHAIN P ==> !n m. ALPHA (P n) = ALPHA (P m)",
	REWRITE_TAC [CHAIN; PROCESS_ORDER] THEN
	GEN_TAC THEN
	DISCH_TAC THEN
	INDUCT_TAC THENL
	[INDUCT_TAC THEN
	 FILTER_ASM_REWRITE_TAC (free_in "m:num") [] THEN
	 POP_ASSUM_LIST
	  (SUBST_TAC o
	   (map (\thm. (is_forall (concl thm)) =>
		 CONJUNCT1 (SPEC "m:num" thm) | I thm))) THEN
         REWRITE_TAC [];
	 GEN_TAC THEN
	 POP_ASSUM (ASSUME_TAC o (SYM o SPEC_ALL)) THEN
	 FILTER_ASM_REWRITE_TAC (free_in "m:num") [] THEN
	 POP_ASSUM_LIST
	  (SUBST_TAC o
	   (map (\thm. (is_forall (concl thm)) =>
		 SYM (CONJUNCT1 (SPEC "n:num" thm)) | I thm))) THEN
         REWRITE_TAC []]);;

let LIM_PROC =
    new_definition
       (`LIM_PROC`,
	"LIM_PROC P =
         @Q. CHAIN P ==>
             (Q = ABS_process
	          ((ALPHA (P 0)), (IT_UNION (\n:num. TRACES (P n)))))");;

let LIM_PROC_THM =
    save_thm
       (`LIM_PROC_THM`,
	GEN_ALL
	 (DISCH_ALL (ELIM_SELECT_RULE (ASSUME "CHAIN P") LIM_PROC)));;

let IS_PROCESS_LIMIT =
    prove_thm
       (`IS_PROCESS_LIMIT`,
	"!P. CHAIN P ==>
             IS_PROCESS ((ALPHA (P 0)), (IT_UNION (\n:num. TRACES (P n))))",
	REWRITE_TAC [IS_PROCESS; SUBSET_DEF; IT_UNION] THEN
	SET_SPEC_TAC THEN
	BETA_TAC THEN
	REPEAT STRIP_TAC THENL
	[IMP_RES_THEN (ASSUME_TAC o (SPECL ["0"; "n:num"])) CHAIN_EQ_ALPHA THEN
	 IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
	 ASM_REWRITE_TAC [];
	 REWRITE_TAC [NIL_IN_TRACES];
	 IMP_RES_TAC APPEND_IN_TRACES THEN
	 EXISTS_TAC "n:num" THEN
	 ASM_REWRITE_TAC []]);;

let ALPHA_LIMIT =
    save_thm
       (`ALPHA_LIMIT`,
	DISCH_ALL
	 (REWRITE_RULE
	  [SYM (UNDISCH (SPEC_ALL LIM_PROC_THM))]
	  (MP (SPECL ["ALPHA (P 0)";
		      "(IT_UNION (\n:num. TRACES (P n)))"] ALPHA_FST)
	      (UNDISCH (SPEC_ALL IS_PROCESS_LIMIT)))));;

let TRACES_LIMIT =
    save_thm
       (`TRACES_LIMIT`,
	DISCH_ALL
	 (REWRITE_RULE
	  [SYM (UNDISCH (SPEC_ALL LIM_PROC_THM))]
	  (MP (SPECL ["ALPHA (P 0)";
		      "(IT_UNION (\n:num. TRACES (P n)))"] TRACES_SND)
	      (UNDISCH (SPEC_ALL IS_PROCESS_LIMIT)))));;

let LEAST_PROCESS =
    prove_thm
       (`LEAST_PROCESS`,
	"!A P. (A = ALPHA P) ==> (STOP A << P)",
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC
	 [PROCESS_ORDER; ALPHA_STOP; TRACES_STOP; SUBSET_DEF; IN_SING] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [NIL_IN_TRACES]);;

let LUB_CHAIN1 =
    prove_thm
       (`LUB_CHAIN1`,
	"!P. CHAIN P ==> !n. (P n) << (LIM_PROC P)",
	REWRITE_TAC [PROCESS_ORDER] THEN
	REPEAT STRIP_TAC THENL
	[IMP_RES_TAC ALPHA_LIMIT THEN
	 IMP_RES_THEN (ASSUME_TAC o (SPECL ["n:num"; "0"])) CHAIN_EQ_ALPHA THEN
	 ASM_REWRITE_TAC [];
	 IMP_RES_TAC TRACES_LIMIT THEN
	 ASM_REWRITE_TAC [IT_UNION; SUBSET_DEF] THEN
	 BETA_TAC THEN
	 SET_SPEC_TAC THEN
	 REPEAT STRIP_TAC THEN
	 EXISTS_TAC "n:num" THEN
	 ASM_REWRITE_TAC []]);;

let LUB_CHAIN2 =
    prove_thm
       (`LUB_CHAIN2`,
	"!P Q. ((CHAIN P) /\ (!n. (P n) << Q)) ==> ((LIM_PROC P) << Q)",
	REWRITE_TAC [PROCESS_ORDER] THEN
	REPEAT STRIP_TAC THENL
	[IMP_RES_TAC ALPHA_LIMIT THEN
	 ASM_REWRITE_TAC [];
	 POP_ASSUM
	  (ASSUME_TAC o
	   (\x. REWRITE_RULE
	         [SUBSET_DEF] (GEN_ALL (CONJUNCT2 (SPEC_ALL x))))) THEN
	 IMP_RES_TAC TRACES_LIMIT THEN
	 ASM_REWRITE_TAC [IT_UNION; SUBSET_DEF] THEN
	 SET_SPEC_TAC THEN
	 BETA_TAC THEN
	 REPEAT STRIP_TAC THEN
	 RES_TAC]);;

let CONT_PROCESS =
    new_definition
       (`CONTINUOUS`,
        "CONTINUOUS fun =
         !P. CHAIN P ==> (fun (LIM_PROC P) = (LIM_PROC (\n.fun(P n))))");;

let MONO_PROCESS =
    new_definition
       (`MONO_PROCESS`,
        "MONO fun =
         !p1 p2. (p1 << p2) ==> ((fun p1) << (fun p2))");;

close_theory();;
