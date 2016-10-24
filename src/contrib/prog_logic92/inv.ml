%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        | 
|                                                              |
| inv.ml                                                       |
|                                                              |
| DESCRIPTION:	                                               |
|                                                              |
| Invariant Relations                                          |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

new_theory `inv`;;

loadf `mytactics`;;

load_library `reduce`;; 

loadf `l_arith_hack`;;
loadf `l_cpo`;;
loadf `l_lnum`;;
loadf `l_exseq`;;
loadf `l_pred`;;
loadf `l_sem`;;
loadf `l_wp`;;
loadf `l_hoare`;;

%
| Relations invariant throughout exseqs
%

let exseq_inv = new_definition
(	`exseq_inv`,
	"!e R. 
	 exseq_inv e R = 
		~ABORT e /\
		!n. WHOLE n <+ PR(length e) ==> 
			R(elt(WHOLE n) e, elt(WHOLE(SUC n)) e)"
);;

%
| Joining exseqs preserves invariance of relations
%

let exseq_inv_join = prove_thm
(	`exseq_inv_join`,
	"!e1 e2.!R1 R2.
	 (first e2 = last e1) ==>
	 TERM e1 ==>
	 exseq_inv e1 R1 ==>
	 exseq_inv e2 R2 ==>
	 exseq_inv (e1<*>e2) (R1 OR R2)",
	REWRITE_TAC[exseq_inv;OR]
	THEN REPEAT STRIP_TAC
	THENL	[IMP_RES_TAC join_ABORT
		 THEN RES_TAC
		;IMP_RES_TAC join_length
		 THEN IMP_RES_TAC join_elts
		 THEN ASM_REWRITE_TAC[]
		 THEN COND_CASES_TAC
		 THEN COND_CASES_TAC
		 THENL	[IMP_RES_TAC exseq_length_SUC_PR_shift
			 THEN BETA_TAC
			 THEN RES_TAC
			 THEN ASM_REWRITE_TAC[]
			;IMP_RES_TAC exseq_length_SUC_PR_shift
			 THEN REWRITE_ASM[]
			 THEN ASM_REWRITE_TAC[]
			 THEN IMP_RES_TAC length_less_suc_less_eq
			 THEN IMP_RES_TAC lnum_less_eq_as_less
			 THEN RES_TAC
			 THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
			 THEN REWRITE_TAC[lnum_sub;PR]
			 THEN UNDISCH_TAC "WHOLE(SUC n) = length e1"
			 THEN REWRITE_TAC
				[length_less_suc_swop
				;ADD1;ADD_SUB;ADD_SUB_SYM
				]
			 THEN DISCH_THEN SUBST1_TAC
			 THEN REWRITE_TAC[SYM_th last]
			 THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
			 THEN REWRITE_TAC[first]
			 THEN CONV_TAC (DEPTH_CONV num_CONV)
			 THEN BETA_TAC
			 THEN HALF_ASM_REWRITE_TAC[]
			 THEN REWRITE_TAC
				[SYM_th exseq_length_SUC_PR_shift]
			 THEN REDUCE_TAC
			 THEN REWRITE_TAC[length_min]
			;IMP_RES_TAC exseq_length_SUC_PR_shift
			 THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
			 THEN COND_CASES_TAC
			 THENL	[IMP_RES_TAC exseq_length_SUC_PR_shift
				 THEN IMP_RES_TAC length_PR_less
				 THEN IMP_RES_TAC lnum_less_trans_alt
				 THEN BETA_TAC
				 THEN RES_TAC
				 THEN ASM_REWRITE_TAC[]
				;REWRITE_ASM[TERM]
				 THEN BETA_TAC
				 THEN ASSUME_TAC(SPEC "e1:exseq" length_min)
				 THEN IMP_RES_TAC is_WHOLE_choose 
				 THEN REWRITE_ASM[lnum_less_reduce]
				 THEN ASM_REWRITE_TAC[lnum_sub;PR;ADD1]
				 THEN IMP_RES_TAC NOT_LESS
				 THEN IMP_RES_TAC ONE_LESS_NOUGHT_LESS
				 THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
				 THEN IMP_RES_TAC(SYM_th INV_PRE_LESS_EQ)
				 THEN RULE_ASSUM_TAC
					(REWRITE_RULE
					 [PRE_SUB1;ADD1;ADD_SUB])
				 THEN IMP_RES_TAC(SYM_th LESS_EQ_SUB_ADD)
				 THEN ASM_REWRITE_TAC[]
				 THEN HALF_ASM_REWRITE_TAC[]
				 THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
				 THEN IMP_RES_TAC SUB_SUB
				 THEN APPLY_TO 
					"!a. a - (n' - 1) = (a + 1) - n'"
					(\th.REWRITE_TAC[th])
				 THEN POP_IT
					"!n''. (n + n'') - n' = (n - n') + n''" 
				 THEN SUPPOSE_TAC "WHOLE n' <-+ WHOLE(n+1)"
				 THEN ASM_REWRITE_TAC[lnum_less_eq_reduce]
				 THEN RULE_ASSUM_TAC
					(ONCE_REWRITE_RULE
					 [SYM_th lnum_plus_sym])
				 THEN IMP_RES_TAC
					(SYM_th lnum_strict_plus_sub_move)
				 THEN ASM_REWRITE_TAC[SYM_th lnum_sub]
				]
			;IMP_RES_TAC lnum_WHOLE_less_PR_less
			 THEN REWRITE_ASM[]
			 THEN UNDISCH_TAC "F"
			 THEN REWRITE_TAC[]
			]
		]
);;

let exseq_inv_join_single = prove_thm
(	`exseq_inv_join_single`,
	"!e1 e2.!R.
	 (first e2 = last e1) ==>
	 TERM e1 ==>
	 exseq_inv e1 R ==>
	 exseq_inv e2 R ==>
	 exseq_inv (e1<*>e2) R",
	REPEAT STRIP_TAC
	THEN IMP_RES_TAC exseq_inv_join
	THEN REWRITE_ASM[OR;ETA_AX]
	THEN ASM_REWRITE_TAC[]
);;


%
| lubs preserve invariance
%

let lemma = PROVE
(	"!n. length(C n) = lengths C n",
	REWRITE_TAC[lengths]
	THEN BETA_TAC
	THEN REWRITE_TAC[]
);;

let lub_exseq_inv = prove_thm
(	`lub_exseq_inv`,
	"!C R. 
	 chain $<=| C ==>
	 (!n:num. exseq_inv (C n) R) ==>
	 exseq_inv(lub $<=| C) R",
	REPEAT GEN_TAC
	THEN DISCH_TAC
	THEN REWRITE_TAC[exseq_inv]
	THEN REPEAT STRIP_TAC
	THENL	[RULE_ASSUM_TAC(REWRITE_RULE[ABORT])
		 THEN RULE_ASSUM_TAC(CONV_RULE (TRY_CONV FORALL_AND_CONV))
		 THEN REPLACE_FIRST_ASSUM (ASSUME_TAC o CONJUNCT1)
		 THEN IMP_RES_TAC length_chain
		 THEN RULE_ASSUM_TAC(REWRITE_RULE[lemma])
		 THEN IMP_RES_TAC frag_lub
		 THEN IMP_RES_TAC exseq_lub_length
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		;IMP_RES_TAC exseq_length_SUC_PR_shift
		 THEN IMP_RES_TAC exseq_lub_elts
		 THEN SUPPOSE_TAC "WHOLE n <+ WHOLE (SUC n)"
		 THEN REWRITE_TAC[lnum_less_reduce;LESS_SUC_REFL]
		 THEN IMP_RES_TAC lnum_less_trans_alt	
		 THEN IMP_RES_TAC lub_fn_elt_n_SUC_n 
		 THEN IMP_RES_TAC exseq_lub_length
		 THEN REWRITE_ASM[]
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[] 
		 THEN IMP_RES_TAC (SYM_th exseq_length_SUC_PR_shift)
		 THEN RES_TAC
		]	
);; 

%
| Domain and range of a relation
%

let dom = new_definition
(	`dom`,
	"!R.!s:state. dom R s = ?t:state. R(s,t)"
);;

let dom_OR = prove_thm
(	`dom_OR`,
	"!R1 R2. dom(R1 OR R2) = (dom R1) OR (dom R2)",
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[OR;dom]
	THEN BETA_TAC
	THEN CONV_TAC(DEPTH_CONV EXISTS_OR_CONV)
	THEN REWRITE_TAC[]
);;

let OR_sym = prove_thm
(	`OR_sym`,
	"!R1 R2:*->bool. R1 OR R2 = R2 OR R1",
	REWRITE_TAC[OR]
	THEN REPEAT GEN_TAC
	THEN ONCE_RIGHT_SUBST_TAC DISJ_SYM
	THEN REFL_TAC
);;

let exseq_inv_OR = prove_thm
(	`exseq_inv_OR`,
	"!e R1 R2. 
	 exseq_inv e R1 ==> exseq_inv e (R1 OR R2)",
	REWRITE_TAC[exseq_inv;OR]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;

let ran = new_definition
(	`ran`,
	"!R.!t:state. ran R t = ?s:state.R(s,t)"
);;

%
| Sequences invariant under a relation terminate in the range 
| of the relation
%

let exseq_inv_ran = prove_thm
(	`exseq_inv_ran`,
	"!e. TERM e ==> exseq_inv e R ==> (ran R)(last e)",
	REWRITE_TAC[exseq_inv;ran;last]
	THEN GEN_TAC
	THEN DISCH_TAC
	THEN IMP_RES_TAC length_PR_as_SUC
	THEN REPEAT STRIP_TAC
	THEN EXISTS_TAC "elt(WHOLE n)e"
	THEN ASM_REWRITE_TAC[]
	THEN HALF_ASM_REWRITE_TAC[]
	THEN ASM_REWRITE_TAC[lnum_less_reduce;LESS_SUC_REFL]
);;

%
| Relations invariant under programs wrt a precondition
| No termination assertion
%

let rinv = new_infix_definition
(	`rinv`,
	"!R c. rinv c (P,R) = !e. c e ==> P(first e) ==> exseq_inv e R"  
);;

%
| Little logic of invariant relations wrt a precondition
%

%     skip preserves reflexive relations
|
|                !s. P s ==> R(s, s)
|     ----------------------------------------
|                  skip rinv (P,R)              
%

let skip_rinv = prove_thm
(	`skip_rinv`,
	"!P R.
	 (!s. P s ==> R(s,s)) ==>
	 skip rinv (P,R)", 
	REWRITE_TAC[skip;rinv;exseq_inv]
	THEN REPEAT STRIP_TAC
	THENL	[REWRITE_ASM[ABORT;is_FRAG;pair_length]
		 THEN ASM_REWRITE_TAC[]
		;REWRITE_ASM[pair_length;PR;lnum_less_reduce;pair_first]
		 THEN RULE_ASSUM_TAC REDUCE_RULE
		 THEN IMP_RES_TAC NOUGHT_LESS_ONE
		 THEN ASM_REWRITE_TAC[]
		 THEN SUPPOSE_TAC "WHOLE(SUC 0)=PR(length(pair(s',s')))"
  		 THENL	[ASM_REWRITE_TAC
				[SYM_th first
				;SYM_th last
				;pair_first
				;pair_last
				]
		 	 THEN RES_TAC
			;REWRITE_TAC[pair_length;PR;lnum_const_one_one]
			 THEN REDUCE_TAC
			]
		]
);;

%     empty preserves any relation from anywhere 
|                 
|     ----------------------------------------
|                  empty rinv (P,R)              
%

let empty_rinv = prove_thm
(	`empty_rinv`,
	"!P R. empty rinv (P,R)",
	REWRITE_TAC[empty;rinv]
);;

%     abort preserves no relation, except from nowhere
|
|                    P = false
|     -------------------------------------------------
|                  abort rinv (P,R)              
%

let abort_rinv = prove_thm
(	`abort_rinv`,
	"!P R.
	 (P = false) ==> 
	 abort rinv (P,R)",
	REWRITE_TAC[abort;rinv;abort_pair_ABORT;NONE]
	THEN REPEAT STRIP_TAC
	THEN REWRITE_ASM[]
	THEN UNDISCH_TAC "F"
	THEN REWRITE_TAC[]
);;

%     havoc preserves the universal relation
|
|                  !s t. R(s,t)  
|     ----------------------------------------
|                 havoc rinv (P,R)               
%

let havoc_rinv = prove_thm
(	`havoc_rinv`,
	"!P R. 
	 (!s t. R(s,t)) ==>
	 havoc rinv (P,R)",
	REWRITE_TAC[havoc;rinv;exseq_inv]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN IMP_RES_TAC TERM_not_ABORT
);;

%
|                 c rinv (b AND P, R)
|     ----------------------------------------
|                (b --> c) rinv (P, R)
%

let gcom_rinv = prove_thm
(	`gcom_rinv`,
	"!c P R.
	 c rinv (b AND P, R) ==> (b --> c) rinv (P, R)",
	REWRITE_TAC[gcom;rinv;AND]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

%
|           !s. P s ==> R(s, bnd (e s) x s)    
|     ----------------------------------------
|                 (x := e) rinv (P,R)
%

let pair_lemma = PROVE 
(	"!s s'. ~ABORT(pair(s,s'))",
	REWRITE_TAC[ABORT;pair_length;is_FRAG]
);;

let pair_lemma2 = PROVE
(	"!s s'. 
	 (elt(WHOLE 0)(pair(s,s')) = s) /\
	 (elt(WHOLE 1)(pair(s,s')) = s')",
	REPEAT GEN_TAC
	THEN SUPPOSE_TAC "WHOLE 1 = PR(length(pair(s,s')))"
	THENL	[ASM_REWRITE_TAC
			[SYM_th first
			;SYM_th last
			;pair_first
			;pair_last
			]
		;REWRITE_TAC[PR;pair_length;lnum_const_one_one]
		 THEN REDUCE_TAC
		]
);;

let pair_lemma3 = PROVE
(	"!s s'.
	 (!n.((WHOLE n) <+ (PR(length(pair(s,s')))) ==>
	   R(elt(WHOLE n)(pair(s,s')),elt(WHOLE(SUC n))(pair(s,s'))))) =
	 R(s,s')",
	REWRITE_TAC[pair_length;PR;lnum_less_reduce]
	THEN REDUCE_TAC
	THEN REWRITE_TAC[NOUGHT_LESS_ONE]
	THEN REPEAT STRIP_TAC
	THEN EQ_TAC
	THEN DISCH_TAC
	THENL	[STRIP_ASSUME_TAC(SPECL["s:state";"s':state"] pair_lemma2)
		 THEN ASSUM_LIST(ONCE_REWRITE_TAC o SYML_th)
		 THEN CONV_TAC(DEPTH_CONV num_CONV)
		 THEN HALF_ASM_REWRITE_TAC[]
		;REPEAT STRIP_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN REDUCE_TAC
		 THEN ASM_REWRITE_TAC[pair_lemma2]
		]
);;

let assign_rinv = prove_thm
(	`assign_rinv`,
	"!P R x exp.
 	 (!s. P s ==> R(s, bnd (exp s) x s)) ==>
	 (x := exp) rinv (P,R)",
	REWRITE_TAC[assign;rinv;exseq_inv]
	THEN BETA_TAC
	THEN REPEAT (GEN_TAC ORELSE (DISCH_THEN STRIP_ASSUME_TAC))
	THEN ASM_REWRITE_TAC[pair_lemma3;pair_lemma]
	THEN REWRITE_ASM[pair_first]
	THEN RES_TAC
);;

%
|          !s val. P s ==> R(s, bnd val x s)    
|     ----------------------------------------
|               (update x) rinv (P, R)
%

let update_rinv = prove_thm
(	`update_rinv`,
	"!P R x.
 	 (!s val. P s ==> R(s, bnd val x s)) ==>
	 (update x) rinv (P,R)",
	REWRITE_TAC[update;rinv;exseq_inv]
	THEN BETA_TAC
	THEN REPEAT (GEN_TAC ORELSE (DISCH_THEN STRIP_ASSUME_TAC))
	THEN ASM_REWRITE_TAC[pair_lemma3;pair_lemma]
	THEN REWRITE_ASM[pair_first]
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;

%
|              c1 rinv (P, R),  c2 rinv (ran R, R)
|     ----------------------------------------------------
|                     (c1 ;; c2) rinv (P, R)              
%

let seq_rinv = prove_thm
(	`seq_rinv`,
	"!c1 c2 P R.
	 c1 rinv (P,R) ==>
	 c2 rinv (ran R,R) ==>
	 (c1 ;; c2) rinv (P,R)",
	REWRITE_TAC[rinv;seq]
	THEN REPEAT STRIP_TAC
	THENL	[RES_TAC
		;ASM_REWRITE_TAC[]
		 THEN HALF_ASM_REWRITE_TAC[de_imp exseq_inv_join_single]
		 THEN IMP_RES_TAC join_first
		 THEN REWRITE_ASM[]
		 THEN RES_TAC
		 THEN IMP_RES_TAC exseq_inv_ran
		 THEN REWRITE_ASM[]	
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]	
		 THEN REWRITE_ASM[]
		 THEN RES_TAC
		]
);;

%
|             c1 rinv (P,R),  c2 rinv (P,R)
|     -------------------------------------------
|               (c1 || c2) rinv (P,R)              
%

let choose_rinv = prove_thm
(	`choose_rinv`,
	"!c1 c2 R P.
	  c1 rinv (P,R) /\  c2 rinv (P,R) ==>
	  (c1 || c2) rinv (P,R)",
	REWRITE_TAC[rinv;choose]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

%
|             c1 rinv (P,R),  c2 rinv ((NOT(grd c1)) AND P, R)
|     ---------------------------------------------------------------
|                        (c1 |X| c2) rinv (P,R)              
%

let orelse_rinv = prove_thm
(	`orelse_rinv`,
	"!c1 c2 R P.
	  c1 rinv (P,R) /\  c2 rinv ((NOT(grd c1)) AND P,R) ==>
	  (c1 |X| c2) rinv (P,R)",
	REWRITE_TAC[rinv;orelse;AND;NOT]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;


%
|                c rinv (P,R), P IMPLIES (grd c1)
|     ---------------------------------------------------
|                       (If c fI) rinv (P,R)              
%

let If_fI_rinv = prove_thm
(	`If_fI_rinv`,
	"!c P R.
 	 c rinv (P,R) /\ (!s.P s ==> (grd c)s) ==>
	 (If_fI c) rinv (P,R)",
	REWRITE_TAC[If_fI]
	THEN REPEAT STRIP_TAC
	THEN HALF_REWRITE_TAC[orelse_rinv;abort_rinv]
	THEN ASM_REWRITE_TAC[NOT;AND;NONE]
	THEN CONV_TAC FUN_EQ_CONV
	THEN BETA_TAC
	THEN REWRITE_TAC[]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
);;

%
|                   c rinv (P,R), (ran R) IMPLIES P
|     -------------------------------------------------------
|                        (rec c) rinv (P,R)              
%

let lemma = PROVE
(	"!Seq c m.
	 (!n. n < m ==> next c(Seq n)(Seq(SUC n))) ==>  
	 (!n. n < m ==> TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n)))", 
	REWRITE_TAC[next]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[SYM_th ADD1]
);;

let TTseq_exseq_inv = prove_thm
(	`TTseq_exseq_inv`,
	"!c Seq R m.
	 (!n. n < m ==> next c(Seq n)(Seq(SUC n))) ==> 
	 (!n. n<=m ==> exseq_inv(Seq n)R) ==> exseq_inv(TTseq Seq m)R",
	GEN_TAC THEN GEN_TAC THEN GEN_TAC
	THEN INDUCT_TAC
	THEN REPEAT DISCH_TAC
	THENL	[REWRITE_TAC[TTseq]
		 THEN ASSUME_TAC (SPEC "0" LESS_EQ_REFL) 
		 THEN RES_TAC
		;REWRITE_TAC[TTseq]
		 THEN SUPPOSE_TAC 
			"(!n. n < m ==> next c(Seq n)(Seq(SUC n))) /\
			 (!n. n <= m ==> exseq_inv(Seq n)R)"
		 THENL	[EVERY_ASSUM STRIP_ASSUME_TAC 
			 THEN RES_TAC
			 THEN ASSUME_TAC(SPEC "m:num" LESS_SUC_REFL)
			 THEN RES_TAC
			 THEN REWRITE_ASSUM[next] "next c(Seq m)(Seq(SUC m))"
			 THEN EVERY_ASSUM STRIP_ASSUME_TAC
			 THEN ONE_IMP_RES_TAC lemma
			 THEN IMP_RES_TAC TTseq_first_last_finite
			 THEN UNDISCH_TAC "first(Seq(SUC m)) = last(Seq m)"
			 THEN UNDISCH_TAC "last(TTseq Seq m) = last(Seq m)"
			 THEN DISCH_THEN (SUBST1_TAC o SYM_th)
			 THEN DISCH_TAC
			 THEN ASSUME_TAC (SPEC "SUC m" LESS_EQ_REFL)
			 THEN RES_TAC
 			 THEN IMP_RES_TAC exseq_inv_join_single
			 THEN ASM_REWRITE_TAC[SYM_th ADD1]
			;REPEAT STRIP_TAC
			 THENL	[IMP_RES_TAC LESS_SUC
				 THEN RES_TAC
				;HALF_ASM_REWRITE_TAC[]
				 THEN ASSUME_TAC
					(SPEC "m:num" LESS_EQ_SUC_REFL)
				 THEN IMP_RES_TAC LESS_EQ_TRANS
				]
			]
			 
		]
);;

let lemma2 = PROVE
(	"!Seq c.
	 (!n. next c(Seq n)(Seq(SUC n))) ==>  
	 (!n. TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n)))", 
	REWRITE_TAC[next]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[SYM_th ADD1]
);;

let TTseq_exseq_inv_lub = prove_thm
(	`TTseq_exseq_inv_lub`,
	"!c Seq R.
	 (!n. next c(Seq n)(Seq(SUC n))) ==>
	 (!n. exseq_inv (Seq n) R) ==>	
	 exseq_inv(lub $<=| (TTseq Seq)) R",
	HALF_REWRITE_TAC[de_imp lub_exseq_inv;de_imp TTseq_exseq_inv]
	THEN REPEAT STRIP_TAC
	THENL	[HALF_REWRITE_TAC[TTseq_chain]
		 THEN ONE_IMP_RES_TAC lemma2
		 THEN ASM_REWRITE_TAC[]
		;EXISTS_TAC "c:command"
		 THEN ASM_REWRITE_TAC[]
		]
);;

let lemma3 = PROVE
(	"!c Seq. 
	 (!n.next c(Seq n)(Seq(SUC n)))
 	  ==> c(Seq 0) 
	  ==> !n. c(Seq n)",
	REWRITE_TAC[next]
	THEN REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THEN ASM_REWRITE_TAC[]
);;

let rec_rinv = prove_thm
(	`rec_rinv`,
	"!c R. 
	 c rinv (P,R) /\
	 (!s.(ran R)s ==> P s) ==> (rec c) rinv (P,R)",
	REWRITE_TAC[rinv;rec]
	THEN REPEAT STRIP_TAC
	THENL	[ASM_REWRITE_TAC[]
		 THEN HALF_REWRITE_TAC[de_imp TTseq_exseq_inv]
		 THEN EXISTS_TAC "c:command"
		 THEN ASM_REWRITE_TAC[]
		 THEN INDUCT_TAC
		 THENL	[ONE_IMP_RES_TAC lemma
			 THEN IMP_RES_TAC TTseq_first_last_finite
			 THEN REWRITE_ASM[]
			 THEN REPEAT(POP_IT "T")
			 THEN RES_TAC
		 	 THEN ASM_REWRITE_TAC[]
			;REWRITE_TAC[SYM_th LESS_EQ]
			 THEN DISCH_TAC
			 THEN RES_TAC
			 THEN REWRITE_ASM[next]
			 THEN EVERY_ASSUM STRIP_ASSUME_TAC
			 THEN RES_TAC
		 	 THEN HALF_ASM_REWRITE_TAC[]
			 THEN ASM_REWRITE_TAC[]
			 THEN HALF_REWRITE_TAC[de_imp exseq_inv_ran]
			 THEN ASM_REWRITE_TAC[]
			 THEN HALF_ASM_REWRITE_TAC[]
			 THEN ASM_REWRITE_TAC[LESS_OR_EQ]
			]
		;ASM_REWRITE_TAC[]
		 THEN HALF_REWRITE_TAC[de_imp TTseq_exseq_inv_lub]
		 THEN EXISTS_TAC "c:command"
		 THEN ASM_REWRITE_TAC[]
		 THEN INDUCT_TAC
		 THENL	[RULE_ASSUM_TAC de_imp
			 THEN ONE_IMP_RES_TAC lemma2
			 THEN IMP_RES_TAC TTseq_chain
			 THEN IMP_RES_TAC lub_first 
			 THEN REWRITE_ASM[TTseq]
			 THEN RES_TAC
			;RULE_ASSUM_TAC de_imp
			 THEN REWRITE_ASM[next]
			 THEN HALF_ASM_REWRITE_TAC[]
			 THEN ASM_REWRITE_TAC[]
			 THEN HALF_ASM_REWRITE_TAC[de_imp exseq_inv_ran]
			]
		]
);;

%
|      !s.(ran R)s ==> P s, c rinv (P, R), !s. NOT(grd c)s /\ P s ==> R(s,s)
|     ------------------------------------------------------------------------
|                             (do c od) rinv (P,R)              
%

let do_od_rinv = prove_thm 
(	`do_od_rinv`,
	"!R c P.
	 (!s. (ran R)s ==> P s) 
		/\ c rinv (P, R)
		/\ (!s. ((NOT(grd c)) AND P) s ==> R(s,s))
	  ==> (do_od c) rinv (P,R)",
	REWRITE_TAC[do_od]
	THEN REPEAT STRIP_TAC
	THEN HALF_REWRITE_TAC[orelse_rinv;skip_rinv;rec_rinv]
	THEN ASM_REWRITE_TAC[SYM_th rec_grd]
);;

close_theory();;




