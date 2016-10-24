%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        | 
|                                                              |
| wp.ml                                                        |
|                                                              |
| DESCRIPTION:	                                               |
|                                                              |
| Derives Dijkstra's calculus of weakest (liberal)             |
| preconditions                                                |
| for the language defined in sem.ml			       |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

new_theory `wp`;;
loadf `mytactics`;;

load_library `taut`;;
load_library `reduce`;;

loadf `l_arith_hack`;;
loadf `l_cpo`;;
loadf `l_lnum`;;
loadf `l_exseq`;;
loadf `l_pred`;;
loadf `l_sem`;;

%
| Define Dijkstra's weakest precondition operator wp c R
%

let wp = new_definition (
	`wp`,
	"!c:command.!R.!s:state.
	 wp c R s  = 
		!e. c e ==> (first e = s) ==> (TERM e /\ R (last e))"
);;

%
| Define Dijkstra's weakest liberal precondition operator wlp c R
%

let wlp = new_definition (
	`wlp`,
	"!c:command.!R.!s:state.
	 wlp c R s  = 
		!e. c e ==> (first e = s) ==> TERM e ==> R (last e)"
);;

%
| Prove the "pairing" condition
%

let wp_wlp_pairing = prove_thm
(	`wp_wlp_pairing`,
	"!c R. wp c R = (wlp c R) AND (wp c true)",
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[wlp;wp;AND;ALL]
	THEN BETA_TAC
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;

%
| Verify the `Healthiness Conditions`. Partial commands exclude 
| `the law of the excluded miracle`, but this holds for total commands
%
                                                                      
let excluded_miracle = prove_thm (
	`excluded_miracle`,
	"!c. (grd c = true) ==> (wp c false = false)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [grd;wp;ALL;NONE] 
	THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) 
	THEN REWRITE_TAC [NOT_IMP;NOT_CLAUSES] 
);;

let conjunctivity_wp = prove_thm (
	`conjunctivity_wp`,
	"!c Q R. (wp c Q) AND (wp c R) = wp c (Q AND R)",
	REPEAT GEN_TAC
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC [wp;AND]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;
 
let conjunctivity_wlp = prove_thm (
	`conjunctivity_wlp`,
	"!c Q R. (wlp c Q) AND (wlp c R) = wlp c (Q AND R)",
	REPEAT GEN_TAC
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC [wlp;AND]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);; 

let disjunctivity_wp = prove_thm (
	`disjunctivity_wp`,
	"!c Q R. EWR(((wp c Q) OR (wp c R)) IMPLIES (wp c (Q OR R)))",
        REPEAT GEN_TAC
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC [wp;OR;IMPLIES;ALL;EWR]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;

let disjunctivity_wlp = prove_thm (
	`disjunctivity_wlp`,
	"!c:command.!Q R. 
	 EWR(((wlp c Q) OR (wlp c R)) IMPLIES 
		(wlp c (Q OR R)))",
        REPEAT GEN_TAC
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC [wlp;OR;IMPLIES;EWR]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;
  
let LEFT_OR_OVER_IMP = TAUT_PROVE "!p q r. r\/(p==>q) = p==>(r\/q)";;
let RIGHT_OR_OVER_IMP= TAUT_PROVE "!p q r. (p ==>q)\/r = p==>(r\/q)";;

let det_disjunctivity_wp = prove_thm (
	`det_disjunctivity_wp`,
	"!c Q R. det c ==> ((wp c Q) OR (wp c R) = wp c (Q OR R))",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC [det;wp;OR;IMPLIES;ALL]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT STRIP_TAC 
	THEN CONV_TAC (RATOR_CONV (ONCE_DEPTH_CONV RIGHT_OR_FORALL_CONV))
        THEN CONV_TAC (RATOR_CONV (ONCE_DEPTH_CONV LEFT_OR_FORALL_CONV))
	THEN REWRITE_TAC [LEFT_OR_OVER_IMP;RIGHT_OR_OVER_IMP;LEFT_AND_OVER_OR]
	THEN EQ_TAC 
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
	THEN EVERY_ASSUM (\th.TRY (SUBST_ALL_TAC th)) 
	THEN SUBST_ALL_TAC (EQT_INTRO (REFL "f:state"))
	THEN RES_TAC 
	THEN FILTER_ASM_REWRITE_TAC (\t.t="e'=e:exseq") [] 
	THEN ASSUM_REDUCE_TAC
);;

let det_disjunctivity_wlp = prove_thm (
	`det_disjunctivity_wlp`,
	"!c Q R. det c ==> ((wlp c Q) OR (wlp c R) = wlp c (Q OR R))",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC [det;wlp;OR;IMPLIES;ALL]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT STRIP_TAC 
	THEN CONV_TAC (RATOR_CONV (ONCE_DEPTH_CONV RIGHT_OR_FORALL_CONV))
        THEN CONV_TAC (RATOR_CONV (ONCE_DEPTH_CONV LEFT_OR_FORALL_CONV))
	THEN REWRITE_TAC [LEFT_OR_OVER_IMP;RIGHT_OR_OVER_IMP;LEFT_AND_OVER_OR]
	THEN EQ_TAC 
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
	THEN EVERY_ASSUM (\th.TRY (SUBST_ALL_TAC th)) 
	THEN SUBST_ALL_TAC (EQT_INTRO (REFL "f:state"))
	THEN RES_TAC 
	THEN FILTER_ASM_REWRITE_TAC (\t.t="e'=e:exseq") [] 
	THEN ASSUM_REDUCE_TAC
);;
 
let skip_wp = prove_thm (
	`skip_wp`,
	"!R. wp skip R = R",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;skip]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV)
	THEN REPEAT GEN_TAC 
	THEN EQ_TAC 
        THENL	[DISCH_THEN 
			 ( MP_TAC  
			 o REWRITE_RULE[pair_first;pair_last;pair_TERM] 
			 o (SPEC "pair(f,f)")
			 )
	 	  THEN SUPPOSE_TAC "?s'. pair(f,f) = pair(s',s')" 
	       	  THENL	[ASSUM_REDUCE_TAC
			;EXISTS_TAC "f:state"
		 	 THEN REFL_TAC
			] 
		; REPEAT STRIP_TAC
		  THENL	[ASM_REWRITE_TAC [pair_last;pair_first;pair_TERM]
		  	;ONCE_REWRITE_TAC [SYM_th pair_first] 
		    	 THEN ASM_REWRITE_TAC[pair_last]
			 THEN UNDISCH_TAC "first e = f"
			 THEN ASM_REWRITE_TAC[pair_first] 
			 THEN DISCH_THEN \th.ASM_REWRITE_TAC[th]
	          	] 
		]
);;

let skip_wlp = prove_thm 
(	`skip_wlp`,
	"!R. wlp skip R = R",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;skip]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV)
	THEN REPEAT GEN_TAC 
	THEN CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[REPLACE_FIRST_ASSUM
			(ASSUME_TAC o (SPECL["pair(f,f)";"f:state"]))
		 THEN REWRITE_ASM[pair_first;pair_TERM;pair_last]
		 THEN ASM_REWRITE_TAC[]
		;ASM_REWRITE_TAC[pair_last]
		 THEN REWRITE_ASM[pair_first]
		 THEN ASM_REWRITE_TAC[]
		]
);;
 
let empty_wp = prove_thm (
	`empty_wp`,
	"!R. wp empty R = true",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;empty;ALL]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV)
);;

let empty_wlp = prove_thm (
	`empty_wlp`,
	"!R. wlp empty R = true",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;empty;ALL]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV)
);;

let NOT_OVER_IMP = TAUT_PROVE "!p q:bool. ~(p==>q) = (p /\ ~q)";; 

let abort_wp = prove_thm (
	`abort_wp`,
	"!R. wp abort R = false",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;abort;NONE]
	THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
	THEN REWRITE_TAC [NOT_OVER_IMP]
	THEN REPEAT GEN_TAC
	THEN EXISTS_TAC "abort_pair (f,f)" 
	THEN REWRITE_TAC 
		[DE_MORGAN_THM
		;abort_pair_first
		;TERM
		;abort_pair_length
		;is_WHOLE
		]
	THEN EXISTS_TAC "f:state"
	THEN REFL_TAC
);;
 
let abort_wlp = prove_thm (
	`abort_wlp`,
	"!R. wlp abort R = true",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;abort;ALL]
	THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
	THEN CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV)
	THEN REPEAT STRIP_TAC
	THEN REWRITE_ASM 
		[abort_pair_first
		;TERM
		;abort_pair_length
		;is_WHOLE
		]
	THEN UNDISCH_TAC "F"
	THEN REWRITE_TAC[]
);;

let havoc_wp = prove_thm (
	`havoc_wp`,
	"!R. wp havoc R =  \s. EWR R",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [EWR;wp;havoc;NONE]
        THEN CONV_TAC 
		(DEPTH_CONV 
			(BETA_CONV 
			 ORELSEC NOT_FORALL_CONV 
			)
		)
	THEN REPEAT GEN_TAC 
        THEN EQ_TAC 
	THEN REPEAT STRIP_TAC
        THENL	[
		 FIRST_ASSUM (MP_TAC o (SPEC "pair(f,t)"))
		 THEN REWRITE_TAC [pair_first;pair_last;pair_TERM]
                ;ASM_REWRITE_TAC[]
		;ASM_REWRITE_TAC[]
		]
);;

let havoc_wlp = prove_thm (
	`havoc_wlp`,
	"!R. wlp havoc R = \s.EWR R",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [EWR;wlp;havoc;NONE]
        THEN BETA_TAC
	THEN REPEAT GEN_TAC 
        THEN EQ_TAC 
	THEN REPEAT STRIP_TAC
        THENL	[FIRST_ASSUM (MP_TAC o (SPEC "pair(f,t)"))
		 THEN REWRITE_TAC [pair_first;pair_last;pair_TERM]
                ;ASM_REWRITE_TAC[]
		]
);;

% wp (x:=exp) R = \s. s = s[(exp s)/x] % 

let assign_wp = prove_thm (
	`assign_wp`,
	"!R x exp. wp (x := exp) R = subs exp x R",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;assign;subs]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THENL	[DISCH_THEN (MP_TAC o (SPEC "pair (f, bnd(exp f)x f)"))
		 THEN SUPPOSE_TAC 
			"(?s s'. (pair(f,bnd(exp f)x f) = pair(s,s')) /\ 
					(s' = bnd(exp s)x s))" 
		 THENL	[ASM_REWRITE_TAC[pair_first;pair_TERM;pair_last]
			;EXISTS_TAC "f:state"
			 THEN EXISTS_TAC "bnd(exp f)x f"
			 THEN REWRITE_TAC[]
			]
		;REPEAT STRIP_TAC
		 THENL	[ASM_REWRITE_TAC[pair_TERM]
			;ASM_REWRITE_TAC[pair_last]
			 THEN UNDISCH_TAC "first e = f"	
			 THEN ASM_REWRITE_TAC[pair_first]
			 THEN DISCH_TAC
			 THEN ASM_REWRITE_TAC[]
			] 
		]
);;

let assign_wlp = prove_thm (
	`assign_wlp`,
	"!R x exp. wlp (x := exp) R = subs exp x R",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;assign;subs]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV)
	THEN CONV_TAC (TOP_DEPTH_CONV LEFT_IMP_EXISTS_CONV)
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[REPLACE_FIRST_ASSUM
			(ASSUME_TAC
			o (SPECL
			   ["pair(f,bnd(exp f)x f)";"f:state";"bnd(exp f)x f"])
			)
		 THEN REWRITE_ASM[pair_first;pair_last;pair_TERM]
		 THEN ASM_REWRITE_TAC[]
		;REPEAT STRIP_TAC
		 THEN REWRITE_ASM[pair_first]
		 THEN ASM_REWRITE_TAC[pair_last]
		]
);;

let update_wp = prove_thm
(	`update_wp`,
	"!x P. wp (update x) P = forevery x P",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[wp;update;forevery]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN EQ_TAC
	THENL	[REPEAT STRIP_TAC 
		 THEN REPLACE_FIRST_ASSUM 
			(ASSUME_TAC 
			o (SPEC "pair(f,bnd val x f)")
			)
		 THEN REWRITE_ASM[pair_first;pair_TERM;pair_last]
		 THEN FIRST_ASSUM(\th.HALF_REWRITE_TAC[th])
		 THEN MAP_EVERY EXISTS_TAC ["f:state";"val:num"]
		 THEN REWRITE_TAC[]
		;DISCH_TAC
		 THEN GEN_TAC
		 THEN REPEAT DISCH_TAC
		 THEN REPLACE_FIRST_ASSUM(CHOOSE_THEN CHOOSE_TAC)
		 THEN ASM_REWRITE_TAC[pair_TERM;pair_last]
		 THEN REWRITE_ASM[pair_first]
		 THEN ASM_REWRITE_TAC[]
		]
);;

let update_wlp = prove_thm
(	`update_wlp`,
	"!x P. wlp (update x) P = forevery x P",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[wlp;update;forevery]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN EQ_TAC
	THENL	[REPEAT STRIP_TAC 
		 THEN REPLACE_FIRST_ASSUM 
			(ASSUME_TAC 
			o (SPEC "pair(f,bnd val x f)")
			)
		 THEN REWRITE_ASM[pair_first;pair_TERM;pair_last]
		 THEN FIRST_ASSUM (\th.HALF_REWRITE_TAC[th])
		 THEN MAP_EVERY EXISTS_TAC ["f:state";"val:num"]
		 THEN REWRITE_TAC[]
		;DISCH_TAC
		 THEN GEN_TAC
		 THEN REPEAT DISCH_TAC
		 THEN REPLACE_FIRST_ASSUM(CHOOSE_THEN CHOOSE_TAC)
		 THEN ASM_REWRITE_TAC[pair_TERM;pair_last]
		 THEN REWRITE_ASM[pair_first]
		 THEN ASM_REWRITE_TAC[]
		]
);;

let ANTE_DISJ_IMP = 
	TAUT_PROVE "!p q r. (p \/ q) ==> r = (p==>r) /\ (q==>r)";; 

let choose_wp = prove_thm (
	`choose_wp`,
	"!c1 c2 R. wp (c1 || c2) R = (wp c1 R) AND (wp c2 R)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;choose;AND]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REWRITE_TAC [ANTE_DISJ_IMP]
	THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
	THEN REWRITE_TAC[]
);;

let choose_wlp = prove_thm (
	`choose_wlp`,
	"!c1 c2 R. wlp (c1 || c2) R = (wlp c1 R) AND (wlp c2 R)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;choose;AND]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REWRITE_TAC [ANTE_DISJ_IMP]
	THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
	THEN REWRITE_TAC[]
);;

let orelse_wp = prove_thm (
	`orelse_wp`,
	"!c1 c2 R. wp (c1 |X| c2) R = wp c1 R AND (grd c1 OR (wp c2 R))",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;orelse;AND;OR]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
        THEN REWRITE_TAC [ANTE_DISJ_IMP]
	THEN REPEAT GEN_TAC 
	THEN EQ_TAC 
	THENL	[REPEAT DISCH_TAC
		 THEN DISJ_CASES_TAC (SPEC "grd c1 f" EXCLUDED_MIDDLE)
		 THEN ASM_REWRITE_TAC[]
		 THEN REPEAT STRIP_TAC
		 THEN UNDISCH_TAC "~grd c1 f"
		 THEN ASSUM_LIST (REWRITE_TAC o SYML_th)
		 THEN DISCH_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		;REPEAT STRIP_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN UNDISCH_TAC  "~grd c1(first e)" 
		 THEN ASM_REWRITE_TAC[]  
		]
);;
   
let orelse_wlp = prove_thm (
	`orelse_wlp`,
	"!c1 c2 R. wlp (c1 |X| c2) R = wlp c1 R AND (grd c1 OR (wlp c2 R))",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;orelse;AND;OR]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
        THEN REWRITE_TAC [ANTE_DISJ_IMP]
	THEN REPEAT GEN_TAC 
	THEN EQ_TAC 
	THENL	[REPEAT DISCH_TAC
		 THEN DISJ_CASES_TAC (SPEC "grd c1 f" EXCLUDED_MIDDLE)
		 THEN ASM_REWRITE_TAC[]
		 THEN REPEAT STRIP_TAC
		 THEN UNDISCH_TAC "~grd c1 f"
		 THEN ASSUM_LIST (REWRITE_TAC o SYML_th)
		 THEN DISCH_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		;REPEAT STRIP_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN UNDISCH_TAC  "~grd c1(first e)" 
		 THEN ASM_REWRITE_TAC[]  
		]
);;   

let RIGHT_IMP_OVER_OR = TAUT_PROVE "!p q r.(p\/q)==>r = (p==>r)/\ (q==>r)";;
let lemma = TAUT_PROVE "!p q. ~p ==> (p/\q) = p";;
let lemma2 = TAUT_PROVE "!a b c d. (b/\~a)==>c==>(a/\d) = c==>b==>a";;

let seq_wp = prove_thm (
	`seq_wp`,
	"!c1 c2 R. wp (c1 ;; c2) R = wp c1 (wp c2 R)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;seq]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV)
	THEN REPEAT GEN_TAC 
        THEN REWRITE_TAC[RIGHT_IMP_OVER_OR;lemma2] 
	THEN EQ_TAC 
        THENL	[DISCH_TAC
		 THEN GEN_TAC
                 THEN REPEAT DISCH_TAC
		 THEN FIRST_ASSUM (MP_TAC o CONJUNCT1 o (SPEC "e:exseq"))
                 THEN ASSUM_REDUCE_TAC
		 THEN DISCH_TAC
		 THEN ASM_REWRITE_TAC[]
                 THEN GEN_TAC
		 THEN REPEAT DISCH_TAC
                 THEN FIRST_ASSUM (MP_TAC o (SPEC "e <*> e':exseq"))
                 THEN IMP_RES_TAC join_first
                 THEN FILTER_ASM_REWRITE_TAC
			(\t.t="first(e <*> e') = first e")
			[]
                 THEN FILTER_ASM_REWRITE_TAC
			(\t.t="first e  = f")
			[]
		 THEN CONV_TAC (DEPTH_CONV ANTE_CONJ_CONV) 
		 THEN REPEAT DISCH_TAC
		 THEN UNDISCH_TAC 
                       "(?e1 e2.
        		 c1 e1 /\
     			    TERM e1 /\
        			 c2 e2 /\
     			    (first e2 = last e1) /\
        			 (e <*> e' = e1 <*> e2)) ==>
   			    TERM(e <*> e') /\ R(last(e <*> e'))"
		 THEN IMP_RES_TAC join_TERM 
		 THEN SUPPOSE_TAC 
                         "?e1 e2.
        		 c1 e1 /\
     			    TERM e1 /\
        			 c2 e2 /\
     			    (first e2 = last e1) /\
        			 (e <*> e' = e1 <*> e2)"
		 THENL	[ASSUM_REDUCE_TAC
			 THEN CONV_TAC (DEPTH_CONV ANTE_CONJ_CONV) 
			 THEN REPEAT DISCH_TAC
			 THEN UNDISCH_TAC
				"TERM(e <*> e') ==> TERM e'" 
			 THEN FILTER_ASM_REWRITE_TAC
				(\t.t="TERM(e <*> e')")
				[]
			 THEN DISCH_TAC
			 THEN ASM_REWRITE_TAC[]
			 THEN IMP_RES_TAC join_last
                         THEN APPLY_TO
				"last(e <*> e') = last e'"
				(\th.REWRITE_TAC [SYM_th th]) 
			 THEN ASSUM_REDUCE_TAC
			;EXISTS_TAC "e:exseq"
			 THEN EXISTS_TAC "e':exseq" 
			 THEN ASM_REWRITE_TAC[]
			]
		;DISCH_TAC
		 THEN GEN_TAC 
		 THEN CONJ_TAC 
		 THEN REPEAT DISCH_TAC
		 THENL	[RES_TAC
			;UNDISCH_TAC 
                              "?e1 e2.
   				c1 e1 /\
       				TERM e1 /\
    				 c2 e2 /\
    				 (first e2 = last e1) /\
  				 (e = e1 <*> e2)"
			 THEN STRIP_TAC
			 THEN RES_TAC 
			 THEN IMP_RES_TAC join_first 
                         THEN APPLY_TO 
				"first(e1 <*> e2) = first e1" 
				(SUBST_ALL_TAC o SYM_th)
			 THEN APPLY_TO
				"e = e1 <*> e2" 
				SUBST_ALL_TAC 
			 THEN RES_TAC
			 THEN IMP_RES_TAC join_last
			 THEN APPLY_TO
				"last(e1 <*> e2) = last e2"
				SUBST1_TAC
			 THEN ASSUM_REDUCE_TAC
			 THEN IMP_RES_TAC join_TERM
			] 
		]
);;

let seq_wlp = prove_thm (
	`seq_wlp`,
	"!c1 c2 R. wlp (c1 ;; c2) R = wlp c1 (wlp c2 R)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;seq]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV)
	THEN REPEAT GEN_TAC
	THEN CONV_TAC (TOP_DEPTH_CONV RIGHT_OR_EXISTS_CONV) 
	THEN CONV_TAC (TOP_DEPTH_CONV LEFT_IMP_EXISTS_CONV)
	THEN CONV_TAC (DEPTH_CONV RIGHT_IMP_FORALL_CONV)
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[MAP_EVERY IMP_RES_TAC[join_first;join_last;join_TERM]
		 THEN REWRITE_ASM[]
		 THEN ASSUME_TAC(REFL "e<*>e'")
		 THEN RES_TAC
		 THEN POP_IT "e <*> e' = e <*> e'"
		 THEN REWRITE_ASM[]
		 THEN ASSUM_REDUCE_TAC
		;RES_TAC
		;REWRITE_ASM[]
		 THEN MAP_EVERY IMP_RES_TAC
		 	[join_TERM;join_first;join_last]
		 THEN REWRITE_ASM[]
		 THEN RES_TAC	
		 THEN ASM_REWRITE_TAC[]				
        	]
);;

% Unused lemma

let lemma = TAUT_PROVE "!p q. ~p \/ q = p ==> q";;
let lemma2 = TAUT_PROVE "!p q. p \/ ~q = q ==> p";;

let grd_seq_lemma = PROVE (
	"!c1 c2 s. 
	 ~grd (c1 ;; c2) s ==> wp c1 (NOT (grd c2)) s ",
	REPEAT GEN_TAC
	THEN REWRITE_TAC [grd; seq; wp; NOT]
        THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
        THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) 
	THEN REWRITE_TAC [DE_MORGAN_THM]
        THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) 
        THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) 
        THEN REWRITE_TAC [DE_MORGAN_THM;lemma;lemma2] 
	THEN DISCH_TAC
	THEN GEN_TAC
	THEN FIRST_ASSUM (MP_TAC o SPEC_ALL)
	THEN DISCH_THEN STRIP_ASSUME_TAC
	THEN ASM_REWRITE_TAC[]
	THEN REPEAT STRIP_TAC 
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
   	THEN FIRST_ASSUM (MP_TAC o (SPEC "e <*> e'"))
	THEN IMP_RES_TAC join_first 
	THEN FILTER_ASM_REWRITE_TAC 
		(\t.t="first(e <*> e') = first e") []
	THEN ASM_REWRITE_TAC[]
	THEN REWRITE_TAC [DE_MORGAN_THM]
	THEN CONV_TAC (DEPTH_CONV  NOT_FORALL_CONV)
	THEN CONV_TAC (DEPTH_CONV  NOT_FORALL_CONV)
	THEN DISJ2_TAC
	THEN EXISTS_TAC "e:exseq"
	THEN EXISTS_TAC "e':exseq"
	THEN ASM_REWRITE_TAC[]
);;
%

let gcom_wp = prove_thm (
	`gcom_wp`,
	"!c P R. wp (P --> c) R = P IMPLIES (wp c R)",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wp;gcom;IMPLIES]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THENL	[REPEAT STRIP_TAC
		 THEN FIRST_ASSUM (ASSUME_TAC o (SPEC "e:exseq"))
		 THEN UNDISCH_TAC 
			"P(first e) /\ c e ==> (first e = f) 
				==> TERM e /\ R(last e)" 
		 THEN ASSUM_REDUCE_TAC
		 THEN ASM_REWRITE_TAC[] 
		 THEN DISCH_TAC
		 THEN ASM_REWRITE_TAC[]
		;REPEAT STRIP_TAC 
		 THEN UNDISCH_TAC "(P(first e)):bool"
		 THEN ASM_REWRITE_TAC[]
		 THEN DISCH_TAC
		 THEN RES_TAC 
		]
);;

let gcom_wlp = prove_thm (
	`gcom_wlp`,
	"!c P R. wlp (P --> c) R = P IMPLIES (wlp c R)",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [wlp;gcom;IMPLIES]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[RES_TAC
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		;REWRITE_ASM[]
		 THEN RES_TAC
		]
);;

let If_fI_wp = prove_thm (
	`If_fI_wp`,
	"!c R. wp (If_fI c) R = (wp c R) AND (grd c)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [If_fI; orelse_wp; abort_wp;NONE;AND;OR]
	THEN BETA_TAC
	THEN REWRITE_TAC[]
);;
 
let If_fI_wlp = prove_thm (
	`If_fI_wlp`,
	"!c R. wlp (If_fI c) R = (wlp c R)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [If_fI; orelse_wlp; abort_wlp;ALL;AND;OR]
	THEN BETA_TAC
	THEN REWRITE_TAC[]
);;
  
%
| Prove Dijkstra's "if a1 -> c1 | a2 -> c2 fi"  w(l)p postulate
| for total commands
%

let gcom_If_fI_wp = prove_thm (
	`gcom_If_fI_wp`,
	"!c1 c2 P1 P2 R.
	 total c1 /\ total c2 ==> 
	 (wp (If_fI ((P1-->c1) || (P2-->c2))) R =  
		( (P1 OR P2) AND 
		  (P1 IMPLIES (wp c1 R)) AND
		  (P2 IMPLIES (wp c2 R))
		)
	)",
	REWRITE_TAC 
		[If_fI_wp;gcom_wp;choose_wp;gcom_grd;choose_grd;total]
        THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [AND;IMPLIES;OR;NOT;ALL;grd]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN TAUT_TAC
);; 

let gcom_If_fI_wlp = prove_thm (
	`gcom_If_fI_wlp`,
	"!c1 c2 P1 P2 R.
	 total c1 /\ total c2 ==> 
	 (wlp (If_fI ((P1-->c1) || (P2-->c2))) R =  
		( (P1 IMPLIES (wlp c1 R)) AND
		  (P2 IMPLIES (wlp c2 R))
		)
	)",
	REWRITE_TAC 
		[If_fI_wlp;gcom_wlp;choose_wlp;gcom_grd;choose_grd;total]
        THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [AND;IMPLIES;OR;NOT;ALL;grd]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN TAUT_TAC
);; 

%
| Long series of lemmas to prove wp(do_od c, R) is STRONGEST soln
| and wlp(do_od c,R) is WEAKEST soln of fixpoint equation
%

let lemma1 = PROVE
(	"!e Seq.
	 TERM e ==>
	 (first(Seq 0) = last e) ==>
	 (!n.TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==> 
	 ((\i. (i=0) => e | e <*> (TTseq Seq(i-1))) =
		TTseq(\i. (i=0) => e | Seq(i-1)))",
	REPEAT STRIP_TAC
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN INDUCT_TAC
	THEN REWRITE_TAC [TTseq]
	THEN BETA_TAC
	THEN REWRITE_TAC[SYM_th ADD1;SUC_NOT_0]
	THEN ASSUM_LIST (REWRITE_TAC o SYML_th)
	THEN BETA_TAC
	THEN COND_CASES_TAC
	THENL	[ASM_REWRITE_TAC []
		 THEN REDUCE_TAC
		 THEN REWRITE_TAC[TTseq]
		;IMP_RES_TAC SUC_1_SHIFT
		 THEN ASM_REWRITE_TAC[TTseq;SYM_th ADD1]
		 THEN IMP_RES_TAC TTseq_first_last
		 THEN MAPFILTER_ASSUM 
			(STRIP_ASSUME_TAC o (SPEC "(n-1)"))
		 THEN UNDISCH_TAC 
			"first(TTseq Seq(n - 1)) = first(Seq 0)"
		 THEN ASSUM_LIST (REWRITE_TERML "first(Seq 0)")
		 THEN DISCH_TAC
		 THEN UNDISCH_TAC
			"first(Seq((n - 1) + 1)) = last(Seq(n - 1))"
		 THEN ASSUM_LIST 
			((REWRITE_TERML "last(Seq(n-1))") 
			o SYML_th)
		 THEN DISCH_TAC
		 THEN REWRITE_TAC [ADD1]
		 THEN IMP_RES_TAC join_assoc
		]
);;

let lemma1_finite_contract = PROVE
(	"!e Seq.
	 TERM e ==>
	 (first(Seq 0) = last e) ==>
	 !m.(!n. n<m ==> TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==> 
	    (e <*> (TTseq Seq m) =
		TTseq(\i. (i=0) => e | Seq(i-1)) (m+1))",
	REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THENL	[REWRITE_TAC [SYM_th ADD1; TTseq]
		 THEN BETA_TAC
		 THEN REDUCE_TAC
		 THEN REWRITE_TAC[]
		;ALL_TAC
		]
	THEN DISCH_TAC
	THEN REWRITE_TAC [SYM_th ADD1; TTseq]
	THEN BETA_TAC
	THEN REWRITE_TAC[SUC_NOT_0;ADD1;ADD_SUB]
	THEN SUPPOSE_TAC  
		"(!n. n < m ==> TERM(Seq n) /\ (first(Seq(n + 1)) = 
			last(Seq n)))"
	THENL	[ALL_TAC
		;GEN_TAC
		 THEN DISCH_TAC
		 THEN ASSUME_TAC (SPEC "m:num" LESS_SUC_REFL)
		 THEN IMP_RES_TAC LESS_TRANS
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		]
	THEN RES_TAC 
	THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "m:num"))
	THEN RULE_ASSUM_TAC (REWRITE_RULE[LESS_SUC_REFL])
	THEN EVERY_ASSUM STRIP_ASSUME_TAC
	THEN IMP_RES_TAC TTseq_first_last_finite
	THEN UNDISCH_TAC "first(TTseq Seq m) = first(Seq 0)"
	THEN ASM_REWRITE_TAC[]
	THEN DISCH_TAC
	THEN UNDISCH_TAC "last(TTseq Seq m) = last(Seq m)"
	THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
	THEN DISCH_THEN (ASSUME_TAC o SYM)	
	THEN IMP_RES_TAC join_assoc
	THEN ASM_REWRITE_TAC[SYM_th ADD1;TTseq]
	THEN BETA_TAC
	THEN REWRITE_TAC [NOT_SUC;ADD1;ADD_SUB]
);;

let Seq_expand = PROVE
(	"(\i. ((i = 0) => Seq 0 | Seq((i - 1) + 1))) = 		
			(Seq:num->exseq)",
	CONV_TAC FUN_EQ_CONV
	THEN GEN_TAC
	THEN BETA_TAC
	THEN COND_CASES_TAC
	THEN ASM_REWRITE_TAC[]
	THEN IMP_RES_TAC NOT_ZERO_LESS
	THEN IMP_RES_TAC ZERO_LESS_ONE_LESS_EQ
	THEN IMP_RES_TAC SUB_ADD
	THEN ASM_REWRITE_TAC[]
);;

let lemma1_finite_expand = PROVE
(	"!Seq m.
	 (!n. n<m ==> TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 (0 < m) ==> 
	 (TTseq Seq m =
		(Seq 0) <*> (TTseq(\i.Seq(i+1))(m-1)))",
	REPEAT STRIP_TAC
	THEN RES_TAC
	THEN SUPPOSE_TAC 
		 "!n. n < (m-1) ==> 
			TERM((\i.Seq(i+1)) n) /\ 
			(first((\i.Seq(i+1))(n + 1)) = 
			last((\i.Seq(i+1)) n))"
	THENL	[ALL_TAC
		;GEN_TAC THEN DISCH_TAC
		 THEN BETA_TAC
		 THEN FIRST_ASSUM (ASSUME_TAC o (SPEC "n+1"))
		 THEN IMP_RES_TAC ZERO_LESS_ONE_LESS_EQ
		 THEN IMP_RES_TAC LESS_SUB_TO_ADDL_LESS
		 THEN UNDISCH_TAC "(1 + n) < m"
		 THEN ONCE_REWRITE_TERML "1+n" [ADD_SYM]
		 THEN DISCH_TAC
		 THEN RES_TAC 
		 THEN ASM_REWRITE_TAC[]
		]
	THEN IMP_RES_TAC TTseq_first_last_finite
	THEN SUPPOSE_TAC
	 	"first((\i. Seq(i + 1))0) = last(Seq 0)"
	THEN BETA_TAC
	THEN ASM_REWRITE_TAC[]
	THEN IMP_RES_TAC lemma1_finite_contract
	THEN ASM_REWRITE_TAC[]
	THEN BETA_TAC
	THEN IMP_RES_TAC ZERO_LESS_ONE_LESS_EQ
	THEN IMP_RES_TAC SUB_ADD
	THEN ASM_REWRITE_TAC[]
	THEN REWRITE_TAC[Seq_expand]
);;

let lemma2 = PROVE
(	"!e Seq.
	 TERM e ==>
	 (first(Seq 0) = last e) ==>
	 (!n.TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 chain $<=| (\i. e <*> (TTseq Seq i))",
	REWRITE_TAC [chain]
	THEN REPEAT STRIP_TAC
	THEN BETA_TAC
	THEN REWRITE_TAC[SYM_th ADD1; TTseq]
	THEN IMP_RES_TAC TTseq_first_last
	THEN MAPFILTER_ASSUM (STRIP_ASSUME_TAC o (SPEC "i:num"))
	THEN UNDISCH_TAC "first(Seq(i + 1)) = last(Seq i)"
	THEN ASSUM_LIST ((REWRITE_TERML "last(Seq (i:num))") o SYML_th)
	THEN DISCH_TAC
	THEN UNDISCH_TAC "first(Seq 0) = last e"
	THEN ASSUM_LIST ((REWRITE_TERML "first(Seq 0)") o SYML_th)
	THEN DISCH_TAC
	THEN DETOUR
		(IMP_RES_TAC join_assoc
		 THEN ASM_REWRITE_TAC[ADD1])
	THEN MAP_EVERY IMP_RES_TAC [join_TERM;join_last]
	THEN UNDISCH_TAC "first(Seq(i + 1)) = last(TTseq Seq i)" 
	THEN ASSUM_LIST ((REWRITE_TERML "last(TTseq Seq i)") o SYML_th)
	THEN DISCH_TAC 
	THEN MAP_EVERY IMP_RES_TAC [join_inc;exseq_strict_imp_subseq]	
);;

let lub_contract = PROVE
(	"!Seq.
	 TERM e ==>
	 (first(Seq 0) = last e) ==>
	 (!n.TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 (e <*> (lub $<=| (TTseq Seq)) = 
		lub $<=| (TTseq (\i.(i=0) => e | Seq(i-1))))",
	REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC [TTseq_chain;join_distrib_lub]
	THEN RULE_ASSUM_TAC (REWRITE_RULE[TTseq])
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
	THEN IMP_RES_TAC lemma2
	THEN IMP_RES_TAC (REWRITE_RULE[cpo] exseq_cpo)
	THEN ASSUME_TAC exseq_po
	THEN IMP_RES_TAC TTseq_first_last
	THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "0"))
	THEN UNDISCH_TAC "first(TTseq Seq 0) = first(Seq 0)"
	THEN ASSUM_LIST(ONCE_REWRITE_TERML "first(Seq 0)")
	THEN DISCH_TAC
	THEN MAP_EVERY IMP_RES_TAC[join_inc;exseq_strict_imp_subseq]
	THEN SUPPOSE_TAC  "e <=| ((\i.e <*> (TTseq Seq i)) 0)"
	THENL	[IMP_RES_TAC lub_add_one
		 THEN ASM_REWRITE_TAC[]
		 THEN BETA_TAC
		 THEN IMP_RES_TAC lemma1
		 THEN ASM_REWRITE_TAC[]
		;BETA_TAC
		 THEN ASM_REWRITE_TAC[]
		]	
);;

let lub_expand = PROVE 
(	"!Seq.
	 (!n.TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 (lub $<=| (TTseq Seq) = 
		(Seq 0) <*> (lub $<=|(TTseq (\i.Seq(i+1)))))",
	REPEAT STRIP_TAC
	THEN SUPPOSE_TAC  
		"(!n.TERM((\i.Seq(i+1)) n) /\ (first((\i.Seq(i+1))(n+1)) = 
			last((\i.Seq(i+1)) n)))"
	THENL	[SUPPOSE_TAC "first((\i.Seq(i+1))0) = last(Seq 0)"
		 THEN BETA_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN MAPFILTER_ASSUM (STRIP_ASSUME_TAC o (SPEC "0"))
		 THEN IMP_RES_TAC lub_contract
		 THEN ASM_REWRITE_TAC[]
		 THEN BETA_TAC
		 THEN REWRITE_TAC[Seq_expand]	
		;BETA_TAC
		 THEN ASM_REWRITE_TAC[]
		]
);;

% Unused lemmas
let lemma5 = PROVE
(	"!e c.	(TERM e ==> ~(?e'. c e' /\ (first e' = last e))) =
		(!e'. ~(TERM e /\ c e' /\ (first e' = last e)))",
	CONV_TAC 
		(DEPTH_CONV NOT_EXISTS_CONV 
		 THENC DEPTH_CONV RIGHT_IMP_FORALL_CONV
		)
	THEN REWRITE_TAC [DE_MORGAN_THM]
	THEN REPEAT GEN_TAC
	THEN AP_TERM_TAC
	THEN CONV_TAC FUN_EQ_CONV
	THEN BETA_TAC
	THEN TAUT_TAC
);;

let lemma6 = PROVE
(	"!e c m. 
	 ~((TERM(choose_seq c e m)) /\
           c(choose_seq c e(SUC m)) /\
           (first(choose_seq c e(SUC m)) = last(choose_seq c e m))) =
	 (!e'. ~ ((TERM(choose_seq c e m)) /\
                 (c e') /\
                 (first e' = last(choose_seq c e m))))",	
	REWRITE_TAC [choose_seq]
	THEN CONV_TAC (DEPTH_CONV SELECT_CONV)
	THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN REWRITE_TAC[]
);;
%

let lemma7 = PROVE
(	"!Seq c m.
	 (!n. n < m ==> next c(Seq n)(Seq(SUC n))) ==>  
	 (!n. n < m ==> TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n)))", 
	REWRITE_TAC[next]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[SYM_th ADD1]
);;

let lemma8 = PROVE
(	"!Seq c.
	 (!n. next c(Seq n)(Seq(SUC n))) ==>  
	 (!n. TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n)))", 
	REWRITE_TAC[next]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[SYM_th ADD1]
);;

let lemma9 = PROVE
(	"!e c n. 
	  ~next c(select_seq c e n)(select_seq c e(SUC n)) =
	  !e'. ~ next c (select_seq c e n) e'",
	REWRITE_TAC [select_seq]
	THEN CONV_TAC (DEPTH_CONV SELECT_CONV)
	THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN REWRITE_TAC[]
);;

%
| Right restriction of a command, complements grd which is left
| restriction
%

new_special_symbol `<--`;;

let right_grd = new_infix_definition
(	`right_grd`,
	"!c P e. <-- c P e = c e /\ TERM e /\ P(last e)" 
);;

%
| Conservative composition of commands
%

new_special_symbol `<o>`;;

let conseq = new_infix_definition
(	`conseq`,
	"!c1 c2. <o> c1 c2 = (c1 ;; c2) || (c1 <-- NOT(grd c2))"
);;

let rec_fixed_lemma1 = PROVE
(	"!c e. (c <-- NOT(grd(rec c))) e ==> (rec c) e",
	REPEAT GEN_TAC
	THEN REWRITE_TAC [SYM_th rec_grd]
	THEN REWRITE_TAC [right_grd;NOT;grd]
	THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN BETA_TAC
	THEN REWRITE_TAC [rec;next]
	THEN REPEAT STRIP_TAC	
	THEN EXISTS_TAC "\n:num. (e:exseq)"
	THEN BETA_TAC
	THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC "0"
	THEN REWRITE_TAC [TTseq;NOT_LESS_0]
);;

let rec_fixed_lemma2 = PROVE
(	"!c e. (c ;; (rec c)) e ==> rec c e",
	REPEAT GEN_TAC
	THEN REWRITE_TAC [seq]
	THEN REPEAT STRIP_TAC
	THENL	[REWRITE_TAC [rec]
		 THEN EXISTS_TAC "\n:num.e:exseq"
		 THEN BETA_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN DISJ1_TAC
		 THEN EXISTS_TAC "0"
		 THEN ASM_REWRITE_TAC [TTseq;next;NOT_LESS_0]
		;REWRITE_TAC [rec]
		 THEN RULE_ASSUM_TAC (REWRITE_RULE[rec])
		 THEN EVERY_ASSUM STRIP_ASSUME_TAC
		 THENL	[ASSUM_LIST (REWRITE_TERML "e:exseq")
			 THEN EXISTS_TAC "\i. (i=0) => (e1:exseq) | Seq(i-1)"
			 THEN BETA_TAC
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ1_TAC
			 THEN EXISTS_TAC "m+1"
		 	 THEN REWRITE_TAC [ADD1;ADD_SUB]
			 THEN ASM_REWRITE_TAC [SYM_th ADD1;NOT_SUC]
			 THEN ONE_IMP_RES_TAC lemma7
			 THEN IMP_RES_TAC TTseq_first_last_finite
			 THEN UNDISCH_TAC  "e = e1 <*> e2"
			 THEN UNDISCH_TAC  "first e2 = last e1"
			 THEN ASM_REWRITE_TAC[]
			 THEN REPEAT DISCH_TAC
			 THEN IMP_RES_TAC lemma1_finite_contract
			 THEN ASM_REWRITE_TAC[ADD1;next]
			 THEN GEN_TAC
			 THEN ASM_CASES_TAC "n=0"
			 THEN ASM_REWRITE_TAC[]
			 THEN IMP_RES_TAC NOT_ZERO_LESS
			 THEN IMP_RES_TAC ADD1_CHOOSE
			 THEN ASSUM_LIST(REWRITE_TERML "n:num")
			 THEN REWRITE_TAC[LESS_MONO_ADD_EQ;ADD_SUB]
			 THEN ASM_REWRITE_TAC
				[SYM_th next;SYM_th ADD1
				]
			;ONE_IMP_RES_TAC lemma8
			 THEN MAP_EVERY IMP_RES_TAC 
				[TTseq_chain;lub_first]
			 THEN UNDISCH_TAC  "first e2 = last e1"
			 THEN ASM_REWRITE_TAC [TTseq]
			 THEN DISCH_TAC
			 THEN IMP_RES_TAC lub_contract
			 THEN EXISTS_TAC 
				"\i. (i = 0) => (e1:exseq) | Seq(i - 1)"
			 THEN BETA_TAC 	
			 THEN ASM_REWRITE_TAC[NOT_SUC]
			 THEN DISJ2_TAC	
			 THEN REWRITE_TAC[ADD1;ADD_SUB;next] 
			 THEN GEN_TAC
			 THEN COND_CASES_TAC
			 THENL	[ASM_REWRITE_TAC[];ALL_TAC]
			 THEN MAP_EVERY IMP_RES_TAC
				[NOT_ZERO_LESS;ADD1_CHOOSE]
			 THEN ASSUM_LIST(REWRITE_TERML "n:num")
			 THEN REWRITE_TAC [ADD_SUB]
			 THEN ASM_REWRITE_TAC[SYM_th ADD1;SYM_th next]
			]
		]
);;

let rec_fixed_lemma3 = PROVE
(	"!c e. rec c e ==> (c <o> (rec c)) e",
	REWRITE_TAC [rec;conseq;SYM_th rec_grd]
	THEN REPEAT STRIP_TAC
	THENL	[REWRITE_TAC[choose]
		 THEN BETA_TAC
		 THEN ASM_CASES_TAC "m=0"
		 THENL	[ASM_CASES_TAC "TERM e"
			 THENL	[DISJ2_TAC
			 	 THEN REWRITE_TAC[NOT;grd;right_grd]
			 	 THEN BETA_TAC
			 	 THEN REWRITE_ASM[TTseq;next]
			 	 THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
				 THEN REWRITE_TAC[DE_MORGAN_THM]
				 THEN RULE_ASSUM_TAC
					(REWRITE_RULE[DE_MORGAN_THM])
			 	 THEN REWRITE_ASM[]
			 	 THEN ASM_REWRITE_TAC[]
				;DISJ1_TAC
				 THEN REWRITE_TAC[seq]
				 THEN REWRITE_ASM[TTseq]
				 THEN ASM_REWRITE_TAC[]
				]
			;ONE_IMP_RES_TAC lemma7
			 THEN MAP_EVERY IMP_RES_TAC 
				[NOT_ZERO_LESS;lemma1_finite_expand]
			 THEN DISJ1_TAC
			 THEN REWRITE_TAC[seq]
			 THEN DISJ2_TAC
			 THEN MAP_EVERY EXISTS_TAC 
				["Seq 0:exseq"
				;"TTseq(\i. Seq(i + 1))(m - 1)"
				]
			 THEN RES_TAC
			 THEN ASM_REWRITE_TAC[]
			 THEN MP_TAC
				(SPECL["\i.Seq(i+1):exseq";"m-1"]
				 TTseq_first_last_finite)
			 THEN BETA_TAC
			 THEN IMP_RES_TAC ZERO_LESS_ONE_LESS_EQ	
			 THEN IMP_RES_TAC SUB_ADD
			 THEN ASM_REWRITE_TAC[]
			 THEN REDUCE_TAC
			 THEN IMP_RES_TAC LESS_SUB_TO_ADDR_LESS
			 THEN ASM_REWRITE_TAC[]	
			 THEN DISCH_THEN (\th.REWRITE_TAC[th])	
			 THEN REWRITE_TAC[rec]
			 THEN EXISTS_TAC "\i.Seq(i+1):exseq"
			 THEN BETA_TAC
			 THEN REWRITE_ASSUM[next;ADD1]
				 "next c(Seq 0)(Seq(SUC 0))"
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ1_TAC
			 THEN EXISTS_TAC "m-1"
	  		 THEN ASM_REWRITE_TAC[SYM_th ADD1]
			]
		;REWRITE_TAC [choose]
		 THEN BETA_TAC
		 THEN DISJ1_TAC
		 THEN REWRITE_TAC [seq]
		 THEN DISJ2_TAC
		 THEN ONE_IMP_RES_TAC lemma8
		 THEN IMP_RES_TAC lub_expand
		 THEN MAP_EVERY EXISTS_TAC 
			["Seq 0:exseq"
			;"lub $<=|(TTseq(\i. Seq(i + 1)))"
			]
		 THEN ASM_REWRITE_TAC[]
		 THEN ASSUME_TAC (SPEC "\i.Seq(i+1):exseq" TTseq_chain)
		 THEN RULE_ASSUM_TAC BETA_RULE
		 THEN REWRITE_ASM[]
		 THEN MAP_EVERY IMP_RES_TAC[TTseq_chain;lub_first]
		 THEN ASM_REWRITE_TAC[TTseq]
		 THEN BETA_TAC
		 THEN ASM_REWRITE_TAC[rec]
		 THEN EXISTS_TAC "\i.Seq(i+1):exseq"
		 THEN BETA_TAC 
		 THEN REWRITE_TAC[SYM_th ADD1]
		 THEN REWRITE_ASSUM[next] "!n. next c(Seq n)(Seq(SUC n))"
		 THEN ASM_REWRITE_TAC[next]
		]
);;

let rec_fixed = prove_thm
(	`rec_fixed`,
	"!c. c <o> (rec c) = rec c",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THENL	[REWRITE_TAC[conseq;choose]
		 THEN BETA_TAC
		 THEN REPEAT STRIP_TAC
		 THENL	[IMP_RES_TAC rec_fixed_lemma2 
			;IMP_RES_TAC rec_fixed_lemma1
			]
		;REWRITE_TAC[rec_fixed_lemma3]
		]
);;

let lemma = PROVE
(	"!c e.
	 (c ;; skip) e =
		(c e /\ ~TERM e) \/ 
		 ?e'.c e'/\ TERM e' 
		         /\ (e = e' <*> (pair(last e',last e')))",
	REPEAT GEN_TAC
	THEN REWRITE_TAC[seq;skip]
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THENL	[DISJ2_TAC
		 THEN EXISTS_TAC "e1:exseq"
		 THEN ASM_REWRITE_TAC[]
		 THEN REWRITE_ASM[pair_first]
		 THEN ASSUM_LIST ((REWRITE_TERML "last e1") o SYML_th)
		;DISJ2_TAC
		 THEN MAP_EVERY EXISTS_TAC
			["e':exseq";"pair(last e',last e')"]
		 THEN ASM_REWRITE_TAC[pair_first] 
		 THEN EXISTS_TAC "last e'"
		 THEN REFL_TAC
		]
);;

let skip_right_id_wp = prove_thm
(	`skip_right_id_wp`,
	"!c R. wp (c ;; skip) R = wp c R",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REPEAT GEN_TAC
	THEN REWRITE_TAC[wp;lemma]
	THEN EQ_TAC
	THEN DISCH_TAC
	THENL	[GEN_TAC
		 THEN REPEAT DISCH_TAC
		 THEN ASM_CASES_TAC "TERM e"
		 THENL	[REPLACE_FIRST_ASSUM 
			   (ASSUME_TAC o (SPEC "e <*> (pair(last e, last e))"))
		 	 THEN SUPPOSE_TAC "first(pair(last e,last e)) = last e"
			 THEN ASM_REWRITE_TAC[pair_first]
			 THEN ASSUME_TAC(SPECL["last e";"last e"]pair_TERM)
			 THEN MAP_EVERY IMP_RES_TAC
				[join_last;join_TERM;join_first]
			 THEN REWRITE_ASM[pair_last]
			 THEN HALF_ASM_REWRITE_TAC[]
			 THEN EXISTS_TAC "e:exseq"
			 THEN ASM_REWRITE_TAC[]
			;RES_TAC
			 THEN RES_TAC
			]
		;REPEAT STRIP_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN SUPPOSE_TAC 
			"first(pair(last e',last e')) = last e'"
		 THEN REWRITE_TAC[pair_first]
		 THENL	[IMP_RES_TAC join_TERM
		 	 THEN HALF_ONCE_ASM_REWRITE_TAC[]
		 	 THEN REWRITE_TAC[pair_TERM]
			;IMP_RES_TAC join_last
			 THEN RULE_ASSUM_TAC(REWRITE_RULE[pair_TERM])
			 THEN ASM_REWRITE_TAC[pair_last]
			 THEN IMP_RES_TAC join_first
			 THEN UNDISCH_TAC "first e = f"
			 THEN ASM_REWRITE_TAC[]
			]
		]
);;

let skip_right_id_wlp = prove_thm
(	`skip_right_id_wlp`,
	"!c R. wlp (c ;; skip) R = wlp c R",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REPEAT GEN_TAC
	THEN REWRITE_TAC[wlp;lemma]
	THEN EQ_TAC
	THEN DISCH_TAC
	THENL	[GEN_TAC
		 THEN REPEAT DISCH_TAC
		 THEN REPLACE_FIRST_ASSUM 
		   	(ASSUME_TAC o (SPEC "e <*> (pair(last e, last e))"))
		 THEN SUPPOSE_TAC "first(pair(last e,last e)) = last e"
		 THEN REWRITE_TAC[pair_first]
		 THEN ASSUME_TAC(SPECL["last e";"last e"]pair_TERM)
		 THEN MAP_EVERY IMP_RES_TAC
			[join_last;join_TERM;join_first]
		 THEN REWRITE_ASM[pair_last]
		 THEN HALF_ASM_REWRITE_TAC[]
		 THEN EXISTS_TAC "e:exseq"
		 THEN ASM_REWRITE_TAC[]
		;REPEAT STRIP_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		 THEN SUPPOSE_TAC 
			"first(pair(last e',last e')) = last e'"
		 THEN REWRITE_TAC[pair_first]
		 THEN IMP_RES_TAC join_last
		 THEN RULE_ASSUM_TAC(REWRITE_RULE[pair_TERM])
		 THEN ASM_REWRITE_TAC[pair_last]
		 THEN IMP_RES_TAC join_first
		 THEN UNDISCH_TAC "first e = f"
		 THEN ASM_REWRITE_TAC[]
		 THEN DISCH_TAC
		 THEN RES_TAC
		]
);;

let fix = new_definition
(	`fix`,
	"!c R pt. fix pt c R P = (P = (pt c P) AND (grd c OR R))" 
);;


let lemma = PROVE
(	"!c R. wp c (wp (do_od c) R) AND ((grd c) OR R) =
		wp ((c ;; do_od c)|X|skip) R",
	REPEAT GEN_TAC
	THEN REWRITE_TAC[seq_wp;orelse_wp;skip_wp]
	THEN ASSUME_TAC (SPEC "c:command" do_od_total)
	THEN IMP_RES_TAC seq_grd_total
	THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
);;

let orelse_seq = prove_thm
(	`orelse_seq`,
	"!c1 c2 c3. 
	 c1 ;; (c2 |X| c3) = (c1 ;; c2) || ((c1 <-- (NOT(grd c2))) ;; c3)",
	CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[seq;orelse;choose]
	THEN REPEAT GEN_TAC
	THEN BETA_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THENL	[DISJ1_TAC
		 THEN DISJ2_TAC
		 THEN MAP_EVERY EXISTS_TAC["e1:exseq";"e2:exseq"]
		 THEN ASM_REWRITE_TAC[]
		;DISJ2_TAC
		 THEN DISJ2_TAC
		 THEN MAP_EVERY EXISTS_TAC["e1:exseq";"e2:exseq"]
		 THEN REWRITE_TAC[right_grd;NOT]
		 THEN BETA_TAC
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		;DISJ2_TAC
		 THEN MAP_EVERY EXISTS_TAC["e1:exseq";"e2:exseq"]
		 THEN ASM_REWRITE_TAC[]
		;REWRITE_ASM[right_grd;NOT]
		 THEN UNDISCH_ALL_TAC
		 THEN REWRITE_TAC[]
		;DISJ2_TAC
		 THEN MAP_EVERY EXISTS_TAC["e1:exseq";"e2:exseq"]
		 THEN REWRITE_ASM[right_grd;NOT]
		 THEN RULE_ASSUM_TAC BETA_RULE
		 THEN ASM_REWRITE_TAC[]	
		]
);;

let rec_fixed_wp = prove_thm
(	`rec_fixed_wp`,
	"!c R. wp (rec c) R = wp (c ;; ((rec c) |X| skip)) R",
  	REWRITE_TAC [orelse_seq;choose_wp;skip_right_id_wp]
	THEN ONCE_REWRITE_TERM "wp(rec c) R" (SYM_th rec_fixed)
	THEN REWRITE_TAC[conseq;choose_wp]
);;

let do_od_wp_fix = prove_thm
(	`do_od_wp_fix`,
	"!c R. fix wp c R (wp (do_od c) R)",
	REWRITE_TAC 
		[fix;do_od;SYM_th seq_wp
		;orelse_wp;SYM_th rec_grd
		;skip_wp
		;rec_fixed_wp
		]
);;

let do_od_wp_fix1 = REWRITE_RULE[fix] do_od_wp_fix;;

let rec_fixed_wlp = prove_thm
(	`rec_fixed_wlp`,
	"!c R. wlp (rec c) R = wlp (c ;; ((rec c) |X| skip)) R",
  	REWRITE_TAC [orelse_seq;choose_wlp;skip_right_id_wlp]
	THEN ONCE_REWRITE_TERM "wlp(rec c) R" (SYM_th rec_fixed)
	THEN REWRITE_TAC[conseq;choose_wlp]
);;

let do_od_wlp_fix = prove_thm
(	`do_od_wlp_fix`,
	"!c R. fix wlp c R (wlp (do_od c) R)",
	REWRITE_TAC 
		[fix;do_od;SYM_th seq_wlp
		;orelse_wlp;SYM_th rec_grd
		;skip_wlp
		;rec_fixed_wlp
		]
);;

let lemma1 = PROVE
(	"!P s. 
	 fix wp c R P ==>
	 wp(do_od c) R s ==> ~ P s ==> 
	 ?e. c e /\ (first e = s) /\ TERM e /\ 
	     wp (do_od c) R (last e) /\ ~P(last e)",
	REWRITE_TAC[fix]
	THEN REPEAT STRIP_TAC
	THEN ONCE_REWRITE_ASM[]
	THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE[do_od_wp_fix1])
	THEN POP_IT "P = (wp c P) AND ((grd c) OR R)"
	THEN RULE_ASSUM_TAC (REWRITE_RULE[AND;OR])
	THEN RULE_ASSUM_TAC BETA_RULE
	THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE[DE_MORGAN_THM])
	THEN REWRITE_ASM[wp]
	THEN REPLACE_FIRST_ASSUM (ASSUME_TAC o CONJUNCT1)
	THEN REPLACE_FIRST_ASSUM
		(CHOOSE_TAC o (CONV_RULE NOT_FORALL_CONV))
	THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_IMP;DE_MORGAN_THM])
	THEN EVERY_ASSUM STRIP_ASSUME_TAC
	THENL	[RES_TAC
		 THEN RES_TAC	
		;EXISTS_TAC "e:exseq"
		 THEN ASM_REWRITE_TAC[wp]
		 THEN REPEAT STRIP_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		]
);;


let div_Seq = new_prim_rec_definition
(	`div_Seq`,
	"(div_Seq c R P s 0 = 
		@e. c e /\ (first e = s) /\ TERM e /\ 
	     		wp (do_od c) R (last e) /\ ~P(last e)) /\
	 (div_Seq c R P s (SUC n) =
		@e. c e /\ (first e = last(div_Seq c R P s n)) 
			/\ TERM e /\ 
	     		wp (do_od c) R (last e) /\ ~P(last e))"
);;

let lemma3 = PROVE
(	"!c R P s.
	 fix wp c R P ==>
	 wp(do_od c) R s ==> ~P s ==> 	 
	 c (div_Seq c R P s 0)
		/\ (first (div_Seq c R P s 0) = s) 
		/\ TERM (div_Seq c R P s 0)
		/\ wp (do_od c) R (last (div_Seq c R P s 0)) 
		/\ ~P(last (div_Seq c R P s 0))",
	REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN REWRITE_TAC[div_Seq]
	THEN CONV_TAC SELECT_CONV
	THEN IMP_RES_TAC lemma1
	THEN EXISTS_TAC "e:exseq"
	THEN ASM_REWRITE_TAC[]
);;

let lemma4 = PROVE
(	"!c R P s.
	 fix wp c R P ==>
	 wp(do_od c) R s ==> ~P s ==> 
	 !n. c (div_Seq c R P s (SUC n))
		 /\ (first (div_Seq c R P s (SUC n))
			 = last(div_Seq c R P s n)) 
		 /\ TERM (div_Seq c R P s (SUC n)) 
		 /\ wp (do_od c) R (last (div_Seq c R P s (SUC n))) 
		 /\ ~P(last (div_Seq c R P s (SUC n)))",
	REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THENL	[IMP_RES_TAC lemma3
		 THEN REWRITE_TAC[div_Seq]
		 THEN CONV_TAC SELECT_CONV
		 THEN IMP_RES_TAC lemma1
		 THEN EXISTS_TAC "e:exseq"
		 THEN ASM_REWRITE_TAC[SYM_th div_Seq]
		;REWRITE_TAC[div_Seq]
		 THEN CONV_TAC SELECT_CONV
		 THEN EVERY_ASSUM STRIP_ASSUME_TAC
		 THEN REWRITE_TAC[SYM_th div_Seq]
		 THEN IMP_RES_TAC lemma1
		 THEN EXISTS_TAC "e:exseq"
		 THEN ASM_REWRITE_TAC[]
		] 
);;

let lemma5= PROVE
(	"!c R P s.
	 fix wp c R P ==>
	 wp(do_od c) R s ==> ~ P s ==> 
	 c(div_Seq c R P s 0) /\
	 !n. next c(div_Seq c R P s n)(div_Seq c R P s (SUC n))",
	REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN IMP_RES_TAC lemma3
	THEN ASM_REWRITE_TAC[next]
	THEN GEN_TAC
	THEN IMP_RES_TAC lemma4
	THEN ASM_REWRITE_TAC[]
	THEN SPEC_TAC ("n:num","n:num")
	THEN INDUCT_TAC
	THEN ASM_REWRITE_TAC[]	
);;

let lemma6 = PROVE
(	"!c R P s.
	 fix wp c R P ==>
	 wp(do_od c) R s ==> ~ P s ==> 
	 (do_od c)(lub $<=| (TTseq(div_Seq c R P s))) 
		/\ (first(lub $<=| (TTseq(div_Seq c R P s))) = s)",
	REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN CONJ_TAC
	THENL	[IMP_RES_TAC lemma5
		 THEN REWRITE_TAC[do_od;orelse;rec]
		 THEN DISJ1_TAC
		 THEN EXISTS_TAC "div_Seq c R P s"
		 THEN ASM_REWRITE_TAC[TTseq]
		;IMP_RES_TAC lemma5
		 THEN ONE_IMP_RES_TAC lemma8
		 THEN IMP_RES_TAC TTseq_chain
		 THEN IMP_RES_TAC lub_first
		 THEN IMP_RES_TAC lemma3
		 THEN ASM_REWRITE_TAC[TTseq]
		]
);;

let lub_div_seq = prove_thm
(	`lub_div_seq`,
	"!Seq.
	 (!n. TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 ~TERM(lub $<=| (TTseq Seq))",
	GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN REWRITE_TAC[TERM]
	THEN MAP_EVERY IMP_RES_TAC [TTseq_chain;length_chain;exseq_lub_length]
	THEN REWRITE_ASM[TERM]
	THEN MAP_EVERY IMP_RES_TAC[whole_lub;stunt_chain;is_ub]
	THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "n+1"))
	THEN RULE_ASSUM_TAC (REWRITE_RULE[lengths])
	THEN RULE_ASSUM_TAC BETA_RULE
	THEN IMP_RES_TAC exseq_subseq_as_length
	THEN RULE_ASSUM_TAC (REWRITE_RULE [SYM_th ADD1;TTseq;SYM_th TERM])
	THEN IMP_RES_TAC (REWRITE_RULE[SYM_th ADD1] TTseq_first_last)
	THEN MAPFILTER_ASSUM (STRIP_ASSUME_TAC o (SPEC "n:num"))
	THEN IMP_RES_TAC join_inc
	THEN UNDISCH_TAC "first(Seq(SUC n)) = last(Seq n)"
	THEN APPLY_TO "last(TTseq Seq n) = last(Seq n)" 
		(\th.REWRITE_TAC[SYM_th th])
	THEN DISCH_TAC
	THEN MAP_EVERY IMP_RES_TAC[join_inc;exseq_subseq_strict_not_swop]
);;

let do_od_wp_strongest_fix = prove_thm
(	`do_od_wp_strongest_fix`,
	"!P c R. 
	 fix wp c R P ==> !s.(wp (do_od c) R)s ==> P s", 
	REPEAT GEN_TAC
	THEN DISCH_TAC
	THEN GEN_TAC
	THEN CONV_TAC CONTRAPOS_CONV
	THEN REPEAT DISCH_TAC
	THEN IMP_RES_TAC lemma6
	THEN IMP_RES_TAC lemma5
	THEN ONE_IMP_RES_TAC lemma8
	THEN IMP_RES_TAC lub_div_seq
	THEN RULE_ASSUM_TAC(REWRITE_RULE[wp])
	THEN RES_TAC
	THEN RES_TAC
);;

%Bug here it seems -- theorem should be autoloaded%

load_theorem `prim_rec` `LESS_LEMMA2`;;

let lemma1 = PROVE
(	"!Seq.!m.
	 c(Seq 0) ==> 
	 (!n. n<m ==> next c (Seq n) (Seq(SUC n))) ==>
	 ((c ^^ m) (TTseq Seq m))",
	GEN_TAC
	THEN INDUCT_TAC
	THENL	[REWRITE_TAC[iter;TTseq]
		 THEN DISCH_THEN (\th.REWRITE_TAC[th])
		;REPEAT DISCH_TAC
		 THEN SUPPOSE_TAC "m < SUC m"
		 THEN REWRITE_TAC[LESS_SUC_REFL]
		 THEN RES_TAC
		 THEN SUPPOSE_TAC 
			"(!n. n < m ==> next c(Seq n)(Seq(SUC n)))"	
		 THENL	[RES_TAC
			 THEN REWRITE_TAC[iter;TTseq;SYM_th iter_swop]
			 THEN REWRITE_ASSUM[next;ADD1] 
				"next c(Seq m)(Seq(SUC m))"
			 THEN EVERY_ASSUM STRIP_ASSUME_TAC
			 THEN ONE_IMP_RES_TAC lemma7
			 THEN IMP_RES_TAC TTseq_first_last_finite
			 THEN UNDISCH_TAC "first(Seq(m + 1)) = last(Seq m)" 
			 THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
			 THEN DISCH_TAC
			 THEN REWRITE_TAC[seq]
			 THEN DISJ2_TAC
			 THEN MAP_EVERY EXISTS_TAC
				["TTseq Seq m";"Seq(m+1):exseq"]
			 THEN ASM_REWRITE_TAC[]
			;REPEAT STRIP_TAC
			 THEN HALF_ASM_REWRITE_TAC[]
			 THEN IMP_RES_TAC LESS_LEMMA2
			]
		]
);;

let lemma2 = PROVE
(	"!c e.(!e'.~next c e e') ==> TERM e ==> ~grd c(last e)",
	REWRITE_TAC[next;grd]
	THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	THEN REWRITE_TAC[DE_MORGAN_THM]
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN REWRITE_ASM[]
	THEN ASM_REWRITE_TAC[]
);;

let lemma3 = PROVE
(	"!c e. 
	 rec c e ==> TERM e ==>
	 ?Seq. c(Seq 0) /\
		 ?m.(!n. (n<m ==> next c (Seq n) (Seq(SUC n)))) /\
		    (!e'. ~ next c (Seq m) e') /\
		    (e = TTseq Seq m)",
	REWRITE_TAC[rec]
	THEN REPEAT STRIP_TAC
	THENL	[EXISTS_TAC "Seq:num->exseq"
		 THEN ASM_REWRITE_TAC[]
		 THEN EXISTS_TAC "m:num"
		 THEN ASM_REWRITE_TAC[]
		;ONE_IMP_RES_TAC lemma8
		 THEN IMP_RES_TAC lub_div_seq
		 THEN REWRITE_ASM[]
		 THEN UNDISCH_TAC "F"
		 THEN REWRITE_TAC[]
		]
);;

let lemma4 = PROVE
(	"!c e.
	 rec c e ==> TERM e ==> 
	 ?m. (c ^^ m) e /\ ~grd c (last e)",
	REPEAT STRIP_TAC
	THEN IMP_RES_TAC lemma3
	THEN IMP_RES_TAC lemma1
	THEN EXISTS_TAC "m:num"
	THEN ASM_REWRITE_TAC[]
	THEN ONE_IMP_RES_TAC lemma7
	THEN REWRITE_ASM[]
	THEN IMP_RES_TAC TTseq_first_last_finite
	THEN IMP_RES_TAC lemma2
	THEN ASM_REWRITE_TAC[]
);;

let lemma5 = PROVE
(	"!P c R s. 
	 fix wlp c R P ==> 
	 P s ==> 
	 ~(wlp (do_od c) R)s ==>
	 ~(wlp (rec c) R)s",
	REWRITE_TAC[fix;do_od;orelse_wlp;AND;OR;skip_wlp;SYM_th rec_grd]
	THEN REPEAT GEN_TAC
	THEN DISCH_THEN SUBST1_TAC
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN REWRITE_ASM[]
	THEN ASM_REWRITE_TAC[]
);;

let lemma6 = PROVE
(	"!P c R s.
	 fix wlp c R P ==>
	 P s ==>
	 !n. wlp (c ^^ n) P s",  
	REPEAT GEN_TAC
	THEN REWRITE_TAC[fix]
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THEN REWRITE_TAC[iter]
	THENL	[ONCE_REWRITE_ASM[]
		 THEN POP_IT "P = (wlp c P) AND ((grd c) OR R)"
		 THEN REWRITE_ASM[AND] 
		 THEN RULE_ASSUM_TAC BETA_RULE
		 THEN ASM_REWRITE_TAC[]
		;REWRITE_TAC[SYM_th iter_swop]
		 THEN REWRITE_TAC[seq_wlp]
		 THEN ONCE_REWRITE_ASM[]
		 THEN POP_IT "P = (wlp c P) AND ((grd c) OR R)"
		 THEN REWRITE_ASM[SYM_th conjunctivity_wlp;AND]
		 THEN RULE_ASSUM_TAC BETA_RULE
		 THEN ASM_REWRITE_TAC[]
		]
);;

let lemma9 = PROVE
(	"!P c R s.
	 fix wlp c R P ==>
	 P s ==>
	 !n. wlp (c ^^ n) ((grd c) OR R) s",
	REPEAT STRIP_TAC
	THEN IMP_RES_TAC lemma6
	THEN REWRITE_ASM[fix]
	THEN ONCE_REWRITE_ASM[]
	THEN POP_IT "P = (wlp c P) AND ((grd c) OR R)"
	THEN REWRITE_ASM[SYM_th conjunctivity_wlp;AND]
	THEN RULE_ASSUM_TAC BETA_RULE
	THEN ASM_REWRITE_TAC[]
);;

let do_od_wlp_weakest_fix = prove_thm
(	`do_od_wlp_weakest_fix`,
	"!P c R. 
	 fix wlp c R P ==> !s.P s ==> (wlp (do_od c) R)s",
	REPEAT GEN_TAC
	THEN DISCH_TAC
	THEN GEN_TAC
	THEN CONV_TAC CONTRAPOS_CONV
	THEN REPEAT DISCH_TAC 
	THEN IMP_RES_TAC lemma5
	THEN REWRITE_ASM[wlp]
	THEN MAPFILTER_ASSUM
		(CHOOSE_TAC o (CONV_RULE NOT_FORALL_CONV))
	THEN REWRITE_ASM[NOT_IMP;DE_MORGAN_THM]
	THEN EVERY_ASSUM STRIP_ASSUME_TAC
	THEN IMP_RES_TAC lemma4
	THEN IMP_RES_TAC (REWRITE_RULE[wlp]lemma9)
	THEN RULE_ASSUM_TAC(REWRITE_RULE[OR])
	THEN RULE_ASSUM_TAC BETA_RULE
	THEN FIRST_ASSUM DISJ_CASES_TAC
	THEN RES_TAC
);;

close_theory();;

