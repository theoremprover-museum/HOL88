%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        | 
|                                                              |
| hoare.ml                                                     |
|                                                              |
| DESCRIPTION:	                                               |
|                                                              |
| Derives Hoare logic for the language defined in sem.ml       |
| Partial and total correctness                                |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

new_theory `hoare`;;
loadf `mytactics`;;

loadf `l_arith_hack`;;
loadf `l_cpo`;;
loadf `l_lnum`;;
loadf `l_exseq`;;
loadf `l_pred`;;
loadf `l_sem`;;
loadf `l_wp`;;

%
|  Define Hoare specification {P} c {Q} of partial correctness
%

let spec = new_definition
(	`spec`,
	"!P Q c. 
	 spec P c Q = 
		!e. c e ==> 
		    P(first e) ==> 
		    TERM e ==>
		    Q(last e)"
);;

%
| Define a termination assertion halts
%

let halts = new_definition
(	`halts`,
	"!P c. 
	 halts P c = 
	 !s e. c e ==> (first e = s) ==> P s ==> TERM e"
);;

let halts_alt = prove_thm
(	`halts_alt`,
	"!P c. 
	 halts P c = !e. c e ==> P(first e) ==> TERM e",
	REWRITE_TAC[halts]
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THENL	[ASSUME_TAC(REFL "first e")
		 THEN RES_TAC
		;REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		]
);;

%
| Define a total correctness assertion
%

let total_spec = new_definition
(	`total_spec`,
	"!c P Q. total_spec P c Q = spec P c Q /\ halts P c"
);;

let total_spec_alt = prove_thm
(	`total_spec_alt`,
	"!c P Q. 
	 total_spec P c Q = 
		!e. c e ==> 
		    P(first e) ==> 
		    (TERM e /\ Q(last e))",
	 REWRITE_TAC[total_spec;halts;spec]
	 THEN REPEAT STRIP_TAC
	 THEN EQ_TAC
	 THEN REPEAT DISCH_TAC
	 THENL	[GEN_TAC
		 THEN REPEAT DISCH_TAC
		 THEN SUPPOSE_TAC "first e = first e"
		 THEN REWRITE_TAC[] 
		 THEN RES_TAC
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[] 
		;REPEAT STRIP_TAC
		 THEN RES_TAC
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		]
);;

%
| Hoare specs in terms of w(l)p
| For historical reasons hoare and wp are derived independently
| here but obviously one can be obtained from the other
%

let spec_as_wlp = prove_thm
(	`spec_as_wlp`,
	"!P Q c. spec P c Q = (!s. P s ==> wlp c Q s)",
	REWRITE_TAC[wlp;spec]
	THEN REPEAT GEN_TAC
	THEN CONV_TAC(TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV) 
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN REWRITE_ASM[]
	THEN ASM_REWRITE_TAC[]
);;

let halts_as_wp = prove_thm
(	`halts_as_wp`,
	 "!P c. halts P c = (!s. P s ==> wp c true s)",
	REWRITE_TAC[halts;wp;ALL]
	THEN BETA_TAC
	THEN REPEAT GEN_TAC
	THEN CONV_TAC(TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV) 
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

let total_spec_as_wp = prove_thm
(	`total_spec_as_wp`,
	"!P Q c. total_spec P c Q = (!s. P s ==> wp c Q s)",
	ONCE_REWRITE_TAC[wp_wlp_pairing]
	THEN REWRITE_TAC[total_spec;halts_as_wp;spec_as_wlp;AND]
	THEN BETA_TAC
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

%     
|        P IMPLIES P1, {P1} c {Q1}, Q1 IMPLIES Q
|      -------------------------------------------
|                       {P} c {Q}
%

let weaken_spec = prove_thm
(	`weaken_spec`,
	"!P1 Q1 P Q.
	 (!s.P s ==> P1 s) /\
	 (!s.Q1 s ==> Q s) /\
	 spec P1 c Q1 ==>
	 spec P c Q", 
	REWRITE_TAC [spec]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
	THEN RES_TAC
);;

let weaken_spec2 = prove_thm
(	`weaken_spec2`,
	"!P1 P Q.
	 (!s.P s ==> P1 s) /\
	 spec P1 c Q ==>
	 spec P c Q", 
	REWRITE_TAC [spec]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
	THEN RES_TAC
);;

let weaken_spec3 = prove_thm
(	`weaken_spec3`,
	"!Q1 P Q.
	 (!s.Q1 s ==> Q s) /\
	 spec P c Q1 ==>
	 spec P c Q", 
	REWRITE_TAC [spec]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
	THEN RES_TAC
);;

%     
|        P IMPLIES P1, [P1] c [Q1], Q1 IMPLIES Q
|      -------------------------------------------
|                       [P] c [Q]
%

let weaken_halts = prove_thm
(	`weaken_halts`,
	"!P P1. 
	 (!s. P s ==> P1 s) /\ halts P1 c ==> halts P c",
	REWRITE_TAC[halts]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
);;

let weaken_total_spec = prove_thm
(	`weaken_total_spec`,
	"!P1 Q1 P Q.
	 (!s.P s ==> P1 s) /\
	 (!s.Q1 s ==> Q s) /\
	 total_spec P1 c Q1 ==>
	 total_spec P c Q", 
	REWRITE_TAC [total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[weaken_spec;weaken_halts]
);;

let weaken_total_spec2 = prove_thm
(	`weaken_total_spec2`,
	"!P1 P Q.
	 (!s.P s ==> P1 s) /\
	 total_spec P1 c Q ==>
	 total_spec P c Q", 
	REWRITE_TAC [total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[weaken_spec2;weaken_halts]
);;

let weaken_total_spec3 = prove_thm
(	`weaken_total_spec3`,
	"!Q1 P Q.
	 (!s.Q1 s ==> Q s) /\
	 total_spec P c Q1 ==>
	 total_spec P c Q", 
	REWRITE_TAC [total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[weaken_spec3;weaken_halts]
	THEN ASM_REWRITE_TAC[]
);;

%
|       {P} skip {P}
%

let skip_spec = prove_thm
(	`skip_spec`,
	"!P. spec P skip P",
	REWRITE_TAC [spec;skip]
	THEN REPEAT GEN_TAC
	THEN DISCH_THEN CHOOSE_TAC
	THEN ASM_REWRITE_TAC[pair_first;pair_last;pair_TERM]
);;

%
|       [P] skip [P]
%

let skip_halts = prove_thm
(	`skip_halts`,
	"!P. halts P skip",
	REWRITE_TAC[halts;skip]
	THEN CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV)
	THEN REPEAT STRIP_TAC
	THEN REWRITE_ASM[pair_first]
	THEN ASM_REWRITE_TAC[pair_TERM]
);;

let skip_total_spec = prove_thm
(	`skip_total_spec`,
	"!P. total_spec P skip P",
	REWRITE_TAC[total_spec;skip_spec;skip_halts]
);;

%
|       {true} abort {Q}
%

let abort_spec = prove_thm
(	`abort_spec`,
	"!P. spec true abort P",
	REWRITE_TAC [spec;abort;ALL]
	THEN REPEAT GEN_TAC
	THEN DISCH_THEN CHOOSE_TAC
	THEN ASM_REWRITE_TAC[abort_pair_first;abort_pair_ABORT]
	THEN DISCH_TAC
	THEN IMP_RES_TAC TERM_not_ABORT
	THEN REWRITE_ASM[abort_pair_ABORT]
	THEN UNDISCH_TAC "F"
	THEN REWRITE_TAC[]
);;

%
|       [false] abort [Q]
%

let abort_halts = prove_thm
(	`abort_halts`,
	"halts false abort",
	REWRITE_TAC[halts;abort;NONE]
);;

let abort_total_spec = prove_thm
(	`abort_total_spec`,
	"!P. total_spec false abort P",
	REWRITE_TAC [total_spec;abort_halts]
	THEN HALF_ONCE_REWRITE_TAC[SPEC "true:state->bool" weaken_spec2]
	THEN REWRITE_TAC[ALL;abort_spec]
);;
	
%
|       {\s.EWR P} havoc {P}
%

let havoc_spec = prove_thm
(	`havoc_spec`,
	"!P. spec (\s.EWR P) havoc P",
	REWRITE_TAC [spec;havoc;EWR]
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
);;

%
|       [\s.EWR P] havoc [P]
%

let havoc_halts = prove_thm
(	`havoc_halts`,
	"!P. halts P havoc",
	REWRITE_TAC[halts;havoc]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
);;

let havoc_total_spec = prove_thm
(	`havoc_total_spec`,
	"!P. total_spec (\s.EWR P) havoc P",
	REWRITE_TAC [total_spec;havoc_halts;havoc_spec]
);;

%
|       {true} empty {P}
%

let empty_spec = prove_thm
(	`empty_spec`,
	"!P. spec true empty P",
	REWRITE_TAC [spec;empty]
);;

%
|       [true] empty [P]
%

let empty_halts = prove_thm
(	`empty_halts`,
	"halts true empty",
	REWRITE_TAC[halts;empty]
);;

let empty_total_spec = prove_thm
(	`empty_total_spec`,
	"!P. total_spec true empty P",
	REWRITE_TAC [total_spec;empty_halts;empty_spec]
);;

%
|       {P[e/x]} x := e {P}
%

let assign_spec = prove_thm
(	`assign_spec`,
	"!P Q:state->bool.!x e.
	  spec (subs e x P) (x := e) P",
	REWRITE_TAC [subs;spec;assign]
	THEN REPEAT GEN_TAC
	THEN BETA_TAC
	THEN DISCH_THEN STRIP_ASSUME_TAC
	THEN ASM_REWRITE_TAC[pair_first;pair_last;pair_TERM]
);;

%
|       [P[e/x]] x := e [P]
%

let assign_halts = prove_thm
(	`assign_halts`,
	"!P x e. halts P (x := e)",
	REWRITE_TAC[halts;assign]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[pair_TERM]
);;

let assign_total_spec = prove_thm
(	`assign_total_spec`,
	"!P x e. total_spec (subs e x P) (x := e) P",
	REWRITE_TAC[total_spec;assign_spec;assign_halts]
);;

%
|      {forevery x P} update x {P}
%

let update_spec = prove_thm
(	`update_spec`,
	"!x P. spec (forevery x P) (update x) P",
	REWRITE_TAC[forevery;spec;update]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[pair_last]
	THEN REPLACE_FIRST_ASSUM(ASSUME_TAC o (SPEC "val:num"))
	THEN REWRITE_ASM[pair_first]
	THEN ASM_REWRITE_TAC[]
);;

%
|      [forevery x P] update x [P]
%

let update_halts = prove_thm
(	`update_halts`,
	"!P x. halts P (update x)",
	REWRITE_TAC[halts;update]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[pair_TERM]
);;

let update_total_spec = prove_thm
(	`update_total_spec`,
	"!P x. total_spec (forevery x P) (update x) P",
	REWRITE_TAC[forevery;total_spec;update_spec;update_halts]
);;

%
|     {P} c1 {Q}, {Q} c2 {R}
|     ----------------------
|        {P} c1 ;; c2 {R}
%

let seq_spec = prove_thm
(	`seq_spec`,
	"!P Q R c1 c2.
	 spec P c1 Q /\
	 spec Q c2 R ==>
	 spec P (c1 ;; c2) R",
	REWRITE_TAC [spec;seq]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN IMP_RES_TAC join_first
	THEN REWRITE_ASM[]
	THEN MAP_EVERY IMP_RES_TAC [join_TERM;join_last]
	THEN RES_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;

%
|     [P] c1 [Q], [Q] c2 [R]
|     ----------------------
|        [P] c1 ;; c2 [R]
%

let seq_halts = prove_thm
(	`seq_halts`,
	"!P Q c1 c2.
	 halts P c1 ==>
	 spec P c1 Q ==>
	 halts Q c2 ==>
	 halts P (c1 ;; c2)",
	REWRITE_TAC[halts;spec;seq]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN REWRITE_ASM[]
	THEN MAP_EVERY IMP_RES_TAC[join_first]
	THEN UNDISCH_TAC "first(e1 <*> e2) = s"
	THEN DISCH_THEN (ASSUME_TAC o SYM)
	THEN REWRITE_ASM[]
	THEN RES_TAC
	THEN IMP_RES_TAC join_TERM
	THEN ASM_REWRITE_TAC[]
);;

let seq_total_spec = prove_thm
(	`seq_total_spec`,
	"!P Q R c1 c2.
	 total_spec P c1 Q /\
	 total_spec Q c2 R ==>
	 total_spec P (c1 ;; c2) R",
	REWRITE_TAC[total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[seq_spec;seq_halts]
);;

%
|         {P AND b} c {Q}
|       --------------------
|         {P} b --> c {Q}
%

let gcom_spec = prove_thm
(	`gcom_spec`,
	"!P Q b c.
	 spec (P AND b) c Q ==> spec P (b --> c) Q",
	REWRITE_TAC [spec;gcom;AND]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

%
|         [P AND b] c [Q]
|       --------------------
|         [P] b --> c [Q]
%

let gcom_halts = prove_thm
(	`gcom_halts`,
	"!P b c.
	 halts (P AND b) c ==> halts P (b --> c)",
	REWRITE_TAC[halts;AND;gcom]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN REWRITE_ASM[]
	THEN RES_TAC
);;

let gcom_total_spec = prove_thm
(	`gcom_total_spec`,
	"!P Q b c.
	 total_spec (P AND b) c Q ==> total_spec P (b --> c) Q",
	REWRITE_TAC[total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[gcom_spec;gcom_halts]
	THEN ASM_REWRITE_TAC[]
);;

%
|        {P} c1 {Q}, {P} c2 {Q}
|      -------------------------
|           {P} c1 || c2 {Q}  
%

let choose_spec =prove_thm
(	`choose_spec`,
	"!P Q c1 c2.
	 spec P c1 Q /\
	 spec P c2 Q ==>
	 spec P (c1 || c2) Q",
	REWRITE_TAC [spec;choose]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

%
|        [P] c1 [Q], [P] c2 [Q]
|      -------------------------
|           [P] c1 || c2 [Q]  
%

let choose_halts = prove_thm
(	`choose_halts`,
	"!P c1 c2. halts P c1 /\ halts P c2 ==> halts P (c1 || c2)",
	REWRITE_TAC[choose;halts]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);; 

let choose_total_spec = prove_thm
(	`choose_total_spec`,
	"!P Q c1 c2.
	 total_spec P c1 Q /\
	 total_spec P c2 Q ==>
	 total_spec P (c1 || c2) Q",
	REWRITE_TAC [total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[choose_halts;choose_spec]
);;

%
|     {P} c1 {Q}, {P AND (NOT(grd c1))} c2 {Q}
|    -------------------------------------------
|                 {P} c1 |X| c2 {Q}
%

let orelse_spec = prove_thm
(	`orelse_spec`,
	"!P Q c1 c2.
	 spec P c1 Q /\
	 spec (P AND (NOT(grd c1))) c2 Q ==>
	 spec P (c1 |X| c2) Q",
	REWRITE_TAC [spec;AND;NOT;orelse]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

%
|     [P] c1 [Q], [P AND (NOT(grd c1))] c2 [Q]
|    -------------------------------------------
|                 [P] c1 |X| c2 [Q]
%

let orelse_halts = prove_thm
(	`orelse_halts`,
	"!P c1 c2.
	 halts P c1 /\
	 halts  (P AND (NOT(grd c1))) c2 ==>
	 halts P (c1 |X| c2)",
	REWRITE_TAC[orelse;halts;AND;OR;NOT]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN REWRITE_ASM[]
	THEN RES_TAC
);;

let orelse_total_spec = prove_thm
(	`orelse_total_spec`,
	"!P Q c1 c2.
	 total_spec P c1 Q /\
	 total_spec (P AND (NOT(grd c1))) c2 Q ==>
	 total_spec P (c1 |X| c2) Q",
	REWRITE_TAC [total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[orelse_spec;orelse_halts]
);;

%
|            {P} c {Q}
|     -----------------------
|         {P} If c fI {Q}
%

let If_fI_spec = prove_thm
(	`If_fI_spec`,
	"!P Q c.
	 spec P c Q ==>
	 spec P (If_fI c) Q",
	REWRITE_TAC [spec;If_fI;orelse;grd;abort]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THENL	[RES_TAC
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		;REWRITE_ASM[TERM;abort_pair_length;is_WHOLE]
		 THEN FIRST_ASSUM CONTR_TAC
		]
);;

%
|       P IMPLIES (grd c)      [P] c [Q]
|     ------------------------------------
|               [P] If c fI [Q]
%

let If_fI_halts = prove_thm
(	`If_fI_halts`,
	"!P c.
	 (!s. P s ==> grd c s) ==>
	 halts P c ==>
	 halts P (If_fI c)",
	REWRITE_TAC[If_fI]
	THEN REPEAT STRIP_TAC
	THEN HALF_REWRITE_TAC[orelse_halts]
	THEN ASM_REWRITE_TAC[halts;AND;NOT]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
);;

let If_fI_total_spec = prove_thm
(	`If_fI_total_spec`,
	"!P Q c.
	 (!s. P s ==> grd c s) /\
	 total_spec P c Q ==>
	 total_spec P (If_fI c) Q",
	REWRITE_TAC [total_spec]
	THEN REPEAT STRIP_TAC
	THEN MAP_EVERY IMP_RES_TAC[If_fI_spec;If_fI_halts]	
);;


% 
|       {P AND b1} c1 {Q}, {P AND b2} c2 {Q}
|    ------------------------------------------  
|      {P} If (b1 --> c1) || (b2 --> c2) fI {Q}
%

let gcom_If_fI_spec = prove_thm
(	`gcom_If_fI_spec`,
	"!P Q b1 b2 c1 c2.
	 spec (P AND b1) c1 Q ==>
	 spec (P AND b2) c2 Q ==>
	 spec P (If_fI((b1 --> c1) || (b2 --> c2))) Q",
	REPEAT STRIP_TAC
	THEN HALF_REWRITE_TAC [If_fI_spec]
	THEN HALF_REWRITE_TAC [choose_spec]
	THEN REWRITE_TAC [gcom_grd;choose_grd]
	THEN HALF_REWRITE_TAC[gcom_spec]
	THEN ASM_REWRITE_TAC[]
);;

% 
|       P IMPLIES ((b1 AND (grd c1)) OR (b2 AND (grd c2))))   
|       [P AND b1] c1 [Q]
|       [P AND b2] c2 [Q]
|     -------------------------------------------------------  
|       [P] If (b1 --> c1) || (b2 --> c2) fI [Q]
%

let gcom_If_fI_total_spec = prove_thm
(	`gcom_If_fI_total_spec`,
	"!P Q b1 b2 c1 c2.
	 (!s. P s ==> ((b1 AND (grd c1)) OR (b2 AND (grd c2)))s) /\
	 total_spec (P AND b1) c1 Q /\
	 total_spec (P AND b2) c2 Q ==>
	 total_spec P (If_fI((b1 --> c1) || (b2 --> c2))) Q",
	REPEAT STRIP_TAC
	THEN HALF_REWRITE_TAC [If_fI_total_spec]
	THEN HALF_REWRITE_TAC [choose_total_spec]
	THEN REWRITE_TAC [gcom_grd;choose_grd]
	THEN HALF_REWRITE_TAC[gcom_total_spec]
	THEN ASM_REWRITE_TAC[]
);;

%
|                   {P} c {P}
|        ---------------------------------
|         {P} rec c {P AND (NOT (grd c))}     
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

let rec_spec = prove_thm
(	`rec_spec`,
	"!c P. spec P c P ==> spec P (rec c) (P AND (NOT(grd c)))",
	REWRITE_TAC[spec;rec;AND;NOT]
	THEN BETA_TAC
	THEN REPEAT STRIP_TAC
	THENL	[REWRITE_ASM[]
		 THEN ASM_CASES_TAC "m=0"
		 THENL	[REWRITE_ASM[TTseq]
			 THEN RES_TAC
			 THEN ASM_REWRITE_TAC[]
			;SUPPOSE_TAC "!n.n<m ==> P(last(Seq n))"
			 THENL	[MAPFILTER_ASSUM 
					(ASSUME_TAC o (SPEC "PRE m"))
				 THEN IMP_RES_TAC NOT_ZERO_LESS
				 THEN IMP_RES_TAC PRE_K_K
				 THEN RES_TAC
				 THEN REWRITE_ASSUM [next] 
					"next c(Seq(PRE m))(Seq(SUC(PRE m)))" 
				 THEN EVERY_ASSUM STRIP_ASSUME_TAC
				 THEN UNDISCH_TAC "P(last(Seq(PRE m))):bool"
				 THEN ASSUM_LIST
					((REWRITE_TERML "last(Seq(PRE m))")
						 o SYML_th)
				 THEN ONE_IMP_RES_TAC lemma7
				 THEN IMP_RES_TAC TTseq_first_last_finite 
				 THEN IMP_RES_TAC SUC_PRE
				 THEN APPLY_TO  "SUC(PRE m) = m" 
					SUBST_ALL_TAC
				 THEN DISCH_TAC
				 THEN RES_TAC
				 THEN POP_IT "m=m:num"
				 THEN ASM_REWRITE_TAC[]
				;ONE_IMP_RES_TAC lemma7
				 THEN IMP_RES_TAC TTseq_first_last_finite
				 THEN REWRITE_ASM[next]
				 THEN INDUCT_TAC
				 THENL	[DISCH_TAC
					 THEN RES_TAC
					;DISCH_TAC
					 THEN ASSUME_TAC
						(SPEC "n:num" LESS_SUC_REFL)
					 THEN IMP_RES_TAC LESS_TRANS
					 THEN RES_TAC
					 THEN UNDISCH_TAC
						 "P(last(Seq (n:num))):bool" 
					 THEN ASSUM_LIST
						((REWRITE_TERML
						 "P(last(Seq (n:num))):bool") 
						o SYML_th
						)
					 THEN REWRITE_TAC[SYM_th ADD1]
					 THEN DISCH_TAC
					 THEN RES_TAC
					]			 
				]
			]
		;ONE_IMP_RES_TAC lemma7
		 THEN IMP_RES_TAC TTseq_first_last_finite
		 THEN RULE_ASSUM_TAC(REWRITE_RULE[grd;next])
		 THEN REPLACE_FIRST_ASSUM CHOOSE_TAC
		 THEN UNDISCH_TAC "TERM e"
 		 THEN ASM_REWRITE_TAC[]
		 THEN DISCH_TAC
		 THEN RES_TAC
		 THEN RES_TAC
		 THEN UNDISCH_TAC "c e' /\ (first e' = last e)"
		 THEN ASM_REWRITE_TAC[]
		 THEN DISCH_TAC
		 THEN RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM])
		 THEN EVERY_ASSUM STRIP_ASSUME_TAC
		 THEN RES_TAC
		;ONE_IMP_RES_TAC lemma8
		 THEN IMP_RES_TAC lub_div_seq
		 THEN FIRST_ASSUM SUBST_ALL_TAC
		 THEN RES_TAC
		;ONE_IMP_RES_TAC lemma8
		 THEN IMP_RES_TAC lub_div_seq
		 THEN FIRST_ASSUM SUBST_ALL_TAC
		 THEN RES_TAC
		]
);;

%
|                   {P} c {P}
|        ---------------------------------
|         {P} do c od {P AND (NOT (grd c))}     
%

let do_od_spec = prove_thm
(	`do_od_spec`,
	"!c P. spec P c P ==> spec P (do_od c) (P AND (NOT(grd c)))",
	REPEAT STRIP_TAC
	THEN REWRITE_TAC[do_od]
	THEN HALF_REWRITE_TAC[orelse_spec]
	THEN IMP_RES_TAC rec_spec
	THEN ASM_REWRITE_TAC[SYM_th rec_grd;skip_spec]
);;


%
|           wfp W R                      
|           (!s. P s /\ (grd c s) ==> W(t s))  
|           [P AND (\s.t s = val)] c [P AND (\s.R(t s) val))]
|        ----------------------------------------------------------------------
|           [P] do c od [P AND (NOT (grd c))]     
%

let lemma1 = PROVE
(	"!W:*->bool.!R c P.!t:state->*.
	 (!val:*. total_spec 
			(P AND (\s.t s = val)) c (P AND (\s.R(t s) val)))
	 ==> total_spec P c P",
	REWRITE_TAC[total_spec;spec;halts]
	THEN REPEAT STRIP_TAC
	THENL	[RES_TAC
		 THEN REPLACE_FIRST_ASSUM(ASSUME_TAC o (SPEC "t(first e):*"))
		 THEN REWRITE_ASM[AND]
		 THEN RULE_ASSUM_TAC BETA_RULE
		 THEN POP_IT "T"
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		;REPLACE_FIRST_ASSUM
			(ASSUME_TAC 
			o CONJUNCT2
			o (SPEC "t(first e):*")
			)
		 THEN REWRITE_ASM[AND]
		 THEN RULE_ASSUM_TAC BETA_RULE
		 THEN RES_TAC
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		]
);;

let lemma2 = PROVE
(	"!Seq c m.
	 c(Seq 0) ==>
	 (!n. n < m ==> next c(Seq n)(Seq(SUC n))) ==>
	 !n. n <= m ==> c(Seq n)",
	REWRITE_TAC[next]
	THEN REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THEN DISCH_TAC
	THENL	[ASM_REWRITE_TAC[]
		;ASSUME_TAC(SPEC "n:num" LESS_SUC_REFL)
		 THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
		 THEN RES_TAC
		]
);;

let lemma3 = PROVE
(	"!P c Seq.
	 total_spec P c P ==>
	 P(first(Seq 0)) ==>
	 c(Seq 0) ==>
	 (!m.(!n. n < m ==> next c(Seq n)(Seq(SUC n))) ==>
	 TERM(TTseq Seq m) /\ P(first(Seq m)))",
	REWRITE_TAC[total_spec;spec;halts]
	THEN REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THENL	[RES_TAC
		 THEN REPLACE_FIRST_ASSUM(ASSUME_TAC o (SPEC "first(Seq 0)"))
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[TTseq]
		;DISCH_TAC
		 THEN REWRITE_TAC[TTseq]
		 THEN SUPPOSE_TAC "!n.n<m ==> next c(Seq n)(Seq(SUC n))"
		 THENL	[ONE_IMP_RES_TAC
				(SPECL["Seq:num->exseq";"c:command";"m:num"]
				 lemma7)
			 THEN RES_TAC
			 THEN ASSUME_TAC(SPEC "m:num" LESS_SUC_REFL)
			 THEN RES_TAC
			 THEN IMP_RES_TAC TTseq_first_last_finite
			 THEN ASSUME_TAC(SPEC "m:num" LESS_EQ_REFL)
			 THEN IMP_RES_TAC lemma2
			 THEN RES_TAC
			 THEN ASSUME_TAC(SPEC "SUC m" LESS_EQ_REFL)
			 THEN IMP_RES_TAC lemma2
			 THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD1;next])
			 THEN EVERY_ASSUM STRIP_ASSUME_TAC
			 THEN RES_TAC
			 THEN UNDISCH_TAC "first(Seq(m + 1)) = last(Seq m)"
			 THEN ASSUM_LIST(REWRITE_TAC o SYML_th)
			 THEN DISCH_TAC
			 THEN IMP_RES_TAC join_TERM
			 THEN ASM_REWRITE_TAC[ADD1]
			;REPEAT STRIP_TAC
			 THEN ASSUME_TAC(SPEC "m:num" LESS_SUC_REFL)
			 THEN IMP_RES_TAC LESS_TRANS 
			 THEN RES_TAC		
			]
		]
);;

let lemma4 = PROVE
(	"!P e c.
	 P(first e) ==>
	 total_spec P c P ==>
	 do_od c e ==>
	 ~TERM e ==>
	 ?Seq. 	c(Seq 0) 
		/\ (!n. next c(Seq n)(Seq(SUC n)))
		/\ (e = lub $<=| (TTseq Seq))",
	REWRITE_TAC[do_od;orelse;rec]
	THEN REPEAT STRIP_TAC
	THENL	[REWRITE_ASM[]
		 THEN ONE_IMP_RES_TAC lemma7
		 THEN IMP_RES_TAC TTseq_first_last_finite
		 THEN REWRITE_ASM[]
		 THEN IMP_RES_TAC lemma3
		 THEN RES_TAC
		;EXISTS_TAC "Seq:num->exseq"
		 THEN ASM_REWRITE_TAC[]
		;REWRITE_ASM[skip]
		 THEN REPLACE_FIRST_ASSUM CHOOSE_TAC
		 THEN REWRITE_ASM[pair_TERM]
		 THEN UNDISCH_TAC "F"
		 THEN REWRITE_TAC[]
		]
);;

let lemma5 = PROVE
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

let lemma6 = PROVE
(	"!P c.
	 total_spec P c P
	 ==> (!n.next c(Seq n)(Seq(SUC n)))
	 ==> P(first(Seq 0))
	 ==> c(Seq 0) 
	 ==> !n. P(first(Seq n)) /\ (grd c (first(Seq n)))",
	REWRITE_TAC[total_spec_alt;grd]
	THEN REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN IMP_RES_TAC lemma5
	THEN INDUCT_TAC
	THENL	[ASM_REWRITE_TAC[]
		 THEN EXISTS_TAC "Seq 0:exseq"
		 THEN ASM_REWRITE_TAC[]
		;MAPFILTER_ASSUM(STRIP_ASSUME_TAC o (SPEC "n:num"))
		 THEN EVERY_ASSUM STRIP_ASSUME_TAC
		 THEN RES_TAC
		 THEN RULE_ASSUM_TAC(REWRITE_RULE[next])
		 THEN ASM_REWRITE_TAC[]
		 THEN EXISTS_TAC "Seq(SUC n):exseq"
		 THEN ASM_REWRITE_TAC[]
		]
);;

let lemma9 = PROVE
(	"!P c Seq t.!W:*->bool.!R.
	 (!s. P s /\ (grd c s) ==> W(t s)) 
	 ==> (!val. total_spec 
			(P AND (\s.t s = val)) c (P AND (\s.R(t s) val)))
	 ==> P(first(Seq 0))
	 ==> c(Seq 0)
	 ==> (!n. next c(Seq n)(Seq(SUC n)))
	 ==> (!n. R(t(first(Seq(SUC n)))) (t(first(Seq n))) 
			/\ W(t(first(Seq n))))",
	REPEAT GEN_TAC
	THEN REPEAT DISCH_TAC
	THEN IMP_RES_TAC lemma1
	THEN IMP_RES_TAC lemma6
	THEN RULE_ASSUM_TAC(REWRITE_RULE[total_spec_alt;AND])
	THEN RULE_ASSUM_TAC BETA_RULE
	THEN INDUCT_TAC
	THENL	[REPLACE_FIRST_ASSUM(ASSUME_TAC o (SPEC "t(first(Seq 0)):*"))
		 THEN RES_TAC
		 THEN REWRITE_ASM[next]
		 THEN REPEAT (POP_IT "T")
		 THEN ASM_REWRITE_TAC[]
		;RULE_ASSUM_TAC(REWRITE_RULE[next])
		 THEN MAPFILTER_ASSUM(ASSUME_TAC o (SPEC "n:num"))
 		 THEN MAPFILTER_ASSUM(ASSUME_TAC o (SPEC "SUC n"))
		 THEN EVERY_ASSUM STRIP_ASSUME_TAC
		 THEN ASSUME_TAC(REFL "t(first(Seq(SUC n))):*")
		 THEN RES_TAC
		 THEN POP_IT "t(first(Seq(SUC n))) = t(first(Seq(SUC n))):*"
		 THEN REWRITE_ASM[]
		 THEN REPEAT (POP_IT "T")
	 	 THEN ASM_REWRITE_TAC[]
		]
);;

let lemma10 = PROVE
(	"!P c.!W:*->bool.!R t.
	 (!s. P s /\ (grd c s) ==> W(t s)) 
	 ==> (!val. total_spec 
			(P AND (\s.t s = val)) c (P AND (\s.R(t s) val)))
	 ==> ~halts P (do_od c) 
	 ==> ?C. dec_chain C W R",
	REWRITE_TAC[halts_alt]
	THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	THEN REWRITE_TAC[NOT_IMP]
	THEN REPEAT STRIP_TAC
	THEN IMP_RES_TAC lemma1
	THEN IMP_RES_TAC lemma4
	THEN ONE_IMP_RES_TAC lemma8
	THEN IMP_RES_TAC TTseq_chain
	THEN IMP_RES_TAC lub_first
	THEN REWRITE_ASM[TTseq]
	THEN IMP_RES_TAC lemma9
	THEN EXISTS_TAC "\n:num.t(first(Seq n)):*"
	THEN REWRITE_TAC[dec_chain]
	THEN BETA_TAC
	THEN ASM_REWRITE_TAC[]		
);;

let lemma11 = PROVE
(	"!W:*->bool.!R c P t.
	 wfp W R
	 ==> (!s. P s /\ (grd c s) ==> W(t s)) 
	 ==> (!val. total_spec 
			(P AND (\s.t s = val)) c (P AND (\s.R(t s) val)))
	 ==> halts P (do_od c)",
	REWRITE_TAC[wfp]
	THEN REPEAT STRIP_TAC
	THEN ASM_CASES_TAC "halts P(do_od c)"
	THENL	[ASM_REWRITE_TAC[] 
		;IMP_RES_TAC lemma10
		 THEN RULE_ASSUM_TAC(CONV_RULE (TRY_CONV NOT_EXISTS_CONV))
		 THEN RES_TAC
		]
);;

let do_od_total_spec = prove_thm
(	`do_od_total_spec`,
	"!W:*->bool.!R c P t.
	 wfp W R
	 ==> (!s. P s /\ (grd c s) ==> W(t s)) 
	 ==> (!val.total_spec 
			(P AND (\s.t s = val)) c (P AND (\s.R(t s) val)))
	 ==> total_spec P (do_od c) (P AND (NOT (grd c)))",
	REPEAT STRIP_TAC
	THEN REWRITE_TAC[total_spec]
	THEN HALF_REWRITE_TAC[do_od_spec]
	THEN IMP_RES_TAC lemma1
	THEN IMP_RES_TAC lemma11
	THEN RULE_ASSUM_TAC(REWRITE_RULE[total_spec])
	THEN ASM_REWRITE_TAC[]
);; 
