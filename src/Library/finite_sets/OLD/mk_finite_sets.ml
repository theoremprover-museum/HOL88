%----------------------------------------------------------------

   File:         mk_finite_sets.ml (previously sets.ml -- MJCG)
   Description:  

   Defines a new type for finite sets and proves properties of
   sets.  The theory is a formalization of the theory of sets
   presented in chapter 10 of Manna and Waldingers "The Logical
   Basis of Computer Programming, VOL 1."

   The axiomatization is definitional.  An induction principle is
   defined but no recursive definitions are allowed.

   Authors:      (c) P. J. Windley 1989
                 (c) Philippe Leveiley 1989
   Date:         May 12, 1989
                 Cardinality definition added 25 may 1989

   Usage:        After making sets a parent theory, execute
                 "loadf `sets.ml`;;".  Ensure that sets.ml
                 and sets.th are both in the current load path.

----------------------------------------------------------------%

set_flag (`sticky`, true);;

% system `rm finite_sets.th`;;		DELETED [TFM 91.01.23]	%

new_theory `finite_sets`;;

%----------------------------------------------------------------
 rules
----------------------------------------------------------------%

% BINDER_CONV conv "B x. tm[x]" applies conv to tm[x]			%
let BINDER_CONV conv =  (RAND_CONV (ABS_CONV conv));;

% DEPTH_FORALL_CONV : BINDER_CONV in depth				%
letrec DEPTH_FORALL_CONV conv tm = 
       if (is_forall tm) then
          BINDER_CONV (DEPTH_FORALL_CONV conv) tm else
	  conv tm;;

let SYM_RULE =
  (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
? failwith `SYM_RULE`;;


%----------------------------------------------------------------
 tactics
----------------------------------------------------------------%

let SWAP_TOP_ASSUMP_TAC = 
     POP_ASSUM (\th1. 
        POP_ASSUM (\th2 . (ASSUME_TAC th1
             THEN ASSUME_TAC th2)));;

let POP_TOP_ASSUMP_TAC = POP_ASSUM (K ALL_TAC);;


%----------------------------------------------------------------
 lemmas
----------------------------------------------------------------%

let NOT_EQ_REV = TAC_PROOF
   (([], "!(x:bool) y . (~x = y) = (x = ~y)"),
    REPEAT GEN_TAC
    THEN MAP_EVERY BOOL_CASES_TAC ["x:bool"; "y:bool"]
    THEN REWRITE_TAC []
   );;

let CONJ_DISJ_DISTRIB = TAC_PROOF
   (([],"!p q r. p /\ (q \/ r) = (p /\ q) \/ (p /\ r)"),
    REPEAT GEN_TAC
    THEN MAP_EVERY BOOL_CASES_TAC ["p"; "q"; "r"]
    THEN REWRITE_TAC []
   );;

let DISJ_CONJ_DISTRIB = TAC_PROOF
   (([],"!p q r. p \/ (q /\ r) = (p \/ q) /\ (p \/ r)"),
    REPEAT GEN_TAC
    THEN MAP_EVERY BOOL_CASES_TAC ["p"; "q"; "r"]
    THEN REWRITE_TAC []
   );;

let N_LEQ_SUC_M = TAC_PROOF
    (([],"! n m . (n <= (SUC m)) = ((n <= m) \/ (n = (SUC m)))"),
     REWRITE_TAC[LESS_OR_EQ;
                 LESS_THM;
                 SPECL ["n=m"; "n<m"] DISJ_SYM]
   );;


%----------------------------------------------------------------
  define type; representation is functions (*->bool).
----------------------------------------------------------------%

let EMPTY_REP_DEF = new_definition
   (`EMPTY_REP_DEF`,
    "EMPTY_REP = \x:*.F"
   );;

let INSERT_REP_DEF = new_definition
   (`INSERT_REP_DEF`,
    "! (x:*) (s:*->bool) . INSERT_REP x s = 
         (\y:* . (y = x) \/ (s y))"
   );;


%----------------------------------------------------------------

let IS_SET_REP = new_definition
   (`IS_SET_REP`,
    "IS_SET_REP (s:*->bool) = ? x t .(s = EMPTY_REP) \/ 
                                     (s  = INSERT_REP x t)"
   );;
----------------------------------------------------------------%

let IS_SET_REP = new_definition
   (`IS_SET_REP`,
    "IS_SET_REP (s:*->bool) = 
       !P:((*->bool)->bool) . P EMPTY_REP /\
          (!n x. P n ==> P(INSERT_REP x n)) ==>  P s"
   );;

let SET_REP_EXISTS = TAC_PROOF
   (([], "?(x:*->bool) . IS_SET_REP x"),
    PURE_REWRITE_TAC [IS_SET_REP]
    THEN EXISTS_TAC "EMPTY_REP:*->bool"
    THEN REPEAT STRIP_TAC
   );;

let set_TY_DEF = 
   new_type_definition
      (`set`,
       "IS_SET_REP:(*->bool)->bool",
       SET_REP_EXISTS);;

%----------------------------------------------------------------
set_TY_DEF = 
|- ?rep. TYPE_DEFINITION IS_SET_REP rep
----------------------------------------------------------------%

let set_ISO_DEF = 
    define_new_type_bijections
        `set_ISO_DEF` `ABS_set` `REP_set` set_TY_DEF;;


let R_11 = prove_rep_fn_one_one set_ISO_DEF     and
    R_ONTO = prove_rep_fn_onto set_ISO_DEF      and
    A_11   = prove_abs_fn_one_one set_ISO_DEF   and
    A_ONTO = prove_abs_fn_onto set_ISO_DEF      and
    A_R = CONJUNCT1 set_ISO_DEF                 and
    R_A = CONJUNCT2 set_ISO_DEF;;

%----------------------------------------------------------------
R_11 = |- !a a'. (REP_set a = REP_set a') = (a = a')
R_ONTO = |- !r. IS_SET_REP r = (?a. r = REP_set a)
A_11 = 
|- !r r'.
    IS_SET_REP r ==>
    IS_SET_REP r' ==>
    ((ABS_set r = ABS_set r') = (r = r'))
A_ONTO = |- !a. ?r. (a = ABS_set r) /\ IS_SET_REP r
A_R = |- !a. ABS_set(REP_set a) = 
a
R_A = |- !r. IS_SET_REP r = (REP_set(ABS_set r) = r)
----------------------------------------------------------------%

let EMPTY_DEF = new_definition
   (`EMPTY_DEF`,
    "EMPTY = (ABS_set \x:*.F)"
   );;

let EMPTY_DEF_LEMMA = TAC_PROOF
   (([], "EMPTY = (ABS_set (EMPTY_REP:*->bool))"),
    REWRITE_TAC [EMPTY_DEF; EMPTY_REP_DEF]
   );;

let IN_DEF = new_infix_definition
   (`IN`,
    "$IN (x:*) (s:(*)set) = (REP_set s) x"
   );;

let INSERT_DEF = new_definition
   (`INSERT_DEF`,
    "! (x:*) (s:(*)set) . INSERT x s = 
        (ABS_set (\y:* . (y = x) \/ ((REP_set s) y)))"
   );;

let INSERT_DEF_LEMMA = TAC_PROOF
   (([], "!s x. INSERT x s = (ABS_set (INSERT_REP x (REP_set s)))"),
    REWRITE_TAC [INSERT_DEF; INSERT_REP_DEF]
   );;

let IS_SET_REP_EMPTY = TAC_PROOF
   (([], "IS_SET_REP (EMPTY_REP:*->bool)"),
    REWRITE_TAC [IS_SET_REP; EMPTY_REP_DEF; ]
    THEN REPEAT STRIP_TAC
   );;


let R_A_lemma_1 = TAC_PROOF
   (([], "REP_set (ABS_set (\x. F)) = (\x.F)"),
    ACCEPT_TAC (REWRITE_RULE [
                       (REWRITE_RULE [EMPTY_REP_DEF] 
                               (SPEC_ALL IS_SET_REP_EMPTY))]
		 (SPEC "\x.F" R_A))
   );;

let IS_SET_INSERT_REP = TAC_PROOF
   (([],"! x s.(IS_SET_REP s) ==> IS_SET_REP (INSERT_REP x s)"),
    PURE_REWRITE_TAC [IS_SET_REP; EMPTY_REP_DEF; 
		      INSERT_REP_DEF]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (\th . ASSUME_TAC (SPECL ["s"; "x"] th)
                 THEN ASSUME_TAC th)
    THEN RES_TAC
    THEN RES_TAC
   );;

let IS_SET_REP_INSERT_REP = TAC_PROOF
   (([],"! x s. IS_SET_REP (INSERT_REP x (REP_set s))"),
    REPEAT GEN_TAC
    THEN MATCH_MP_TAC IS_SET_INSERT_REP
    THEN REWRITE_TAC[R_ONTO]
    THEN EXISTS_TAC "s"
    THEN REFL_TAC
   );;

let R_A_lemma_2 = TAC_PROOF
   (([], 
    "!s x.  REP_set (ABS_set (\y. (y = x) \/ REP_set s y)) =
            (\y. (y = x) \/ REP_set s y)"),
    REPEAT STRIP_TAC
    THEN ACCEPT_TAC (REWRITE_RULE [
                       (REWRITE_RULE [INSERT_REP_DEF]
                         (SPEC_ALL IS_SET_REP_INSERT_REP))]
		 (SPEC "(\y. (y = x) \/ REP_set s y)" R_A))
   );;

let R_A_lemma = CONJ R_A_lemma_1  R_A_lemma_2;;

let REP_LEMMA = TAC_PROOF
   (([], "IS_SET_REP (REP_set (s:(*)set))"),
    REWRITE_TAC [R_ONTO]
    THEN EXISTS_TAC "s:(*)set"
    THEN REFL_TAC
   );;

%----------------------------------------------------------------
  prove some basic properties of sets
----------------------------------------------------------------%
let im_lemma = TAC_PROOF 
   (([],
    "(\y. (y = x) \/ (y = x) \/ REP_set s y) =
     (\y. (y = x) \/ REP_set s y)"),
    CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
    THEN GEN_TAC
    THEN BETA_TAC
    THEN BOOL_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
);;

let INSERT_MULTIPLICITY = prove_thm
   (`INSERT_MULTIPLICITY`,
    "! x s . INSERT x (INSERT x s) = INSERT x s",
    REPEAT GEN_TAC
    THEN REWRITE_TAC 
	 [INSERT_DEF;IN_DEF; R_11;A_11;A_R; R_A_lemma]
    THEN BETA_TAC
    THEN REWRITE_TAC [im_lemma]
   );;

let lemma1 = TAC_PROOF 
   (([],
    "(\y'. (y' = x) \/ (y' = y) \/ REP_set s y') =
     (\y'. (y' = y) \/ (y' = x) \/ REP_set s y')"),
    CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)
    THEN GEN_TAC
    THEN BETA_TAC
    THEN BOOL_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
);;


let INSERT_ASSOC = prove_thm
   (`INSERT_ASSOC`,
    "! x y s . INSERT x (INSERT y s) = INSERT y (INSERT x s)",
    REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC 
	 [INSERT_DEF;IN_DEF; R_11;A_R;R_A_lemma_2;]
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC []
    THEN ASM_CASES_TAC "x = y"
    THEN ASM_REWRITE_TAC []
    THEN POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
    THEN ASM_REWRITE_TAC []
    THEN SUBST1_TAC lemma1
    THEN REFL_TAC
);;

%----------------------------------------------------------------
 set equality
----------------------------------------------------------------%
let SET_EQ = prove_thm
   (`SET_EQ`,
   "! s1 s2 . (s1 = s2) = !x.(x IN s1) = (x IN s2)",
    REPEAT STRIP_TAC
    THEN EQ_TAC
    THENL [ % 1 %
	REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC []
    ; % 2 %
	REWRITE_TAC [IN_DEF]
	THEN REPEAT STRIP_TAC
	THEN POP_ASSUM (\th . ACCEPT_TAC (REWRITE_RULE [R_11] (EXT th)))
    ]
   );;


%----------------------------------------------------------------
  Set Membership  this is a hack, a cleaner proof exists
----------------------------------------------------------------%
let IN = prove_thm
   (`IN`,
    "(!x.  x IN EMPTY = F) /\
     (!x y s . x IN (INSERT y s) = (x = y) \/ x IN s)",
    REWRITE_TAC [IN_DEF; EMPTY_DEF; INSERT_DEF;
		 R_11;A_11;A_R;R_A_lemma]
    THEN REPEAT GEN_TAC
    THEN ASM_CASES_TAC "REP_set s y"
    THEN ASM_REWRITE_TAC [R_A_lemma_2]
    THENL [ % 1 %
	ASM_CASES_TAC "x = y"
        THEN BETA_TAC
	THEN ASM_REWRITE_TAC []
    ; % 2 %
	BETA_TAC
	THEN REFL_TAC
    ]
   );;

%----------------------------------------------------------------
  induction -- this parallels the derivation of induction by
               T. Melham for natural numbers.
----------------------------------------------------------------%
let ind_lemma_1 = TAC_PROOF
   (([],"!P. P EMPTY_REP /\ 
         (!(s:*->bool) x. (P s ==> P (INSERT_REP x s))) ==>
            (!(s:*->bool). IS_SET_REP s ==> P s)"),
    PURE_ONCE_REWRITE_TAC [IS_SET_REP]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
);;

let lemma = TAC_PROOF
   (([], "(A ==> A /\ B) = (A ==> B)"),
    ASM_CASES_TAC "A:bool"
    THEN ASM_REWRITE_TAC []
   );;

let ind_lemma_2 = TAC_PROOF
   (([],"!P. P EMPTY_REP /\ 
         (!(s:*->bool) x. 
            (IS_SET_REP s /\ P s ==> P (INSERT_REP x s))) ==>
               (!(s:*->bool). IS_SET_REP s ==> P s)"),
    GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (SPEC "\s:*->bool. IS_SET_REP s /\ P s" ind_lemma_1) THEN
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC [lemma;IS_SET_REP_EMPTY] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THENL 
    [IMP_RES_THEN MATCH_ACCEPT_TAC IS_SET_INSERT_REP;
     RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let lemma1 = TAC_PROOF
   (([], "(! s:*->bool. IS_SET_REP s ==> P(ABS_set s)) = (! s. P s)"),
    EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN STRIP_ASSUME_TAC (SPEC "s:(*)set" A_ONTO)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
  );;

% --------------------------------------------------------------------- %
% NB: set_induction modified, because it was NOT in the standard form	%
% expected by INDUCT_THEN.			        [TFM 90.06.24]	%
% --------------------------------------------------------------------- %

let set_induction = prove_thm 
   (`set_induction`,
   "!P. (P EMPTY /\ (!s. P s ==> !x:*. P(INSERT x s))) ==> !s. P s",
    GEN_TAC
    THEN STRIP_TAC
    THEN MP_TAC (SPEC "\s:*->bool. P(ABS_set s):bool" ind_lemma_2)
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC [(SYM_RULE EMPTY_DEF_LEMMA); lemma1]
    THEN DISCH_THEN MATCH_MP_TAC
    THEN REWRITE_TAC [R_ONTO]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC ANTE_CONJ_CONV
    THEN DISCH_THEN (STRIP_THM_THEN SUBST1_TAC)
    THEN ASM_REWRITE_TAC [A_R; (SYM_RULE (SPEC_ALL INSERT_DEF_LEMMA))] 
    THEN STRIP_TAC THEN RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC
   );;

let SET_INDUCT_TAC = INDUCT_THEN set_induction ASSUME_TAC;;

%----------------------------------------------------------------
SET_CASES_THM = |- !s. (s = EMPTY) \/ (?s' x. s = INSERT x s')
----------------------------------------------------------------%
let SET_CASES_THM = 
   save_thm(`SET_CASES_THM`, prove_cases_thm set_induction);;

let SET_CASES_TAC t = DISJ_CASES_THEN 
                       STRIP_ASSUME_TAC (SPEC t SET_CASES_THM);;


%----------------------------------------------------------------
 SET_DISTINCT
----------------------------------------------------------------%
let SET_DISTINCT = prove_thm
   (`SET_DISTINCT`,
    "!(x:*) s. ~(EMPTY = INSERT x s)",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SET_EQ; IN]
    THEN CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV)
    THEN EXISTS_TAC "x"
    THEN REWRITE_TAC []
   );;

%----------------------------------------------------------------
 some properties of INSERT and EMPTY
----------------------------------------------------------------%
let COMPONENT = prove_thm
   (`COMPONENT`,
    "! (x:*) s . x IN INSERT x s",
    REWRITE_TAC [IN]
   );;

let NONEMPTY_MEMBER = prove_thm
   (`NONEMPTY_MEMBER`,
    "!s. ~(s = EMPTY) = ? x:* . x IN s",
    SET_INDUCT_TAC
    THEN REWRITE_TAC [IN]
    THEN REWRITE_TAC [SYM_RULE SET_DISTINCT]
    THEN GEN_TAC THEN EXISTS_TAC "x"			% [TFM 90.06.24] %
    THEN REWRITE_TAC []
   );;

let ABSORPTION = prove_thm
   (`ABSORPTION`,
    "! x s . x IN s ==> (INSERT x s = s)",
    GEN_TAC
    THEN SET_INDUCT_TAC
    THEN REWRITE_TAC [IN; INSERT_MULTIPLICITY] 
    THEN GEN_TAC					% [TFM 90.06.24] %
    THEN ASM_CASES_TAC "x = x'"
    THEN ASM_REWRITE_TAC [INSERT_MULTIPLICITY]
    THEN STRIP_TAC
    THEN RES_TAC
    THEN SUBST1_TAC (SPECL["x";"x'";"s"] INSERT_ASSOC)
    THEN ASM_REWRITE_TAC []
   );; 

let set_induction_2 = prove_thm
   (`set_induction_2`,
    "!P. P EMPTY /\ 
          (!s  .!x. (~(x IN s) ==> (P s ==> P(INSERT x s))))  ==> (!s. P s)",
    GEN_TAC
    THEN STRIP_TAC
    THEN SET_INDUCT_TAC
    THEN ASM_REWRITE_TAC []
    THEN REPEAT GEN_TAC
    THEN SWAP_TOP_ASSUMP_TAC
    THEN POP_ASSUM (\th. ASSUME_TAC (SPECL ["s"; "x"] th))
    THEN ASSUME_TAC (SPEC_ALL ABSORPTION)
    THEN ASM_CASES_TAC "x IN s"
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
);;


%----------------------------------------------------------------
  Taken from T. Melham's INDUCT_THEN 

  (pre-1.12 version! [TFM 90.06.24])
----------------------------------------------------------------%
let SET_INDUCT_2_TAC (A,t) = 
    (let x,body = dest_forall t in
     let th = set_induction_2 in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in
     let th_tac = ASSUME_TAC in
     let tac = 
     (MATCH_MP_TAC thm THEN
      REPEAT CONJ_TAC THEN
      FIRST [CONV_TAC (DEPTH_FORALL_CONV BETA_CONV);
             CONV_TAC (GEN_ALPHA_CONV x) THEN
             REPEAT GEN_TAC THEN 
             DISCH_TAC THEN
             DISCH_THEN (\th. 
              CONV_TAC (DEPTH_FORALL_CONV BETA_CONV) THEN
              MAP_EVERY (th_tac o (CONV_RULE BETA_CONV)) (CONJUNCTS th))]) in
      (tac (A,t))) ? failwith `INDUCT_THEN`;;

%----------------------------------------------------------------
 member decomposition  (there has to be a nicer proof)
 totally rewritten for version 12 resolution tools [TFM 91.01.23]
----------------------------------------------------------------%

let MEMBER_DECOMP = prove_thm
   (`MEMBER_DECOMP`,
    "!s x. x IN s ==> ? t. ((s = INSERT x t) /\ ~(x IN t))",
    SET_INDUCT_2_TAC THEN REWRITE_TAC [IN] THEN
    REPEAT STRIP_TAC THENL
    [EXISTS_TAC "s:(*)set" THEN ASM_REWRITE_TAC [];
     RES_TAC THEN EXISTS_TAC "INSERT x t" THEN
     ASM_REWRITE_TAC [IN] THEN CONJ_TAC THENL
     [MATCH_ACCEPT_TAC INSERT_ASSOC;
      DISCH_THEN SUBST_ALL_TAC THEN RES_TAC]]);;

%----------------------------------------------------------------
  set union
----------------------------------------------------------------%   

let UNION_P = new_definition
   (`UNION_P`,
    "!(t:(*)set) s1 s2 . UNION_P t s1 s2 = 
               !x . x IN t = x IN s1 \/ x IN s2"
   );;

let UNION_DEF = new_infix_definition
   (`UNION_DEF`,
    "$UNION (s1:(*)set) s2 = @ t . UNION_P t s1 s2" 
   );;

let UNION_MEMBER_LEMMA = TAC_PROOF
   (([],
    "! (s1:(*)set) s2 . UNION_P (s1 UNION s2) s1 s2"),
    REWRITE_TAC [UNION_DEF]
    THEN REWRITE_TAC [SYM_RULE UNION_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [UNION_P]
    THEN SPEC_TAC ("s1","s1")
    THEN SET_INDUCT_2_TAC
    THENL [ % 1 %
	REWRITE_TAC [IN]
	THEN EXISTS_TAC "s2"
	THEN REWRITE_TAC []
    ;  % 2 %
	UNDISCH_TAC "?t. !x'. x' IN t = x' IN s1 \/ x' IN s2"
	THEN REPEAT STRIP_TAC
	THEN EXISTS_TAC "(INSERT x t)"
	THEN GEN_TAC
	THEN REWRITE_TAC [IN]
	THEN ASM_CASES_TAC "x' = x"
	THEN ASM_REWRITE_TAC []
    ]
   );;

let IN_UNION = save_thm (`IN_UNION`,
                 REWRITE_RULE [UNION_P] UNION_MEMBER_LEMMA);;

let UNION_EMPTY_LEMMA = TAC_PROOF
   (([], "! s:(*)set . EMPTY UNION s = s"),
    REWRITE_TAC [SET_EQ; IN_UNION;IN]
   );;

let UNION_INSERT_LEMMA = TAC_PROOF
    (([],  "! (x:*) (s1:(*)set) s2 .
      (INSERT x s1) UNION s2 = 
          x IN s2 => s1 UNION s2 | (INSERT x (s1 UNION s2))"),
    REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC [SET_EQ; IN_UNION;IN]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
   );;

let UNION = save_thm (`UNION`, CONJ UNION_EMPTY_LEMMA UNION_INSERT_LEMMA);;

let UNION_ASSOC = prove_thm
   (`UNION_ASSOC`,
    "! (s1:(*)set) (s2:(*)set) (s3:(*)set) .
         (s1 UNION s2) UNION s3 = s1 UNION (s2 UNION s3)",
    SET_INDUCT_TAC
    THEN ASM_REWRITE_TAC [UNION]
    THEN REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC [IN; IN_UNION]
    THEN ASM_CASES_TAC "x IN s3"
    THEN ASM_REWRITE_TAC [UNION]
);;

let UNION_IDENT = prove_thm
   (`UNION_IDENT`,
    "! (s:(*)set)  . s UNION s = s",
    GEN_TAC
    THEN REWRITE_TAC [SET_EQ;IN_UNION]
   );;

let UNION_SYM = prove_thm
   (`UNION_SYM`,
    "! (s1:(*)set) (s2:(*)set) . (s1 UNION s2) = (s2 UNION s1)",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SET_EQ; IN_UNION]
    THEN GEN_TAC
    THEN SUBST1_TAC (SPECL ["x IN s1"; "x IN s2"] DISJ_SYM)
    THEN REFL_TAC
   );;

%----------------------------------------------------------------
  set intersection
----------------------------------------------------------------%

let INTERSECT_P = new_definition
   (`INTERSECT_P`,
    "!(t:(*)set) s1 s2 . INTERSECT_P t s1 s2 = 
               !x . x IN t = x IN s1 /\ x IN s2"
   );;

let INTERSECT_DEF = new_infix_definition
   (`INTERSECT_DEF`,
    "$INTERSECT (s1:(*)set) s2 = @ t . INTERSECT_P t s1 s2" 
   );;

let INTERSECT_MEMBER_LEMMA = TAC_PROOF
   (([],
    "! (s1:(*)set) s2 . INTERSECT_P (s1 INTERSECT s2) s1 s2"),
    REWRITE_TAC [INTERSECT_DEF]
    THEN REWRITE_TAC [SYM_RULE INTERSECT_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [INTERSECT_P]
    THEN SPEC_TAC ("s1","s1")
    THEN SET_INDUCT_2_TAC
    THENL [ % 1 %
	REWRITE_TAC [IN]
	THEN EXISTS_TAC "EMPTY:(*)set"
	THEN REWRITE_TAC [IN]
    ;  % 2 %
	POP_ASSUM MP_TAC
	THEN REPEAT STRIP_TAC
        THEN ASM_CASES_TAC "x IN s2"
        THENL [ % 2.1 %
	    EXISTS_TAC "(INSERT x t)"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ; % 2.2 %
	    EXISTS_TAC "t"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ]
	THEN ASM_CASES_TAC "x' = x"
	THEN ASM_REWRITE_TAC []
    ]
   );;

let IN_INTERSECT = save_thm (`IN_INTERSECT`,
                 REWRITE_RULE [INTERSECT_P] INTERSECT_MEMBER_LEMMA);;

let INTERSECT_EMPTY_LEMMA = TAC_PROOF
   (([], "! s:(*)set . EMPTY INTERSECT s = EMPTY"),
    REWRITE_TAC [SET_EQ; IN_INTERSECT;IN]
   );;

let INTERSECT_INSERT_LEMMA = TAC_PROOF
    (([],  "! (x:*) (s1:(*)set) s2 .
      (INSERT x s1) INTERSECT s2 = 
          x IN s2 => (INSERT x (s1 INTERSECT s2)) | s1 INTERSECT s2"),  
    REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC [SET_EQ; IN_INTERSECT;IN]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
   );;

let INTERSECT = save_thm (`INTERSECT`, 
         CONJ INTERSECT_EMPTY_LEMMA INTERSECT_INSERT_LEMMA);;

let INTERSECT_ASSOC = prove_thm
   (`INTERSECT_ASSOC`,
    "! (s1:(*)set) (s2:(*)set) (s3:(*)set) .
         (s1 INTERSECT s2) INTERSECT s3 = s1 INTERSECT (s2 INTERSECT s3)",
    SET_INDUCT_TAC
    THEN ASM_REWRITE_TAC [INTERSECT]
    THEN REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC [IN; IN_INTERSECT]
    THEN ASM_CASES_TAC "x IN s3"
    THEN ASM_REWRITE_TAC [INTERSECT]
);;

let INTERSECT_IDENT = prove_thm
   (`INTERSECT_IDENT`,
    "! (s:(*)set)  . s INTERSECT s = s",
    GEN_TAC
    THEN REWRITE_TAC [SET_EQ;IN_INTERSECT]
   );;

let INTERSECT_SYM = prove_thm
   (`INTERSECT_SYM`,
    "! (s1:(*)set) (s2:(*)set) . (s1 INTERSECT s2) = (s2 INTERSECT s1)",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SET_EQ; IN_INTERSECT]
    THEN GEN_TAC
    THEN SUBST1_TAC (SPECL ["x IN s1"; "x IN s2"] CONJ_SYM)
    THEN REFL_TAC
   );;

%----------------------------------------------------------------
 distributivity of union and intersection
----------------------------------------------------------------%

let UNION_OVER_INTERSECT = prove_thm
   (`UNION_OVER_INTERSECT`,
    "! (s1:(*)set) s2 s3 . (s1 INTERSECT (s2 UNION s3)) = 
                 ((s1 INTERSECT s2) UNION (s1 INTERSECT s3))",
    REWRITE_TAC [SET_EQ; IN_INTERSECT;IN_UNION]
    THEN REPEAT GEN_TAC
    THEN SUBST1_TAC 
         (SPECL ["x IN s1"; "x IN s2"; "x IN s3"] CONJ_DISJ_DISTRIB)
    THEN REFL_TAC
);;

let INTERSECT_OVER_UNION = prove_thm
   (`INTERSECT_OVER_UNION`,
    "! (s1:(*)set) s2 s3 . (s1 UNION (s2 INTERSECT s3)) = 
                 ((s1 UNION s2) INTERSECT (s1 UNION s3))",
    REWRITE_TAC [SET_EQ; IN_UNION;IN_INTERSECT]
    THEN REPEAT GEN_TAC
    THEN SUBST1_TAC 
         (SPECL ["x IN s1"; "x IN s2"; "x IN s3"] DISJ_CONJ_DISTRIB)
    THEN REFL_TAC
);;

%----------------------------------------------------------------
  disjoint
----------------------------------------------------------------%
let DISJOINT = new_definition
   (`DISJOINT`,
    "! (s:(*)set) t. DISJOINT s t = (s INTERSECT t = EMPTY)"
   );;

let DISJOINT_MEMBER = prove_thm 
   (`DISJOINT_MEMBER`,
    "! s t. (DISJOINT s t) = ~(? x . x IN s /\ x IN t)",
    REWRITE_TAC [DISJOINT]
    THEN SET_INDUCT_2_TAC
    THEN REWRITE_TAC [IN;INTERSECT]
    THEN GEN_TAC
    THEN COND_CASES_TAC
    THENL [% subgoal 1 %
       REWRITE_TAC [(SYM_RULE SET_DISTINCT)]
       THEN EXISTS_TAC "x"
       THEN ASM_REWRITE_TAC []
    ; % subgoal 2 %
       SWAP_TOP_ASSUMP_TAC
       THEN POP_ASSUM (\th. ASSUME_TAC (SPEC_ALL th))
       THEN ASM_REWRITE_TAC [NOT_EQ_REV]
       THEN EQ_TAC
       THEN REPEAT STRIP_TAC
       THENL [% subgoal 1 %
	  EXISTS_TAC "x'"
	  THEN ASM_REWRITE_TAC []
       ; % subgoal 2 %
	  MAP_EVERY UNDISCH_TAC ["x' IN t"]
	  THEN ASM_REWRITE_TAC []
       ; % subgoal 3 %
	  EXISTS_TAC "x'"
	  THEN ASM_REWRITE_TAC []
       ]
    ]
   );;
  

%----------------------------------------------------------------
  deletion 
----------------------------------------------------------------%

let DELETE_P = new_definition
   (`DELETE_P`,
    "!(t:(*)set) s (y:*). DELETE_P t s y= 
               !x . x IN t = x IN s /\ ~(x = y)"
   );;

let DELETE_DEF = new_infix_definition
   (`DELETE_DEF`,
    "$DELETE (s:(*)set) y = @ t . DELETE_P t s y" 
   );;

let DELETE_MEMBER_LEMMA = TAC_PROOF
   (([],
    "! (s:(*)set) y . DELETE_P (s DELETE y) s y"),
    REWRITE_TAC [DELETE_DEF]
    THEN REWRITE_TAC [SYM_RULE DELETE_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC [DELETE_P]
    THEN SPEC_TAC ("s","s")
    THEN SET_INDUCT_2_TAC
    THENL [ % 1 %
	EXISTS_TAC "EMPTY:(*)set"
	THEN REWRITE_TAC [IN]
    ;  % 2 %
	POP_ASSUM MP_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_CASES_TAC "x = y"
	THEN ASM_REWRITE_TAC []
        THENL [ % 2.1 %
	    EXISTS_TAC "s"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ; % 2.2 %
	    EXISTS_TAC "(INSERT x t)"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ]
        THEN POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
	THEN ASM_CASES_TAC "x' = y"
	THEN ASM_REWRITE_TAC []
    ]
   );;

% Previously DELETE_MEMBER was saved with name IN_DELETE (MJCG 25 May 89) %

let DELETE_MEMBER = save_thm (`DELETE_MEMBER`,
                 REWRITE_RULE [DELETE_P] DELETE_MEMBER_LEMMA);;

let DELETE_EMPTY_LEMMA = TAC_PROOF
   (([], "! y:* . EMPTY DELETE y = EMPTY"),
    REWRITE_TAC [SET_EQ; DELETE_MEMBER;IN]
   );;

let DELETE_INSERT_LEMMA = TAC_PROOF
    (([],  "! (x:*) (s:(*)set) y .
      (INSERT x s) DELETE y = 
          ((x = y) => s DELETE y | (INSERT x (s DELETE y)))"),
    REPEAT GEN_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC [SET_EQ; DELETE_MEMBER;IN]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
   );;

let DELETE = save_thm (`DELETE`, 
         CONJ DELETE_EMPTY_LEMMA DELETE_INSERT_LEMMA);;

let DELETE_DECOMPOSITION = prove_thm
   (`DELETE_DECOMPOSITION`,
    "! s x . x IN s ==> (s = (INSERT x (s DELETE x)))",
    REPEAT STRIP_TAC
    THEN REWRITE_TAC [SET_EQ;DELETE_MEMBER]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC [IN; DELETE_MEMBER]
   );;

let DELETE_ABSORPTION = prove_thm
   (`DELETE_ABSORPTION`,
    "! s x . ~(x IN s) ==> (s = s DELETE x)",
    REPEAT STRIP_TAC
    THEN REWRITE_TAC [SET_EQ; DELETE_MEMBER]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
   );;


%----------------------------------------------------------------
 choice and rest  (delayed so that they are definitional)
----------------------------------------------------------------%
let CHOICE = new_definition
   (`CHOICE`,
    "! s:(*)set . CHOICE s = @ x . x IN s"
   );;

let REST = new_definition
   (`REST`,
    "! s:(*)set . REST s = s DELETE (CHOICE s)"
   );;

let CHOICE_MEMBER = prove_thm
   (`CHOICE_MEMBER`,
    "! s:(*)set . ~(s = EMPTY) ==> (CHOICE s) IN s",
    SET_INDUCT_2_TAC
    THEN REWRITE_TAC [IN; (SYM_RULE SET_DISTINCT)]
    THEN ASM_CASES_TAC "s = EMPTY:(*)set"
    THEN RES_TAC
    THEN ASM_REWRITE_TAC [IN]
    THEN REWRITE_TAC [CHOICE; IN]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN EXISTS_TAC "x"
    THEN REWRITE_TAC []
   );;

let CHOICE_DECOMPOSITION = prove_thm
   (`CHOICE_DECOMPOSITION`,
    "! s:(*)set . ~(s = EMPTY) ==> (s = (INSERT (CHOICE s) (REST s)))",
    REPEAT STRIP_TAC
    THEN REWRITE_TAC [CHOICE; REST]
    THEN ASSUME_TAC (REWRITE_RULE [CHOICE] (SPEC_ALL CHOICE_MEMBER))
    THEN ASSUME_TAC (SPECL ["s"; "@ x . x IN s"] DELETE_DECOMPOSITION)
    THEN RES_TAC THEN RES_TAC
   );;

let CHOICE_NON_MEMBER = prove_thm
   (`CHOICE_NON_MEMBER`,
    "! s:(*)set . ~(s = EMPTY) ==> ~((CHOICE s) IN (REST s))",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [CHOICE; REST; DELETE_MEMBER]
   );;

%----------------------------------------------------------------
 set difference
----------------------------------------------------------------%
 
let DIFF_P = new_definition
   (`DIFF_P`,
    "!(t:(*)set) s1 s2. DIFF_P t s1 s2= 
               !x . x IN t = x IN s1 /\ ~(x IN s2)"
   );;

let DIFF_DEF = new_infix_definition
   (`DIFF_DEF`,
    "$DIFF (s:(*)set) y = @ t . DIFF_P t s y" 
   );;

let DIFF_EXISTS = TAC_PROOF
   (([], "!(s1:(*)set) s2 .? t:(*)set . DIFF_P t s1 s2"),
    REPEAT GEN_TAC
    THEN REWRITE_TAC [DIFF_P]
    THEN SPEC_TAC ("s1","s1")
    THEN SET_INDUCT_2_TAC
    THENL [ % 1 %
	EXISTS_TAC "EMPTY:(*)set"
	THEN REWRITE_TAC [IN]
    ;  % 2 %
	POP_ASSUM MP_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_CASES_TAC "x IN s2"
	THEN ASM_REWRITE_TAC []
        THENL [ % 2.1 %
	    EXISTS_TAC "t"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ; % 2.2 %
	    EXISTS_TAC "(INSERT x t)"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ]
	THEN ASM_CASES_TAC "x' = x"
	THEN ASM_REWRITE_TAC []
    ]
   );;

let DIFF_MEMBER_LEMMA = TAC_PROOF
   (([],
    "! (s1:(*)set) s2. DIFF_P (s1 DIFF s2) s1 s2"),
    REWRITE_TAC [DIFF_DEF]
    THEN REWRITE_TAC [SYM_RULE DIFF_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN ACCEPT_TAC DIFF_EXISTS
   );;

let DIFF_MEMBER = save_thm (`IN_DIFF`,
                 REWRITE_RULE [DIFF_P] DIFF_MEMBER_LEMMA);;

let DIFF_EMPTY_LEMMA = TAC_PROOF
   (([], "! s:(*)set . s DIFF EMPTY = s"),
    REWRITE_TAC [SET_EQ; DIFF_MEMBER;IN]
   );;

let DIFF_INSERT_LEMMA = TAC_PROOF
    (([],  "! (s:(*)set) t (x:*).
      s DIFF (INSERT x t) = (s DELETE x) DIFF t"),
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SET_EQ; DIFF_MEMBER;IN; DELETE_MEMBER]
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x' = x"
    THEN ASM_REWRITE_TAC []
   );;

let DIFF = save_thm (`DIFF`, 
         CONJ DIFF_EMPTY_LEMMA DIFF_INSERT_LEMMA);;


%----------------------------------------------------------------
  subsets
----------------------------------------------------------------%

let SUBSET_MEMBER = new_infix_definition
   (`SUBSET_MEMBER`,
    "! (s:(*)set) (t:(*)set) . $SUBSET s t = (! y. y IN s ==> y IN t)"
   );;

let SUBSET_EMPTY_LEMMA = TAC_PROOF
   (([], "! (s:(*)set). (EMPTY SUBSET s = T)"),
    REWRITE_TAC [SET_EQ; SUBSET_MEMBER;IN]
   );;

let SUBSET_INSERT_LEMMA = TAC_PROOF
   (([], "!(x:*) (s:(*)set) t .(((INSERT x s) SUBSET t) = 
                                x IN t /\ (SUBSET s t))"),
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SUBSET_MEMBER;IN]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [ % 1 %
        POP_ASSUM (\th. ACCEPT_TAC (REWRITE_RULE [] (SPEC "x" th)))
    ; % 2 %
	RES_TAC
    ;% 3 %
       ASM_REWRITE_TAC []
    ; % 4 %
	RES_TAC
    ]
   );;

let SUBSET = save_thm (`SUBSET`, 
         CONJ SUBSET_EMPTY_LEMMA SUBSET_INSERT_LEMMA);;

let SUBSET_UNION = prove_thm
   (`SUBSET_UNION`,
    "! (s:(*)set) t . s SUBSET (s UNION t) 
                          /\ 
                     (t SUBSET (s UNION t))",
    REPEAT GEN_TAC
    THEN CONJ_TAC
    THEN REWRITE_TAC [SUBSET_MEMBER; IN_UNION]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC []
   );;

let SUBSET_INTERSECT = prove_thm
   (`SUBSET_INTERSECT`,
    "! (s:(*)set) t . (s INTERSECT t) SUBSET s 
                          /\ 
                     ((s INTERSECT t) SUBSET t)",
    REPEAT GEN_TAC
    THEN CONJ_TAC
    THEN REWRITE_TAC [SUBSET_MEMBER; IN_INTERSECT]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC []
   );;

let SUBSET_DELETE = prove_thm
   (`SUBSET_DELETE`,
    "!(s:(*)set) x. ~(s = EMPTY) ==>
           (s DELETE x) SUBSET s ",
    REPEAT STRIP_TAC
    THEN REWRITE_TAC [SUBSET_MEMBER; DELETE_MEMBER]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC []
   );;

let SUBSET_UNION_ABSORPTION = prove_thm
   (`SUBSET_UNION_ABSORPTION`,
    "! (s:(*)set) t . s SUBSET t = (s UNION t = t)",
    REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [ % 1 %
	POP_ASSUM MP_TAC
	THEN SPEC_TAC ("s", "s")
	THEN SET_INDUCT_2_TAC
	THEN REWRITE_TAC [SUBSET; UNION]
	THEN ASM_CASES_TAC "x IN t"
	THEN ASM_REWRITE_TAC []
    ; % 2 %
	POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
	THEN ONCE_ASM_REWRITE_TAC []
	THEN REWRITE_TAC [SUBSET_UNION]
    ]
   );;

let SUBSET_INTERSECT_ABSORPTION = prove_thm
   (`SUBSET_INTERSECT_ABSORPTION`,
    "! (s:(*)set) t . s SUBSET t = (s INTERSECT t = s)",
    REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [ % 1 %
	POP_ASSUM MP_TAC
	THEN SPEC_TAC ("s", "s")
	THEN SET_INDUCT_2_TAC
	THEN REWRITE_TAC [SUBSET; INTERSECT]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC []
    ; % 2 %
	POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
	THEN ONCE_ASM_REWRITE_TAC []
	THEN REWRITE_TAC [SUBSET_INTERSECT]
    ]
   );;


let SUBSET_TRANS = prove_thm
   (`SUBSET_TRANS`,
    "! (s1:(*)set) s2 s3 . 
        (s1 SUBSET s2) /\ ( s2 SUBSET s3) ==> s1 SUBSET s3",
    REWRITE_TAC [SUBSET_UNION_ABSORPTION]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
    THEN ONCE_ASM_REWRITE_TAC []
    THEN POP_ASSUM (K ALL_TAC)
    THEN ASM_REWRITE_TAC [(SYM_RULE UNION_ASSOC)]
   );;


let SUBSET_ANTISYM = prove_thm
   (`SUBSET_ANTISYM`,
    "! (s:(*)set) t . 
        (s SUBSET t) /\ (t SUBSET s) ==> (s = t)",
    REWRITE_TAC [SUBSET_UNION_ABSORPTION]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
    THEN ONCE_ASM_REWRITE_TAC []
    THEN POP_TOP_ASSUMP_TAC
    THEN ASM_REWRITE_TAC [UNION_SYM]
   );;


let SUBSET_REFL = prove_thm
   (`SUBSET_REFL`,
    "! (s:(*)set) . s SUBSET s",
    REWRITE_TAC [SUBSET_UNION_ABSORPTION; UNION_IDENT]
);;

%----------------------------------------------------------------
 proper subset
----------------------------------------------------------------%
let PSUBSET = new_infix_definition
   (`PSUBSET`,
    "! (s:(*)set) t . PSUBSET s t = (s SUBSET t) /\ ~(s = t)"
   );;

let PSUBSET_TRANS = prove_thm
   (`PSUBSET_TRANS`,
    "! (s:(*)set) t . s PSUBSET t = 
         (! x .  x IN s ==> x IN t)
              /\
         (? y . y IN t /\ ~(y IN s))",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [PSUBSET; SUBSET_MEMBER]
    THEN REWRITE_TAC [SET_EQ]
    THEN CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV)
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC []
    THENL [ % 1 %
	EXISTS_TAC "x"
	THEN POP_ASSUM MP_TAC
	THEN POP_ASSUM (\th. ASSUME_TAC (SPEC "x" th))
	THEN POP_ASSUM MP_TAC
	THEN MAP_EVERY BOOL_CASES_TAC ["x IN s"; "x IN t"]
	THEN REWRITE_TAC []
    ; % 2 %
	EXISTS_TAC "y"
	THEN POP_ASSUM MP_TAC
	THEN POP_ASSUM MP_TAC
	THEN MAP_EVERY BOOL_CASES_TAC ["y IN s"; "y IN t"]
	THEN REWRITE_TAC []
    ]
   );;

let PSUBSET_REFL = prove_thm
   (`PSUBSET_REFL`,
    "! s:(*)set . ~(s PSUBSET s)",
    REWRITE_TAC [PSUBSET]
   );;

let PSUBSET_REST = prove_thm
   (`PSUBSET_REST`,
    "! s:(*)set . ~(s = EMPTY) ==> ((REST s) PSUBSET s)",
    REWRITE_TAC [REST; PSUBSET]
    THEN GEN_TAC
    THEN STRIP_TAC
    THEN ASSUME_TAC (SPECL ["s"; "(CHOICE s):*"] SUBSET_DELETE)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
    THEN REWRITE_TAC [SET_EQ; DELETE_MEMBER]
    THEN ASSUME_TAC (SPEC_ALL CHOICE_MEMBER)
    THEN RES_TAC
    THEN CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV)
    THEN EXISTS_TAC "(CHOICE s):*"
    THEN ASM_REWRITE_TAC []
   );;

%----------------------------------------------------------------
 set constructor
----------------------------------------------------------------%
 
let MK_SET_P = new_definition
   (`MK_SET_P`,
    "!(t:(*)set) s (f:*->bool). MK_SET_P t s f= 
               !x . x IN t = x IN s /\ f x"
   );;

let MK_SET_DEF = new_definition
   (`MK_SET_DEF`,
    "MK_SET (s:(*)set) y = @ t . MK_SET_P t s y" 
   );;

let MK_SET_EXISTS = TAC_PROOF
   (([], "!(s:(*)set) (f:*->bool).? t:(*)set . MK_SET_P t s f"),
    REPEAT GEN_TAC
    THEN REWRITE_TAC [MK_SET_P]
    THEN SPEC_TAC ("s","s")
    THEN SET_INDUCT_2_TAC
    THENL [ % 1 %
	EXISTS_TAC "EMPTY:(*)set"
	THEN REWRITE_TAC [IN]
    ;  % 2 %
	POP_ASSUM MP_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_CASES_TAC "(f:*->bool) x"
	THEN ASM_REWRITE_TAC []
        THENL [ % 2.1 %
	    EXISTS_TAC "(INSERT x t)"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ; % 2.2 %
	    EXISTS_TAC "t"
	    THEN GEN_TAC
	    THEN ASM_REWRITE_TAC [IN]
        ]
	THEN ASM_CASES_TAC "x' = x"
	THEN ASM_REWRITE_TAC []
    ]
   );;

let MK_SET_MEMBER_LEMMA = TAC_PROOF
   (([],
    "! (s:(*)set) (f:*->bool). MK_SET_P (MK_SET s f) s f"),
    REWRITE_TAC [MK_SET_DEF]
    THEN REWRITE_TAC [SYM_RULE MK_SET_P]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN ACCEPT_TAC MK_SET_EXISTS
   );;

let MK_SET_MEMBER = save_thm (`IN_MK_SET`,
                 REWRITE_RULE [MK_SET_P] MK_SET_MEMBER_LEMMA);;

let MK_SET_EMPTY_LEMMA = TAC_PROOF
   (([], "! f:*->bool . MK_SET (EMPTY:(*)set) f = EMPTY"),
    REWRITE_TAC [SET_EQ; MK_SET_MEMBER;IN]
   );;

let MK_SET_INSERT_LEMMA = TAC_PROOF
    (([],  "! (x:*) (s:(*)set) (f:*->bool).
                  MK_SET (INSERT x s) f = 
                     (f x => INSERT x (MK_SET s f) | MK_SET s f)"),
     REPEAT GEN_TAC
     THEN COND_CASES_TAC
     THEN REWRITE_TAC [SET_EQ; MK_SET_MEMBER;IN; DELETE_MEMBER]
     THEN GEN_TAC
     THEN ASM_CASES_TAC "x' = x"
     THEN ASM_REWRITE_TAC []
   );;

let MK_SET = save_thm (`MK_SET`, 
         CONJ MK_SET_EMPTY_LEMMA MK_SET_INSERT_LEMMA);;

let MK_SET_TRUE = prove_thm
   (`MK_SET_TRUE`,
    "! s:(*)set . MK_SET s (\x:*.T) = s",
    SET_INDUCT_TAC
    THEN REWRITE_TAC [MK_SET]
    THEN ASM_REWRITE_TAC []
   );;

let MK_SET_FALSE = prove_thm
   (`MK_SET_FALSE`,
    "! s:(*)set . MK_SET s (\x:*.F) = EMPTY",
    SET_INDUCT_TAC
    THEN REWRITE_TAC [MK_SET]
    THEN ASM_REWRITE_TAC []
   );;

let MK_SET_INTERSECT = prove_thm
   (`MK_SET_INTERSECT`,
    "! s t. s INTERSECT t = (MK_SET s (\x:*. x IN t))",
    SET_INDUCT_TAC
    THEN REWRITE_TAC [MK_SET; INTERSECT]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
    THEN POP_ASSUM (\th. ASSUME_TAC (SPEC_ALL th))
    THEN ASM_REWRITE_TAC []
   );;

let MK_SET_DELETE = prove_thm
   (`MK_SET_DELETE`,
    "! s y . s DELETE y = (MK_SET s (\x:*. ~(x = y)))",
    SET_INDUCT_TAC
    THEN REWRITE_TAC [MK_SET; DELETE]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
    THEN POP_ASSUM (\th. ASSUME_TAC (SPEC_ALL th))
    THEN ASM_CASES_TAC "x = y"
    THEN ASM_REWRITE_TAC []
   );;

let MK_SET_DIFF = prove_thm
   (`MK_SET_DIFF`,
    "! t s . s DIFF t = (MK_SET s (\x:*. ~(x IN t)))",
    SET_INDUCT_TAC
    THEN REWRITE_TAC [MK_SET; DIFF]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
    THENL [% 1 %
        REWRITE_TAC [IN; MK_SET_TRUE]
    ; % 2 %
	REWRITE_TAC [IN; MK_SET_DELETE]
	THEN REWRITE_TAC [DE_MORGAN_THM]
	THEN POP_ASSUM (\th. ASSUME_TAC 
		   (SPEC "(MK_SET s(\x'. ~(x' = x)))" th))
	THEN ASM_REWRITE_TAC []
	THEN REWRITE_TAC [SET_EQ; MK_SET_MEMBER]
	THEN GEN_TAC
	THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
	THEN REWRITE_TAC [(SYM_RULE CONJ_ASSOC)]
    ]
   );;

let MK_SET_OR = prove_thm
   (`MK_SET_OR`,
    "! s f g . MK_SET s (\x . (f x) \/ (g x)) = 
                   (MK_SET s f) UNION (MK_SET s g)",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SET_EQ; MK_SET_MEMBER; IN_UNION]
    THEN GEN_TAC
    THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC [CONJ_DISJ_DISTRIB]
   );;

let MK_SET_AND = prove_thm
   (`MK_SET_AND`,
    "! s f g . MK_SET s (\x . (f x) /\ (g x)) = 
                  (MK_SET s f) INTERSECT (MK_SET s g)",
    GEN_TAC
    THEN REWRITE_TAC [SET_EQ; MK_SET_MEMBER; IN_INTERSECT]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
    THEN BOOL_CASES_TAC " x IN s"
    THEN REWRITE_TAC [(SYM_RULE CONJ_ASSOC)]
   );;

%----------------------------------------------------------------
  singleton sets
----------------------------------------------------------------%
let SING = new_definition
   (`SING`,
    "! s:(*)set . SING(s) = ? x . s = (INSERT x EMPTY)"
   );;

let SING_CHOICE = prove_thm
   (`SING_CHOICE`,
    "! (x:*) . (CHOICE (INSERT x EMPTY)) = x",
    GEN_TAC
    THEN REWRITE_TAC [CHOICE; IN]
    THEN CONV_TAC (TOP_DEPTH_CONV SELECT_CONV)
    THEN EXISTS_TAC "x"
    THEN REFL_TAC
   );;

% Proof of SING_REST rewritten for version 12		[TFM 91.01.23] 	%

let SING_REST = prove_thm
   (`SING_REST`,
    "! s:(*)set . SING s = ~(s = EMPTY) /\ (REST s = EMPTY)",
    PURE_ONCE_REWRITE_TAC [SING;REST] THEN
    GEN_TAC THEN EQ_TAC THENL
    [DISCH_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
     REWRITE_TAC [SING_CHOICE;DELETE] THEN
     DISCH_THEN (ASSUME_TAC o SYM) THEN
     IMP_RES_TAC SET_DISTINCT;
     STRIP_TAC THEN EXISTS_TAC "(CHOICE s):*" THEN
     IMP_RES_TAC CHOICE_MEMBER THEN
     IMP_RES_THEN (\th. SUBST_OCCS_TAC [[1],th]) DELETE_DECOMPOSITION THEN
     ASM_REWRITE_TAC []]);;

loadt `card`;; % This loads in a definition from Philippe Leveilley
                 and his proof from this definition of Phil Windley's
                 axiom CARD %



%----------------------------------------------------------------

 Obsolete comment:

 cardinality

 If you must use cardinality, realize that it uses new_axiom.
 I'm fairly certain that this leads to no inconsistancies, but
 I'm not guarenteeing anything.


 The axiom below is now replaced by the theorem with the same name
 proved in card.ml. This file was created by Philippe Leveilley.

let CARD = new_axiom
   (`CARD`,
    "(CARD (EMPTY:(*)set) = 0) /\
     ! (x:*) (s:(*)set) .
        CARD (INSERT x s) = (x IN s => (CARD s) | SUC (CARD s))"
   );;

----------------------------------------------------------------%

let CARD_EQ_0 = prove_thm
   (`CARD_EQ_0`,
    "! s:(*)set . (CARD s = 0) ==> (s = EMPTY)",
    SET_INDUCT_2_TAC
    THEN ASM_REWRITE_TAC [CARD; num_CONV "1"; ADD_CLAUSES; NOT_SUC]
   );;

let CARD_ABSORPTION = prove_thm
   (`CARD_ABSORPTION`,
    "! (s:(*)set) x. x IN s ==> (((CARD (INSERT x s)):num) = (CARD s))",
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASSUME_TAC (SPEC_ALL ABSORPTION)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
   );;


let CARD_INTERSECT = prove_thm
   (`CARD_INTERSECT`,
    "! (s:(*)set) t . 
             (CARD (s INTERSECT t)) <= (CARD s)
                 /\ 
             (CARD (s INTERSECT t)) <= (CARD t)",
    REPEAT GEN_TAC
    THEN CONJ_TAC
    THENL [ % 1 %
	SPEC_TAC ("s", "s")
	THEN SET_INDUCT_2_TAC
	THEN REWRITE_TAC [INTERSECT; CARD]
	THENL [ % 1.1 %
	    REWRITE_TAC [LESS_OR_EQ; 
		     (ONCE_REWRITE_RULE [DISJ_SYM] LESS_0_CASES)]
	; % 1.2 %
	    ASM_CASES_TAC "x IN t"
	    THEN ASM_REWRITE_TAC [CARD]
	    THENL [
		ASM_REWRITE_TAC [IN_INTERSECT;
			     num_CONV "1"; ADD_CLAUSES; LESS_OR_EQ; 
			     LESS_MONO_EQ;INV_SUC_EQ]
		THEN ASM_REWRITE_TAC [(SYM_RULE LESS_OR_EQ)]
	    ; 
		ASM_REWRITE_TAC [(SYM_RULE ADD1); N_LEQ_SUC_M]
	    ]
	]
    ; % 2 %
	SPEC_TAC ("t", "t")
	THEN ONCE_REWRITE_TAC [INTERSECT_SYM]
	THEN SET_INDUCT_2_TAC
	THEN REWRITE_TAC [INTERSECT; CARD]
	THENL [ % 2.1 %
	    REWRITE_TAC [LESS_OR_EQ; 
		     (ONCE_REWRITE_RULE [DISJ_SYM] LESS_0_CASES)]
	; % 2.2 %
	    ASM_CASES_TAC "x IN s"
	    THEN ASM_REWRITE_TAC [CARD]
	    THENL [
		ASM_REWRITE_TAC [IN_INTERSECT;
			     num_CONV "1"; ADD_CLAUSES; LESS_OR_EQ; 
			     LESS_MONO_EQ;INV_SUC_EQ]
		THEN ASM_REWRITE_TAC [(SYM_RULE LESS_OR_EQ)]
	    ; 
		ASM_REWRITE_TAC [(SYM_RULE ADD1); N_LEQ_SUC_M]
	    ]
	]
    ]
   );;


let CARD_UNION = prove_thm
   (`CARD_UNION`,
    "! (s:(*)set) t . 
         CARD (s UNION t) + CARD (s INTERSECT t) = CARD s + CARD t",
    SET_INDUCT_2_TAC
    THEN REWRITE_TAC [CARD; INTERSECT; UNION]
    THENL [ % 1 %
	GEN_TAC
	THEN SUBST1_TAC (SPECL ["(CARD (t:(*)set)):num"; "0"] ADD_SYM)
	THEN REFL_TAC
    ; % 2 %
	GEN_TAC
	THEN ASM_CASES_TAC "x IN t"
	THEN ASM_REWRITE_TAC [CARD; IN_INTERSECT; IN_UNION]
	THEN ASM_REWRITE_TAC [(SYM_RULE ADD1); ADD_CLAUSES; INV_SUC_EQ]
    ]
   );;


let CARD_SUBSET = prove_thm
   (`CARD_SUBSET`,
    "! (s:(*)set) t . s SUBSET t ==> CARD s <= CARD t",
    REPEAT GEN_TAC
    THEN REWRITE_TAC [SUBSET_INTERSECT_ABSORPTION]
    THEN STRIP_TAC
    THEN POP_ASSUM (\th. ASSUME_TAC (SYM_RULE th))
    THEN ONCE_ASM_REWRITE_TAC []
    THEN REWRITE_TAC [CARD_INTERSECT]
   );;


let PSUBSET_LEMMA_1 = TAC_PROOF
   (([],
    "! (s:(*)set) t . (? x . ~ x IN s /\ (INSERT x s) SUBSET t)
                ==> CARD s < CARD t"),
    REPEAT STRIP_TAC
    THEN ASSUME_TAC CARD_SUBSET
    THEN RES_TAC
    THEN POP_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC [CARD; (SYM_RULE ADD1); OR_LESS]
   );;
 

let PSUBSET_LEMMA_2 = TAC_PROOF
   (([],
    "! (s:(*)set) t . s PSUBSET t ==>  
               (? x . ~ x IN s /\ (INSERT x s) SUBSET t)"),
    REPEAT GEN_TAC
    THEN REWRITE_TAC [PSUBSET]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC [SUBSET]
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC [SET_EQ]
    THEN CONV_TAC (TOP_DEPTH_CONV NOT_FORALL_CONV)
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC "x"
    THEN SWAP_TOP_ASSUMP_TAC
    THEN POP_ASSUM (\th. ASSUME_TAC 
	      (SPEC "x" (REWRITE_RULE [SUBSET_MEMBER] th)))
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN BOOL_CASES_TAC "x IN t"
    THEN REWRITE_TAC []
   );;

% Proof revised for version 1.12 		[TFM 91.01.23]		%

let CARD_PSUBSET = prove_thm
   (`CARD_PSUBSET`,
    "! (s:(*)set) t . s PSUBSET t ==> CARD s < CARD t",
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC PSUBSET_LEMMA_2 THEN
    IMP_RES_TAC PSUBSET_LEMMA_1);;

let SING_CARD = prove_thm
   (`SING_CARD`,
    "! s:(*)set . SING(s) = (CARD(s) = 1)",
    GEN_TAC
    THEN REWRITE_TAC [SING]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [% 1 %
        ASM_REWRITE_TAC [CARD; IN; num_CONV "1"; ADD_CLAUSES]
    ; % 2 %
	POP_ASSUM MP_TAC
	THEN SPEC_TAC ("s","s")
	THEN SET_INDUCT_2_TAC
	THEN ASM_REWRITE_TAC [CARD; num_CONV "1"; 
			      ADD_CLAUSES; INV_SUC_EQ;
			      (SYM_RULE NOT_SUC);
			      ]            
	THEN STRIP_TAC
	THEN EXISTS_TAC "x"
	THEN ASSUME_TAC CARD_EQ_0
	THEN RES_TAC
	THEN ASM_REWRITE_TAC []
    ]
   );;



quit();; % Needed for Common Lisp %
