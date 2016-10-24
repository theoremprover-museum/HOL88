% ===================================================================== %
% FILE		: more_integers.ml					%
% DESCRIPTION   : Enriches the sets of theorems and constants to use    %
%                 with the integers library.                            %
% WRITES FILES	: more_integers.th					%
%									%
% AUTHOR	: (c) B. Graham						%
% DATE		: 30.07.92					        %
% ===================================================================== %

new_theory `more_integers`;;

load_library `integer`;;

% ===================================================================== %
% NEW CONSTANTS                                                         %
% ===================================================================== %

% --------------------------------------------------------------------- %
% An integer equivalent of <=                                           %
% --------------------------------------------------------------------- %
let below_eq = new_infix_definition
    (`below_eq`, "$below_eq n m = (n below m) \/ (n = m)");;

close_theory ();;

% ================================================================= %
% BINDER_EQ_TAC: tactic                                             %
% *************                                                     %
%                                                                   %
% Synopsis: strips matching binders from a top-level equality goal. %
%                                                                   %
% Description: The tactic effects the inverse of the forward        %
%    inference rules FORALL_EQ, EXISTS_EQ, and SELECT_EQ.           %
%                                                                   %
% {A} *t. t1[t] = *t'. t2[t']  (* in [!,?,@])                       %
% ===========================                                       %
%    {A} t1[t''] = t2[t'']                                          %
%                                                                   %
% (t'' not free in *t.t1 nor t2)                                    %
%                                                                   %
%   The quantified terms need not be identical, but                 %
%   instead only alpha convertable (the types must match).          %
%                                                                   %
% Failure: fails if binders differ, or bound variables have         %
%    different types.                                               %
%                                                                   %
% Written by: Brian Graham 05.12.90                                 %
% ================================================================= %

let BINDER_EQ_TAC:tactic(l,t) =
 (let t1,t2 = dest_eq t
  in
  let q1,n1,w1 = ((I#dest_abs) o dest_comb) t1
  and q2,n2,w2 = ((I#dest_abs) o dest_comb) t2
  in
  if (q1 = q2)
  then if (type_of n1 = type_of n2)
       then if (n1 = n2)
            then let p[th] =  MK_COMB(REFL(fst(dest_comb t1)), ABS n1 th)
                 in
		 ([l,mk_eq(w1,w2)], p)
            else let n = variant ((frees t1)@(frees w2)) n1
	         in
		 let p[th] =
		   let abs_th = (ABS n th)
		   in
		   let lhs,rhs = dest_eq(concl abs_th)
		   in
	           MK_COMB(REFL(fst(dest_comb t1)),
			   TRANS (SYM (GEN_ALPHA_CONV n1 lhs))
			         (TRANS abs_th
					(GEN_ALPHA_CONV n2 rhs)))
						 
	    in
            ([l,mk_eq(subst [n,n1]w1,(subst [n,n2] w2))], p)
       else failwith `BINDER_EQ_TAC: quantified variables have different types`
  else failwith `BINDER_EQ_TAC: different binders at top level`
  ) ? failwith `BINDER_EQ_TAC`;;

let SYM_TAC =
 (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV))
 ? failwith `SYM_TAC`;;

let SYM_RULE =
 (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
 ? failwith `SYM_RULE`;;

% ===================================================================== %
% THEOREMS ABOUT integers                                               %
% ===================================================================== %

% ===================================================================== %
% INT 0 is the identity for minus.                                      %
% ===================================================================== %
let MINUS_ID = prove
("!i. i minus (INT 0) = i",
 REWRITE_TAC[MINUS_DEF; neg_ZERO; PLUS_IDENTITY] );;

% ===================================================================== %
% The result of adding a larger magnitude negative integer to a smaller %
% magnitude positive integer is negative.                               %
% ===================================================================== %
let LESS_PLUS_LEMMA = prove
("(x < y) ==> (NEG ((INT x) plus (neg(INT y))))",
 PURE_ONCE_REWRITE_TAC[NUM_LESS_IS_INT_BELOW]
 THEN PURE_REWRITE_TAC[BELOW_DEF;MINUS_DEF]
 THEN STRIP_TAC
 THEN PURE_ONCE_REWRITE_TAC[NEG_DEF]
 THEN PURE_ONCE_REWRITE_TAC[SYM_RULE PLUS_DIST_INV_LEMMA]
 THEN PURE_ONCE_REWRITE_TAC[NEG_NEG_IS_IDENTITY]
 THEN FIRST_ASSUM ACCEPT_TAC);;

% ===================================================================== %
% LESS_MINUS_LEMMA = |- x < y ==> NEG((INT x) minus (INT y))            %
% ===================================================================== %
let LESS_MINUS_LEMMA =
    PURE_ONCE_REWRITE_RULE[SYM_RULE MINUS_DEF] LESS_PLUS_LEMMA;;

% ===================================================================== %
% An integer cannot be both positive and negative.                      %
% ===================================================================== %
let POS_NOT_NEG = prove
("POS i ==> ~(NEG i)",
 REPEAT STRIP_TAC THEN IMP_RES_TAC TRICHOTOMY);;

% ===================================================================== %
% NEG_NOT_POS =                                                         %
% |- NEG i ==> ~POS i                                                   %
% ===================================================================== %
let NEG_NOT_POS = REWRITE_RULE[](CONTRAPOS POS_NOT_NEG);;

% ===================================================================== %
% ~NEG is equivalent to POS or ZERO                                     %
% ===================================================================== %
let nonNEG_POS_OR_ZERO = prove
("!i. ~NEG i = POS i \/ (i = INT 0)",
 GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN IMP_RES_TAC TRICHOTOMY
 THEN MP_TAC (CONJUNCT1 (SPEC "i:integer" TRICHOTOMY))
 THEN ASM_REWRITE_TAC[]);;

% ===================================================================== %
% positive and negative integers are distinct.                          %
% ===================================================================== %
let NEQ_POS_NEG = prove
("POS i /\ NEG j ==> ~(i = j)",
 STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN IMP_RES_TAC NEG_NOT_POS);;

% ===================================================================== %
% non-negative and negative integers are distinct.                      %
% ===================================================================== %
let NEQ_NON_NEG_NEG = prove
("(~NEG i) /\ NEG j ==> ~(i = j)",
 STRIP_TAC
 THEN DISCH_THEN SUBST_ALL_TAC
 THEN RES_TAC);;

% ===================================================================== %
let NOT_NEG_INT = prove
("!n. ~NEG(INT n)",
 PURE_ONCE_REWRITE_TAC[NON_NEG_INT_IS_NUM]
 THEN GEN_TAC
 THEN EXISTS_TAC "n:num"
 THEN REFL_TAC
 );;

% ===================================================================== %
% |- !n.~POS(neg(INT n))                                                %
% ===================================================================== %
let NOT_POS_NEG_INT = PURE_ONCE_REWRITE_RULE[NEG_DEF] NOT_NEG_INT;;

% ===================================================================== %
let NOT_POSNEG_ZERO = prove
("~NEG(INT 0) /\ ~POS(INT 0)",
 PURE_ONCE_REWRITE_TAC[NOT_NEG_INT]
 THEN SUBST1_TAC (SYM neg_ZERO)
 THEN REWRITE_TAC[NOT_POS_NEG_INT]
 );;

% ===================================================================== %
let POS_INT = prove
("!n.POS(INT(SUC n))",
 PURE_ONCE_REWRITE_TAC[POS_DEF]
 THEN GEN_TAC
 THEN EXISTS_TAC "n:num"
 THEN REFL_TAC
 );;

% ===================================================================== %
let NEG_INT = prove
("!n.NEG(neg(INT(SUC n)))",
 PURE_ONCE_REWRITE_TAC[NEG_DEF]
 THEN PURE_ONCE_REWRITE_TAC[NEG_NEG_IS_IDENTITY]
 THEN ACCEPT_TAC POS_INT
 );;

% ===================================================================== %
let NEG_below_NONNEG = prove
("((neg(INT n)) below (INT m)) \/
    ((n = 0) /\ (m = 0))",
 PURE_ONCE_REWRITE_TAC[BELOW_DEF]
 THEN PURE_ONCE_REWRITE_TAC[MINUS_DEF]
 THEN PURE_ONCE_REWRITE_TAC[NEG_NEG_IS_IDENTITY]
 THEN PURE_ONCE_REWRITE_TAC[NUM_ADD_IS_INT_ADD]
 THEN DISJ_CASES_THEN2 (\th. ASSUME_TAC th
			     THEN IMP_RES_THEN
    	    	    	    	 (\t.PURE_ONCE_REWRITE_TAC[t]) ADD_EQ_0
			     THEN REWRITE_TAC[])
                       (\th. CHOOSE_THEN SUBST1_TAC th
			     THEN REWRITE_TAC[POS_INT])
      (SPEC "m+n" num_CASES)
 );;

% ===================================================================== %
let NEG_BELOW_POS_SUC = prove
( "!n m. (neg(INT n)) below (INT (SUC m))",
 PURE_ONCE_REWRITE_TAC[BELOW_DEF]
 THEN PURE_ONCE_REWRITE_TAC[MINUS_DEF]
 THEN PURE_ONCE_REWRITE_TAC[NEG_NEG_IS_IDENTITY]
 THEN PURE_ONCE_REWRITE_TAC[NUM_ADD_IS_INT_ADD]
 THEN PURE_ONCE_REWRITE_TAC[ADD_CLAUSES]
 THEN MATCH_ACCEPT_TAC POS_INT
 );;

% ===================================================================== %
let NEG_SUC_BELOW_POS = prove
( "!n m. (neg(INT (SUC n))) below (INT m)",
 PURE_ONCE_REWRITE_TAC[BELOW_DEF]
 THEN PURE_ONCE_REWRITE_TAC[MINUS_DEF]
 THEN PURE_ONCE_REWRITE_TAC[NEG_NEG_IS_IDENTITY]
 THEN PURE_ONCE_REWRITE_TAC[NUM_ADD_IS_INT_ADD]
 THEN PURE_ONCE_REWRITE_TAC[ADD_CLAUSES]
 THEN MATCH_ACCEPT_TAC POS_INT
 );;

% ===================================================================== %
let  NEG_BELOW_EQ_POS = prove
( "!n m. (neg(INT n)) below_eq (INT m)",
 PURE_ONCE_REWRITE_TAC[below_eq]
 THEN INDUCT_TAC
 THENL
 [ INDUCT_TAC
   THENL
   [ REWRITE_TAC[neg_ZERO]
   ; REWRITE_TAC[neg_ZERO; INT_ONE_ONE; SYM_RULE NUM_LESS_IS_INT_BELOW; LESS_0]
   ]
 ; REWRITE_TAC [NEG_SUC_BELOW_POS]
 ]);;

% ===================================================================== %
let NEG_BELOW = prove
( "!n m. (neg(INT n)) below (neg(INT m)) = (m < n)",
 PURE_ONCE_REWRITE_TAC[neg_REV_BELOW]
 THEN REWRITE_TAC[NUM_LESS_IS_INT_BELOW]
 );;

% ===================================================================== %
let NEG_BELOW_EQ = prove
("!n m. (neg(INT n)) below_eq (neg(INT m)) = m <= n",
 REPEAT GEN_TAC
 THEN PURE_REWRITE_TAC[below_eq;LESS_OR_EQ;neg_ONE_ONE;INT_ONE_ONE;NEG_BELOW]
 THEN CONV_TAC (RATOR_CONV(ONCE_DEPTH_CONV (SYM_CONV)))
 THEN REFL_TAC);;



% ===================================================================== %
% :num ARITHMETIC RESULTS                                               %
% ===================================================================== %

% ===================================================================== %
% NOT_ZERO_SUC = |- 0 < m ==> (?n. m = SUC n)                           %
% ===================================================================== %
let NOT_ZERO_SUC =
  DISCH_ALL (REWRITE_RULE[SYM_RULE(MATCH_MP (LESS_NOT_EQ) (ASSUME "0 < m"))]
               (SPEC_ALL num_CASES));;

% ===================================================================== %
let LESS_1_IS_0 = prove
("!n. (n < 1) = (n = 0)",
 PURE_ONCE_REWRITE_TAC[num_CONV"1"]
 THEN INDUCT_TAC
 THENL
 [ REWRITE_TAC[LESS_0]
 ; REWRITE_TAC[LESS_MONO_EQ; NOT_LESS_0]
   THEN SYM_TAC
   THEN MATCH_MP_TAC LESS_NOT_EQ
   THEN MATCH_ACCEPT_TAC LESS_0
 ]);;

% ===================================================================== %
% LESS_EQ_0_IS_0 = |- !n. n <= 0 = (n = 0)                              %
% ===================================================================== %
let LESS_EQ_0_IS_0 = 
  PURE_REWRITE_RULE[num_CONV "1"; LESS_EQ; LESS_EQ_MONO] LESS_1_IS_0;;


% ===================================================================== %
% MORE INTEGER THEOREMS                                                 %
% ===================================================================== %

% ===================================================================== %
% plus_RIGHT_CANCELLATION =                                             %
% |- !y x z. (y plus x = z plus x) = (y = z)                            %
% ===================================================================== %
let plus_RIGHT_CANCELLATION =
 GEN_ALL(IMP_ANTISYM_RULE (SPEC_ALL PLUS_RIGHT_CANCELLATION)
        (DISCH_ALL (AP_THM (AP_TERM "$plus" (ASSUME "(y:integer) = z"))
                           "x:integer")));;

% ===================================================================== %
% plus_LEFT_CANCELLATION =                                              %
% |- !y x z. (x plus y = x plus z) = (y = z)                            %
% ===================================================================== %
let plus_LEFT_CANCELLATION =
  PURE_ONCE_REWRITE_RULE[COMM_PLUS] plus_RIGHT_CANCELLATION;;

% ===================================================================== %
% BELOW_INT_SUC_REFL = |- !n. (INT n) below (INT(SUC n))                %
% ===================================================================== %
let BELOW_INT_SUC_REFL =
  PURE_ONCE_REWRITE_RULE[NUM_LESS_IS_INT_BELOW] LESS_SUC_REFL;;

% ===================================================================== %
% NEG_BELOW_INT_SUC_REFL = |- !n. (neg(INT(SUC n))) below (neg(INT n))  %
% ===================================================================== %
let NEG_BELOW_INT_SUC_REFL =
  PURE_ONCE_REWRITE_RULE[SYM_RULE NEG_BELOW] LESS_SUC_REFL;;

% ===================================================================== %
let PLUS_INCREASING = prove
("!i n. (i below (i plus (INT n))) \/ (i = (i plus (INT n)))",
 GEN_TAC
 THEN SUBST_OCCS_TAC [[1;3],SYM_RULE(SPEC "i:integer"
     (PURE_ONCE_REWRITE_RULE[COMM_PLUS]PLUS_ID))]
 THEN PURE_ONCE_REWRITE_TAC[SYM_RULE(PURE_ONCE_REWRITE_RULE
     [COMM_PLUS]PLUS_BELOW_TRANSL);plus_LEFT_CANCELLATION]
 THEN PURE_ONCE_REWRITE_TAC[INT_ONE_ONE; SYM_RULE NUM_LESS_IS_INT_BELOW]
 THEN INDUCT_TAC THEN REWRITE_TAC[LESS_0]
 );;

% ===================================================================== %
let MINUS_DECREASING = prove
("!i n. ((i minus (INT n)) below i) \/
          (i minus (INT n) = i)",
 GEN_TAC
 THEN PURE_ONCE_REWRITE_TAC[MINUS_DEF]
 THEN SUBST_OCCS_TAC [[2;4],SYM_RULE(SPEC "i:integer"
     (PURE_ONCE_REWRITE_RULE[COMM_PLUS]PLUS_ID))]
 THEN PURE_ONCE_REWRITE_TAC[SYM_RULE(PURE_ONCE_REWRITE_RULE
     [COMM_PLUS]PLUS_BELOW_TRANSL); plus_RIGHT_CANCELLATION]
 THEN INDUCT_TAC
 THENL
 [ REWRITE_TAC[neg_ZERO]
 ; DISJ1_TAC
   THEN PURE_ONCE_REWRITE_TAC[SYM_RULE neg_REV_BELOW]
   THEN PURE_ONCE_REWRITE_TAC[neg_ZERO;NEG_NEG_IS_IDENTITY]
   THEN PURE_ONCE_REWRITE_TAC[SYM_RULE NUM_LESS_IS_INT_BELOW]
   THEN MATCH_ACCEPT_TAC LESS_0
 ]);;

% ===================================================================== %
let INT_SUC_ADD1 = prove
("!n. INT(SUC n) = ((INT n) plus (INT 1))",
 PURE_ONCE_REWRITE_TAC[NUM_ADD_IS_INT_ADD]
 THEN REWRITE_TAC[ADD1]
 );;

% ===================================================================== %
let INT_SUC_MINUS_ADD1 = prove
("!n m. ((INT (SUC n)) minus m) = ((INT n) minus m) plus (INT 1)",
 PURE_ONCE_REWRITE_TAC[MINUS_DEF]
 THEN PURE_ONCE_REWRITE_TAC[SYM_RULE ASSOC_PLUS]
 THEN PURE_ONCE_REWRITE_TAC[COMM_PLUS]
 THEN PURE_ONCE_REWRITE_TAC[PURE_ONCE_REWRITE_RULE[COMM_PLUS]INT_SUC_ADD1]
 THEN REWRITE_TAC[ASSOC_PLUS]);;

% ===================================================================== %
let NUM_SUB_IS_INT_MINUS = prove
("!n m. (n <= m) ==> (((INT m) minus (INT n)) = (INT(m - n)))",
 GEN_TAC THEN INDUCT_TAC
 THENL
 [ PURE_ONCE_REWRITE_TAC[LESS_EQ_0_IS_0]
   THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUB_0; MINUS_ID]
 ; PURE_ONCE_REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
   THENL
   [ PURE_ONCE_REWRITE_TAC[INT_SUC_MINUS_ADD1]
     THEN IMP_RES_THEN (\th.(ANTE_RES_THEN SUBST1_TAC
    	 (REWRITE_RULE[LESS_EQ_MONO] th))) LESS_OR
     THEN PURE_ONCE_REWRITE_TAC[SYM_RULE INT_SUC_ADD1]
     THEN PURE_ONCE_REWRITE_TAC[INT_ONE_ONE]
     THEN PURE_ONCE_REWRITE_TAC[SUB]
     THEN IMP_RES_THEN (ASSUME_TAC o (REWRITE_RULE[LESS_EQ_MONO])) LESS_OR
     THEN IMP_RES_TAC NOT_LESS
     THEN ASM_REWRITE_TAC[]
   ; PURE_ONCE_ASM_REWRITE_TAC[]
     THEN PURE_REWRITE_TAC[MINUS_DEF; PLUS_INVERSE; SUB_MONO_EQ]
     THEN PURE_ONCE_REWRITE_TAC[REWRITE_RULE[LESS_EQ_REFL]
    	 (SPECL["m:num";"m:num"]SUB_EQ_0)]
     THEN REFL_TAC
   ]
 ]);;

% ===================================================================== %
% NUM_SUB_IS_PLUS_NEG =                                                 %
% |- !n m. n <= m ==> ((INT m) plus (neg(INT n)) = INT(m - n))          %
% ===================================================================== %
let NUM_SUB_IS_PLUS_NEG =
    PURE_ONCE_REWRITE_RULE [ MINUS_DEF ] NUM_SUB_IS_INT_MINUS;;

% ===================================================================== %
let BELOW_EQ_REFL = prove
("!N. N below_eq N", REWRITE_TAC [below_eq]);;


map save_thm
[ `MINUS_ID`			,MINUS_ID
; `LESS_PLUS_LEMMA`	,LESS_PLUS_LEMMA
; `LESS_MINUS_LEMMA`	,LESS_MINUS_LEMMA
; `NEQ_POS_NEG`			,NEQ_POS_NEG
; `NEQ_NON_NEG_NEG`		,NEQ_NON_NEG_NEG
; `NOT_NEG_INT`			,NOT_NEG_INT
; `NOT_POS_NEG_INT`		,NOT_POS_NEG_INT
; `NOT_POSNEG_ZERO`		,NOT_POSNEG_ZERO
; `POS_INT`			,POS_INT
; `NEG_INT`			,NEG_INT
; `NEG_BELOW_POS_SUC`		,NEG_BELOW_POS_SUC
; `NEG_SUC_BELOW_POS`		,NEG_SUC_BELOW_POS
; `NEG_BELOW_EQ_POS`		,NEG_BELOW_EQ_POS
; `NEG_BELOW`			,NEG_BELOW
; `NEG_BELOW_EQ`		,NEG_BELOW_EQ
; `plus_RIGHT_CANCELLATION`	,plus_RIGHT_CANCELLATION
; `plus_LEFT_CANCELLATION`	,plus_LEFT_CANCELLATION
; `BELOW_INT_SUC_REFL`		,BELOW_INT_SUC_REFL
; `NEG_BELOW_INT_SUC_REFL`	,NEG_BELOW_INT_SUC_REFL
; `PLUS_INCREASING`		,PLUS_INCREASING
; `MINUS_DECREASING`		,MINUS_DECREASING
; `NUM_SUB_IS_INT_MINUS`	,NUM_SUB_IS_INT_MINUS
; `NUM_SUB_IS_PLUS_NEG`		,NUM_SUB_IS_PLUS_NEG
; `BELOW_EQ_REFL`		,BELOW_EQ_REFL
];;


%< theorems not presently saved:

; `POS_NOT_NEG`	,POS_NOT_NEG
; `NEG_NOT_POS`	,NEG_NOT_POS
; `nonNEG_POS_OR_ZERO`	,nonNEG_POS_OR_ZERO
; `NEG_below_NONNEG`	,NEG_below_NONNEG
; `NOT_ZERO_SUC`	,NOT_ZERO_SUC
; `LESS_1_IS_0`	,LESS_1_IS_0
; `LESS_EQ_0_IS_0`	,LESS_EQ_0_IS_0
; `INT_SUC_ADD1`	,INT_SUC_ADD1
; `INT_SUC_MINUS_ADD1`	,INT_SUC_MINUS_ADD1
>%
