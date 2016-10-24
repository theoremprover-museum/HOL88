% ===================================================================== %
% FILE		: mk_wordn_ints.ml					%
% DESCRIPTION   : Creates a theory of n-bit words as 2's complement     %
%                 integers.                                             %
% WRITES FILES	: wordn_ints.th						%
%									%
% AUTHOR	: (c) B. Graham						%
% DATE		: 13.07.92					        %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory                                                 %
% --------------------------------------------------------------------- %

new_theory `wordn_ints`;;

load_library `integer`;;

map new_parent 
[ `wordn_num`
; `more_integers`
];;

map (load_definition `wordn_num`)
[ `VAL`
; `BV`
];;

map (load_theorem `wordn_num`)
[ `VAL_ONE_ONE`
; `VAL_LESS`
; `VAL_ONTO_LEMMA`
];;

load_definition `more_integers` `below_eq`;;

map (load_theorem `more_integers`)
[ `LESS_PLUS_LEMMA`
; `NEQ_NON_NEG_NEG`
; `NEG_INT`
; `NOT_NEG_INT`
; `NEG_BELOW_POS_SUC`
; `NEG_SUC_BELOW_POS`
; `NEG_BELOW_EQ_POS`
; `NEG_BELOW_EQ`
; `NUM_SUB_IS_PLUS_NEG`
; `plus_LEFT_CANCELLATION`
; `plus_RIGHT_CANCELLATION`
; `BELOW_EQ_REFL`
];;

let ASM_CASES_THEN2 tac1 tac2 u =
    DISJ_CASES_THEN2 (tac1 o EQT_INTRO) (tac2 o EQF_INTRO)
                     (SPEC u EXCLUDED_MIDDLE);;
let ASM_CASES_THEN tac = ASM_CASES_THEN2 tac tac;;

let SYM_TAC =
 (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV))
 ? failwith `SYM_TAC`;;

let SYM_RULE =
 (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
 ? failwith `SYM_RULE`;;

let in_conv       =                  DEPTH_CONV o CHANGED_CONV
and re_conv       =                REDEPTH_CONV o CHANGED_CONV
and in1_conv      =             ONCE_DEPTH_CONV 
and in_conv_tac   = CONV_TAC  o      DEPTH_CONV o CHANGED_CONV
and re_conv_tac   = CONV_TAC  o    REDEPTH_CONV o CHANGED_CONV
and in1_conv_tac  = CONV_TAC  o ONCE_DEPTH_CONV 
and in_conv_rule  = CONV_RULE o      DEPTH_CONV o CHANGED_CONV
and re_conv_rule  = CONV_RULE o    REDEPTH_CONV o CHANGED_CONV
and in1_conv_rule = CONV_RULE o ONCE_DEPTH_CONV 
;;

let port  = PURE_ONCE_REWRITE_TAC
and prt   = PURE_REWRITE_TAC
and ort   = ONCE_REWRITE_TAC
and rt    = REWRITE_TAC
and poart = PURE_ONCE_ASM_REWRITE_TAC
and part  = PURE_ASM_REWRITE_TAC
and oart  = ONCE_ASM_REWRITE_TAC
and art   = ASM_REWRITE_TAC
;;

let rr    = REWRITE_RULE
and prr   = PURE_REWRITE_RULE
and orr   = ONCE_REWRITE_RULE
and porr  = PURE_ONCE_REWRITE_RULE
and poarr = PURE_ONCE_ASM_REWRITE_RULE
and parr  = PURE_ASM_REWRITE_RULE
and oarr  = ONCE_ASM_REWRITE_RULE
and arr   = ASM_REWRITE_RULE
;;

let port1 th = port[th]
and prt1 th = prt[th]
and porr1 th = porr[th]
and prr1 th = prr[th]
;;

letrec IMP_RES_n_THEN n (ttac:thm_tactic) thm =
  (n = 0) => ttac thm
           | (TRY o (IMP_RES_THEN (IMP_RES_n_THEN (n - 1) ttac))) thm;;

% --------------------------------------------------------------------- %
% The VAL function on boolean lists.                                    %
% --------------------------------------------------------------------- %
let iVal = new_definition
(`iVal`,
 "iVal (l:(bool)list) =
  (NULL l) => INT 0
            | neg(INT((BV (HD l)) * (2 EXP (LENGTH (TL l)))))
              plus (INT(VAL(TL l)))");;

% --------------------------------------------------------------------- %
% TWOS_COMPLEMENT                                                       %
% --------------------------------------------------------------------- %
%< functionally ...
let TWOS_COMP = new_definition
(`TWOS_COMP`,
 "TWOS_COMP =
  SND o (FOLDR (\x y. ((~x)/\ (HD y)), CONS (x=(HD y)) (TL y)) (F,[]))");;
>%

let TWOS_COMP = new_list_rec_definition
(`TWOS_COMP`,
 "(TWOS_COMP []          = (T,[])) /\
  (TWOS_COMP (CONS x xs) = let xp = TWOS_COMP xs in
                            (((~x)/\(FST xp)), CONS (x=(FST xp)) (SND xp)))");;

let TWOS_COMPLEMENT = new_definition
(`TWOS_COMPLEMENT`,
 "TWOS_COMPLEMENT l = SND(TWOS_COMP l)");;

% ===================================================================== %
% Theorems about integers                                               %
% ===================================================================== %

% ================================================================= %
let PLUS_BOTH_MONO = PROVE
("(a below_eq b) /\ (c below d) ==> (a plus c) below (b plus d)",
 port[below_eq]
 THEN STRIP_TAC
 THENL
 [ MATCH_MP_TAC TRANSIT
   THEN EXISTS_TAC "b plus c"
   THEN port[SYM_RULE PLUS_BELOW_TRANSL]
   THEN art[]
 ; ALL_TAC ]
 THEN port[COMM_PLUS]
 THEN art[SYM_RULE PLUS_BELOW_TRANSL]
 );;

% ================================================================= %
let BELOW_EQ_TRANS = PROVE
("!M N P. M below_eq N /\ N below_eq P ==> M below_eq P",
 port[below_eq]
 THEN REPEAT GEN_TAC
 THEN STRIP_TAC
 THEN art[]
 THEN DISJ1_TAC
 THENL 
 [ IMP_RES_TAC TRANSIT
 ; FIRST_ASSUM SUBST_ALL_TAC
   THEN FIRST_ASSUM MATCH_ACCEPT_TAC
 ]);;

% ================================================================= %
let PLUS_BELOW_EQ_TRANSL = PROVE
("!M N P. M below_eq N = (M plus P) below_eq (N plus P)",
 REPEAT GEN_TAC THEN port[below_eq]
 THEN port[SYM_RULE PLUS_BELOW_TRANSL; plus_RIGHT_CANCELLATION]
 THEN REFL_TAC);;

% ================================================================= %
let PLUS_MONO_EQ = PROVE
("(a below_eq b) /\ (c below_eq d) ==> (a plus c) below_eq (b plus d)",
 STRIP_TAC
 THEN MATCH_MP_TAC BELOW_EQ_TRANS
 THEN EXISTS_TAC "a plus d"
 THEN port [ SYM_RULE PLUS_BELOW_EQ_TRANSL
           ; porr[COMM_PLUS](SYM_RULE PLUS_BELOW_EQ_TRANSL) ]
 THEN art[]);;

% ================================================================= %
% not used????                                                      %
% ================================================================= %
let NEG_BELOW_LEMMA = PROVE
("!n m. (0 < n) \/ (0 < m) ==> neg(INT n) below (INT m)",
 REPEAT STRIP_TAC
 THENL
 [ IMP_RES_THEN (\th. CHOOSE_THEN SUBST1_TAC
		                  (rr[SYM_RULE th](SPEC "n:num" num_CASES)))
                LESS_NOT_EQ
   THEN rt[NEG_SUC_BELOW_POS]
 ; IMP_RES_THEN (\th. CHOOSE_THEN SUBST1_TAC
                                  (rr[SYM_RULE th](SPEC "m:num" num_CASES)))
                LESS_NOT_EQ
   THEN rt[NEG_BELOW_POS_SUC]
 ]);;

% ================================================================= %
% |- ?n. 2 EXP (LENGTH l) = SUC n                                   %
% ================================================================= %
let EXP_SUC = 
  rr[SYM_RULE(porr[SYM_RULE (num_CONV "2")]
                  (MATCH_MP LESS_NOT_EQ
			    (SPECL ["LENGTH (l:bool list)"; "1"]
				   ZERO_LESS_EXP)))]
    (SPEC "2 EXP (LENGTH (l:bool list))" num_CASES);;

% ================================================================= %
let SAME_LENGTH = PROVE
("(!l. (LENGTH (l:* list) = LENGTH ([]:* list)) = (l = [])) /\
  (!l a b. (LENGTH (l:* list) = LENGTH (CONS (a:*) b)) =
   ? (a':*) b'. (LENGTH b' = LENGTH b) /\ (l = CONS a' b'))",
 CONJ_TAC
 THENL
 [ REWRITE_TAC [LENGTH; LENGTH_NIL]
 ; PURE_ONCE_REWRITE_TAC [LENGTH]
   THEN MATCH_ACCEPT_TAC (SPECL ["l:* list"; "LENGTH (b:* list)"] LENGTH_CONS)
 ]);;

% ================================================================= %
% For use with list induction over two lists of the same length.    %
% Induct on one list only, and use the following two tactics when   %
% the goal is of the form :                                         %
%                                                                   %
%    (LENGTH l = LENGTH []) ==> ...                                 %
%    or                                                             %
%    (LENGTH l = LENGTH (CONS a b)) ==> ...                         %
%                                                                   %
% The antecedent may be in the SYM'ed form also.                    %
% ================================================================= %
let NULL_LENGTH_TAC =
  DISCH_THEN
  (\th. let a,b = (rand#rand) (dest_eq(concl th)) in
        (is_const a) => SUBST1_TAC (EQ_MP(ISPEC b(CONJUNCT1 SAME_LENGTH))(SYM th))
      | (is_const b) => SUBST1_TAC (EQ_MP(ISPEC a(CONJUNCT1 SAME_LENGTH))th)
      | failwith `NULL_LENGTH_TAC: goal antecedent of incorrect form`
  );;

let CONS_LENGTH_TAC =
  DISCH_THEN
  (\th. let a,b = (rand#rand) (dest_eq(concl th)) in
        (not((is_var a) or (is_var b)))
      => failwith `CONS_LENGTH_TAC: goal antecedent of incorrect form`
      | let s = (is_var a) in
        (SUBST_ALL_TAC (s=>th|SYM th)
         THEN REPEAT_TCL CHOOSE_THEN
         (\th1. ASSUME_TAC ((s=>I|SYM)(CONJUNCT1 th1))
	        THEN CONJUNCTS_THEN2 ((ANTE_RES_THEN ASSUME_TAC) o (s=>I|SYM))
			             (SUBST_ALL_TAC) th1)
	 (EQ_MP (ISPECL (s => a.(snd(strip_comb b)) | b.(snd(strip_comb a)))
			(CONJUNCT2 SAME_LENGTH))
                (s=>th|SYM th))));;


% --------------------------------------------------------------------- %
% Theorem: bounds on the range of an n-bit integer                      %
% --------------------------------------------------------------------- %
let iVal_BOUNDS = PROVE
    ("!(l:(bool)list) a. 
       (neg(INT(2 EXP (LENGTH l))) below_eq (iVal (CONS a l))) /\
       ((iVal (CONS a l))           below   (INT(2 EXP (LENGTH l))))",
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC
     THEN REPEAT GEN_TAC
     THENL
     [ REWRITE_TAC [iVal;HD;TL;NULL;LENGTH;EXP;num_CONV "1";VAL;PLUS_IDENTITY]
       THEN BOOL_CASES_TAC "a:bool"
       THEN rt[BV;MULT_CLAUSES;ADD_CLAUSES;below_eq]
       THENL 
       [ MATCH_ACCEPT_TAC NEG_BELOW_POS_SUC
       ; rt[neg_ZERO;NEG_BELOW_POS_SUC;NEG_SUC_BELOW_POS]
       ]
     ; REWRITE_TAC [iVal;HD;TL; NULL;LENGTH;EXP;VAL;TIMES2]
       THEN MAP_EVERY port1 [ LEFT_ADD_DISTRIB; SYM_RULE NUM_ADD_IS_INT_ADD
                             ; neg_PLUS_DISTRIB]
       THEN FREEZE_THEN port1 (SYM_RULE (SPEC "INT(VAL l)" COMM_PLUS))
       THEN port[ASSOC_PLUS]
       THEN FREEZE_THEN port1
       (SYM_RULE(GEN_ALL(SPECL ["M:integer";"N:integer";"INT(VAL l)"] ASSOC_PLUS)))
       THEN MAP_EVERY port1
            [ SYM_RULE (rr[NULL;HD;TL] (SPEC "CONS a (l:bool list)" iVal))
	    ; COMM_PLUS ; ASSOC_PLUS]
       THEN CONJ_TAC
       THENL
       [ 
         MATCH_MP_TAC PLUS_MONO_EQ
	 THEN art[]
	 THEN MAP_EVERY BOOL_CASES_TAC [ "a:bool"; "h:bool" ]
	 THEN REWRITE_TAC [ BV;MULT_CLAUSES;ADD_CLAUSES ]
	 THEN rt [ PLUS_INVERSE; PLUS_IDENTITY; neg_ZERO ]
	 THEN rt [ NEG_BELOW_EQ_POS;BELOW_EQ_REFL ]
       ; MATCH_MP_TAC PLUS_BOTH_MONO
	 THEN art[below_eq]
	 THEN MAP_EVERY BOOL_CASES_TAC ["a:bool"; "h:bool"]
	 THEN REWRITE_TAC [BV;MULT_CLAUSES;ADD_CLAUSES]
	 THEN rt[PLUS_INVERSE; PLUS_IDENTITY; neg_ZERO]
	 THEN CHOOSE_THEN SUBST1_TAC EXP_SUC
	 THEN rt[NEG_BELOW_POS_SUC]
	 THEN rt[SYM_RULE NUM_LESS_IS_INT_BELOW; LESS_0]
	 ]
       ]);;

% --------------------------------------------------------------------- %
% Theorem: iVal is one-to-one for equal-length lists.                   %
% --------------------------------------------------------------------- %
let iVal_ONE_ONE = PROVE
    ("!l1 l2. (LENGTH l1 = LENGTH l2) ==> (iVal l1 = iVal l2) ==> (l1 = l2)",
     INDUCT_THEN list_INDUCT ASSUME_TAC THENL
     [ GEN_TAC THEN NULL_LENGTH_TAC THEN REWRITE_TAC []
     ; REPEAT GEN_TAC THEN CONS_LENGTH_TAC
       THEN PURE_REWRITE_TAC [ iVal;CONS_11;NULL;COND_CLAUSES;HD;TL ]
       THEN MAP_EVERY BOOL_CASES_TAC [ "h:bool";"a':bool" ]
       THEN REWRITE_TAC [ BV;MULT_CLAUSES;ADD_CLAUSES;PLUS_IDENTITY;neg_ZERO ]
       THENL
       [ PURE_ONCE_ASM_REWRITE_TAC []
         THEN DISCH_THEN (MP_TAC o (MATCH_MP PLUS_LEFT_CANCELLATION))
	 THEN PURE_ONCE_REWRITE_TAC [ INT_ONE_ONE ]
	 THEN IMP_RES_THEN MATCH_ACCEPT_TAC VAL_ONE_ONE
       ; MATCH_MP_TAC (PURE_ONCE_REWRITE_RULE [ CONJ_SYM; EQ_SYM_EQ ]
	                                      NEQ_NON_NEG_NEG)
	 THEN REWRITE_TAC [ NOT_NEG_INT ]
	 THEN PURE_ONCE_REWRITE_TAC [ SYM_RULE COMM_PLUS ]
	 THEN MATCH_MP_TAC LESS_PLUS_LEMMA
	 THEN MATCH_ACCEPT_TAC VAL_LESS
       ; MATCH_MP_TAC NEQ_NON_NEG_NEG
	 THEN REWRITE_TAC [ NOT_NEG_INT ]
	 THEN PURE_ONCE_REWRITE_TAC [ SYM_RULE COMM_PLUS ]
	 THEN MATCH_MP_TAC LESS_PLUS_LEMMA
	 THEN MATCH_ACCEPT_TAC VAL_LESS
       ; PURE_ONCE_REWRITE_TAC [ INT_ONE_ONE ]
	 THEN IMP_RES_THEN MATCH_ACCEPT_TAC VAL_ONE_ONE
       ]
     ]);;
    
% --------------------------------------------------------------------- %
% Lemma: iVal l --> [0,...,2 ^ (LENGTH l) -1] is onto.                  %
% --------------------------------------------------------------------- %

let iVal_ONTO_LEMMA = PROVE
("!n m. (neg(INT(2 EXP m)) below_eq n) /\ (n below (INT(2 EXP m))) ==>
        ?l. (LENGTH l = SUC m) /\ (n = iVal l)",
 % th1 = |- ~(2 EXP m = 0) %
 let th1 = NOT_EQ_SYM(MATCH_MP LESS_NOT_EQ
		   (porr[SYM(num_CONV "2")]
		        (SPECL ["m:num";"1"] ZERO_LESS_EXP))) in
 INT_CASES_TAC THEN GEN_TAC THENL
 [ rt [ SYM_RULE NUM_LESS_IS_INT_BELOW;NEG_BELOW_EQ_POS ]
   THEN rt [ NEG_BELOW_EQ_POS ]
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_THEN
        (X_CHOOSE_THEN "l':bool list" (\th. EXISTS_TAC "CONS F l'"
		THEN rt [ LENGTH;iVal;NULL;HD;TL;INV_SUC_EQ;BV;MULT_CLAUSES;
    	    	    	neg_ZERO;PLUS_IDENTITY ;INT_ONE_ONE]
	        THEN MATCH_ACCEPT_TAC th))
	VAL_ONTO_LEMMA
 ; GEN_TAC
   THEN DISJ_CASES_THEN2 (STRIP_ASSUME_TAC o (MATCH_MP VAL_ONTO_LEMMA))
                         (SUBST1_TAC o (rr [ SUB_EQ_EQ_0;th1 ]))
			 (porr [ LESS_OR_EQ ]
 			       (SPECL ["2 EXP m"; "n2:num"] SUB_LESS_EQ))
   THENL
   [ port[NEG_BELOW_EQ]
     THEN REPEAT STRIP_TAC
     THEN EXISTS_TAC "CONS T l"
     THEN art [ LENGTH;iVal;NULL;HD;TL;INV_SUC_EQ;BV;MULT_CLAUSES;ADD_CLAUSES ]
     THEN port[SYM_RULE neg_ONE_ONE]
     THEN port[neg_PLUS_DISTRIB]
     THEN prt[PLUS_INV_INV_LEMMA]
     THEN SUBST1_TAC (MATCH_MP NUM_SUB_IS_PLUS_NEG
                               (MATCH_MP LESS_IMP_LESS_OR_EQ
                                         (rr [ASSUME "LENGTH (l:bool list) = m"]
   			 	             (SPEC "l:bool list" VAL_LESS))))
     THEN port [ INT_ONE_ONE ]
     THEN port[SYM(ASSUME "(2 EXP m) - n2 = VAL l")]
     THEN IMP_RES_THEN port1 SUB_SUB
     THEN port[GEN_ALL(GSYM(MATCH_MP ADD_EQ_SUB (SPECL ["2 EXP m'"; "n2:num"] LESS_EQ_ADD)))]
     THEN MATCH_ACCEPT_TAC ADD_SYM
   ; art[neg_ZERO]
   ]
 ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let TWOS_COMPLEMENT_LENGTH = PROVE
("!l. LENGTH(TWOS_COMPLEMENT l) = LENGTH l",
 LIST_INDUCT_TAC
 THEN rt[TWOS_COMPLEMENT;TWOS_COMP;LENGTH;SND]
 THEN in_conv_tac let_CONV
 THEN rt[SND;LENGTH]
 THEN port[SYM_RULE TWOS_COMPLEMENT]
 THEN art[]);;


% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let lemma0 = PROVE
("!n (l:bool list). (n * (2 EXP (LENGTH l)) = 0) = (n = 0)",
 REPEAT GEN_TAC
 THEN CHOOSE_THEN SUBST1_TAC EXP_SUC
 THEN port[MULT_CLAUSES]
 THEN port[ADD_EQ_0]
 THEN EQ_TAC
 THEN STRIP_TAC
 THEN art[MULT_0]
 THEN port[MULT_SYM]
 THEN rt[MULT_0]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let BV_0 = PROVE
("!x. (BV x = 0) = (x = F)",
 GEN_TAC
 THEN BOOL_CASES_TAC "x:bool"
 THEN rt[BV]
 THEN SYM_TAC
 THEN MATCH_MP_TAC LESS_NOT_EQ
 THEN MATCH_ACCEPT_TAC LESS_SUC_REFL);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let MOST_NEG_LEMMA = PROVE
("!ll l. (iVal(CONS l ll) = neg(INT(2 EXP(LENGTH ll)))) =
           (l /\ (VAL ll = 0))",
 REPEAT GEN_TAC
 THEN prt[iVal;HD;TL;NULL;COND_CLAUSES]
 THEN BOOL_CASES_TAC "l:bool" THEN rt[BV;MULT_CLAUSES;ADD_CLAUSES]
 THENL
 [ SUBST_OCCS_TAC
     [[2],SYM(CONJUNCT1(SPEC "neg(INT(2 EXP (LENGTH (ll:bool list))))"
			     PLUS_IDENTITY))]
   THEN port[plus_LEFT_CANCELLATION]
   THEN port[INT_ONE_ONE]
   THEN REFL_TAC
 ; prt [ neg_ZERO;PLUS_IDENTITY ]
   THEN SYM_TAC
   THEN CHOOSE_THEN SUBST1_TAC (SPEC "ll:bool list" (GEN_ALL EXP_SUC))
   THEN DISCH_THEN (MP_TAC o (AP_TERM "NEG"))
   THEN rt[NEG_INT;NOT_NEG_INT]
 ]);;
 
% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let TWOS_COMP_FLAG = PROVE
("!l. FST (TWOS_COMP l) = (VAL l = 0)",
 LIST_INDUCT_TAC THEN rt [ TWOS_COMP;VAL ]
 THEN GEN_TAC
 THEN in_conv_tac let_CONV
 THEN rt [ FST;VAL ]
 THEN poart []
 THEN prt [ ADD_EQ_0 ]
 THEN port [ CONJ_SYM ]
 THEN AP_TERM_TAC
 THEN rt [ lemma0;BV_0 ] );;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let TWOS_COMP_MOST_NEG_iVal = PROVE
("!ll l. (iVal(CONS l ll) = neg(INT(2 EXP(LENGTH ll)))) ==> 
          (iVal(TWOS_COMPLEMENT(CONS l ll)) = iVal(CONS l ll))",
 prt [ MOST_NEG_LEMMA;TWOS_COMPLEMENT ]
 THEN INDUCT_THEN list_INDUCT MP_TAC
 THENL
 [ REPEAT STRIP_TAC 
   THEN prt [ TWOS_COMP ]
   THEN in_conv_tac let_CONV
   THEN art []
 ; port [ TWOS_COMP ]
   THEN in1_conv_tac let_CONV
   THEN port [ TWOS_COMP_FLAG ]
   THEN port [ TWOS_COMP ]
   THEN in1_conv_tac let_CONV
   THEN port [ TWOS_COMP_FLAG; ]
   THEN rt [ SND;iVal;HD;TL;NULL;VAL;ADD_EQ_0;lemma0;BV_0 ]
   THEN DISCH_THEN (\th.REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL th))
   THEN art [ BV;MULT_CLAUSES;ADD_CLAUSES;PLUS_IDENTITY ]
   THEN prt [ SYM_RULE TWOS_COMPLEMENT;LENGTH;TWOS_COMPLEMENT_LENGTH ]
   THEN prt [ EXP;TIMES2;SYM_RULE NUM_ADD_IS_INT_ADD;neg_PLUS_DISTRIB ]
   THEN port [ SYM_RULE ASSOC_PLUS ]
   THEN DISCH_THEN SUBST1_TAC
   THEN REFL_TAC
 ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let TWOS_COMP_iVal = PROVE
("!ll l. ~(iVal(CONS l ll) = neg(INT(2 EXP(LENGTH ll)))) ==> 
          (iVal(TWOS_COMPLEMENT(CONS l ll)) = neg(iVal(CONS l ll)))",
 prt [ MOST_NEG_LEMMA;DE_MORGAN_THM;TWOS_COMPLEMENT ]
 THEN INDUCT_THEN list_INDUCT (\th. REPEAT GEN_TAC THEN MP_TAC (SPEC "h:bool" th))
 THENL
 [ GEN_TAC
   THEN port [ TWOS_COMP ]
   THEN in_conv_tac let_CONV
   THEN port [ TWOS_COMP_FLAG;TWOS_COMP ]
   THEN rt [ iVal;HD;TL;SND;NULL;VAL;PLUS_IDENTITY ]
   THEN DISCH_THEN port1
   THEN rt[BV;MULT_CLAUSES;neg_ZERO]
 ; MP_TAC (prr [ MOST_NEG_LEMMA;TWOS_COMPLEMENT ]
               (SPECL [ "ll:bool list";"h:bool" ] TWOS_COMP_MOST_NEG_iVal))
   THEN MAP_EVERY port1 [ VAL;ADD_SYM;ADD_EQ_0;DE_MORGAN_THM ]
   THEN rt [ lemma0;BV_0 ]
   THEN port [ TWOS_COMP ]
   THEN in1_conv_tac let_CONV
   THEN port [ TWOS_COMP_FLAG;TWOS_COMP ]
   THEN in1_conv_tac let_CONV
   THEN port [ TWOS_COMP_FLAG ]
   THEN port [ SYM_RULE TWOS_COMPLEMENT ]
   THEN prt [ iVal;NULL;HD;TL;SND;COND_CLAUSES;VAL;LENGTH ]
   THEN port [ TWOS_COMPLEMENT_LENGTH ]
   THEN rt [ EXP;TIMES2;SYM_RULE NUM_ADD_IS_INT_ADD;ADD_EQ_0;lemma0
           ; LEFT_ADD_DISTRIB;neg_PLUS_DISTRIB;NEG_NEG_IS_IDENTITY;BV_0 ]
   THEN MAP_EVERY ASM_CASES_TAC [ "h:bool";"l:bool";"VAL ll = 0" ]
   THEN art [ BV;MULT_CLAUSES;ADD_CLAUSES;neg_ZERO;PLUS_IDENTITY
            ; SYM_RULE NUM_ADD_IS_INT_ADD ]
   THENL
   [ SUBST_OCCS_TAC
     [[2],SYM(CONJUNCT1(SPEC "neg(INT(2 EXP (LENGTH (ll:bool list))))"
			     PLUS_IDENTITY))]
     THEN port [ plus_LEFT_CANCELLATION ]
     THEN DISCH_THEN SUBST1_TAC
     THEN prt [ SYM_RULE ASSOC_PLUS;plus_LEFT_CANCELLATION;PLUS_INVERSE ]
     THEN REFL_TAC
   ; DISCH_THEN SUBST1_TAC
   ; SUBST_OCCS_TAC
     [[2],SYM(CONJUNCT1(SPEC "neg(INT(2 EXP (LENGTH (ll:bool list))))"
			     PLUS_IDENTITY))]
     THEN port [ plus_LEFT_CANCELLATION ]
     THEN DISCH_THEN SUBST1_TAC
   ; DISCH_THEN SUBST1_TAC
   ; DISCH_THEN (SUBST1_TAC o SYM)
   ; DISCH_THEN (SUBST1_TAC o SYM)
   ] THEN
   prt [ ASSOC_PLUS;plus_RIGHT_CANCELLATION ]
   THEN prt [ SYM_RULE ASSOC_PLUS;PLUS_INVERSE;PLUS_IDENTITY ]
   THEN REFL_TAC
 ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let NULL_APPEND = PROVE
("!j k.NULL(APPEND (j:* list) k) = (NULL j) /\ (NULL k)",
 LIST_INDUCT_TAC THEN rt [ APPEND;NULL ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let APPEND_NULL = PROVE
("!l:* list. APPEND l [] = l",LIST_INDUCT_TAC THEN art[APPEND]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let NOT_SUC_0 = GEN_ALL(NOT_EQ_SYM(MATCH_MP LESS_NOT_EQ (SPEC_ALL LESS_0)));;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let MULT_EQ_0 = PROVE
("!n m. (n * m = 0) = (n = 0) \/ (m = 0)",
 INDUCT_TAC THEN INDUCT_TAC THEN rt[MULT_0;MULT_CLAUSES;ADD_CLAUSES]
 THEN rt [ NOT_SUC_0 ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let VAL_0_APPEND = PROVE
("!l h. (BV h = 0) /\ (VAL l = 0) ==> (CONS h l = APPEND l[h])",
 rt [ BV_0 ]
 THEN LIST_INDUCT_TAC
 THEN REPEAT GEN_TAC
 THEN rt[VAL;APPEND]
 THEN CHOOSE_THEN SUBST1_TAC EXP_SUC
 THEN rt[ ADD_EQ_0; MULT_EQ_0;NOT_SUC_0;BV_0 ]
 THEN STRIP_TAC THEN RES_TAC
 THEN art []);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let VAL_0_iVal_0 = PROVE
("!l. (VAL l = 0) = (iVal l = (INT 0))",
 LIST_INDUCT_TAC THEN rt [ VAL;iVal;NULL;HD;TL ]
 THEN prt [ ADD_EQ_0;lemma0 ]
 THEN GEN_TAC THEN EQ_TAC
 THENL
 [ DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)
   THEN rt [ MULT_CLAUSES;PLUS_IDENTITY;TIMES_ZERO;neg_ZERO ]
 ; STRIP_TAC THEN IMP_RES_THEN MP_TAC PLUS_UNIQUE_INV
   THEN rt [ neg_ONE_ONE;INT_ONE_ONE ]
   THEN rt[BV]
   THEN COND_CASES_TAC
   THEN rt [MULT_CLAUSES;ADD_CLAUSES]
   THENL
   [ rt [ NOT_EQ_SYM (MATCH_MP LESS_NOT_EQ (SPEC_ALL VAL_LESS)) ]
   ; DISCH_THEN SUBST1_TAC THEN REFL_TAC
   ]
 ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let LSHIFT_VAL = PROVE
("!l. VAL (APPEND l [F]) = 2 * (VAL l)",
 INDUCT_THEN list_INDUCT (\th. GEN_TAC THEN MP_TAC th)
 THENL
 [ rt [ VAL;BV;APPEND;MULT_CLAUSES;ADD_CLAUSES ]
 ; rt [ APPEND;VAL ]
   THEN DISCH_THEN SUBST1_TAC
   THEN prt[LENGTH_APPEND;LENGTH;ADD_CLAUSES]
   THEN port[LEFT_ADD_DISTRIB]
   THEN port[MULT_ASSOC]
   THEN FREEZE_THEN port1 (SPEC "2" MULT_SYM)
   THEN rt[EXP;MULT_ASSOC]
 ]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let LSHIFT_iVal = PROVE
("!l. iVal (APPEND l [F]) = (INT 2) times (iVal l)",
 GEN_TAC
 THEN DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC))
                       (ISPEC "l:bool list" list_CASES)
 THENL
 [ rt [ APPEND;iVal;VAL;NULL;HD;TL;BV;neg_ZERO;PLUS_IDENTITY;MULT_CLAUSES
      ; TIMES_ZERO ]
 ; rt [ APPEND;NULL_APPEND;NULL;iVal;HD;TL;LENGTH;EXP;LENGTH_APPEND;ADD_CLAUSES
      ; LSHIFT_VAL ]
   THEN prt [ MULT_ASSOC ]
   THEN FREEZE_THEN (\th. rt [ th ]) (SYM_RULE (SPEC "2" MULT_SYM))
   THEN prt [ SYM_RULE MULT_ASSOC ]
   THEN prt [ SYM_RULE NUM_MULT_IS_INT_MULT ]
   THEN port [ SYM_RULE(CONJUNCT1 TIMES_neg) ]
   THEN port [ SYM_RULE LEFT_PLUS_DISTRIB ]
   THEN port [ TIMES_neg ]
   THEN REFL_TAC
 ]);;
    
% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let LSHIFT_n_VAL = PROVE
("!l1. (VAL l1 = 0) ==> (!l2. VAL(APPEND l2 l1) = (2 EXP (LENGTH l1)) * (VAL l2))",
 LIST_INDUCT_TAC
 THEN rt[VAL;LENGTH;APPEND;APPEND_NULL;EXP;MULT_CLAUSES]
 THEN prt [ ADD_EQ_0;lemma0 ]
 THEN GEN_TAC THEN STRIP_TAC
 THEN IMP_RES_n_THEN 2 port1 VAL_0_APPEND 
 THEN port[ APPEND_ASSOC]
 THEN IMP_RES_THEN port1 BV_0
 THEN port [ LSHIFT_VAL]
 THEN RES_THEN port1
 THEN rt[MULT_ASSOC]);;

% --------------------------------------------------------------------- %
% --------------------------------------------------------------------- %
let LSHIFT_n_iVal = PROVE
("!l1. (VAL l1 = 0) ==>
       (!l2. iVal(APPEND l2 l1) = (INT(2 EXP (LENGTH l1))) times (iVal l2))",
 GEN_TAC THEN STRIP_TAC THEN GEN_TAC
 THEN DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC))
                       (ISPEC "l2:bool list" list_CASES)
 THENL
 [ rt [ APPEND; SPEC "[]:bool list" iVal; NULL;TIMES_ZERO]
   THEN IMP_RES_THEN ACCEPT_TAC VAL_0_iVal_0
 ; rt[APPEND;iVal;NULL;HD;TL]
   THEN IMP_RES_THEN port1 LSHIFT_n_VAL
   THEN port[LENGTH_APPEND]
   THEN port [ EXP_ADD ]
   THEN prt [ LEFT_PLUS_DISTRIB;NUM_MULT_IS_INT_MULT ]
   THEN port [ COMM_PLUS ]
   THEN AP_TERM_TAC
   THEN prt[TIMES_neg;neg_ONE_ONE;INT_ONE_ONE;NUM_MULT_IS_INT_MULT]
   THEN CONV_TAC (RAND_CONV(REWR_CONV MULT_SYM))
   THEN MATCH_ACCEPT_TAC MULT_ASSOC
 ]);;

%<
% ===================================================================== %
% Definition of the WORDN function.                                     %
% ===================================================================== %

fail();;

% --------------------------------------------------------------------- %
% Lemma: iVal l --> {m MOD (2 EXP n)} is onto, where n = LENGTH l       %
% --------------------------------------------------------------------- %

let iVal_MOD_ONTO_LEMMA =
    TAC_PROOF
    (([], "!n m. ?l. (LENGTH l = n) /\ (iVal l = m MOD (2 EXP n))"),
     let th1 = SUBS [SYM(num_CONV "2")] (SPECL ["n:num";"1"] ZERO_LESS_EXP) in
     let thm = CONJUNCT2(SPEC "m:num" (MP (SPEC "2 EXP n" DIVISION) th1)) in
     REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (MATCH_MP iVal_ONTO_LEMMA thm) THEN
     EXISTS_TAC "l:bool list" THEN ASM_REWRITE_TAC []);;

% --------------------------------------------------------------------- %
% Lemma: the required WORDN function exists.                            %
% --------------------------------------------------------------------- %

let WORDN_EXISTS =
    TAC_PROOF
    (([], "?f. !n m. (LENGTH (f n m) = n) /\ (iVal(f n m) = m MOD (2 EXP n))"),
     EXISTS_TAC "\n m. @l. (LENGTH l = n) /\ (iVal l = m MOD 2 EXP n)" THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT GEN_TAC THEN CONV_TAC SELECT_CONV THEN
     MATCH_ACCEPT_TAC iVal_MOD_ONTO_LEMMA);;
     
% --------------------------------------------------------------------- %
% Introduce WORDN by the constant specification:                        %
%                                                                       %
% |- !n m.(LENGTH(WORDN n m) = n) /\ (iVal(WORDN n m) = m MOD (2 EXP n)) %
% --------------------------------------------------------------------- %

let WORDN = new_specification `WORDN` [`constant`,`WORDN`] WORDN_EXISTS;;

% ===================================================================== %
% Theorems about WORDN and iVal.                                         %
% ===================================================================== %

let WORDN_iVal =
    prove_thm
    (`WORDN_iVal`,
     "!l:bool list. WORDN (LENGTH l) (iVal l) = l",
     let th = SPECL ["LENGTH (l:bool list)";"iVal l"] WORDN in
     GEN_TAC THEN STRIP_ASSUME_TAC th THEN
     IMP_RES_TAC iVal_ONE_ONE THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC LESS_MOD THEN
     MATCH_ACCEPT_TAC iVal_LESS);;

% WORDN_0_N = |- !m. WORDN 0 m = [] %
let WORDN_0_N = GEN_ALL (PURE_REWRITE_RULE[LENGTH_NIL]
    (CONJUNCT1 (SPECL ["0";"m:num"] WORDN)));;

let WORDN_N_0 = TAC_PROOF(([],
    "!n. WORDN (SUC n) 0 = (CONS F (WORDN n 0))"),
    let lem = PURE_REWRITE_RULE[iVal;BV;LENGTH;ADD_CLAUSES;EXP;
    	    COND_CLAUSES;MULT] (SPEC "[F]" WORDN_iVal) in
    let lem' = PURE_REWRITE_RULE[iVal;BV;LENGTH;ADD_CLAUSES;COND_CLAUSES;
    	    MULT;WORDN] (SPEC "CONS F (CONS F (WORDN n 0))" WORDN_iVal) in
    INDUCT_TAC THENL[
    	REWRITE_TAC[lem;WORDN_0_N];
    	POP_ASSUM SUBST1_TAC THEN SUBST1_TAC (SYM lem')
    	THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV
    	THEN MATCH_MP_TAC ZERO_MOD THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP]);;

let WORDN_0 = save_thm(`WORDN_0`,
    CONJ WORDN_0_N WORDN_N_0);;


let WORDN_MOD = prove_thm(`WORDN_MOD`,
    "!n m. (WORDN n m) = (WORDN n (m MOD (2 EXP n)))",
    REPEAT GEN_TAC THEN SUBST1_TAC (SYM(CONJUNCT2 (SPEC_ALL WORDN)))
    THEN SUBST_OCCS_TAC [[2],(SYM(CONJUNCT1 (SPEC_ALL WORDN)))]
    THEN CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC WORDN_iVal);;

>%

map save_thm
[ `iVal_BOUNDS`,		iVal_BOUNDS
; `iVal_ONE_ONE`,		iVal_ONE_ONE
; `iVal_ONTO_LEMMA`,		iVal_ONTO_LEMMA
; `MOST_NEG_LEMMA`,		MOST_NEG_LEMMA 
; `TWOS_COMP_MOST_NEG_iVal`,	TWOS_COMP_MOST_NEG_iVal
; `TWOS_COMP_iVal`,		TWOS_COMP_iVal
; `LSHIFT_VAL`,			LSHIFT_VAL
; `LSHIFT_iVal`,		LSHIFT_iVal
; `LSHIFT_n_VAL`,		LSHIFT_n_VAL
; `LSHIFT_n_iVal`,		LSHIFT_n_iVal
];;

