% --------------------------------------------------------------------- %
% FILE		: mk_int_sbgp.ml					%
% DESCRIPTION   : This file contains some of the initial theory of      %
%                 modular arithmetic.                                   %
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.4.22						%
%									%
%-----------------------------------------------------------------------%

new_theory `int_mod`;;

load_library `integer`;;
new_parent `int_sbgp`;;
include_theory `int_sbgp`;;


let INT_MOD_DEF = new_definition(`INT_MOD_DEF`,
"int_mod n = quot_set((\N.T),plus)(int_mult_set n)");;

%INT_MOD_DEF = |- !n. int_mod n = quot_set((\N. T),$plus)(int_mult_set n) %


let MOD_DEF = new_definition(`MOD_DEF`,
"mod n m = LEFT_COSET((\N.T),$plus)(int_mult_set n)m");;

%MOD_DEF = |- !n m. mod n m = LEFT_COSET((\N. T),$plus)(int_mult_set n)m %


let PLUS_MOD_DEF = new_definition(`PLUS_MOD_DEF`,
"plus_mod n = quot_prod((\N.T),plus)(int_mult_set n)");;

%PLUS_MOD_DEF = 
 |- !n. plus_mod n = quot_prod((\N. T),$plus)(int_mult_set n) %


let INT_MOD_MOD_LEMMA = prove_thm(`INT_MOD_MOD_LEMMA`,
"(!m.int_mod n (mod n m)) /\ (int_mod n q ==> ?m.(q = mod n m))",
((REWRITE_TAC
  [INT_MOD_DEF;MOD_DEF;QUOTIENT_SET_DEF;INT_MULT_SET_NORMAL]) THEN
 GEN_TAC THEN (EXISTS_TAC "m:integer") THEN REFL_TAC));;

%INT_MOD_MOD_LEMMA = 
 |- (!m. int_mod n(mod n m)) /\ (int_mod n q ==> (?m. q = mod n m)) %


let int_mod_as_GROUP = prove_thm(`int_mod_as_GROUP`,
"GROUP(int_mod n,plus_mod n)",
((PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]) THEN
 (MATCH_MP_IMP_TAC QUOTIENT_GROUP) THEN
 (ACCEPT_TAC (SPEC_ALL INT_MULT_SET_NORMAL))));;

%int_mod_as_GROUP = |- GROUP(int_mod n,plus_mod n) %


let MOD_NAT_HOM_LEMMA = prove_thm(`MOD_NAT_HOM_LEMMA`,
"NAT_HOM((\N.T),$plus)(int_mult_set n) = mod n",
((EXT_TAC "m:integer") THEN
 (REWRITE_TAC
   [NAT_HOM_DEF;MOD_DEF;integer_as_GROUP;INT_MULT_SET_NORMAL;ETA_AX])));;

%MOD_NAT_HOM_LEMMA = |- NAT_HOM((\N. T),$plus)(int_mult_set n) = mod n %


let PLUS_MOD_LEMMA = prove_thm(`PLUS_MOD_LEMMA`,
 "!x y. plus_mod n(mod n x)(mod n y) = mod n(x plus y)",
((ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]) THEN
 (ASSUM_LIST \thl. (ASSUME_TAC (CONJUNCT1 (REWRITE_RULE thl
  (STRONG_INST_TY_TERM
   (match "NORMAL(G:* -> bool,prod)N" (concl (SPEC_ALL INT_MULT_SET_NORMAL)))
   NAT_HOM_THM))))) THEN
 (POP_ASSUM \thm. (ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE
      [(SYM (SPEC_ALL INT_MOD_DEF));(SYM (SPEC_ALL PLUS_MOD_DEF))] thm))) THEN
 (POP_ASSUM \thm. (ASSUM_LIST \thl.
   (ASSUME_TAC (REWRITE_RULE (GP_HOM_DEF.thl) thm)))) THEN
 (ASM_REWRITE_TAC[(SYM MOD_NAT_HOM_LEMMA)])));;

%PLUS_MOD_LEMMA = |- !x y. plus_mod n(mod n x)(mod n y) = mod n(x plus y) %


let ID_EQ_MOD_0 = prove_thm(`ID_EQ_MOD_0`,
"ID(int_mod n,plus_mod n) = mod n (INT 0)",
((ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]) THEN
 (ASSUM_LIST \thl. (ASSUME_TAC (CONJUNCT1 (REWRITE_RULE thl
  (STRONG_INST_TY_TERM
   (match "NORMAL(G:* -> bool,prod)N" (concl (SPEC_ALL INT_MULT_SET_NORMAL)))
   NAT_HOM_THM))))) THEN
 (POP_ASSUM \thm. (ASSUME_TAC
    (PURE_ONCE_REWRITE_RULE
      [(SYM (SPEC_ALL INT_MOD_DEF));(SYM (SPEC_ALL PLUS_MOD_DEF))] thm))) THEN
 (IMP_RES_TAC (DISCH_ALL (SYM (CONJUNCT1 (UNDISCH HOM_ID_INV_LEMMA))))) THEN
 (ASM_REWRITE_TAC [MOD_NAT_HOM_LEMMA;ID_EQ_0])));;

%ID_EQ_MOD_0 = |- ID(int_mod n,plus_mod n) = mod n(INT 0) %


let INV_EQ_MOD_NEG = prove_thm(`INV_EQ_MOD_NEG`,
"!m.(INV(int_mod n,plus_mod n)(mod n m) = mod n (neg m))",
((ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]) THEN
 (ASSUM_LIST \thl. (ASSUME_TAC (CONJUNCT1 (REWRITE_RULE thl
  (STRONG_INST_TY_TERM
   (match "NORMAL(G:* -> bool,prod)N" (concl (SPEC_ALL INT_MULT_SET_NORMAL)))
   NAT_HOM_THM))))) THEN
 (POP_ASSUM \thm. (ASSUME_TAC
   (PURE_ONCE_REWRITE_RULE
     [(SYM (SPEC_ALL INT_MOD_DEF));(SYM (SPEC_ALL PLUS_MOD_DEF))] thm))) THEN
 (IMP_RES_TAC (DISCH_ALL (CONJUNCT2 (UNDISCH HOM_ID_INV_LEMMA)))) THEN
 (POP_ASSUM \thm. (ASSUME_TAC (NORMALIZE [] thm))) THEN
 (ASM_REWRITE_TAC [(SYM MOD_NAT_HOM_LEMMA);neg_DEF])));;

%INV_EQ_MOD_NEG = 
 |- !m. INV(int_mod n,plus_mod n)(mod n m) = mod n(neg m) %


let MINUS_MOD_DEF = new_definition(`MINUS_MOD_DEF`,
"minus_mod n m p = plus_mod n m (INV(int_mod n,plus_mod n)p)");;

%MINUS_MOD_DEF = 
 |- !n m p. minus_mod n m p = plus_mod n m(INV(int_mod n,plus_mod n)p) %


let MINUS_MOD_LEMMA = prove_thm(`MINUS_MOD_LEMMA`,
"!m p. minus_mod n (mod n m) (mod n p) = mod n (m minus p)",
(REWRITE_TAC [MINUS_MOD_DEF;INV_EQ_MOD_NEG;MINUS_DEF;PLUS_MOD_LEMMA]));;

%MINUS_MOD_LEMMA = 
 |- !m p. minus_mod n(mod n m)(mod n p) = mod n(m minus p) %


let thm_list = return_GROUP_theory `INT_MOD` int_mod_as_GROUP
 [ID_EQ_MOD_0;(SYM (SPEC_ALL MINUS_MOD_DEF))];;

let thl1 = map (\ (name,thm).(name,
(IMP_CANON thm) and_then
 (map (\thm1.
  (STRONG_INST
   [("mod n m1","x:integer -> bool");
    ("mod n m2","y:integer -> bool");
    ("mod n m3","z:integer -> bool")] thm1) and_then
  (REWRITE_RULE[(CONJUNCT1 INT_MOD_MOD_LEMMA);INV_EQ_MOD_NEG]))))) thm_list;;

let thl2 = map (\ (name,thl).(name,
 (LIST_CONJ thl) and_then (REWRITE_RULE []))) thl1;;

let thl3 = map (\ (name,thm).(name,
 GENL (filter (\x.not(x = "n:integer")) (frees (concl thm))) thm))
 thl2;;

let thl4 = filter (\ (name,thm).not((concl thm) = "T")) thl3;;

map (\ (name,thm).
  (save_thm (name,thm));
  (autoload_theory (`theorem`,`int_mod`, name))) thl4;;

%
  INT_MOD_CLOSURE  |- !m1 m2. int_mod n(plus_mod n(mod n m1)(mod n m2))
  INT_MOD_GROUP_ASSOC
    |- !m1 m2 m3.
        plus_mod n(plus_mod n(mod n m1)(mod n m2))(mod n m3) =
        plus_mod n(mod n m1)(plus_mod n(mod n m2)(mod n m3))
  INT_MOD_ID_LEMMA
    |- !m1.
        (plus_mod n(mod n(INT 0))(mod n m1) = mod n m1) /\
        (plus_mod n(mod n m1)(mod n(INT 0)) = mod n m1) /\
        (?y. int_mod n y /\ (plus_mod n y(mod n m1) = mod n(INT 0)))
  INT_MOD_LEFT_RIGHT_INV
    |- !m2 m1.
        (plus_mod n(mod n m2)(mod n m1) = mod n(INT 0)) ==>
        (plus_mod n(mod n m1)(mod n m2) = mod n(INT 0))
  INT_MOD_INV_LEMMA
    |- !m1.
        (plus_mod n(mod n(neg m1))(mod n m1) = mod n(INT 0)) /\
        (minus_mod n(mod n m1)(mod n m1) = mod n(INT 0))
  INT_MOD_LEFT_CANCELLATION
    |- !m1 m2 m3.
        (plus_mod n(mod n m1)(mod n m2) =
         plus_mod n(mod n m1)(mod n m3)) ==>
        (mod n m2 = mod n m3)
  INT_MOD_RIGHT_CANCELLATION
    |- !m2 m1 m3.
        (plus_mod n(mod n m2)(mod n m1) =
         plus_mod n(mod n m3)(mod n m1)) ==>
        (mod n m2 = mod n m3)
  INT_MOD_RIGHT_ONE_ONE_ONTO
    |- !m1 m2.
        ?z.
         int_mod n z /\
         (plus_mod n(mod n m1)z = mod n m2) /\
         (!u.
           int_mod n u /\ (plus_mod n(mod n m1)u = mod n m2) ==> (u = z))
  INT_MOD_LEFT_ONE_ONE_ONTO
    |- !m1 m2.
        ?z.
         int_mod n z /\
         (plus_mod n z(mod n m1) = mod n m2) /\
         (!u.
           int_mod n u /\ (plus_mod n u(mod n m1) = mod n m2) ==>
           (u = z))
  INT_MOD_UNIQUE_ID
    |- !e m1.
        (int_mod n e ==>
         (plus_mod n e(mod n m1) = mod n m1) ==>
         (e = mod n(INT 0))) /\
        (int_mod n e ==>
         (plus_mod n(mod n m1)e = mod n m1) ==>
         (e = mod n(INT 0)))
  INT_MOD_UNIQUE_INV
    |- !u m1.
        int_mod n u ==>
        (plus_mod n u(mod n m1) = mod n(INT 0)) ==>
        (u = mod n(neg m1))
  INT_MOD_INV_INV_LEMMA  |- !m1. mod n(neg(neg m1)) = mod n m1
  INT_MOD_DIST_INV_LEMMA
    |- !m1 m2.
        minus_mod n(mod n(neg m1))(mod n m2) =
        INV(int_mod n,plus_mod n)(plus_mod n(mod n m2)(mod n m1))
%

close_theory ();;		% arg is void [TFM 90.06.12] %

quit();;
