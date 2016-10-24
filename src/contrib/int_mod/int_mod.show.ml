% FILE		: int_mod.ml						%
% DESCRIPTION   : This file gives a history of the development of some  %
%                 of the initial theory of modular arithmetic.   It can %
%                 be loaded by loadt and it will also create int_mod.th,%
%                 but in a most verbose manner.				%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.4.11						%
%									%
%-----------------------------------------------------------------------%
new_theory `int_mod`;;

load_library `group`;;
load_library `integer`;;

new_parent `int_sbgp`;;
include_theory `int_sbgp`;;


let INT_MOD_DEF = new_definition(`INT_MOD_DEF`,
"int_mod n = quot_set((\N.T),plus)(int_mult_set n)");;

let PLUS_MOD_DEF = new_definition(`PLUS_MOD_DEF`,
"plus_mod n = quot_prod((\N.T),plus)(int_mult_set n)");;

let MOD_DEF = new_definition(`MOD_DEF`,
"mod n m = LEFT_COSET((\N.T),$plus)(int_mult_set n)m");;


set_goal([],"(!m.int_mod n (mod n m)) /\
             (int_mod n q ==> ?m.(q = mod n m))");;

expand (REWRITE_TAC
  [INT_MOD_DEF;MOD_DEF;QUOTIENT_SET_DEF;INT_MULT_SET_NORMAL]);;

expand (GEN_TAC THEN (EXISTS_TAC "m:integer") THEN REFL_TAC);;


let INT_MOD_MOD_LEMMA = prove_thm(`INT_MOD_MOD_LEMMA`,
"(!m.int_mod n (mod n m)) /\ (int_mod n q ==> ?m.(q = mod n m))",
((REWRITE_TAC
  [INT_MOD_DEF;MOD_DEF;QUOTIENT_SET_DEF;INT_MULT_SET_NORMAL]) THEN
 GEN_TAC THEN (EXISTS_TAC "m:integer") THEN REFL_TAC));;

set_goal([],"!x y. plus_mod n(mod n x)(mod n y) = mod n(x plus y)");;

expand (REWRITE_TAC [PLUS_MOD_DEF;MOD_DEF]);;

expand (MATCH_MP_IMP_TAC (UNDISCH QUOT_PROD));;

% goal 1 %
expand (REWRITE_TAC []);;

% goal 2 %
expand (ACCEPT_TAC (SPEC_ALL INT_MULT_SET_NORMAL));;

let PLUS_MOD_LEMMA = prove_thm(`PLUS_MOD_LEMMA`,
 "!x y. plus_mod n(mod n x)(mod n y) = mod n(x plus y)",
((REWRITE_TAC [PLUS_MOD_DEF;MOD_DEF]) THEN
 (MATCH_MP_IMP_TAC (UNDISCH QUOT_PROD)) THENL
 [(REWRITE_TAC []);
  (ACCEPT_TAC (SPEC_ALL INT_MULT_SET_NORMAL))]));;


set_goal([],"GROUP(int_mod n,plus_mod n)");;

expand (PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]);;

expand (MATCH_MP_IMP_TAC QUOTIENT_GROUP);;

expand (ACCEPT_TAC (SPEC_ALL INT_MULT_SET_NORMAL));;

let int_mod_as_GROUP = prove_thm(`int_mod_as_GROUP`,
"GROUP(int_mod n,plus_mod n)",
((PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]) THEN
 (MATCH_MP_IMP_TAC QUOTIENT_GROUP) THEN
 (ACCEPT_TAC (SPEC_ALL INT_MULT_SET_NORMAL))));;


set_goal([],"mod n = NAT_HOM((\N.T),$plus)(int_mult_set n)");;

expand (EXT_TAC "m:integer");;

expand (REWRITE_TAC [NAT_HOM_DEF;MOD_DEF]);;

expand (REWRITE_TAC [integer_as_GROUP;INT_MULT_SET_NORMAL;ETA_AX]);;


let MOD_NAT_HOM_LEMMA = prove_thm(`MOD_NAT_HOM_LEMMA`,
"mod n = NAT_HOM((\N.T),$plus)(int_mult_set n)",
((EXT_TAC "m:integer") THEN
 (REWRITE_TAC [NAT_HOM_DEF;MOD_DEF]) THEN
 (REWRITE_TAC [integer_as_GROUP;INT_MULT_SET_NORMAL;ETA_AX])));;


set_goal([],"ID(int_mod n,plus_mod n) = mod n (INT 0)");;

expand (ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]);;

expand (REWRITE_TAC [MOD_NAT_HOM_LEMMA]);;

expand ((PURE_ONCE_REWRITE_TAC[(SYM ID_EQ_0)]) THEN
        (NEW_MATCH_ACCEPT_TAC
         (SYM (CONJUNCT1 (UNDISCH HOM_ID_INV_LEMMA)))));;

expand (PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]);;

expand (NEW_MATCH_ACCEPT_TAC (CONJUNCT1 (UNDISCH NAT_HOM_THM)));;

expand (ASM_REWRITE_TAC []);;

let ID_EQ_MOD_0 = prove_thm(`ID_EQ_MOD_0`,
"ID(int_mod n,plus_mod n) = mod n (INT 0)",
((ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]) THEN
 (REWRITE_TAC [MOD_NAT_HOM_LEMMA]) THEN
 (PURE_ONCE_REWRITE_TAC[(SYM ID_EQ_0)]) THEN
 (NEW_MATCH_ACCEPT_TAC
  (SYM (CONJUNCT1 (UNDISCH HOM_ID_INV_LEMMA)))) THEN
 (PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]) THEN
 (NEW_MATCH_ACCEPT_TAC (CONJUNCT1 (UNDISCH NAT_HOM_THM))) THEN
 (ASM_REWRITE_TAC [])));;


set_goal([],"!m.(INV(int_mod n,plus_mod n)(mod n m) = mod n (neg m))");;

expand (ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]);;

expand (REWRITE_TAC [MOD_NAT_HOM_LEMMA]);;

expand ((PURE_ONCE_REWRITE_TAC[neg_DEF]) THEN
        (NEW_MATCH_ACCEPT_TAC (SYM (UNDISCH (SPEC_ALL
           (CONJUNCT2 (UNDISCH HOM_ID_INV_LEMMA)))))));;

% goal 1 %

expand (PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]);;

expand (NEW_MATCH_ACCEPT_TAC (CONJUNCT1 (UNDISCH NAT_HOM_THM)));;

expand (ASM_REWRITE_TAC []);;

% goal 2 %

expand (REWRITE_TAC []);;

let INV_EQ_MOD_NEG = prove_thm(`INV_EQ_MOD_NEG`,
"!m.(INV(int_mod n,plus_mod n)(mod n m) = mod n (neg m))",
((ASSUME_LIST_TAC
  [integer_as_GROUP;int_mod_as_GROUP;(SPEC_ALL INT_MULT_SET_NORMAL)]) THEN
 (REWRITE_TAC [MOD_NAT_HOM_LEMMA]) THEN
 (PURE_ONCE_REWRITE_TAC[neg_DEF]) THEN
 (NEW_MATCH_ACCEPT_TAC (SYM (UNDISCH (SPEC_ALL
    (CONJUNCT2 (UNDISCH HOM_ID_INV_LEMMA)))))) THENL
 [((PURE_ONCE_REWRITE_TAC[INT_MOD_DEF;PLUS_MOD_DEF]) THEN
   (NEW_MATCH_ACCEPT_TAC (CONJUNCT1 (UNDISCH NAT_HOM_THM))) THEN
   (ASM_REWRITE_TAC []));
  (REWRITE_TAC [])]));;


let MINUS_MOD_DEF = new_definition(`MINUS_MOD_DEF`,
"minus_mod n m p = plus_mod n m (INV(int_mod n,plus_mod n)p)");;


set_goal([], "!m p. minus_mod n (mod n m) (mod n p) = mod n (m minus p)");;

expand (REWRITE_TAC [MINUS_MOD_DEF;INV_EQ_MOD_NEG;
         MINUS_DEF;PLUS_MOD_LEMMA]);;

let MINUS_MOD_LEMMA = prove_thm(`MINUS_MOD_LEMMA`,
"!m p. minus_mod n (mod n m) (mod n p) = mod n (m minus p)",
(REWRITE_TAC [MINUS_MOD_DEF;INV_EQ_MOD_NEG;
              MINUS_DEF;PLUS_MOD_LEMMA]));;



% Get theorems from group theory specialized to int_mod, using (mod n (INT 0))
  in place of (ID(int_mod n,plus_mod n)). %

let thm_list = return_GROUP_theory `INT_MOD` int_mod_as_GROUP
 [ID_EQ_MOD_0;(SYM (SPEC_ALL MINUS_MOD_DEF))];;

% Strip theorems apart and specialize to (mod n m)%

let thl1 = map (\ (name,thm).(name,
(IMP_CANON thm) and_then
 (map (\thm1.
  (STRONG_INST
   [("mod n m1","x:integer -> bool");
    ("mod n m2","y:integer -> bool");
    ("mod n m3","z:integer -> bool")] thm1) and_then
  (REWRITE_RULE[(CONJUNCT1 INT_MOD_MOD_LEMMA);INV_EQ_MOD_NEG]))))) thm_list;;

% Put the theorems back together again, in compact form %

let thl2 = map (\ (name,thl).(name,
 (LIST_CONJ thl) and_then (REWRITE_RULE []))) thl1;;

% bind all free variables, except n which we are thinking of globally %

let thl3 = map (\ (name,thm).(name,
 GENL (filter (\x.not(x = "n:integer")) (frees (concl thm))) thm))
 thl2;;

% Remove all |- T %

let thl4 = filter (\ (name,thm).not((concl thm) = "T")) thl3;;

% Save the list of theorems, and bind them in current memory to there names %

map (\ (name,thm).
  (save_thm (name,thm));
  (autoload_theory (`theorem`,`int_mod`, name))) thl4;;

close_theory `int_mod`;;

