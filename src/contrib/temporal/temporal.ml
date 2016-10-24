%----------------------------------------------------------------
  temporal.ml:  This file contains the ML code (along with the
                proof sessions) of the theory `temporal`.  It is
                a formalization of the propositional temporal
                logic proof system as proposed by Manna & Pnueli.
  author: Amit Jasuja
  date: July 30, 1990
  paper ref: Verification of Concurrent Programs: A temporal Proof
             System (Zohar Manna, Amir Pnueli) - Proceeding of
             the 4th School of Advanced Programming, Amsterdam June '82.
----------------------------------------------------------------%
%----------------------------------------------------------------
definitions of temporal operators in higher order logic
----------------------------------------------------------------%

new_theory `temporal`;;

let henceforth = new_definition (`henceforth`,
"!(w:num->bool) (t:num). henceforth w t = 
  (!(t1:num). (t <= t1) ==> w t1)");;

let eventually = new_definition (`eventually`,
"!(w:num->bool) (t:num). eventually w t =
  (?(t1:num). (t <= t1) /\ (w t1))");;

let next = new_definition (`next`,
"!(w:num->bool) (t:num). next w t = w(SUC t)");;

let until = new_infix_definition (`until`,
"!(w1 w2:num->bool) (t:num). $until w1 w2 t =
  (?(t1:num). (t <= t1) /\ (w2 t1) /\
              (!(t2:num). ((t <= t2) /\ (t2 < t1)) ==> (w1 t2)))");;

%----------------------------------------------------------------
define a new set of temporal connectives
----------------------------------------------------------------%

let Equiv = new_infix_definition (`Equiv`,
"!(w1 w2:num->bool) (t:num). $Equiv w1 w2 t = ((w1 t) = (w2 t))");;

let Not = new_definition (`Not`,
"!(w:num->bool) (t:num). Not w t = ~(w t)");;

let Imp = new_infix_definition (`Imp`,
"!(w1 w2:num->bool) (t:num). $Imp w1 w2 t = ((w1 t) ==> (w2 t))");;

let And = new_infix_definition (`And`,
"!(w1 w2:num->bool) (t:num). $And w1 w2 t = ((w1 t) /\ (w2 t))");;

let Or = new_infix_definition (`Or`,
"!(w1 w2:num->bool) (t:num). $Or w1 w2 t = ((w1 t) \/ (w2 t))");;

%----------------------------------------------------------------
the notion of validity is important when doing proofs in HOL, 
since every assertion has to be either true of false (unlike proper
temporal logic, where it depends on time).
----------------------------------------------------------------%

let VALID = new_definition(`VALID`,
"!P:num->bool. VALID P = (!t:num. P t)");;

%----------------------------------------------------------------
always true and always false (they are not opposites)
----------------------------------------------------------------%

let T_T = new_definition(`T_T`,
"!t:num. T_T t = T");;

let T_F = new_definition(`T_F`,
"!t:num. T_F t = F");;

%----------------------------------------------------------------
conversion rule to make only one change in a theorem
----------------------------------------------------------------%

letrec DEPTH_FIRST_CONV conv trm =
  FIRST_CONV [conv;
              RATOR_CONV (DEPTH_FIRST_CONV conv);
              RAND_CONV (DEPTH_FIRST_CONV conv);
              ABS_CONV (DEPTH_FIRST_CONV conv)
              ] trm;;

let DEPTH_FIRST_CONV_RULE conv thm =
  EQ_MP (DEPTH_FIRST_CONV conv (concl thm)) thm;;

%----------------------------------------------------------------
use this rule to convert any propositional tautology into an 
equivalent temporal tautology.
----------------------------------------------------------------%
%----------------------------------------------------------------
take a variable (term form), break it up and create another one
with type (:num->bool).
----------------------------------------------------------------%

let change_var trm =
 let trm_s,trm_t = dest_var trm in
   mk_comb(mk_var(`T`^trm_s,":num->bool"),"(t:num)");;

%----------------------------------------------------------------
take a prop-tautology and convert it into a temp-tautology.
----------------------------------------------------------------%

let BOOL_TO_TEMP thm = 
 (let (bv, body) = strip_forall (concl thm) in
  let vars = map change_var bv in
  let temp_thm = SPECL vars thm in
  let temp_thm =  GEN "t:num" (PURE_REWRITE_RULE[SYM_RULE And;SYM_RULE Not;
                     SYM_RULE Equiv; SYM_RULE Imp;SYM_RULE Or] temp_thm) in
  GEN_ALL (REWRITE_RULE [SYM_RULE VALID] temp_thm)
)? failwith `BOOL_TO_TEMP`;;

%----------------------------------------------------------------
same as above, but with more control over the connectives that
are being modified (given as an argument list).
----------------------------------------------------------------%

let BOOL_TO_TEMP_L thm l = 
 (let (bv, body) = strip_forall (concl thm) in
  let vars = map change_var bv in
  let temp_thm = SPECL vars thm in
  let temp_thm =  GEN "t:num" (PURE_REWRITE_RULE (map SYM_RULE l) temp_thm) in
  GEN_ALL (REWRITE_RULE [SYM_RULE VALID] temp_thm)
)? failwith `BOOL_TO_TEMP_L`;;

%----------------------------------------------------------------
useful lemmas
----------------------------------------------------------------%

let lemma1 = prove_thm (`lemma1`,
"!a b. (~a = b) = (a = ~b)",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC []);;

let lemma2 = prove_thm (`lemma2`,
"!a b c. (a ==> b ==> c) = ((a /\ b) ==> c)",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool" THEN REWRITE_TAC[]);;
let T_LEM2 = BOOL_TO_TEMP lemma2;;

let lemma3 = prove_thm (`lemma3`,
"!a b. ((a ==> b) /\ a) = a /\ b",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool" THEN REWRITE_TAC[]);;

let lemma4 = prove_thm(`lemma4`,
"!a b c. (a <= b) /\ (b <= c) ==> (a <= c)",
REPEAT GEN_TAC
THEN REWRITE_TAC[LESS_OR_EQ]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[LESS_TRANS]
THENL [
  MP_TAC (SPECL ["a:num";"b:num";"c:num"] LESS_TRANS)
  THEN ASM_REWRITE_TAC[OR_INTRO_THM1]
  ;
  ASSUM_LIST (\thms. (REWRITE_TAC[SYM_RULE (el 1 thms)]))
  THEN ASM_REWRITE_TAC[]
  ]);;

let lemma5 = prove_thm(`lemma5`,
"!n. 0 <= n",
REWRITE_TAC[LESS_OR_EQ;(ONCE_REWRITE_RULE [DISJ_SYM] LESS_0_CASES)]);;

let lemma6 = prove_thm(`lemma6`,
"!m n. (SUC m) <= n ==> m <= n",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC OR_LESS
THEN RES_TAC
THEN ASM_REWRITE_TAC[LESS_OR_EQ]);;

let lemma7 = prove_thm(`lemma7`,
"!a b. (a ==> b) = (~b ==> ~a)",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC[]);;
let T_LEM7 = BOOL_TO_TEMP lemma7;;

let lemma8 = prove_thm(`lemma8`,
"!(a b):bool. (a = b) = ((a ==> b) /\ (b ==> a))",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC[]);;
let T_LEM8 = BOOL_TO_TEMP lemma8;;

let lemma9a = prove_thm(`lemma9a`,
"!a b c. (a ==> (b /\ c)) ==> (a ==> c)",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC[AND2_THM]);;
let T_LEM9a = BOOL_TO_TEMP lemma9a;;

let lemma9b = prove_thm(`lemma9b`,
"!a b c. (a ==> (b /\ c)) ==> (a ==> b)",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC[AND1_THM]);;
let T_LEM9b = BOOL_TO_TEMP lemma9b;;

let lemma10 = prove_thm(`lemma10`,
"!a b c. (a ==> b) /\ (a ==> c) = (a ==> (b /\ c))",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC[]);;
let T_LEM10 = BOOL_TO_TEMP lemma10;;

let lemma11 = prove_thm (`lemma11`,
"!a b. (a ==> (b ==> (a /\ b)))",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "b:bool"
THEN REWRITE_TAC[]);;
let T_LEM11 = BOOL_TO_TEMP lemma11;;

let lemma12 = prove_thm(`lemma12`,
"!a b c. (b ==> a) /\ (c ==> a) = ((b \/ c) ==> a)",
REPEAT GEN_TAC
THEN MAP_EVERY BOOL_CASES_TAC ["b:bool";"c:bool"]
THEN REWRITE_TAC[]);;
let T_LEM12 = BOOL_TO_TEMP lemma12;;

let lemma13 = prove_thm(`lemma13`,
"!a b. (a ==> (b ==> a))",
REPEAT GEN_TAC
THEN BOOL_CASES_TAC "a:bool"
THEN REWRITE_TAC[]);;
let T_LEM13 = BOOL_TO_TEMP lemma13;;

let lemma14a = prove_thm(`lemma14a`,
"!a b c d. (a ==> b) /\ (c ==> d) ==> ((a /\ c) ==> (b /\ d))",
REPEAT GEN_TAC
THEN MAP_EVERY BOOL_CASES_TAC ["a:bool";"c:bool"]
THEN REWRITE_TAC[]);;
let T_LEM14a = BOOL_TO_TEMP lemma14a;;

let lemma14b = prove_thm(`lemma14b`,
"!a b c d. (a ==> b) /\ (c ==> d) ==> ((a \/ c) ==> (b \/ d))",
REPEAT GEN_TAC
THEN MAP_EVERY BOOL_CASES_TAC ["a:bool";"c:bool";"b:bool"]
THEN REWRITE_TAC[OR_INTRO_THM1;OR_INTRO_THM2]);;
let T_LEM14b = BOOL_TO_TEMP lemma14b;;

let lemma15a = prove_thm (`lemma15a`,
"!a b c. (a ==> b) ==> ((a \/ c) ==> (b \/ c))",
REPEAT GEN_TAC
THEN MAP_EVERY BOOL_CASES_TAC ["a:bool";"b:bool"]
THEN REWRITE_TAC[]);;
let T_LEM15a = BOOL_TO_TEMP lemma15a;;

let lemma15b = prove_thm (`lemma15b`,
"!a b c d. (a ==> b) ==> ((d \/ (a /\ c)) ==> (d \/ (b /\ c)))",
REPEAT GEN_TAC
THEN MAP_EVERY BOOL_CASES_TAC ["a:bool";"b:bool"]
THEN REWRITE_TAC[OR_INTRO_THM1]);;
let T_LEM15b = BOOL_TO_TEMP lemma15b;;

let T_AND1_THM = BOOL_TO_TEMP AND1_THM;;

let T_AND2_THM = BOOL_TO_TEMP AND2_THM;;

let T_OR_INTRO_THM1 = BOOL_TO_TEMP OR_INTRO_THM1;;

let T_OR_INTRO_THM2 = BOOL_TO_TEMP OR_INTRO_THM2;;

%----------------------------------------------------------------
a simplistic decision procedure.
----------------------------------------------------------------%

let add_var trm = mk_comb(trm, "(t:num)");;

let T_SIMP_THM trm =
   (let (bv, body) = strip_forall trm in
   let tup = map add_var bv in
   TAC_PROOF(([], trm),
   REWRITE_TAC [VALID]
   THEN REPEAT GEN_TAC
   THEN REWRITE_TAC[ Imp;And;Not;Or ]
   THEN MAP_EVERY BOOL_CASES_TAC tup
   THEN REWRITE_TAC[]
   THEN STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC[]));;

%----------------------------------------------------------------
these here are some transformations from temporal logic formulae
to somewhat more useful (for proof hacking) higher-order forms.
----------------------------------------------------------------%
%----------------------------------------------------------------
substitute 'Equiv' by '=' (for rewriting purposes). mostly, the 
two are used together.  also, the tactic associated with it.
----------------------------------------------------------------%
%----------------------------------------------------------------
theorem that states that Equiv implies '=' (not the other way).
----------------------------------------------------------------%

let T_EQUIV_EXPAND = prove_thm(`T_EQUIV_EXPAND`,
"!U V.VALID(U Equiv V) ==> ((VALID U) = (VALID V))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;Equiv]
THEN STRIP_TAC
THEN FORALL_EQ_TAC
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
rewrite-rule - converts a theorem of the form (u equiv v) to the
form (u = v).
----------------------------------------------------------------%

let T_REWRITE_EQUIV_RULE thm =
  let bv, body = strip_forall(concl thm) in
  let t_a, term_b = (dest_comb (snd (dest_comb body))) in
  let term_a = (snd (dest_comb t_a)) in
  MP (SPECL [term_a;term_b] T_EQUIV_EXPAND) (SPEC_ALL thm);;

%----------------------------------------------------------------
substitute 'Imp' by '==>' (for rewriting purposes). mostly, the 
two are used together.  also, the tactic associated with it.
----------------------------------------------------------------%

let T_IMP_EXPAND = prove_thm(`T_IMP_EXPAND`,
"!U V. (VALID (U Imp V)) ==> ((VALID U) ==> (VALID V))",
REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[VALID;Imp]
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST (\thms. (MATCH_MP_TAC (el 2 thms)))
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
rewrite-rule - converts a theorem of the form (u Imp v) to the
form (u ==> v).
----------------------------------------------------------------%

let T_REWRITE_IMP_RULE thm =
  let bv, body = strip_forall(concl thm) in
  let t_a, term_b = (dest_comb (snd (dest_comb body))) in
  let term_a = (snd (dest_comb t_a)) in
  MP (SPECL [term_a;term_b] T_IMP_EXPAND) (SPEC_ALL thm);;

%----------------------------------------------------------------
substitute 'And' by '/\' (for rewriting purposes). mostly, the 
two are used together.  also, the tactic associated with it.
----------------------------------------------------------------%

let T_AND_EXPAND = prove_thm(`T_AND_EXPAND`,
"!U V. (VALID (U And V)) ==> ((VALID U) /\ (VALID V))",
REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[VALID;And]
THEN depth_conv_tac AND_FORALL_CONV
THEN REWRITE_TAC[]);;

let T_AND_COMB = prove_thm (`T_AND_COMB`,
"!U V. ((VALID U) /\ (VALID V)) ==> (VALID (U And V))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;And]
THEN REPEAT STRIP_TAC
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
rewrite-rule - converts a theorem of the form (u And v) to the
form (u /\ v).
----------------------------------------------------------------%

let T_REWRITE_AND_RULE thm =
  let bv, body = strip_forall(concl thm) in
  let t_a, term_b = (dest_comb (snd (dest_comb body))) in
  let term_a = (snd (dest_comb t_a)) in
  MP (SPECL [term_a;term_b] T_AND_EXPAND) (SPEC_ALL thm);;

%----------------------------------------------------------------
reflexive property of Equiv and Imp for temporal formulae
----------------------------------------------------------------%

let T_REFL_THM = prove_thm(`T_REFL_THM`,
"!U. VALID (U Equiv U)",
REWRITE_TAC[VALID;Equiv]);;

let T_IMP_REFL = prove_thm(`T_IMP_REFL`,
"!U. VALID(U Imp U)",
GEN_TAC
THEN REWRITE_TAC[BOOL_TO_TEMP (GEN_ALL (PURE_REWRITE_RULE[OR_CLAUSES] 
   (SPECL ["t:bool";"F"] OR_INTRO_THM1)))]);;

%----------------------------------------------------------------
symmetry property of Equiv for temporal formulae
----------------------------------------------------------------%

let T_SYM_THM = prove_thm (`T_SYM_THM`,
"!U V. VALID (U Equiv V) = VALID (V Equiv U)",
REWRITE_TAC[VALID;Equiv]
THEN REPEAT GEN_TAC
THEN FORALL_EQ_TAC
THEN EQ_TAC
THEN STRIP_TAC
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
application of Not to temporal formulae
----------------------------------------------------------------%

let T_NOT_APPLICATION = prove_thm (`T_NOT_APPLICATION`,
"!U V. VALID (U Equiv V) = VALID ((Not U) Equiv (Not V))",
REWRITE_TAC[VALID;Equiv;Not]
THEN REPEAT GEN_TAC
THEN FORALL_EQ_TAC
THEN BOOL_CASES_TAC "((U:num->bool) (t:num))"
THEN REWRITE_TAC[]);;

%----------------------------------------------------------------
de-morgans theorem for temporal connectives
----------------------------------------------------------------%

let T_DE_MORGAN_THM1 = prove_thm(`T_DE_MORGAN_THM1`,
"!U V. ((Not (U And V)) = ((Not U) Or (Not V)))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Not;And;Or;DE_MORGAN_THM]);;

let T_DE_MORGAN_THM2 = prove_thm (`T_DE_MORGAN_THM2`,
"!U V. ((Not (U Or V)) = ((Not U) And (Not V)))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Not;And;Or;DE_MORGAN_THM]);;

let T_DE_MORGAN_THM = (CONJ (T_DE_MORGAN_THM1) (T_DE_MORGAN_THM2));;

%----------------------------------------------------------------
equivalent of IMP_DISJ_THM in temporal logic
----------------------------------------------------------------%

let T_IMP_DISJ_THM = prove_thm(`T_IMP_DISJ_THM`,
"!U V. ((Not U) Or V) = (U Imp V)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Imp;Or;Not;IMP_DISJ_THM]);;

%----------------------------------------------------------------
transitivity of Equiv in temporal formulae
----------------------------------------------------------------%

let T_EQ_TRANS = prove_thm(`T_EQ_TRANS`,
"!U V W. (VALID (U Equiv V)) /\ (VALID (V Equiv W)) ==> (VALID (U Equiv W))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;Equiv]
THEN REPEAT STRIP_TAC
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
Equiv can be proved by proving (a Imp b) /\ (b Imp a)
----------------------------------------------------------------%

let T_IMP_IMP_EQ_S = prove_thm(`T_IMP_IMP_EQ_S`,
"!U V. ((U Imp V) And (V Imp U)) = (U Equiv V)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Imp;Equiv;And]
THEN EQ_TAC
THEN STRIP_TAC
THENL [
  EQ_TAC
  ;
  ALL_TAC]
THEN ASM_REWRITE_TAC[]);;

let T_IMP_IMP_EQUIV = prove_thm(`T_IMP_IMP_EQUIV`,
"!U V. (VALID (U Imp V)) /\ (VALID (V Imp U)) ==> (VALID (U Equiv V))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;BOOL_TO_TEMP_L lemma8 [Equiv;Imp]]
THEN REPEAT STRIP_TAC
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
transitivity of Imp in temporal logic.
----------------------------------------------------------------%

let T_IMP_TRANS = prove_thm (`T_IMP_TRANS`,
"!U V W. (VALID (U Imp V)) /\ (VALID (V Imp W)) ==> (VALID (U Imp W))",
REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[Imp;VALID]
THEN depth_conv_tac AND_FORALL_CONV
THEN REPEAT STRIP_TAC
THEN REPEAT RES_TAC);;

%----------------------------------------------------------------
transitivity of Equiv and Imp combined.
----------------------------------------------------------------%

let T_EQ_IMP_TRANS1 = prove_thm(`T_EQ_IMP_TRANS1`,
"!U V W. (VALID (U Imp V)) /\ (VALID (V Equiv W)) ==> (VALID (U Imp W))",
REPEAT GEN_TAC
THEN REWRITE_TAC [VALID;Equiv;Imp]
THEN REPEAT STRIP_TAC
THEN RES_TAC
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC[SYM_RULE (el 3 thms)])));;

let T_EQ_IMP_TRANS2 = prove_thm(`T_EQ_IMP_TRANS2`,
"!U V W. (VALID (U Equiv V)) /\ (VALID (V Imp W)) ==> (VALID (U Imp W))",
REPEAT GEN_TAC
THEN REWRITE_TAC [VALID;Equiv;Imp]
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST (\thms. (ASSUME_TAC 
    (REWRITE_RULE [(el 3 thms)] (el 1 thms))))
THEN RES_TAC);;

%----------------------------------------------------------------
a variation of lemma 10. (a ==> b)/\(a ==> c) ==> (a ==> (b /\ c))
----------------------------------------------------------------%

let T_IMP_IMP_CONJ = prove_thm(`T_IMP_IMP_CONJ`,
"!U V W. (VALID(U Imp V))/\(VALID(U Imp W)) ==> (VALID(U Imp (V And W)))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;Imp;And]
THEN REPEAT STRIP_TAC 
THEN RES_TAC);;

%----------------------------------------------------------------
temporal equivalent of (a = b) /\ (c = d) ==> (a /\ c) = (b /\ d)
----------------------------------------------------------------%

let T_AND_INJECTION = prove_thm(`T_AND_INJECTION`,
"!U V W X. (VALID (U Equiv V)) /\ (VALID (W Equiv X)) ==>
       (VALID ((U And W) Equiv (V And X)))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;And;Equiv]
THEN REPEAT STRIP_TAC
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
temporal equivalent of (a ==> (b ==> c)) /\ (a ==> b) ==> (a ==> c)
----------------------------------------------------------------%

let T_IMP_RES_THM = prove_thm(`T_IMP_RES_THM`,
"!U V W. (VALID (U Imp (V Imp W)))/\(VALID (U Imp V)) ==> (VALID (U Imp W))",
REPEAT GEN_TAC
THEN REWRITE_TAC[VALID;Imp]
THEN REPEAT STRIP_TAC
THEN RES_TAC);;

%----------------------------------------------------------------
associativity of And and Or
----------------------------------------------------------------%

let T_AND_ASSOC = prove_thm(`T_AND_ASSOC`,
"!U V W. (U And (V And W)) = ((U And V) And W)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And]
THEN BOOL_CASES_TAC "((V:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_ASSOC = prove_thm(`T_OR_ASSOC`,
"!U V W. (U Or (V Or W)) = ((U Or V) Or W)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or]
THEN BOOL_CASES_TAC "((V:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

%----------------------------------------------------------------
distributive property of And over Or
----------------------------------------------------------------%

let T_AND_DIST_L = prove_thm (`T_AND_DIST_L`,
"!U V W. (U And (V Or W)) = ((U And V) Or (U And W))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;Or]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_AND_DIST_R = prove_thm (`T_AND_DIST_R`,
"!U V W. ((U Or V) And W) = ((U And W) Or (V And W))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;Or]
THEN BOOL_CASES_TAC "((W:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_DIST_L = prove_thm(`T_OR_DIST_L`,
"!U V W. (U Or (V And W)) = ((U Or V) And (U Or W))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;And]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_DIST_R = prove_thm(`T_OR_DIST_R`,
"!U V W. ((V And W) Or U) = ((V Or U) And (W Or U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;And]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

%----------------------------------------------------------------
simplification rules for And and Or
----------------------------------------------------------------%

let T_AND_SIMP = prove_thm (`T_AND_SIMP`,
"!U. (U And (Not U)) = T_F",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;Not;T_F]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_AND_F1 = prove_thm(`T_AND_F1`,
"!U. (T_F And U) = T_F",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;T_F]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_AND_F2 = prove_thm(`T_AND_F2`,
"!U. (U And T_F) = T_F",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;T_F]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_AND_F = (CONJ (T_AND_F1) (T_AND_F2));;

let T_AND_T1 = prove_thm(`T_AND_T1`,
"!U. (T_T And U) = U",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;T_T]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_AND_T2 = prove_thm(`T_AND_T2`,
"!U. (U And T_T) = U",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And;T_T]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_AND_T = (CONJ T_AND_T1 T_AND_T2);;

let T_OR_SIMP = prove_thm (`T_OR_SIMP`,
"!U. (U Or (Not U)) = T_T",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;Not;T_T]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_T1 = prove_thm(`T_OR_T1`,
"!U. (T_T Or U) = T_T",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;T_T]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_T2 = prove_thm(`T_OR_T2`,
"!U. (U Or T_T) = T_T",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;T_T]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_T = (CONJ T_OR_T1 T_OR_T2);;

let T_OR_F1 = prove_thm(`T_OR_F1`,
"!U. (T_F Or U) = U",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;T_F]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_F2 = prove_thm(`T_OR_F2`,
"!U. (U Or T_F) = U",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Or;T_F]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_F = (CONJ T_OR_F1 T_OR_F2);;

let T_AND_SYM = prove_thm(`T_AND_SYM`,
"!U V. (U And V) = (V And U)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC [And]
THEN BOOL_CASES_TAC "((U:num->bool) (n:num))"
THEN REWRITE_TAC[]);;

let T_OR_SYM = prove_thm(`T_OR_SYM`,
"!U V. (U Or V) = (V Or U)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC [Or]
THEN BOOL_CASES_TAC "((U:num->bool)(n:num))"
THEN REWRITE_TAC[]);;

let T_AND_SELF = prove_thm(`T_AND_SELF`,
"!U. U And U = U",
depth_conv_tac FUN_EQ_CONV
THEN REWRITE_TAC[And]);;

let T_OR_SELF = prove_thm(`T_OR_SELF`,
"!U. U Or U = U",
depth_conv_tac FUN_EQ_CONV
THEN REWRITE_TAC[Or]);;

let T_AND_MV1 = prove_thm (`T_AND_MV1`,
"!U V W X. (U And V) And (W And X) = (U And W) And (V And X)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[And]
THEN MAP_EVERY BOOL_CASES_TAC ["((U:num->bool)(n:num))";
  "((V:num->bool)(n:num))"]
THEN REWRITE_TAC[]);;

%----------------------------------------------------------------
similar stuff for implication
----------------------------------------------------------------%

let T_IMP_F = prove_thm(`T_IMP_F`,
"!V. (V Imp T_F) = (Not V)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[Imp;Not;T_F]
THEN REWRITE_TAC[IMP_CLAUSES]);;

%----------------------------------------------------------------
modus ponens for temporal logic
----------------------------------------------------------------%

let T_MP_RULE = prove_thm(`T_MP_RULE`,
"!U V. (VALID (U Imp V)) /\ (VALID U) ==> VALID V",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC T_IMP_EXPAND
THEN RES_TAC);;

%----------------------------------------------------------------
axiomatization - prove all the axioms for temporal logic using 
higher order logic as the basis.
----------------------------------------------------------------%

%----------------------------------------------------------------
ax1: eventually and henceforth are duals.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w. VALID (((Not (eventually w)) Equiv 
                                  (henceforth (Not w))))");;

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC);;

e(PURE_REWRITE_TAC[Equiv;henceforth;eventually;Not]);;

e(depth_conv_tac NOT_EXISTS_CONV);;

e(FORALL_EQ_TAC);;

e(REWRITE_TAC[DE_MORGAN_THM;IMP_DISJ_THM]);;

----------------------------------------------------------------%
%----------------------------------------------------------------
may be i won't need these after all - since i have the stronger 
results.
----------------------------------------------------------------%

let A1_S = prove_thm (`A1_S`,
"!w. (Not (eventually w)) = (henceforth (Not w))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[eventually;henceforth;Not]
THEN depth_conv_tac NOT_EXISTS_CONV
THEN FORALL_EQ_TAC
THEN REWRITE_TAC[DE_MORGAN_THM;IMP_DISJ_THM]);;

let A1_INV_S = prove_thm (`A1_INV_S`,
"!w. (Not (henceforth w)) = (eventually (Not w))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[eventually;henceforth;Not]
THEN ONCE_REWRITE_TAC[lemma1]
THEN depth_conv_tac NOT_EXISTS_CONV
THEN FORALL_EQ_TAC
THEN REWRITE_TAC[DE_MORGAN_THM;IMP_DISJ_THM]);;

let A1 = prove_thm (`A1`,
"!w. VALID ((Not (eventually w)) Equiv (henceforth (Not w)))",
GEN_TAC
THEN ONCE_REWRITE_TAC [A1_S]
THEN REWRITE_TAC [T_REFL_THM]);;

let A1_INV = prove_thm (`A1_INV`,
"!w. VALID ((Not (henceforth w)) Equiv (eventually (Not w)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[A1_INV_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
ax2: if universally w1 implies w2, then if henceforth w1 is true,
     then so is w2.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w1 w2. VALID (Imp (henceforth (Imp w1 w2))
                                (Imp (henceforth w1) (henceforth w2)))");;

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC);;

e(PURE_REWRITE_TAC[henceforth;Imp]);;

e(REWRITE_TAC[lemma2]);;

e(REPEAT STRIP_TAC);;

e(RES_TAC);;

----------------------------------------------------------------%

let A2 = prove_thm(`A2`,
"!w1 w2. VALID ((henceforth (w1 Imp w2)) Imp
                    ((henceforth w1) Imp (henceforth w2)))",
PURE_REWRITE_TAC[VALID]
THEN REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[henceforth;Imp]
THEN REWRITE_TAC [lemma2]
THEN REPEAT STRIP_TAC
THEN RES_TAC);;

%----------------------------------------------------------------
ax3: henceforth implies true
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w. VALID (Imp (henceforth w) w)");;

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC);;

e(PURE_REWRITE_TAC[henceforth;Imp]);;

e(STRIP_GOAL_THEN MATCH_MP_TAC);;

e(REWRITE_TAC[LESS_OR_EQ]);;

----------------------------------------------------------------%

let A3 = prove_thm(`A3`,
"!w. VALID ((henceforth w) Imp w)",
PURE_REWRITE_TAC[VALID]
THEN REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[henceforth;Imp]
THEN STRIP_GOAL_THEN MATCH_MP_TAC
THEN REWRITE_TAC[LESS_OR_EQ]);;

%----------------------------------------------------------------
ax4: duality of next.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w. VALID (Equiv (Not (next w)) (next (Not w)))");;

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC 
THEN REWRITE_TAC[Equiv;next;Not]);;

----------------------------------------------------------------%
%----------------------------------------------------------------
may be i won't need these either.
----------------------------------------------------------------%

let A4_S = prove_thm(`A4_S`,
"!w. (Not (next w)) = (next (Not w))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC 
THEN REWRITE_TAC[next;Not]);;

let A4 = prove_thm(`A4`,
"!w. VALID ((Not (next w)) Equiv (next (Not w)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[A4_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
ax5: analogue of ax2 for the next operator
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w1 w2. VALID (Imp (next (Imp w1 w2)) 
                                (Imp (next w1) (next w2)))");

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC 
THEN REWRITE_TAC[next;Imp]);;

----------------------------------------------------------------%

let A5 = prove_thm (`A5`,
"!w1 w2. VALID ((next (w1 Imp w2)) Imp ((next w1) Imp (next w2)))",
PURE_REWRITE_TAC[VALID]
THEN REPEAT GEN_TAC
THEN REWRITE_TAC[next;Imp]);;

%----------------------------------------------------------------
ax6: henceforth implies next
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w. VALID (Imp (henceforth w) (next w))");;

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC);;

e(PURE_REWRITE_TAC[henceforth;next;Imp]);;

e(STRIP_GOAL_THEN MATCH_MP_TAC);;

e(REWRITE_TAC[LESS_OR_EQ;LESS_SUC_REFL]);;

----------------------------------------------------------------%

let A6 = prove_thm (`A6`,
"!w. VALID ((henceforth w) Imp (next w))",
PURE_REWRITE_TAC[VALID]
THEN REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[henceforth;next;Imp]
THEN STRIP_GOAL_THEN MATCH_MP_TAC
THEN REWRITE_TAC[LESS_EQ_SUC_REFL]);;

%----------------------------------------------------------------
ax7: henceforth implies henceforth after the next instant also.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w. VALID (Imp (henceforth w) (next (henceforth w)))");;

e(PURE_REWRITE_TAC[VALID]);;

e(REPEAT GEN_TAC);;

e(PURE_REWRITE_TAC[Imp;next;henceforth]);;

e(REPEAT STRIP_TAC);;

e(ASSUM_LIST (\thms. (MATCH_MP_TAC (el 2 thms))));;

e(MATCH_MP_TAC (SPECL ["t:num";"SUC t";"t1:num"] lemma4)
THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]);;

set_flag (`sticky`,true);;

----------------------------------------------------------------%

let A7 = prove_thm(`A7`,
"!w. VALID ((henceforth w) Imp (next (henceforth w)))",
PURE_REWRITE_TAC[VALID]
THEN REPEAT GEN_TAC
THEN PURE_REWRITE_TAC[Imp;next;henceforth]
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST (\thms. (MATCH_MP_TAC (el 2 thms)))
THEN MATCH_MP_TAC (SPECL ["t:num";"SUC t";"t1:num"] lemma4)
THEN ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]);;

%----------------------------------------------------------------
ax8: computational induction axiom - if property is inherited over
     one step transitions, then it is invariant over any suffix
     sequence whose first state satisfies 'w'.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w. VALID (Imp (henceforth (Imp w (next w)))
                            (Imp w (henceforth w)))");;

e(PURE_REWRITE_TAC[VALID]);;

e(PURE_REWRITE_TAC[Imp;henceforth;next]);;

e(GEN_TAC THEN INDUCT_TAC);;

CASE 1

e(REWRITE_TAC[lemma5;lemma2;(ONCE_REWRITE_RULE [CONJ_SYM] INDUCTION)]);;

CASE 2

e(STRIP_TAC THEN STRIP_TAC);;

e(INDUCT_TAC);;

CASE 2.1

e(REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC]);;

CASE 2.2

e(REWRITE_TAC[LESS_OR_EQ;LESS_MONO_EQ;INV_SUC_EQ]);;

e(ASM_CASES_TAC "(SUC t) <= t1" THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [
     REWRITE_RULE [SYM_RULE LESS_EQ] (el 1 thms)])));;

e(STRIP_TAC);;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [(el 1 thms)] (el 4 thms)))));;

----------------------------------------------------------------%

let A8 = prove_thm(`A8`,
"!w. VALID ((henceforth (w Imp (next w))) Imp (w Imp (henceforth w)))",
PURE_REWRITE_TAC[Imp;henceforth;next;VALID]
THEN GEN_TAC 
THEN INDUCT_TAC
THENL [
  REWRITE_TAC[lemma5;lemma2;(ONCE_REWRITE_RULE [CONJ_SYM] INDUCTION)]
  ;
  STRIP_TAC
  THEN STRIP_TAC
  THEN INDUCT_TAC
  THENL [
    REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC]
    ;
    REWRITE_TAC[LESS_OR_EQ;LESS_MONO_EQ;INV_SUC_EQ]
    THEN ASM_CASES_TAC "(SUC t) <= t1" 
    THEN RES_TAC 
    THEN ASM_REWRITE_TAC[]
    THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [
      REWRITE_RULE [SYM_RULE LESS_EQ] (el 1 thms)]))
    THEN STRIP_TAC
    THEN ASSUM_LIST (\thms. (ACCEPT_TAC (
     REWRITE_RULE [(el 1 thms)] (el 4 thms))))
    ]
  ]);;

%----------------------------------------------------------------
ax9: characterizes the until operator by distributing the effect
     into what is implied by the present instant and the next instant.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w1 w2. (w1 until w2) = 
                     (w2 Or (w1 And (next (w1 until w2))))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(PURE_REWRITE_TAC[until;Or;And;next]);;

e(REPEAT GEN_TAC);;

e(EQ_TAC THEN STRIP_TAC);;

CASE 1

e(ASM_CASES_TAC "n < t1");;

case 1.1

e(MATCH_MP_TAC OR_INTRO_THM2);;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [
  (REWRITE_RULE[LESS_EQ_REFL;(el 1 thms)] (SPEC "n:num" (el 2 thms)))])));;

e(EXISTS_TAC "t1:num");;

e(ASM_REWRITE_TAC[SYM_RULE LESS_EQ]);;

e(REPEAT STRIP_TAC);;

e(ASSUM_LIST (\thms. (ACCEPT_TAC 
        (REWRITE_RULE[LESS_OR_EQ;(el 1 thms);(el 2 thms)]
          (SPEC "t2:num" (el 4 thms))))));;

case 1.2

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC[
  (REWRITE_RULE[(el 1 thms);LESS_OR_EQ] (el 4 thms))])));;

CASE 2

e(EXISTS_TAC "n:num");;

e(ASM_REWRITE_TAC[LESS_EQ_REFL;
     (ONCE_REWRITE_RULE[CONJ_SYM]LESS_EQ_ANTISYM)]);;

CASE 3

e(EXISTS_TAC "t1:num");;

e(ASSUME_TAC lemma6);;

e(IMP_RES_TAC lemma6);;

e(ASM_REWRITE_TAC[LESS_OR_EQ]);;

e(REPEAT STRIP_TAC);;

CASE 3.1

e(ASSUME_TAC LESS_SUC_EQ);;

e(RES_TAC);;

CASE 3.2

e(ASSUM_LIST (\thms. (PURE_REWRITE_TAC[
    SYM_RULE (el 2 thms);(el 7 thms)])));;

----------------------------------------------------------------%
%----------------------------------------------------------------
same thing with this proof (another instance of equiv).
----------------------------------------------------------------%

let A9_S = prove_thm(`A9_S`,
"!w1 w2. (w1 until w2) = (w2 Or (w1 And (next (w1 until w2))))",
depth_conv_tac FUN_EQ_CONV
THEN PURE_REWRITE_TAC[until;Or;And;next]
THEN REPEAT GEN_TAC
THEN EQ_TAC 
THEN STRIP_TAC
THENL [
  ASM_CASES_TAC "n < t1"
  THENL [
    MATCH_MP_TAC OR_INTRO_THM2
    THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [
      (REWRITE_RULE[LESS_EQ_REFL;(el 1 thms)] (SPEC "n:num" (el 2 thms)))]))
    THEN EXISTS_TAC "t1:num"
    THEN ASM_REWRITE_TAC[SYM_RULE LESS_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASSUM_LIST (\thms. (ACCEPT_TAC 
      (REWRITE_RULE[LESS_OR_EQ;(el 1 thms);(el 2 thms)]
         (SPEC "t2:num" (el 4 thms)))))
    ;
    ASSUM_LIST (\thms. (ASM_REWRITE_TAC[
      (REWRITE_RULE[(el 1 thms);LESS_OR_EQ] (el 4 thms))]))
    ]
  ;
  EXISTS_TAC "n:num"
  THEN ASM_REWRITE_TAC[LESS_EQ_REFL;
     (ONCE_REWRITE_RULE[CONJ_SYM]LESS_EQ_ANTISYM)]
  ;
  EXISTS_TAC "t1:num"
  THEN IMP_RES_TAC lemma6
  THEN ASM_REWRITE_TAC[LESS_OR_EQ]
  THEN REPEAT STRIP_TAC
  THENL [
    ASSUME_TAC LESS_SUC_EQ
    THEN RES_TAC
    ;
    ASSUM_LIST (\thms. (PURE_REWRITE_TAC[
      SYM_RULE (el 2 thms);(el 7 thms)]))
    ]
  ]);;

let A9 = prove_thm(`A9`,
"!w1 w2. VALID ((w1 until w2) Equiv (w2 Or (w1 And (next (w1 until w2)))))",
GEN_TAC
THEN ONCE_REWRITE_TAC[SYM_RULE A9_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
ax10: until implies eventually the terminating condition will be
      true.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!w1 w2. VALID (Imp (until w1 w2) (eventually w2))");;

e(PURE_REWRITE_TAC[VALID;Imp;until;eventually]);;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(EXISTS_TAC "t1:num");;

e(ASM_REWRITE_TAC[]);;

----------------------------------------------------------------%

let A10 = prove_thm(`A10`,
"!w1 w2. VALID((w1 until w2) Imp (eventually w2))",
PURE_REWRITE_TAC[VALID;Imp;until;eventually]
THEN REPEAT GEN_TAC
THEN STRIP_TAC
THEN EXISTS_TAC "t1:num"
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
basic inference rules
----------------------------------------------------------------%

%----------------------------------------------------------------
a ==> b is equivalent to ~b ==> ~a
 and equivalently :

|- !Ta Tb t. (Ta Imp Tb)t = ((Not Tb) Imp (Not Ta))t
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. (Imp U V) = (Imp (Not V) (Not U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(ACCEPT_TAC (REWRITE_RULE[VALID;Equiv]T_CONTRAPOS_CANON));;

----------------------------------------------------------------%

let T_CONTRAPOS = prove_thm(`T_CONTRAPOS`,
"!U V. (U Imp V) = ((Not V) Imp (Not U))",
depth_conv_tac FUN_EQ_CONV
THEN ACCEPT_TAC (REWRITE_RULE [VALID;Equiv] T_LEM7));;

%----------------------------------------------------------------
collapsing consecutive nots
----------------------------------------------------------------%

let NOT_NOT_RULE = prove_thm(`NOT_NOT_RULE`,
"!U. (Not (Not U)) = U",
depth_conv_tac FUN_EQ_CONV
THEN REWRITE_TAC[Not]);;

%----------------------------------------------------------------
HI:henceforth insertion
----------------------------------------------------------------%

let HF_INSERTION = prove_thm(`HF_INSERTION`,
"!U. VALID U ==> VALID (henceforth U)",
GEN_TAC
THEN PURE_REWRITE_TAC[VALID;henceforth]
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (SPEC ("t1:num") (el 2 thms)))));;

%----------------------------------------------------------------
OI:next insertion
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. VALID U ==> VALID (next U)");;

e(GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC (T_REWRITE_IMP_RULE A6));;

e(IMP_RES_TAC HF_INSERTION);;

----------------------------------------------------------------%

let N_INSERTION = prove_thm(`N_INSERTION`,
"!U. VALID U ==> VALID (next U)",
GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC (T_REWRITE_IMP_RULE A6)
THEN IMP_RES_TAC HF_INSERTION);;

%----------------------------------------------------------------
T1:eventually insertion
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. (VALID (U Imp (eventually U)))");;

e(GEN_TAC);;

e(PURE_REWRITE_TAC [SYM_RULE (REWRITE_RULE 
        [NOT_NOT_RULE] (SPEC "Not U" A1_INV_S))]);;

e(ACCEPT_TAC (REWRITE_RULE [NOT_NOT_RULE] 
             (ONCE_REWRITE_RULE [T_CONTRAPOS] (SPEC "Not U" A3))));;

set_goal([],"!U. VALID U ==> VALID (eventually U)");;

e(REPEAT GEN_TAC);;

e(MATCH_MP_TAC T_IMP_EXPAND);;

e(ACCEPT_TAC (SPEC_ALL EV_INS_THM));;

----------------------------------------------------------------%

let EV_INS_THM = prove_thm(`EV_INS_THM`,
"!U. (VALID (U Imp (eventually U)))",
GEN_TAC
THEN PURE_REWRITE_TAC [SYM_RULE
            (REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" A1_INV_S))]
THEN ACCEPT_TAC (REWRITE_RULE [NOT_NOT_RULE] 
             (ONCE_REWRITE_RULE [T_CONTRAPOS] (SPEC "Not U" A3))));;

let EV_INSERTION = prove_thm(`EV_INSERTION`,
"!U. VALID U ==> VALID (eventually U)",
GEN_TAC
THEN MATCH_MP_TAC T_IMP_EXPAND
THEN ACCEPT_TAC (SPEC_ALL EV_INS_THM));;

%----------------------------------------------------------------
T2:next implies eventually
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. VALID (next U) ==> VALID (eventually U)");;

e(GEN_TAC);;

e(PURE_ONCE_REWRITE_TAC [SYM_RULE
            (REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" A4_S))]);;

e(PURE_ONCE_REWRITE_TAC [SYM_RULE
            (REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" A1_INV_S))]);;

e(MATCH_MP_TAC T_IMP_EXPAND);;

e(ACCEPT_TAC (ONCE_REWRITE_RULE [T_CONTRAPOS] (SPEC "Not U" A6)));;

----------------------------------------------------------------%

let NEXT_IMP_EV = prove_thm(`NEXT_IMP_EV`,
"!U. VALID (next U) ==> VALID (eventually U)",
GEN_TAC
THEN PURE_ONCE_REWRITE_TAC [SYM_RULE
            (REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" A4_S))]
THEN PURE_ONCE_REWRITE_TAC [SYM_RULE
            (REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" A1_INV_S))]
THEN MATCH_MP_TAC T_IMP_EXPAND
THEN ACCEPT_TAC (ONCE_REWRITE_RULE [T_CONTRAPOS] (SPEC "Not U" A6)));;

%----------------------------------------------------------------
HH:henceforth - henceforth rule
----------------------------------------------------------------%

let T_EQ_IMP_RULE = T_LEM8;;

%----------------------------------------------------------------

set_goal([],"!U V.
   VALID (U Imp V) ==> VALID ((henceforth U) Imp (henceforth V))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC (T_REWRITE_IMP_RULE A2));;

e(IMP_RES_TAC (SPEC "U Imp V" HF_INSERTION));;

----------------------------------------------------------------%

let HF_HF_IMP_RULE = prove_thm(`HF_HF_IMP_RULE`,
"!U V. VALID (U Imp V) ==> VALID ((henceforth U) Imp (henceforth V))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC (T_REWRITE_IMP_RULE A2)
THEN IMP_RES_TAC (SPEC "U Imp V" HF_INSERTION));;

%----------------------------------------------------------------

set_goal([],"!U V.
   VALID (U Equiv V) ==> VALID ((henceforth U) Equiv (henceforth V))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC T_IMP_IMP_EQUIV);;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE 
              [T_REWRITE_EQUIV_RULE T_LEM8] (el 1 thms)))));;

e(IMP_RES_TAC T_AND_EXPAND);;

e(IMP_RES_TAC (SPEC_ALL HF_HF_IMP_RULE));;

e(ASM_REWRITE_TAC[]);;

----------------------------------------------------------------%

let HF_HF_RULE = prove_thm(`HF_HF_RULE`,
"!U V. VALID (U Equiv V) ==> VALID ((henceforth U) Equiv (henceforth V))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC T_IMP_IMP_EQUIV
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE 
              [T_REWRITE_EQUIV_RULE T_LEM8] (el 1 thms))))
THEN IMP_RES_TAC T_AND_EXPAND
THEN IMP_RES_TAC (SPEC_ALL HF_HF_IMP_RULE)
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
EE:eventually - eventually rule
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. 
  VALID (U Imp V) ==> (VALID ((eventually U) Imp (eventually V)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(PURE_ONCE_REWRITE_TAC[T_CONTRAPOS]);;

e(PURE_REWRITE_TAC[A1_STRONG]);;

e(MATCH_MP_TAC HF_HF_IMP_RULE);;

e(ASM_REWRITE_TAC[SYM_RULE T_CONTRAPOS]);;

----------------------------------------------------------------%

let EV_EV_IMP_RULE = prove_thm(`EV_EV_IMP_RULE`,
"!U V. VALID (U Imp V) ==> (VALID ((eventually U) Imp (eventually V)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN PURE_ONCE_REWRITE_TAC[T_CONTRAPOS]
THEN PURE_REWRITE_TAC[A1_S]
THEN MATCH_MP_TAC HF_HF_IMP_RULE
THEN ASM_REWRITE_TAC[SYM_RULE T_CONTRAPOS]);;

%----------------------------------------------------------------

set_goal([],"!U V. 
  VALID (U Equiv V) ==> (VALID ((eventually U) Equiv (eventually V)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC T_IMP_IMP_EQUIV);;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE 
              [T_REWRITE_EQUIV_RULE T_EQ_IMP_RULE] (el 1 thms)))));;

e(IMP_RES_TAC T_AND_EXPAND);;

e(IMP_RES_TAC (SPEC_ALL EV_EV_IMP_RULE));;

e(ASM_REWRITE_TAC[]);;

----------------------------------------------------------------%

let EV_EV_RULE = prove_thm(`EV_EV_RULE`,
"!U V. VALID (U Equiv V) ==> (VALID ((eventually U) Equiv (eventually V)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC T_IMP_IMP_EQUIV
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE 
              [T_REWRITE_EQUIV_RULE T_EQ_IMP_RULE] (el 1 thms))))
THEN IMP_RES_TAC T_AND_EXPAND
THEN IMP_RES_TAC (SPEC_ALL EV_EV_IMP_RULE)
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
OO:next-next rules
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID (U Imp V) ==> (VALID ((next U) Imp (next V)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC (T_REWRITE_IMP_RULE (SPECL ["U:num->bool";"V:num->bool"] A5)));;

e(IMP_RES_TAC N_INSERTION);;

----------------------------------------------------------------%

let N_N_IMP_RULE = prove_thm(`N_N_IMP_RULE`,
"!U V. VALID (U Imp V) ==> (VALID ((next U) Imp (next V)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC 
  (T_REWRITE_IMP_RULE (SPECL ["U:num->bool";"V:num->bool"] A5))
THEN IMP_RES_TAC N_INSERTION);;

%----------------------------------------------------------------

set_goal([],"!U V. 
  VALID (U Equiv V) ==> (VALID ((next U) Equiv (next V)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC T_IMP_IMP_EQUIV);;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE 
              [T_REWRITE_EQUIV_RULE T_EQ_IMP_RULE] (el 1 thms)))));;

e(IMP_RES_TAC T_AND_EXPAND);;

e(IMP_RES_TAC (SPEC_ALL N_N_IMP_RULE));;

e(ASM_REWRITE_TAC[]);;

----------------------------------------------------------------%

let N_N_RULE = prove_thm (`N_N_RULE`,
"!U V. VALID (U Equiv V) ==> (VALID ((next U) Equiv (next V)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC T_IMP_IMP_EQUIV
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE 
              [T_REWRITE_EQUIV_RULE T_EQ_IMP_RULE] (el 1 thms))))
THEN IMP_RES_TAC T_AND_EXPAND
THEN IMP_RES_TAC (SPEC_ALL N_N_IMP_RULE)
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
CI:computational induction theorem
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. VALID(U Imp (next U)) ==> VALID(U Imp (henceforth U))");;

e(GEN_TAC);;

e(STRIP_TAC);;

e(MATCH_MP_TAC (T_REWRITE_IMP_RULE A8));;

e(IMP_RES_TAC HF_INSERTION);;

----------------------------------------------------------------%

let T_INDUCTION_RULE = prove_thm(`T_INDUCTION_RULE`,
"!U. VALID(U Imp (next U)) ==> VALID(U Imp (henceforth U))",
GEN_TAC
THEN STRIP_TAC
THEN MATCH_MP_TAC (T_REWRITE_IMP_RULE A8)
THEN IMP_RES_TAC HF_INSERTION);;

%----------------------------------------------------------------
DCI:derived computational induction rule.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. 
  VALID(U Imp (V And (next U))) ==> VALID(U Imp (henceforth V))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(IMP_RES_TAC (T_REWRITE_IMP_RULE T_PROP_REASON1));;

e(IMP_RES_TAC (T_INDUCTION_RULE));;

e(IMP_RES_TAC (T_REWRITE_IMP_RULE T_PROP_REASON2));;

e(IMP_RES_TAC HF_HF_IMP_RULE);;

e(IMP_RES_TAC T_IMP_TRANS);;

----------------------------------------------------------------%

let T_DER_INDUCTION_RULE = prove_thm(`T_DER_INDUCTION_RULE`,
"!U V. VALID(U Imp (V And (next U))) ==> VALID(U Imp (henceforth V))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN IMP_RES_TAC (T_REWRITE_IMP_RULE T_LEM9a)
THEN IMP_RES_TAC (T_INDUCTION_RULE)
THEN IMP_RES_TAC (T_REWRITE_IMP_RULE T_LEM9b)
THEN IMP_RES_TAC HF_HF_IMP_RULE
THEN IMP_RES_TAC T_IMP_TRANS);;

%----------------------------------------------------------------
T3 and T4:henceforth and eventually are idempotent
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. VALID ((henceforth U) Equiv (henceforth (henceforth U)))");;

e(GEN_TAC);;

e(ONCE_REWRITE_TAC[SYM_RULE HF_IDEMPOTENT_S]);;

e(REWRITE_TAC[T_REFL_THM]);;

set_goal([],"!U. (henceforth U) = (henceforth (henceforth U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (SPEC "n:num" (REWRITE_RULE [VALID;Imp] 
    (SPEC "henceforth U" A3))));;

e(ASSUME_TAC (SPEC "n:num" (REWRITE_RULE [VALID;Imp] (MATCH_MP 
   (T_INDUCTION_RULE) (SPEC "U:num->bool" A7)))));;

e(EQ_TAC 
THEN ASM_REWRITE_TAC[]);;

----------------------------------------------------------------%

let HF_IDEMPOTENT_S = prove_thm (`HF_IDEMPOTENT_S`,
"!U. (henceforth U) = (henceforth (henceforth U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (SPEC "n:num" (REWRITE_RULE [VALID;Imp] 
    (SPEC "henceforth U" A3)))
THEN ASSUME_TAC (SPEC "n:num" (REWRITE_RULE [VALID;Imp] (MATCH_MP 
   (T_INDUCTION_RULE) (SPEC "U:num->bool" A7))))
THEN EQ_TAC 
THEN ASM_REWRITE_TAC[]);;

let HF_IDEMPOTENT = prove_thm(`HF_IDEMPOTENT`,
"!U. VALID ((henceforth U) Equiv (henceforth (henceforth U)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[SYM_RULE HF_IDEMPOTENT_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!U. (eventually U) = (eventually (eventually U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE [VALID;Equiv] (DEPTH_FIRST_CONV_RULE
     (REWR_CONV (SYM_RULE A1_S)) (SPEC "henceforth (Not U)" T_REFL_THM))));;

e(ASSUME_TAC (SPEC "Not U" HF_IDEMPOTENT_S));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (ONCE_REWRITE_RULE 
    [el 1 thms] (el 2 thms)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [Not;SYM_RULE A1_S] 
 (el 1 thms)))));;

e(ASM_CASES_TAC "eventually U n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
  (SPEC "n:num" (el 2 thms))])));;

set_goal([],"!U. VALID ((eventually U) Equiv (eventually (eventually U)))");;

e(GEN_TAC);;

e(ONCE_REWRITE_TAC[SYM_RULE EV_IDEMPOTENT_S]);;

e(REWRITE_TAC[T_REFL_THM]);;

----------------------------------------------------------------%

let EV_IDEMPOTENT_S = prove_thm(`EV_IDEMPOTENT_S`,
"!U. (eventually U) = (eventually (eventually U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE [VALID;Equiv] (DEPTH_FIRST_CONV_RULE
     (REWR_CONV (SYM_RULE A1_S)) (SPEC "henceforth (Not U)" T_REFL_THM)))
THEN ASSUME_TAC (SPEC "Not U" HF_IDEMPOTENT_S)
THEN ASSUM_LIST (\thms. (ASSUME_TAC (ONCE_REWRITE_RULE 
    [el 1 thms] (el 2 thms))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [Not;SYM_RULE A1_S] 
 (el 1 thms))))
THEN ASM_CASES_TAC "eventually U n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
  (SPEC "n:num" (el 2 thms))])));;

let EV_IDEMPOTENT = prove_thm (`EV_IDEMPOTENT`,
"!U. VALID ((eventually U) Equiv (eventually (eventually U)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[SYM_RULE EV_IDEMPOTENT_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
T6:henceforth distributes over Imp - and the result is eventaully
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V.
(VALID ((henceforth (U Imp V)) Imp ((eventually U) Imp (eventually V))))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (MATCH_MP HF_HF_RULE 
      (SPECL ["U:num->bool";"V:num->bool"] T_LEM7)));;

e(ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] (SPECL ["Not V";"Not U"] A2)));;

e(ASSUME_TAC (ONCE_REWRITE_RULE [T_SYM_THM] 
      (SPECL ["eventually U";"eventually V"] T_LEM7)));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_EQ_IMP_TRANS1)
       (CONJ (el 2 thms) (el 1 thms))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [(MATCH_MP (T_EQ_IMP_TRANS2)
       (CONJ (el 4 thms) (el 1 thms)))])));;

----------------------------------------------------------------%

let HF_DIST_IMP = prove_thm(`HF_DIST_IMP`,
"!U V. (VALID ((henceforth (U Imp V)) Imp 
           ((eventually U) Imp (eventually V))))",
REPEAT GEN_TAC
THEN ASSUME_TAC (MATCH_MP HF_HF_RULE 
      (SPECL ["U:num->bool";"V:num->bool"] T_LEM7))
THEN ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] (SPECL ["Not V";"Not U"] A2))
THEN ASSUME_TAC (ONCE_REWRITE_RULE [T_SYM_THM] 
      (SPECL ["eventually U";"eventually V"] T_LEM7))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_EQ_IMP_TRANS1)
       (CONJ (el 2 thms) (el 1 thms)))))
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [(MATCH_MP (T_EQ_IMP_TRANS2)
       (CONJ (el 4 thms) (el 1 thms)))])));;

%----------------------------------------------------------------
T7:henceforth distributes over And
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. (henceforth (U And V)) = 
   ((henceforth U) And (henceforth V))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(REWRITE_TAC [REWRITE_RULE [VALID;Imp] (MATCH_MP (T_IMP_IMP_CONJ) 
     (CONJ (MATCH_MP (HF_HF_IMP_RULE)
        (SPECL ["U:num->bool";"V:num->bool"] T_AND1_THM))
         (MATCH_MP (HF_HF_IMP_RULE)
        (SPECL ["U:num->bool";"V:num->bool"] T_AND2_THM))))]);;

e(ASSUME_TAC (MATCH_MP (T_IMP_TRANS)
     (CONJ (MATCH_MP (HF_HF_IMP_RULE)
          (SPECL ["U:num->bool";"V:num->bool"] T_LEM11))
           (SPECL ["V:num->bool";"U And V"] A2))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp] 
     (REWRITE_RULE [GEN_ALL (MATCH_MP (T_EQUIV_EXPAND)
               (SPEC_ALL T_LEM2))] (el 1 thms))])));;

set_goal([],"!U V. (VALID ((henceforth (U And V)) Equiv 
   ((henceforth U) And (henceforth V))))");;

e(REPEAT GEN_TAC);;

e(ONCE_REWRITE_TAC[SYM_RULE HF_DIST_AND_S]);;

e(REWRITE_TAC[T_REFL_THM]);;

----------------------------------------------------------------%

let HF_DIST_AND_S = prove_thm (`HF_DIST_AND_S`,
"!U V. (henceforth (U And V)) = ((henceforth U) And (henceforth V))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  REWRITE_TAC [REWRITE_RULE [VALID;Imp] (MATCH_MP (T_IMP_IMP_CONJ) 
     (CONJ (MATCH_MP (HF_HF_IMP_RULE)
        (SPECL ["U:num->bool";"V:num->bool"] T_AND1_THM))
         (MATCH_MP (HF_HF_IMP_RULE)
        (SPECL ["U:num->bool";"V:num->bool"] T_AND2_THM))))]
  ;
  ASSUME_TAC (MATCH_MP (T_IMP_TRANS)
     (CONJ (MATCH_MP (HF_HF_IMP_RULE)
          (SPECL ["U:num->bool";"V:num->bool"] T_LEM11))
           (SPECL ["V:num->bool";"U And V"] A2)))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp] 
     (REWRITE_RULE [GEN_ALL (MATCH_MP (T_EQUIV_EXPAND)
               (SPEC_ALL T_LEM2))] (el 1 thms))]))
  ]);;

let HF_DIST_AND = prove_thm(`HF_DIST_AND`,
"!U V. VALID ((henceforth (U And V)) Equiv 
        ((henceforth U) And (henceforth V)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC[SYM_RULE HF_DIST_AND_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
T8:eventually distributes over Or.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. (eventually (U Or V)) = 
          ((eventually U) Or (eventually V))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] 
      (MATCH_MP (HF_HF_RULE) (SPECL ["U:num->bool";"V:num->bool"] 
           (BOOL_TO_TEMP (GEN_ALL (CONJUNCT2 (SPEC_ALL DE_MORGAN_THM))))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [NOT_NOT_RULE;Equiv;VALID]
      (ONCE_REWRITE_RULE [T_NOT_APPLICATION] (el 1 thms))])));;

e(ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] 
      (ONCE_REWRITE_RULE [T_NOT_APPLICATION] 
        (SPECL ["Not U";"Not V"] HF_DIST_AND))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv]
      (REWRITE_RULE [T_DE_MORGAN_THM;NOT_NOT_RULE] (el 1 thms))])));;

set_goal([],"!U V. VALID ((eventually (U Or V)) Equiv 
          ((eventually U) Or (eventually V)))");;

e(ONCE_REWRITE_TAC[EV_DIST_OR_S]);;

e(REWRITE_TAC[T_REFL_THM]);;

----------------------------------------------------------------%

let EV_DIST_OR_S = prove_thm (`EV_DIST_OR_S`,
"!U V. (eventually (U Or V)) = ((eventually U) Or (eventually V))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] 
      (MATCH_MP (HF_HF_RULE) (SPECL ["U:num->bool";"V:num->bool"] 
           (BOOL_TO_TEMP (GEN_ALL (CONJUNCT2 (SPEC_ALL DE_MORGAN_THM)))))))
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [NOT_NOT_RULE;
    Equiv;VALID] (ONCE_REWRITE_RULE [T_NOT_APPLICATION] (el 1 thms))]))
THEN ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] 
      (ONCE_REWRITE_RULE [T_NOT_APPLICATION] 
        (SPECL ["Not U";"Not V"] HF_DIST_AND)))
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv]
      (REWRITE_RULE [T_DE_MORGAN_THM;NOT_NOT_RULE] (el 1 thms))])));;

let EV_DIST_OR = prove_thm (`EV_DIST_OR`,
"!U V. VALID ((eventually (U Or V)) Equiv ((eventually U) Or (eventually V)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC[EV_DIST_OR_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
T9:henceforth over Or is only one way
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID (((henceforth U) Or (henceforth V)) Imp
      (henceforth (U Or V)))");;

e(REPEAT GEN_TAC);;

e(REWRITE_TAC [SYM_RULE (T_REWRITE_EQUIV_RULE T_LEM12)]);;

e(MATCH_MP_TAC T_AND_COMB);;

e(ACCEPT_TAC (CONJ (MATCH_MP HF_HF_IMP_RULE 
   (SPECL ["U:num->bool";"V:num->bool"] T_OR_INTRO_THM1))
     (MATCH_MP HF_HF_IMP_RULE 
   (SPECL ["V:num->bool";"U:num->bool"] T_OR_INTRO_THM2))));;

----------------------------------------------------------------%

let HF_DIST_OR = prove_thm(`HF_DIST_OR`,
"!U V. VALID (((henceforth U) Or (henceforth V)) Imp (henceforth (U Or V)))",
REPEAT GEN_TAC
THEN REWRITE_TAC [SYM_RULE (T_REWRITE_EQUIV_RULE T_LEM12)]
THEN MATCH_MP_TAC T_AND_COMB
THEN ACCEPT_TAC (CONJ (MATCH_MP HF_HF_IMP_RULE 
   (SPECL ["U:num->bool";"V:num->bool"] T_OR_INTRO_THM1))
     (MATCH_MP HF_HF_IMP_RULE 
   (SPECL ["V:num->bool";"U:num->bool"] T_OR_INTRO_THM2))));;

%----------------------------------------------------------------
T10:eventually over And is also one way
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID ((eventually (U And V)) Imp 
       ((eventually U) And (eventually V)))");;

e(REPEAT GEN_TAC);;

e(REWRITE_TAC [SYM_RULE (T_REWRITE_EQUIV_RULE T_LEM10)]);;

e(MATCH_MP_TAC T_AND_COMB);;

e(ACCEPT_TAC (CONJ (MATCH_MP EV_EV_IMP_RULE 
    (SPECL ["U:num->bool";"V:num->bool"] T_AND1_THM))
      (MATCH_MP EV_EV_IMP_RULE 
    (SPECL ["U:num->bool";"V:num->bool"] T_AND2_THM))));;

----------------------------------------------------------------%

let EV_DIST_AND = prove_thm (`EV_DIST_AND`,
"!U V. VALID((eventually (U And V)) Imp ((eventually U) And (eventually V)))",
REPEAT GEN_TAC
THEN REWRITE_TAC [SYM_RULE (T_REWRITE_EQUIV_RULE T_LEM10)]
THEN MATCH_MP_TAC T_AND_COMB
THEN ACCEPT_TAC (CONJ (MATCH_MP EV_EV_IMP_RULE 
    (SPECL ["U:num->bool";"V:num->bool"] T_AND1_THM))
      (MATCH_MP EV_EV_IMP_RULE 
    (SPECL ["U:num->bool";"V:num->bool"] T_AND2_THM))));;

%----------------------------------------------------------------
eventually and henceforth mixed over And
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID (((henceforth U) And (eventually V)) Imp
    (eventually (U And V)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (MATCH_MP (HF_HF_IMP_RULE) 
 (SPECL ["U:num->bool";"V:num->bool"] T_LEM11)));;

e(ASSUME_TAC (SPECL ["V:num->bool";"U And V"] HF_DIST_IMP));;

e(REWRITE_TAC[SYM_RULE (GEN_ALL (T_REWRITE_EQUIV_RULE 
   T_LEM2))]);;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS)
   (CONJ (el 2 thms) (el 1 thms))))));;

----------------------------------------------------------------%

let HF_EV_AND_DIST = prove_thm (`HF_EV_AND_DIST`,
"!U V. VALID(((henceforth U) And (eventually V)) Imp (eventually (U And V)))",
REPEAT GEN_TAC
THEN ASSUME_TAC (MATCH_MP (HF_HF_IMP_RULE) 
   (SPECL ["U:num->bool";"V:num->bool"] T_LEM11))
THEN ASSUME_TAC (SPECL ["V:num->bool";"U And V"] HF_DIST_IMP)
THEN REWRITE_TAC[SYM_RULE (GEN_ALL (T_REWRITE_EQUIV_RULE T_LEM2))]
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS)
   (CONJ (el 2 thms) (el 1 thms))))));;

%----------------------------------------------------------------
next distributes over And
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID ((next (U And V)) Equiv ((next U) And (next V)))");;

set_goal([],"!U V. (next (U And V)) = ((next U) And (next V))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(ASSUME_TAC (MATCH_MP (T_AND_COMB) (CONJ 
    (MATCH_MP (N_N_IMP_RULE) 
      (SPECL ["U:num->bool";"V:num->bool"] T_AND1_THM))
    (MATCH_MP (N_N_IMP_RULE) 
      (SPECL ["U:num->bool";"V:num->bool"] T_AND2_THM)))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC[REWRITE_RULE [VALID;Imp] 
    (REWRITE_RULE [GEN_ALL (T_REWRITE_EQUIV_RULE 
         T_LEM10)] (el 1 thms))])));;

e(ASSUME_TAC (MATCH_MP (N_N_IMP_RULE)
    (SPECL ["U:num->bool";"V:num->bool"] T_LEM11)));;

e(ASSUME_TAC (SPECL ["V:num->bool";"U And V"] A5));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS)
  (CONJ (el 2 thms) (el 1 thms))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp] 
   (REWRITE_RULE [(GEN_ALL (T_REWRITE_EQUIV_RULE T_LEM2))]
       (el 1 thms))])));;

----------------------------------------------------------------%

let N_DIST_AND_S = prove_thm (`N_DIST_AND_S`,
"!U V. (next (U And V)) = ((next U) And (next V))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
   ASSUME_TAC (MATCH_MP (T_AND_COMB) (CONJ 
    (MATCH_MP (N_N_IMP_RULE) 
      (SPECL ["U:num->bool";"V:num->bool"] T_AND1_THM))
    (MATCH_MP (N_N_IMP_RULE) 
      (SPECL ["U:num->bool";"V:num->bool"] T_AND2_THM))))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC[REWRITE_RULE [VALID;Imp] 
    (REWRITE_RULE [GEN_ALL (T_REWRITE_EQUIV_RULE 
         T_LEM10)] (el 1 thms))]))
  ;
  ASSUME_TAC (MATCH_MP (N_N_IMP_RULE)
    (SPECL ["U:num->bool";"V:num->bool"] T_LEM11))
  THEN ASSUME_TAC (SPECL ["V:num->bool";"U And V"] A5)
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS)
    (CONJ (el 2 thms) (el 1 thms)))))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp] 
    (REWRITE_RULE [(GEN_ALL (T_REWRITE_EQUIV_RULE T_LEM2))]
       (el 1 thms))]))
  ]);;

let N_DIST_AND = prove_thm (`N_DIST_AND`,
"!U V. VALID ((next (U And V)) Equiv ((next U) And (next V)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC[SYM_RULE N_DIST_AND_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
next distributes over Or
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID ((next (U Or V)) Equiv ((next U) Or (next V)))");;

set_goal([],"!U V. (next (U Or V)) = ((next U) Or (next V))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE[SYM_RULE A4_S;SYM_RULE (CONJUNCT2 
       T_DE_MORGAN_THM)] (SPECL ["Not U";"Not V"] N_DIST_AND)));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv]
  (REWRITE_RULE [SYM_RULE T_NOT_APPLICATION] (el 1 thms))])));;

----------------------------------------------------------------%

let N_DIST_OR_S = prove_thm(`N_DIST_OR_S`,
"!U V. (next (U Or V)) = ((next U) Or (next V))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE[SYM_RULE A4_S;SYM_RULE (CONJUNCT2 
       T_DE_MORGAN_THM)] (SPECL ["Not U";"Not V"] N_DIST_AND))
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv]
    (REWRITE_RULE [SYM_RULE T_NOT_APPLICATION] (el 1 thms))])));;

let N_DIST_OR = prove_thm(`N_DIST_OR`,
"!U V. VALID ((next (U Or V)) Equiv ((next U) Or (next V)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC[N_DIST_OR_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
next distributes over Imp
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. VALID ((next (U Imp V)) Equiv ((next U) Imp (next V)))");;

set_goal([],"!U V.(next (U Imp V)) = ((next U) Imp (next V))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(REWRITE_TAC [REWRITE_RULE [VALID;Equiv] (REWRITE_RULE 
    [SPEC "U:num->bool" (SYM_RULE A4_S); T_IMP_DISJ_THM]
      (SPECL ["Not U";"V:num->bool"] (N_DIST_OR)))]);;

----------------------------------------------------------------%

let N_DIST_IMP_S = prove_thm(`N_DIST_IMP_S`,
"!U V. (next (U Imp V)) = ((next U) Imp (next V))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN REWRITE_TAC [REWRITE_RULE [VALID;Equiv] (REWRITE_RULE 
    [SPEC "U:num->bool" (SYM_RULE A4_S); T_IMP_DISJ_THM]
      (SPECL ["Not U";"V:num->bool"] (N_DIST_OR)))]);;

let N_DIST_IMP = prove_thm(`N_DIST_IMP`,
"!U V. VALID ((next (U Imp V)) Equiv ((next U) Imp (next V)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC [N_DIST_IMP_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
next distributes over Equiv
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. (next (U Equiv V)) = ((next U) Equiv (next V))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (ONCE_REWRITE_RULE[VALID] (REWRITE_RULE 
   [T_IMP_IMP_EQ_S;SYM_RULE N_DIST_AND_S] (MATCH_MP (T_AND_INJECTION)
    (CONJ (SPEC_ALL N_DIST_IMP) (SPECL ["V:num->bool";"U:num->bool"]
     N_DIST_IMP))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [ONCE_REWRITE_RULE 
    [Equiv] (el 1 thms)])));;

----------------------------------------------------------------%

let N_DIST_EQUIV_S = prove_thm (`N_DIST_EQUIV_S`,
"!U V. (next (U Equiv V)) = ((next U) Equiv (next V))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (ONCE_REWRITE_RULE[VALID] (REWRITE_RULE 
   [T_IMP_IMP_EQ_S;SYM_RULE N_DIST_AND_S] (MATCH_MP (T_AND_INJECTION)
    (CONJ (SPEC_ALL N_DIST_IMP) (SPECL ["V:num->bool";"U:num->bool"]
     N_DIST_IMP)))))
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [ONCE_REWRITE_RULE 
    [Equiv] (el 1 thms)])));;

let N_DIST_EQUIV = prove_thm(`N_DIST_EQUIV`,
"!U V. VALID ((next (U Equiv V)) Equiv ((next U) Equiv (next V)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC[N_DIST_EQUIV_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
next is commutative with henceforth and eventually.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. (next (henceforth U)) = (henceforth (next U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(REWRITE_TAC[REWRITE_RULE [VALID;Imp] (MATCH_MP (T_IMP_TRANS) (CONJ
    (MATCH_MP (T_INDUCTION_RULE) (MATCH_MP (N_N_IMP_RULE) 
      (SPEC "U:num->bool" A7)))
    (MATCH_MP (HF_HF_IMP_RULE) (MATCH_MP (N_N_IMP_RULE) 
      (SPEC "U:num->bool" A3)))))]);;
 
e(ASSUME_TAC (MATCH_MP (HF_HF_IMP_RULE)
   (SPECL ["next U";"U:num->bool"] T_LEM13)));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
  (el 1 thms) (SPEC "U Imp (next U)" A7))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [N_DIST_IMP_S] 
  (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms) 
      (MATCH_MP (N_N_IMP_RULE) (SPEC "U:num->bool" A8))))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE[VALID;Imp] 
   (MATCH_MP (T_IMP_RES_THM) (CONJ (el 1 thms) (SPEC "next U" A3)))])));;

----------------------------------------------------------------%

let N_HF_COMM_S = prove_thm(`N_HF_COMM_S`,
"!U. (next (henceforth U)) = (henceforth (next U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  REWRITE_TAC[REWRITE_RULE [VALID;Imp] (MATCH_MP (T_IMP_TRANS) (CONJ
    (MATCH_MP (T_INDUCTION_RULE) (MATCH_MP (N_N_IMP_RULE) 
      (SPEC "U:num->bool" A7)))
    (MATCH_MP (HF_HF_IMP_RULE) (MATCH_MP (N_N_IMP_RULE) 
      (SPEC "U:num->bool" A3)))))]
  ;
  ASSUME_TAC (MATCH_MP (HF_HF_IMP_RULE)
   (SPECL ["next U";"U:num->bool"] T_LEM13))
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
    (el 1 thms) (SPEC "U Imp (next U)" A7)))))
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [N_DIST_IMP_S] 
    (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms) 
      (MATCH_MP (N_N_IMP_RULE) (SPEC "U:num->bool" A8)))))))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE[VALID;Imp] 
     (MATCH_MP (T_IMP_RES_THM) (CONJ (el 1 thms) (SPEC "next U" A3)))]))
  ]);;

let N_HF_COMM = prove_thm(`N_HF_COMM`,
"!U. VALID((next (henceforth U)) Equiv (henceforth (next U)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[N_HF_COMM_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!U. (next (eventually U)) = (eventually (next U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S;SYM_RULE A4_S] 
   (SPEC "Not U" N_HF_COMM_S)));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [Not] (CONV_RULE 
   FUN_EQ_CONV (el 1 thms))))));;

e(ASM_CASES_TAC "eventually(next U)n");;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
   (SPEC_ALL (el 2 thms))])));;

----------------------------------------------------------------%

let N_EV_COMM_S = prove_thm(`N_EV_COMM_S`,
"!U. (next (eventually U)) = (eventually (next U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S;SYM_RULE A4_S] 
   (SPEC "Not U" N_HF_COMM_S))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [Not] (CONV_RULE 
   FUN_EQ_CONV (el 1 thms)))))
THEN ASM_CASES_TAC "eventually(next U)n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
   (SPEC_ALL (el 2 thms))])));;

let N_EV_COMM = prove_thm (`N_EV_COMM`,
"!U. VALID((next (eventually U)) Equiv (eventually (next U)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[N_EV_COMM_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
reducing a string of eventually and henceforth over each other
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. (henceforth (eventually (henceforth U))) =
  (eventually (henceforth U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(REWRITE_TAC[REWRITE_RULE[VALID;Imp] 
   (SPEC "(eventually (henceforth U))" A3)]);;

e(REWRITE_TAC [REWRITE_RULE [VALID;Imp] (MATCH_MP (T_INDUCTION_RULE)
    (REWRITE_RULE[SYM_RULE N_EV_COMM_S] (MATCH_MP (EV_EV_IMP_RULE)
    (SPEC "U:num->bool" A7))))]);;

----------------------------------------------------------------%

let HF_EV_STRING_S = prove_thm(`HF_EV_STRING_S`,
"!U. (henceforth (eventually (henceforth U))) = (eventually (henceforth U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  REWRITE_TAC[REWRITE_RULE[VALID;Imp] 
   (SPEC "(eventually (henceforth U))" A3)]
  ;
  REWRITE_TAC [REWRITE_RULE [VALID;Imp] (MATCH_MP (T_INDUCTION_RULE)
    (REWRITE_RULE[SYM_RULE N_EV_COMM_S] (MATCH_MP (EV_EV_IMP_RULE)
    (SPEC "U:num->bool" A7))))]
  ]);;

let HF_EV_STRING = prove_thm(`HF_EV_STRING`,
"!U. VALID((henceforth (eventually (henceforth U))) Equiv 
  (eventually (henceforth U)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[HF_EV_STRING_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!U. (eventually (henceforth (eventually U))) = 
    (henceforth (eventually U))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE [Not] (CONV_RULE FUN_EQ_CONV (REWRITE_RULE 
   [SYM_RULE A1_S;SYM_RULE A1_INV_S] (SPEC "Not U" HF_EV_STRING_S)))));;

e(ASM_CASES_TAC "henceforth (eventually U)n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
   (SPEC_ALL (el 2 thms))])));;

----------------------------------------------------------------%

let EV_HF_STRING_S = prove_thm(`EV_HF_STRING_S`,
"!U. (eventually (henceforth (eventually U))) = (henceforth (eventually U))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE [Not] (CONV_RULE FUN_EQ_CONV (REWRITE_RULE 
   [SYM_RULE A1_S;SYM_RULE A1_INV_S] (SPEC "Not U" HF_EV_STRING_S))))
THEN ASM_CASES_TAC "henceforth (eventually U)n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
   (SPEC_ALL (el 2 thms))])));;

let EV_HF_STRING = prove_thm(`EV_HF_STRING`,
"!U. VALID((eventually (henceforth (eventually U))) Equiv
    (henceforth (eventually U)))",
GEN_TAC
THEN ONCE_REWRITE_TAC[EV_HF_STRING_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
fixpoint character of henceforth and eventually
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. (henceforth U) = (U And (next (henceforth U)))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(REWRITE_TAC[REWRITE_RULE [VALID;Imp] (MATCH_MP (T_IMP_IMP_CONJ)
   (CONJ (SPEC "U:num->bool" A3) (SPEC "U:num->bool" A7)))]);;

e(ASSUME_TAC (MATCH_MP (N_N_IMP_RULE) (MATCH_MP (T_IMP_IMP_CONJ) 
   (CONJ (SPEC "U:num->bool" A3) (SPEC "U:num->bool" A7)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["U:num->bool";"next (henceforth U)"] T_AND2_THM)
   (el 1 thms))))));;

e(IMP_RES_TAC T_INDUCTION_RULE);;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms)
   (MATCH_MP (HF_HF_IMP_RULE) (SPECL ["U:num->bool";"next (henceforth U)"]
   T_AND1_THM)))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp]
   (el 1 thms)])));;

----------------------------------------------------------------%

let HF_FIXPT_S = prove_thm(`HF_FIXPT_S`,
"!U. (henceforth U) = (U And (next (henceforth U)))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  REWRITE_TAC[REWRITE_RULE [VALID;Imp] (MATCH_MP (T_IMP_IMP_CONJ)
   (CONJ (SPEC "U:num->bool" A3) (SPEC "U:num->bool" A7)))]
  ;
  ASSUME_TAC (MATCH_MP (N_N_IMP_RULE) (MATCH_MP (T_IMP_IMP_CONJ) 
   (CONJ (SPEC "U:num->bool" A3) (SPEC "U:num->bool" A7))))
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["U:num->bool";"next (henceforth U)"] T_AND2_THM)
   (el 1 thms)))))
  THEN IMP_RES_TAC T_INDUCTION_RULE
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (el 1 thms) (MATCH_MP (HF_HF_IMP_RULE) (SPECL ["U:num->bool";
    "next (henceforth U)"] T_AND1_THM))))))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp]
   (el 1 thms)]))
  ]);;

let HF_FIXPT = prove_thm(`HF_FIXPT`,
"!U. VALID ((henceforth U) Equiv (U And (next (henceforth U))))",
GEN_TAC
THEN ONCE_REWRITE_TAC[SYM_RULE HF_FIXPT_S]
THEN REWRITE_TAC [T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!U. (eventually U) = (U Or (next (eventually U)))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE[SYM_RULE (CONJUNCT2  
   T_DE_MORGAN_THM)] ( REWRITE_RULE[SYM_RULE A1_S;SYM_RULE A4_S] 
   (SPEC "Not U" HF_FIXPT_S))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [Not] 
   (CONV_RULE FUN_EQ_CONV (el 1 thms))))));;

e(ASM_CASES_TAC "(eventually U)n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
   (SPEC_ALL (el 2 thms))])));;

----------------------------------------------------------------%

let EV_FIXPT_S = prove_thm (`EV_FIXPT_S`,
"!U. (eventually U) = (U Or (next (eventually U)))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE[SYM_RULE (CONJUNCT2
   T_DE_MORGAN_THM)] ( REWRITE_RULE[SYM_RULE A1_S;SYM_RULE A4_S] 
   (SPEC "Not U" HF_FIXPT_S)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [Not] 
   (CONV_RULE FUN_EQ_CONV (el 1 thms)))))
THEN ASM_CASES_TAC "(eventually U)n"
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [el 1 thms] 
   (SPEC_ALL (el 2 thms))])));;

let EV_FIXPT = prove_thm(`EV_FIXPT`,
"!U. VALID ((eventually U) Equiv (U Or (next (eventually U))))",
GEN_TAC
THEN ONCE_REWRITE_TAC [SYM_RULE EV_FIXPT_S]
THEN REWRITE_TAC [T_REFL_THM]);;

%----------------------------------------------------------------
dual of computational induction
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U. VALID((U And (eventually (Not U))) Imp 
   (eventually (U And (next (Not U)))))");;

e(GEN_TAC);;

e(REWRITE_TAC[REWRITE_RULE [NOT_NOT_RULE;T_IMP_DISJ_THM;A4_S] (
   REWRITE_RULE [A1_INV_S;(CONJUNCT2  
   T_DE_MORGAN_THM)] (REWRITE_RULE[A1_INV_S;SYM_RULE T_IMP_DISJ_THM] (
   ONCE_REWRITE_RULE [GEN_ALL (T_REWRITE_EQUIV_RULE T_LEM7)]
   (SPEC "U:num->bool" A8))))]);;

----------------------------------------------------------------%

let T_INDUCTION_DUAL = prove_thm (`T_INDUCTION_DUAL`,
"!U. VALID((U And (eventually (Not U))) Imp 
   (eventually (U And (next (Not U)))))",
GEN_TAC
THEN REWRITE_TAC[REWRITE_RULE [NOT_NOT_RULE;T_IMP_DISJ_THM;A4_S] (
   REWRITE_RULE [A1_INV_S;(CONJUNCT2  
   T_DE_MORGAN_THM)] (REWRITE_RULE[A1_INV_S;SYM_RULE T_IMP_DISJ_THM] (
   ONCE_REWRITE_RULE [GEN_ALL (T_REWRITE_EQUIV_RULE T_LEM7)]
   (SPEC "U:num->bool" A8))))]);;

%----------------------------------------------------------------
consequence rules for henceforth, eventually, and next
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U1 U2 V1 V2. (VALID (U1 Imp U2)) /\ 
  (VALID (U2 Imp (next V1))) /\ (VALID (V1 Imp V2)) ==>
  (VALID (U1 Imp (next V2)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(ASSUME_TAC (SPECL ["V1:num->bool";"V2:num->bool"] HF_HF_IMP_RULE));;

e(RES_TAC);;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 5 thms)
  (el 4 thms))))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms)
  (el 2 thms))))));;

----------------------------------------------------------------%

let HF_CONSEQUENCE = prove_thm (`HF_CONSEQUENCE`,
"!U1 U2 V1 V2. (VALID (U1 Imp U2)) /\ (VALID (U2 Imp (henceforth V1))) /\ 
  (VALID (V1 Imp V2)) ==> (VALID (U1 Imp (henceforth V2)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC (SPECL ["V1:num->bool";"V2:num->bool"] HF_HF_IMP_RULE)
THEN RES_TAC
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 5 thms)
  (el 4 thms)))))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms)
  (el 2 thms))))));;

let EV_CONSEQUENCE = prove_thm (`EV_CONSEQUENCE`,
"!U1 U2 V1 V2. (VALID (U1 Imp U2)) /\ (VALID (U2 Imp (eventually V1))) /\ 
  (VALID (V1 Imp V2)) ==> (VALID (U1 Imp (eventually V2)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC (SPECL ["V1:num->bool";"V2:num->bool"] EV_EV_IMP_RULE)
THEN RES_TAC
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 5 thms)
  (el 4 thms)))))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms)
  (el 2 thms))))));;

let N_CONSEQUENCE = prove_thm (`N_CONSEQUENCE`,
"!U1 U2 V1 V2. (VALID (U1 Imp U2)) /\ (VALID (U2 Imp (next V1))) /\ 
  (VALID (V1 Imp V2)) ==> (VALID (U1 Imp (next V2)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC (SPECL ["V1:num->bool";"V2:num->bool"] N_N_IMP_RULE)
THEN RES_TAC
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 5 thms)
  (el 4 thms)))))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms)
  (el 2 thms))))));;

%----------------------------------------------------------------
concatenation rules for henceforth and eventually
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V W. (VALID (U Imp (henceforth V))) /\ 
   (VALID (V Imp (henceforth W))) ==> (VALID (U Imp (henceforth W)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(IMP_RES_TAC HF_HF_IMP_RULE);;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [SYM_RULE HF_IDEMPOTENT_S]
   (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms) (el 2 thms)))))));;
  
----------------------------------------------------------------%

let HF_CONCAT = prove_thm(`HF_CONCAT`,
"!U V W. (VALID (U Imp (henceforth V))) /\ (VALID (V Imp (henceforth W))) 
  ==> (VALID (U Imp (henceforth W)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN IMP_RES_TAC HF_HF_IMP_RULE
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [SYM_RULE HF_IDEMPOTENT_S]
   (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms) (el 2 thms)))))));;

let EV_CONCAT = prove_thm(`EV_CONCAT`,
"!U V W. (VALID (U Imp (eventually V))) /\ (VALID (V Imp (eventually W))) 
  ==> (VALID (U Imp (eventually W)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN IMP_RES_TAC EV_EV_IMP_RULE
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [SYM_RULE EV_IDEMPOTENT_S]
   (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms) (el 2 thms)))))));;

%----------------------------------------------------------------
right until introduction
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V W. (VALID (W Imp (eventually V))) /\
  (VALID (W Imp (V Or (U And (next W))))) ==>
     (VALID (W Imp (U until V)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(REWRITE_TAC[SYM_RULE T_IMP_DISJ_THM]);;

e(ONCE_REWRITE_TAC[SYM_RULE (SPEC "U until V" NOT_NOT_RULE)]);;

e(ONCE_REWRITE_TAC[SYM_RULE T_DE_MORGAN_THM1]);;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE[
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] (A9))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM;A4_S]
  (ONCE_REWRITE_RULE [T_CONTRAPOS] thm)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE 
   T_LEM14a)) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;T_AND_SIMP;
   T_OR_F;T_AND_F; T_AND_DIST_R] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC] (
  ONCE_REWRITE_RULE[T_AND_SYM] (REWRITE_RULE [T_AND_DIST_L] thm))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] (
   REWRITE_RULE [(REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" T_AND_SIMP));
   T_OR_F;T_AND_F] thm)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC] (
  ONCE_REWRITE_RULE [(SPECL ["(next (Not (U until V)) And U)";"next W"]
   T_AND_SYM)] thm)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm (
   SPECL ["(((Not V) And (next W)) And (next (Not (U until V))))";
    "U:num->bool"] T_AND1_THM))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
    SYM_RULE N_DIST_AND_S] thm))));;

e(IMP_RES_TAC T_DER_INDUCTION_RULE);;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] thm))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["W:num->bool";"(Not(U until V))"] T_AND1_THM)
   (el 5 thms))))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_AND_SIMP;T_IMP_F]
  (MATCH_MP (T_IMP_IMP_CONJ) (CONJ (el 1 thms) (el 2 thms)))))));;

----------------------------------------------------------------%

let R_UNT_INTRO = prove_thm(`R_UNT_INTRO`,
"!U V W. (VALID (W Imp (eventually V))) /\ 
  (VALID (W Imp (V Or (U And (next W))))) ==> (VALID (W Imp (U until V)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN REWRITE_TAC[SYM_RULE T_IMP_DISJ_THM]
THEN ONCE_REWRITE_TAC[SYM_RULE (SPEC "U until V" NOT_NOT_RULE)]
THEN ONCE_REWRITE_TAC[SYM_RULE T_DE_MORGAN_THM1]
THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE[
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] (A9)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM;A4_S]
  (ONCE_REWRITE_RULE [T_CONTRAPOS] thm))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE 
   T_LEM14a)) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;T_AND_SIMP;
   T_OR_F;T_AND_F; T_AND_DIST_R] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC] (
  ONCE_REWRITE_RULE[T_AND_SYM] (REWRITE_RULE [T_AND_DIST_L] thm)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] (
   REWRITE_RULE [(REWRITE_RULE [NOT_NOT_RULE] (SPEC "Not U" T_AND_SIMP));
   T_OR_F;T_AND_F] thm))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC] (
  ONCE_REWRITE_RULE [(SPECL ["(next (Not (U until V)) And U)";"next W"]
   T_AND_SYM)] thm))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm (
   SPECL ["(((Not V) And (next W)) And (next (Not (U until V))))";
    "U:num->bool"] T_AND1_THM)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
    SYM_RULE N_DIST_AND_S] thm)))
THEN IMP_RES_TAC T_DER_INDUCTION_RULE
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] thm)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["W:num->bool";"(Not(U until V))"] T_AND1_THM)
   (el 5 thms)))))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_AND_SIMP;T_IMP_F]
  (MATCH_MP (T_IMP_IMP_CONJ) (CONJ (el 1 thms) (el 2 thms)))))));;

%----------------------------------------------------------------
left until introduction
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V W. VALID ((V Or (U And (next W))) Imp W) ==>
VALID ((U until V) Imp W)");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(REWRITE_TAC [SYM_RULE T_IMP_DISJ_THM]);;

e(SUBST1_TAC (SYM_RULE (SPEC "W:num->bool" NOT_NOT_RULE)));;

e(ONCE_REWRITE_TAC [SYM_RULE T_DE_MORGAN_THM1]);;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM;A4_S] 
  (ONCE_REWRITE_RULE [T_CONTRAPOS] thm)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE[
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] (A9))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE
   T_LEM14a)) (MATCH_MP (T_AND_COMB) (CONJ (el 1 thms)
   (el 2 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_R] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;T_AND_SIMP;
    T_AND_F;T_OR_F] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_L] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [(REWRITE_RULE [NOT_NOT_RULE]
   (SPEC "Not U" T_AND_SIMP));T_AND_F;T_OR_F] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm 
   (SPECL ["(((next(Not W)) And U) And (next (U until V)))";
   "Not V"] T_AND1_THM))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_ASSOC] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm 
   (SPECL ["((next (U until V)) And (next (Not W)))";"U:num->bool"]
   T_AND1_THM))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S] thm))));;

e(IMP_RES_TAC T_INDUCTION_RULE);;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE
   T_LEM9b)) (el 4 thms)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (
   (SPECL ["(U until V)";"Not W"] T_AND2_THM)) thm)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (HF_HF_IMP_RULE) thm))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] (MATCH_MP
   (T_IMP_TRANS) (CONJ (el 2 thms) (el 1 thms)))))));;

e(ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (SPECL ["U until V";"Not W"]
   T_AND1_THM) (SPECL ["U:num->bool";"V:num->bool"] A10))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_AND_SIMP;T_IMP_F]
   (MATCH_MP (T_IMP_IMP_CONJ) (CONJ (el 1 thms) (el 2 thms)))))));;

----------------------------------------------------------------%

let L_UNT_INTRO =prove_thm(`L_UNT_INTRO`,
"!U V W. VALID ((V Or (U And (next W))) Imp W) ==> VALID ((U until V) Imp W)",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN REWRITE_TAC [SYM_RULE T_IMP_DISJ_THM]
THEN SUBST1_TAC (SYM_RULE (SPEC "W:num->bool" NOT_NOT_RULE))
THEN ONCE_REWRITE_TAC [SYM_RULE T_DE_MORGAN_THM1]
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM;A4_S] 
  (ONCE_REWRITE_RULE [T_CONTRAPOS] thm))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE[
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] (A9)))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE
   T_LEM14a)) (MATCH_MP (T_AND_COMB) (CONJ (el 1 thms)
   (el 2 thms))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_R] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;T_AND_SIMP;
    T_AND_F;T_OR_F] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_L] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [(REWRITE_RULE [NOT_NOT_RULE]
   (SPEC "Not U" T_AND_SIMP));T_AND_F;T_OR_F] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm 
   (SPECL ["(((next(Not W)) And U) And (next (U until V)))";
   "Not V"] T_AND1_THM)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_ASSOC] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm 
   (SPECL ["((next (U until V)) And (next (Not W)))";"U:num->bool"]
   T_AND1_THM)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S] thm)))
THEN IMP_RES_TAC T_INDUCTION_RULE
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE
   T_LEM9b)) (el 4 thms))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (
   (SPECL ["(U until V)";"Not W"] T_AND2_THM)) thm))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (HF_HF_IMP_RULE) thm)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] (MATCH_MP
   (T_IMP_TRANS) (CONJ (el 2 thms) (el 1 thms))))))
THEN ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (SPECL ["U until V";"Not W"]
   T_AND1_THM) (SPECL ["U:num->bool";"V:num->bool"] A10)))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_AND_SIMP;T_IMP_F]
   (MATCH_MP (T_IMP_IMP_CONJ) (CONJ (el 1 thms) (el 2 thms)))))));;

%----------------------------------------------------------------
until - until rules.
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U1 U2 V1 V2. (VALID (U1 Imp U2)) /\ (VALID (V1 Imp V2)) ==>
   (VALID ((U1 until V1) Imp (U2 until V2)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["U2:num->bool";"V2:num->bool"] A9)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (SPEC "(U2 And (next(U2 until V2)))"
   (GEN_ALL (MATCH_MP (T_REWRITE_IMP_RULE T_LEM15a)
   (el 2 thms)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ
   (el 1 thms) (el 2 thms))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (SPECL ["V1:num->bool";
   "(next(U2 until V2))"] (GEN_ALL (MATCH_MP (T_REWRITE_IMP_RULE
    T_LEM15b) (el 5 thms)))))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (L_UNT_INTRO) (MATCH_MP 
   (T_IMP_TRANS) (CONJ (el 1 thms) (el 2 thms)))))));;

----------------------------------------------------------------%

let U_U_IMP_RULE = prove_thm(`U_U_IMP_RULE`,
"!U1 U2 V1 V2. (VALID (U1 Imp U2)) /\ (VALID (V1 Imp V2)) ==>
   (VALID ((U1 until V1) Imp (U2 until V2)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["U2:num->bool";"V2:num->bool"] A9))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (SPEC "(U2 And (next(U2 until V2)))"
   (GEN_ALL (MATCH_MP (T_REWRITE_IMP_RULE T_LEM15a)
   (el 2 thms))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ
   (el 1 thms) (el 2 thms)))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (SPECL ["V1:num->bool";
   "(next(U2 until V2))"] (GEN_ALL (MATCH_MP (T_REWRITE_IMP_RULE
    T_LEM15b) (el 5 thms))))))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (L_UNT_INTRO) (MATCH_MP 
   (T_IMP_TRANS) (CONJ (el 1 thms) (el 2 thms)))))));;

%----------------------------------------------------------------

set_goal([],"!U1 U2 V1 V2. (VALID (U1 Equiv U2)) /\ (VALID (V1 Equiv V2)) ==>
   (VALID ((U1 until V1) Equiv (U2 until V2)))");;

e(REPEAT GEN_TAC);;

e(REWRITE_TAC[SYM_RULE T_IMP_IMP_EQ_S]);;

e(STRIP_TAC);;

e(IMP_RES_TAC T_AND_EXPAND);;

e(MATCH_MP_TAC T_AND_COMB);;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC[(MATCH_MP (U_U_IMP_RULE) (CONJ
   (el 1 thms) (el 2 thms)));(MATCH_MP (U_U_IMP_RULE) (CONJ (el 3 thms)
   (el 4 thms)))])));;

----------------------------------------------------------------%

let U_U_RULE = prove_thm(`U_U_RULE`,
"!U1 U2 V1 V2. (VALID (U1 Equiv U2)) /\ (VALID (V1 Equiv V2)) ==>
   (VALID ((U1 until V1) Equiv (U2 until V2)))",
REPEAT GEN_TAC
THEN REWRITE_TAC[SYM_RULE T_IMP_IMP_EQ_S]
THEN STRIP_TAC
THEN IMP_RES_TAC T_AND_EXPAND
THEN MATCH_MP_TAC T_AND_COMB
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC[(MATCH_MP (U_U_IMP_RULE) (CONJ
   (el 1 thms) (el 2 thms)));(MATCH_MP (U_U_IMP_RULE) (CONJ (el 3 thms)
   (el 4 thms)))])));;

%----------------------------------------------------------------
other theorems related with the until operator
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!W. ((Not W) until W) = (eventually W)");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(REWRITE_TAC [REWRITE_RULE [VALID;Imp] (SPECL
    ["Not W";"W:num->bool"] A10)]);;

e(REWRITE_TAC[SYM_RULE Imp]);;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPEC "W:num->bool" EV_FIXPT)))));;

e(ASSUME_TAC (REWRITE_RULE [T_IMP_REFL] 
   (SPECL ["Not W";"W:num->bool";"eventually W"] R_UNT_INTRO)));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_OR_DIST_L;
    T_OR_SIMP;T_AND_T] thm))));;

e(RES_TAC);;

e(POP_ASSUM (\thm. (ASM_REWRITE_TAC[ REWRITE_RULE[VALID] thm])));;

----------------------------------------------------------------%

let UNTIL_EQ_EV_S = prove_thm(`UNTIL_EQ_EV_S`,
"!W. ((Not W) until W) = (eventually W)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THEN REWRITE_TAC [REWRITE_RULE [VALID;Imp] (SPECL
    ["Not W";"W:num->bool"] A10)]
THEN REWRITE_TAC[SYM_RULE Imp]
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPEC "W:num->bool" EV_FIXPT))))
THEN ASSUME_TAC (REWRITE_RULE [T_IMP_REFL] 
   (SPECL ["Not W";"W:num->bool";"eventually W"] R_UNT_INTRO))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_OR_DIST_L;
    T_OR_SIMP;T_AND_T] thm)))
THEN RES_TAC
THEN POP_ASSUM (\thm. (ASM_REWRITE_TAC[ REWRITE_RULE[VALID] thm])));;

let UNTIL_EQ_EV = prove_thm(`UNTIL_EQ_EV`,
"!W. VALID(((Not W) until W) Equiv (eventually W))",
GEN_TAC
THEN ONCE_REWRITE_TAC[UNTIL_EQ_EV_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!W1 W2. (VALID (((henceforth W1) And (eventually W2))
  Imp (W1 until W2)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (SPECL ["henceforth W1";"eventually W2"] 
   T_AND2_THM));;

e(ASSUME_TAC (MATCH_MP (T_AND_COMB) (CONJ 
   (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
     T_IMP_IMP_EQ_S] (SPEC "W1:num->bool" HF_FIXPT))))
   (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
     T_IMP_IMP_EQ_S] (SPEC "W2:num->bool" EV_FIXPT)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE 
   T_LEM14a)) thm))));;

e(ASSUM_LIST (\thms. (MATCH_MP_TAC (REWRITE_RULE [el 2 thms] (SPECL 
   ["W1:num->bool";"W2:num->bool";"((henceforth W1) And (eventually W2))"]
    R_UNT_INTRO)))));;

e(REWRITE_TAC[N_DIST_AND_S]);;

e(REWRITE_TAC[T_AND_ASSOC]);;

e(ONCE_REWRITE_TAC[T_OR_DIST_L]);;

e(REWRITE_TAC [SYM_RULE (GEN_ALL (T_REWRITE_EQUIV_RULE 
   T_LEM10))]);;

e(MATCH_MP_TAC T_AND_COMB);;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE (GEN_ALL 
   (T_REWRITE_EQUIV_RULE T_LEM10))] thm))));;

e(IMP_RES_TAC T_AND_EXPAND);;

e(ASM_REWRITE_TAC[]);;

e(ASSUME_TAC (SPECL ["(W1 And (next(henceforth W1)))";
  "W2:num->bool"] T_OR_INTRO_THM2));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (el 3 thms) (el 1 thms))))));;

----------------------------------------------------------------%

let HF_EV_UNT_RULE = prove_thm(`HF_EV_UNT_RULE`,
"!W1 W2. (VALID (((henceforth W1) And (eventually W2)) Imp (W1 until W2)))",
REPEAT GEN_TAC
THEN ASSUME_TAC (SPECL ["henceforth W1";"eventually W2"] T_AND2_THM)
THEN ASSUME_TAC (MATCH_MP (T_AND_COMB) (CONJ 
   (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
     T_IMP_IMP_EQ_S] (SPEC "W1:num->bool" HF_FIXPT))))
   (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
     T_IMP_IMP_EQ_S] (SPEC "W2:num->bool" EV_FIXPT))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE 
   T_LEM14a)) thm)))
THEN ASSUM_LIST (\thms. (MATCH_MP_TAC (REWRITE_RULE [el 2 thms] (SPECL 
   ["W1:num->bool";"W2:num->bool";"((henceforth W1) And (eventually W2))"]
    R_UNT_INTRO))))
THEN REWRITE_TAC[N_DIST_AND_S]
THEN REWRITE_TAC[T_AND_ASSOC]
THEN ONCE_REWRITE_TAC[T_OR_DIST_L]
THEN REWRITE_TAC [SYM_RULE (GEN_ALL (T_REWRITE_EQUIV_RULE 
   T_LEM10))]
THEN MATCH_MP_TAC T_AND_COMB
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE (GEN_ALL 
   (T_REWRITE_EQUIV_RULE T_LEM10))] thm)))
THEN IMP_RES_TAC T_AND_EXPAND
THEN ASM_REWRITE_TAC[]
THEN ASSUME_TAC (SPECL ["(W1 And (next(henceforth W1)))";
  "W2:num->bool"] T_OR_INTRO_THM2)
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (el 3 thms) (el 1 thms))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2. ((W1 until W2) until W2) = (W1 until W2)");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [T_OR_DIST_L;SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1 until W2";"W2:num->bool"]
    A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPECL["(W2 Or (W1 until W2))";"(W2 Or (next((W1 until W2) until W2)))"]
   T_AND1_THM))))));;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["W2:num->bool";"(W1 And (next (W1 until W2)))"]
   T_OR_INTRO_THM1) thm )))));;

e(IMP_RES_TAC (SPECL ["W2:num->bool";"W1 until W2";"W1 until W2"] 
  (GEN_ALL (T_REWRITE_IMP_RULE T_LEM15a))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp;T_OR_SELF]
   (MATCH_MP (T_IMP_TRANS) (CONJ (el 3 thms) (el 1 thms)))])));;

CASE 2

e(ASSUME_TAC (SPECL ["W1:num->bool";"W2:num->bool"] A10));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [thm] (SPECL 
   ["W1 until W2";"W2:num->bool";"W1 until W2"] R_UNT_INTRO)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"]
   A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_OR_DIST_L] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE 
   T_LEM9a)) thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (CONJ (SPECL ["W1 until W2";"W2:num->bool"]
   T_OR_INTRO_THM2) thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [GEN_ALL (T_REWRITE_EQUIV_RULE 
   T_LEM10);SYM_RULE T_OR_DIST_L] (MATCH_MP (T_AND_COMB)
    thm)))));;

e(RES_TAC);;

e(POP_ASSUM (\thm. (ASM_REWRITE_TAC [REWRITE_RULE[VALID;Imp] thm])));;

----------------------------------------------------------------%

let R_UNT_ABSORB_S = prove_thm (`R_UNT_ABSORB_S`,
"!W1 W2. ((W1 until W2) until W2) = (W1 until W2)",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [T_OR_DIST_L;SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1 until W2";"W2:num->bool"]
    A9))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPECL["(W2 Or (W1 until W2))";"(W2 Or (next((W1 until W2) until W2)))"]
   T_AND1_THM)))))
  THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["W2:num->bool";"(W1 And (next (W1 until W2)))"]
   T_OR_INTRO_THM1) thm ))))
  THEN IMP_RES_TAC (SPECL ["W2:num->bool";"W1 until W2";"W1 until W2"] 
  (GEN_ALL (T_REWRITE_IMP_RULE T_LEM15a)))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp;T_OR_SELF]
   (MATCH_MP (T_IMP_TRANS) (CONJ (el 3 thms) (el 1 thms)))]))
  ;
  ASSUME_TAC (SPECL ["W1:num->bool";"W2:num->bool"] A10)
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [thm] (SPECL 
   ["W1 until W2";"W2:num->bool";"W1 until W2"] R_UNT_INTRO))))
  THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"]
   A9))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_OR_DIST_L] thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (GEN_ALL (T_REWRITE_IMP_RULE 
   T_LEM9a)) thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (CONJ (SPECL ["W1 until W2";
    "W2:num->bool"] T_OR_INTRO_THM2) thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [GEN_ALL 
    (T_REWRITE_EQUIV_RULE T_LEM10);SYM_RULE T_OR_DIST_L] 
    (MATCH_MP (T_AND_COMB)  thm))))
  THEN RES_TAC
  THEN POP_ASSUM (\thm. (ASM_REWRITE_TAC [REWRITE_RULE[VALID;Imp] thm]))
  ]);;


let R_UNT_ABSORB = prove_thm (`R_UNT_ABSORB`,
"!W1 W2. VALID(((W1 until W2) until W2) Equiv (W1 until W2))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC[R_UNT_ABSORB_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!W1 W2. (W1 until W2) = (W1 until (W1 until W2))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["W2:num->bool";"(W1 And (next (W1 until W2)))"]
   T_OR_INTRO_THM1) thm )))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ 
   (SPEC "W1:num->bool" T_IMP_REFL) thm)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W1 until W2"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [A9] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_OR_ASSOC] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE A9_S] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_OR_S;
   SYM_RULE T_AND_DIST_L] thm ))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_OR_SELF] (MATCH_MP
   (T_REWRITE_IMP_RULE T_LEM14b) (MATCH_MP (T_AND_COMB)
   (CONJ (el 2 thms) (SPEC "W1 until (W1 until W2)" T_IMP_REFL))))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (N_N_IMP_RULE) thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (SPEC "W1:num->bool"
   T_IMP_REFL) thm))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14b) (MATCH_MP (T_AND_COMB) (CONJ (SPEC "W2:num->bool"
   T_IMP_REFL) thm))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (el 2 thms) (el 1 thms))))));;

e(ASSUME_TAC (SPECL ["W1:num->bool";"W1 until W2"] A10));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE EV_IDEMPOTENT_S]
   (MATCH_MP (T_IMP_TRANS) (CONJ thm (MATCH_MP (EV_EV_IMP_RULE) 
   (SPECL ["W1:num->bool";"W2:num->bool"] A10))))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (R_UNT_INTRO) (CONJ (el 1 thms)
   (el 2 thms))))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv]
   (MATCH_MP (T_IMP_IMP_EQUIV) (CONJ (el 6 thms) (el 1 thms)))])));;

----------------------------------------------------------------%

let L_UNT_ABSORB_S = prove_thm(`L_UNT_ABSORB_S`,
"!W1 W2. (W1 until W2) = (W1 until (W1 until W2))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["W2:num->bool";"(W1 And (next (W1 until W2)))"]
   T_OR_INTRO_THM1) thm ))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ 
   (SPEC "W1:num->bool" T_IMP_REFL) thm))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W1 until W2"] A9))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [A9_S] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_OR_ASSOC] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE A9_S] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_OR_S;
   SYM_RULE T_AND_DIST_L] thm )))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_OR_SELF] (MATCH_MP
   (T_REWRITE_IMP_RULE T_LEM14b) (MATCH_MP (T_AND_COMB)
   (CONJ (el 2 thms) (SPEC "W1 until (W1 until W2)" T_IMP_REFL)))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (N_N_IMP_RULE) thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (SPEC "W1:num->bool"
   T_IMP_REFL) thm)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14b) (MATCH_MP (T_AND_COMB) (CONJ (SPEC "W2:num->bool"
   T_IMP_REFL) thm)))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (el 2 thms) (el 1 thms)))))
THEN ASSUME_TAC (SPECL ["W1:num->bool";"W1 until W2"] A10)
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE EV_IDEMPOTENT_S]
   (MATCH_MP (T_IMP_TRANS) (CONJ thm (MATCH_MP (EV_EV_IMP_RULE) 
   (SPECL ["W1:num->bool";"W2:num->bool"] A10)))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (R_UNT_INTRO) (CONJ (el 1 thms)
   (el 2 thms)))))
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv]
   (MATCH_MP (T_IMP_IMP_EQUIV) (CONJ (el 6 thms) (el 1 thms)))])));;

let L_UNT_ABSORB = prove_thm (`L_UNT_ABSORB`,
"!W1 W2. VALID((W1 until W2) Equiv (W1 until (W1 until W2)))",
REPEAT GEN_TAC
THEN ONCE_REWRITE_TAC [SYM_RULE L_UNT_ABSORB_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
until insertion
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. (VALID V) ==> (VALID (U until V))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["V:num->bool";"(U And (next (U until V)))"]
   T_OR_INTRO_THM1) thm )))));;

e(POP_ASSUM (\thm. (IMP_RES_TAC (T_REWRITE_IMP_RULE thm))));;

----------------------------------------------------------------%

let UNT_INSERT1 = prove_thm(`UNT_INSERT1`,
"!U V. (VALID V) ==> (VALID (U until V))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] A9))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ 
   (SPECL ["V:num->bool";"(U And (next (U until V)))"]
   T_OR_INTRO_THM1) thm ))))
THEN POP_ASSUM (\thm. (IMP_RES_TAC (T_REWRITE_IMP_RULE thm))));;

%----------------------------------------------------------------

set_goal([],"!U V. (VALID U) /\ (VALID (eventually V)) ==>
  (VALID (U until V))");;

e(REPEAT GEN_TAC
THEN STRIP_TAC);;

e(IMP_RES_TAC HF_INSERTION);;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [MATCH_MP (T_REWRITE_IMP_RULE 
   (HF_EV_UNT_RULE)) (MATCH_MP (T_AND_COMB) (CONJ 
   (el 1 thms) (el 3 thms)))])));;

----------------------------------------------------------------%

let UNT_INSERT2 = prove_thm(`UNT_INSERT2`,
"!U V. (VALID U) /\ (VALID (eventually V)) ==> (VALID (U until V))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN IMP_RES_TAC HF_INSERTION
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [MATCH_MP (T_REWRITE_IMP_RULE 
   (HF_EV_UNT_RULE)) (MATCH_MP (T_AND_COMB) (CONJ 
   (el 1 thms) (el 3 thms)))])));;

%----------------------------------------------------------------
until concatenation
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V1 V2 V3. (VALID (V1 Imp (U until V2))) /\
  (VALID (V2 Imp (U until V3))) ==> (VALID (V1 Imp (U until V3)))");;

e(REPEAT GEN_TAC
THEN STRIP_TAC);;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ
   (SPEC "U:num->bool" T_IMP_REFL) thm)))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 2 thms)
  (REWRITE_RULE [SYM_RULE L_UNT_ABSORB_S] (el 1 thms)))))));;

----------------------------------------------------------------%

let UNT_CONCAT = prove_thm(`UNT_CONCAT`,
"!U V1 V2 V3. (VALID (V1 Imp (U until V2))) /\
  (VALID (V2 Imp (U until V3))) ==> (VALID (V1 Imp (U until V3)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ
   (SPEC "U:num->bool" T_IMP_REFL) thm))))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 2 thms)
  (REWRITE_RULE [SYM_RULE L_UNT_ABSORB_S] (el 1 thms)))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID (((henceforth W1) And (W2 until W3)) Imp
  ((W1 And W2) until (W1 And W3))))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (SPECL ["W2:num->bool";"W3:num->bool"] A10));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (SPEC
   "henceforth W1" T_IMP_REFL) thm))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
  (SPECL ["W1:num->bool";"W3:num->bool"] HF_EV_AND_DIST))))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W2:num->bool";"W3:num->bool"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_L] (MATCH_MP
   (T_REWRITE_IMP_RULE T_LEM14a) (MATCH_MP (T_AND_COMB) 
   (CONJ (SPEC "henceforth W1" T_IMP_REFL) thm)))))));;

e(ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a) 
   (MATCH_MP (T_AND_COMB) (CONJ (SPEC "W1:num->bool" A3) (SPEC "W3:num->bool"
   T_IMP_REFL)))));;

e(ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;SYM_RULE N_DIST_AND_S]
   (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a) 
    (MATCH_MP (T_AND_COMB) (CONJ (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (
      REWRITE_RULE [SYM_RULE T_IMP_IMP_EQ_S] (SPEC "W1:num->bool" HF_FIXPT))))
    (SPEC "(next (W2 until W3))" T_IMP_REFL))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a)
   (MATCH_MP (T_AND_COMB) (CONJ thm (SPEC "W2:num->bool" T_IMP_REFL)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE 
   T_AND_ASSOC] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE 
   T_AND_ASSOC] thm))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14b)
   ) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms)
   (el 1 thms))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_ASSOC] thm))));;

e(MATCH_MP_TAC R_UNT_INTRO);;

e(ASM_REWRITE_TAC[]);;

----------------------------------------------------------------%

let HF_AND_UNTIL = prove_thm(`HF_AND_UNTIL`,
"!W1 W2 W3. (VALID (((henceforth W1) And (W2 until W3)) Imp
  ((W1 And W2) until (W1 And W3))))",
REPEAT GEN_TAC
THEN ASSUME_TAC (SPECL ["W2:num->bool";"W3:num->bool"] A10)
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (SPEC
   "henceforth W1" T_IMP_REFL) thm)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
  (SPECL ["W1:num->bool";"W3:num->bool"] HF_EV_AND_DIST)))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [
   SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W2:num->bool";"W3:num->bool"] A9))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_L] (MATCH_MP
   (T_REWRITE_IMP_RULE T_LEM14a) (MATCH_MP (T_AND_COMB) 
   (CONJ (SPEC "henceforth W1" T_IMP_REFL) thm))))))
THEN ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a) 
   (MATCH_MP (T_AND_COMB) (CONJ (SPEC "W1:num->bool" A3) (SPEC "W3:num->bool"
   T_IMP_REFL))))
THEN ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;SYM_RULE N_DIST_AND_S]
   (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a) 
    (MATCH_MP (T_AND_COMB) (CONJ (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (
      REWRITE_RULE [SYM_RULE T_IMP_IMP_EQ_S] (SPEC "W1:num->bool" HF_FIXPT))))
    (SPEC "(next (W2 until W3))" T_IMP_REFL)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a
   ) (MATCH_MP (T_AND_COMB) (CONJ thm (SPEC "W2:num->bool" T_IMP_REFL))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE 
   T_AND_ASSOC] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [SYM_RULE 
   T_AND_ASSOC] thm)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14b
   ) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms) (el 1 thms))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms)
   (el 1 thms)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_ASSOC] thm)))
THEN MATCH_MP_TAC R_UNT_INTRO
THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------
next commutes over until
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!W1 W2. ((next W1) until (next W2)) = (next (W1 until W2))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (REWRITE_RULE [N_DIST_OR_S;N_DIST_AND_S] (MATCH_MP (N_N_RULE) 
   (SPECL ["W1:num->bool";"W2:num->bool"] A9))));;

e(POP_ASSUM (\thm. (ASSUME_LIST_TAC (CONJUNCTS (MATCH_MP (T_AND_EXPAND) 
   (REWRITE_RULE [SYM_RULE T_IMP_IMP_EQ_S] thm))))));;

e(IMP_RES_TAC L_UNT_INTRO);;

e(ASSUME_TAC (REWRITE_RULE [N_EV_COMM_S] (MATCH_MP (N_N_IMP_RULE) (SPECL [
   "W1:num->bool";"W2:num->bool"] A10))));;

e(IMP_RES_TAC R_UNT_INTRO);;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv] 
   (MATCH_MP (T_IMP_IMP_EQUIV) (CONJ (el 4 thms) (el 1 thms)))])));;

----------------------------------------------------------------%

let N_DIST_UNT_S = prove_thm(`N_DIST_UNT_S`,
"!W1 W2. ((next W1) until (next W2)) = (next (W1 until W2))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN ASSUME_TAC (REWRITE_RULE [N_DIST_OR_S;N_DIST_AND_S] (MATCH_MP (N_N_RULE) 
   (SPECL ["W1:num->bool";"W2:num->bool"] A9)))
THEN POP_ASSUM (\thm. (ASSUME_LIST_TAC (CONJUNCTS (MATCH_MP (T_AND_EXPAND) 
   (REWRITE_RULE [SYM_RULE T_IMP_IMP_EQ_S] thm)))))
THEN IMP_RES_TAC L_UNT_INTRO
THEN ASSUME_TAC (REWRITE_RULE [N_EV_COMM_S] (MATCH_MP (N_N_IMP_RULE) (SPECL [
   "W1:num->bool";"W2:num->bool"] A10)))
THEN IMP_RES_TAC R_UNT_INTRO
THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Equiv] 
   (MATCH_MP (T_IMP_IMP_EQUIV) (CONJ (el 4 thms) (el 1 thms)))])));;

let N_DIST_UNT = prove_thm(`N_DIST_UNT`,
"!W1 W2. VALID (((next W1) until (next W2)) Equiv (next (W1 until W2)))",
REPEAT GEN_TAC
THEN REWRITE_TAC[N_DIST_UNT_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------
commutation properties of until
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. ((W1 And W2) until W3) = ((W1 until W3) And
  (W2 until W3))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W1:num->bool";
   "W2:num->bool"] T_AND1_THM) (SPEC "W3:num->bool"
   T_IMP_REFL))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W1:num->bool";
   "W2:num->bool"] T_AND2_THM) (SPEC "W3:num->bool"
   T_IMP_REFL))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC[REWRITE_RULE[VALID;Imp]
   (REWRITE_RULE [T_REWRITE_EQUIV_RULE T_LEM10]
   (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms) (el 1 thms))))])));;

case 2

e(ASSUME_TAC (SPECL ["W1:num->bool";"W3:num->bool"] A10));;

e(ASSUME_TAC (SPECL ["W2:num->bool";"W3:num->bool"] A10));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_AND_SELF] (MATCH_MP 
   (T_REWRITE_IMP_RULE T_LEM14a) (MATCH_MP (T_AND_COMB)
   (CONJ (el 2 thms) (el 1 thms))))))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W3:num->bool"] A9)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W2:num->bool";"W3:num->bool"] A9)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_OR_DIST_L] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S]
   (ONCE_REWRITE_RULE [T_AND_MV1] thm)))));;

e(IMP_RES_TAC R_UNT_INTRO);;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp]
   (el 3 thms)])));;

----------------------------------------------------------------%

let UNT_DIST_R_S = prove_thm(`UNT_DIST_R_S`,
"!W1 W2 W3. ((W1 And W2) until W3) = ((W1 until W3) And (W2 until W3))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W1:num->bool";
    "W2:num->bool"] T_AND1_THM) (SPEC "W3:num->bool"
     T_IMP_REFL)))
  THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W1:num->bool";
    "W2:num->bool"] T_AND2_THM) (SPEC "W3:num->bool"
     T_IMP_REFL)))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC[REWRITE_RULE[VALID;Imp]
    (REWRITE_RULE [T_REWRITE_EQUIV_RULE T_LEM10]
    (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms) (el 1 thms))))]))
    ;
  ASSUME_TAC (SPECL ["W1:num->bool";"W3:num->bool"] A10)
  THEN ASSUME_TAC (SPECL ["W2:num->bool";"W3:num->bool"] A10)
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_AND_SELF] (MATCH_MP 
   (T_REWRITE_IMP_RULE T_LEM14a) (MATCH_MP (T_AND_COMB)
   (CONJ (el 2 thms) (el 1 thms)))))))
  THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W3:num->bool"] A9))))
  THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W2:num->bool";"W3:num->bool"] A9))))
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms))))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_OR_DIST_L] thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S]
   (ONCE_REWRITE_RULE [T_AND_MV1] thm))))
  THEN IMP_RES_TAC R_UNT_INTRO
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp]
   (el 3 thms)]))
  ]);;

let UNT_DIST_R = prove_thm(`UNT_DIST_R`,
"!W1 W2 W3. VALID (((W1 And W2) until W3) Equiv
   ((W1 until W3) And (W2 until W3)))",
REPEAT GEN_TAC
THEN REWRITE_TAC[UNT_DIST_R_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (W1 until (W2 Or W3)) = ((W1 until W2) Or
  (W1 until W3))");;

e(depth_conv_tac FUN_EQ_CONV);;

e(REPEAT GEN_TAC);;

e(EQ_TAC);;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2 Or W3"] A9)))));;

e(ASSUME_TAC (REWRITE_RULE [A4_S;T_DE_MORGAN_THM] (ONCE_REWRITE_RULE 
   [T_CONTRAPOS] (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"]
   A9)))))));;

e(ASSUME_TAC (REWRITE_RULE [A4_S;T_DE_MORGAN_THM] (ONCE_REWRITE_RULE 
   [T_CONTRAPOS] (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W3:num->bool"]
   A9)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 3 thms)
   (el 2 thms)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 1 thms)
   (el 2 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID (
        ((((W2 Or W3) Or (W1 And (next(W1 until (W2 Or W3))))) And
          ((Not W2) And ((Not W1) Or (next(Not(W1 until W2)))))) And
         ((Not W3) And ((Not W1) Or (next(Not(W1 until W3)))))) Imp
        (((Not W2) And (Not W3)) And (next(W1 until(W2 Or W3))) And
         (next(Not (W1 until W2))) And (next(Not (W1 until W3)))))")))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_DE_MORGAN_THM2;
   SYM_RULE N_DIST_AND_S]  thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
   SYM_RULE T_DE_MORGAN_THM2] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] (MATCH_MP 
   (T_DER_INDUCTION_RULE) thm)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_IMP_DISJ_THM;
   T_DE_MORGAN_THM1;NOT_NOT_RULE] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_AND_COMB) (CONJ thm
   (REWRITE_RULE [SYM_RULE T_IMP_DISJ_THM] (SPECL [ "W1:num->bool";
   "W2 Or W3"] A10)))))));;

e(IMP_RES_TAC (T_REWRITE_IMP_RULE (T_SIMP_THM ("!W1 W2 W3. VALID
      (((((Not(W1 until (W2 Or W3))) Or
          ((W1 until W2) Or (W1 until W3))) Or
         (Not(eventually(W2 Or W3)))) And
        ((Not(W1 until (W2 Or W3))) Or (eventually(W2 Or W3)))) Imp
    ((W1 until (W2 Or W3)) Imp ((W1 until W2) Or (W1 until W3))))"))));;

e(POP_ASSUM (\thm. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp] thm])));;

CASE 2

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool" 
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_OR_INTRO_THM1))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool" 
   T_IMP_REFL) (SPECL ["W3:num->bool";"W2:num->bool"] T_OR_INTRO_THM2))));;

e(ASSUM_LIST (\thms. (ASM_REWRITE_TAC[REWRITE_RULE [VALID;Imp;T_OR_SELF] 
   (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14b) (MATCH_MP
   (T_AND_COMB) (CONJ (el 2 thms) (el 1 thms))))])));;

----------------------------------------------------------------%

let UNT_DIST_L_S = prove_thm(`UNT_DIST_L_S`,
"!W1 W2 W3. (W1 until (W2 Or W3)) = ((W1 until W2) Or (W1 until W3))",
depth_conv_tac FUN_EQ_CONV
THEN REPEAT GEN_TAC
THEN EQ_TAC
THENL [
  ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2 Or W3"] A9))))
  THEN ASSUME_TAC (REWRITE_RULE [A4_S;T_DE_MORGAN_THM] (ONCE_REWRITE_RULE 
   [T_CONTRAPOS] (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"]
   A9))))))
  THEN ASSUME_TAC (REWRITE_RULE [A4_S;T_DE_MORGAN_THM] (ONCE_REWRITE_RULE 
   [T_CONTRAPOS] (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE 
   [SYM_RULE T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W3:num->bool"]
   A9))))))
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 3 thms)
   (el 2 thms))))))
  THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 1 thms)
   (el 2 thms))))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID (
        ((((W2 Or W3) Or (W1 And (next(W1 until (W2 Or W3))))) And
          ((Not W2) And ((Not W1) Or (next(Not(W1 until W2)))))) And
         ((Not W3) And ((Not W1) Or (next(Not(W1 until W3)))))) Imp
        (((Not W2) And (Not W3)) And (next(W1 until(W2 Or W3))) And
         (next(Not (W1 until W2))) And (next(Not (W1 until W3)))))"))))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_DE_MORGAN_THM2;
   SYM_RULE N_DIST_AND_S]  thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
   SYM_RULE T_DE_MORGAN_THM2] thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE A1_S] (MATCH_MP 
   (T_DER_INDUCTION_RULE) thm))))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_IMP_DISJ_THM;
   T_DE_MORGAN_THM1;NOT_NOT_RULE] thm)))
  THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_AND_COMB) (CONJ thm
   (REWRITE_RULE [SYM_RULE T_IMP_DISJ_THM] (SPECL [ "W1:num->bool";
   "W2 Or W3"] A10))))))
  THEN IMP_RES_TAC (T_REWRITE_IMP_RULE (T_SIMP_THM ("!W1 W2 W3. VALID
      (((((Not(W1 until (W2 Or W3))) Or
          ((W1 until W2) Or (W1 until W3))) Or
         (Not(eventually(W2 Or W3)))) And
        ((Not(W1 until (W2 Or W3))) Or (eventually(W2 Or W3)))) Imp
    ((W1 until (W2 Or W3)) Imp ((W1 until W2) Or (W1 until W3))))")))
  THEN POP_ASSUM (\thm. (ASM_REWRITE_TAC [REWRITE_RULE [VALID;Imp] thm]))
  ;
  ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool" 
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_OR_INTRO_THM1)))
  THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool" 
   T_IMP_REFL) (SPECL ["W3:num->bool";"W2:num->bool"] T_OR_INTRO_THM2)))
  THEN ASSUM_LIST (\thms. (ASM_REWRITE_TAC[REWRITE_RULE [VALID;Imp;T_OR_SELF] 
   (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14b) (MATCH_MP
   (T_AND_COMB) (CONJ (el 2 thms) (el 1 thms))))]))
  ]);;

let UNT_DIST_L = prove_thm (`UNT_DIST_L`,
"!W1 W2 W3. VALID((W1 until (W2 Or W3)) Equiv 
    ((W1 until W2) Or (W1 until W3)))",
REPEAT GEN_TAC
THEN REWRITE_TAC [UNT_DIST_L_S]
THEN REWRITE_TAC[T_REFL_THM]);;

%----------------------------------------------------------------

set_goal([],"!W1 W2. (VALID (((eventually W1) Or (eventually W2)) Imp
  (((Not W1) until W2) Or ((Not W2) until W1))))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] EV_DIST_OR)))));;

e(ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1 Or W2"] UNTIL_EQ_EV)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM2] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [UNT_DIST_L_S] thm))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["Not W1";"Not W2"]
   T_AND2_THM) (SPEC "W1:num->bool" T_IMP_REFL))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["Not W1";"Not W2"]
   T_AND1_THM) (SPEC "W2:num->bool" T_IMP_REFL))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms)
   (el 3 thms))) THEN ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14b) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 2 thms)
   (el 1 thms))))));;

e(POP_ASSUM (\thm. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm 
   (DEPTH_FIRST_CONV_RULE (REWR_CONV (T_OR_SYM)) 
   (SPEC "(((Not W1) until W2) Or ((Not W2) until W1))" T_IMP_REFL)))))));;

----------------------------------------------------------------%

let EV_IMP_UNTIL = prove_thm(`EV_IMP_UNTIL`,
"!W1 W2. (VALID (((eventually W1) Or (eventually W2)) Imp
  (((Not W1) until W2) Or ((Not W2) until W1))))",
REPEAT GEN_TAC
THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] EV_DIST_OR))))
THEN ASSUME_TAC (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1 Or W2"] UNTIL_EQ_EV))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM2] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [UNT_DIST_L_S] thm)))
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["Not W1";"Not W2"]
   T_AND2_THM) (SPEC "W1:num->bool" T_IMP_REFL)))
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["Not W1";"Not W2"]
   T_AND1_THM) (SPEC "W2:num->bool" T_IMP_REFL)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms)
   (el 3 thms))) THEN ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14b) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 2 thms)
   (el 1 thms)))))
THEN POP_ASSUM (\thm. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm 
   (DEPTH_FIRST_CONV_RULE (REWR_CONV (T_OR_SYM)) 
   (SPEC "(((Not W1) until W2) Or ((Not W2) until W1))" T_IMP_REFL)))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID ((W1 until (W2 And W3)) Imp 
  ((W1 until W2) And (W1 until W3))))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool"
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_AND1_THM))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool"
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_AND2_THM))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_REWRITE_EQUIV_RULE
   T_LEM10] (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

----------------------------------------------------------------%

let UNT_DIST_AND1 = prove_thm(`UNT_DIST_AND1`,
"!W1 W2 W3. (VALID ((W1 until (W2 And W3)) Imp 
   ((W1 until W2) And (W1 until W3))))",
REPEAT GEN_TAC
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool"
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_AND1_THM)))
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool"
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_AND2_THM)))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_REWRITE_EQUIV_RULE
   T_LEM10] (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID (((W1 until W3) Or (W2 until W3)) Imp
  ((W1 Or W2) until W3)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W1:num->bool";
   "W2:num->bool"] T_OR_INTRO_THM1) (SPEC "W3:num->bool"
   T_IMP_REFL))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W2:num->bool";
   "W1:num->bool"] T_OR_INTRO_THM2) (SPEC "W3:num->bool"
   T_IMP_REFL))));;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_REWRITE_EQUIV_RULE
   T_LEM12] (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

----------------------------------------------------------------%

let UNT_DIST_OR = prove_thm(`UNT_DIST_OR`,
"!W1 W2 W3. (VALID (((W1 until W3) Or (W2 until W3)) Imp
  ((W1 Or W2) until W3)))",
REPEAT GEN_TAC
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W1:num->bool";
   "W2:num->bool"] T_OR_INTRO_THM1) (SPEC "W3:num->bool"
   T_IMP_REFL)))
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPECL ["W2:num->bool";
   "W1:num->bool"] T_OR_INTRO_THM2) (SPEC "W3:num->bool"
   T_IMP_REFL)))
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (REWRITE_RULE [T_REWRITE_EQUIV_RULE
   T_LEM12] (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID (((W1 Imp W2) until W3) Imp
  ((W1 until W3) Imp (W2 until W3))))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (SPECL ["W1 Imp W2";"W3:num->bool"] A10));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1 Imp W2";"W3:num->bool"] A9)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W3:num->bool"] A9)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_OR_DIST_L] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID ((W3 Or
       (((W1 Imp W2) And (next((W1 Imp W2) until W3))) And
       (W1 And (next(W1 until W3))))) Imp
    (W3 Or 
      (W2 And ((next((W1 Imp W2) until W3)) And (next(W1 until W3))))))"
   )))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S] thm))));;

e(REWRITE_TAC [T_REWRITE_EQUIV_RULE T_LEM2]);;

e(MATCH_MP_TAC R_UNT_INTRO);;

e(ASM_REWRITE_TAC[]);;

e(ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (
   SPECL ["((W1 Imp W2) until W3)";"W1 until W3"] T_AND1_THM)
   (el 4 thms))))));;

----------------------------------------------------------------%

let UNT_DIST_IMP = prove_thm (`UNT_DIST_IMP`,
"!W1 W2 W3. (VALID (((W1 Imp W2) until W3) Imp
  ((W1 until W3) Imp (W2 until W3))))",
REPEAT GEN_TAC
THEN ASSUME_TAC (SPECL ["W1 Imp W2";"W3:num->bool"] A10)
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1 Imp W2";"W3:num->bool"] A9))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W3:num->bool"] A9))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_OR_DIST_L] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID ((W3 Or
       (((W1 Imp W2) And (next((W1 Imp W2) until W3))) And
       (W1 And (next(W1 until W3))))) Imp
    (W3 Or 
      (W2 And ((next((W1 Imp W2) until W3)) And (next(W1 until W3))))))"
   ))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S] thm)))
THEN REWRITE_TAC [T_REWRITE_EQUIV_RULE T_LEM2]
THEN MATCH_MP_TAC R_UNT_INTRO
THEN ASM_REWRITE_TAC[]
THEN ASSUM_LIST (\thms. (ACCEPT_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (
   SPECL ["((W1 Imp W2) until W3)";"W1 until W3"] T_AND1_THM)
   (el 4 thms))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID (((W1 until W2) And ((Not W2) until W3)) Imp
  (W1 until W3)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (SPECL ["W1 until W2";"(Not W2) until W3"] T_AND2_THM));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
  (SPECL ["Not W2";"W3:num->bool"] A10))))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["Not W2";"W3:num->bool"] A9)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID(
     ((W2 Or (W1 And (next(W1 until W2)))) And
       (W3 Or ((Not W2) And (next((Not W2) until W3))))) Imp
     (W3 Or (W1 And ((next(W1 until W2)) And (next((Not W2) until W3))))))"
   )))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S] thm))));;

e(IMP_RES_TAC R_UNT_INTRO);;

----------------------------------------------------------------%

let UNT_TRANS_THM = prove_thm(`UNT_TRANS_THM`,
"!W1 W2 W3. (VALID (((W1 until W2) And ((Not W2) until W3)) Imp
   (W1 until W3)))",
REPEAT GEN_TAC
THEN ASSUME_TAC (SPECL ["W1 until W2";"(Not W2) until W3"] T_AND2_THM)
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
  (SPECL ["Not W2";"W3:num->bool"] A10)))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["Not W2";"W3:num->bool"] A9))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE 
   T_LEM14a) (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID(
     ((W2 Or (W1 And (next(W1 until W2)))) And
       (W3 Or ((Not W2) And (next((Not W2) until W3))))) Imp
     (W3 Or (W1 And ((next(W1 until W2)) And (next((Not W2) until W3))))))"
   ))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE N_DIST_AND_S] thm)))
THEN IMP_RES_TAC R_UNT_INTRO);;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID ((W1 until (W2 And W3)) Imp
  ((W1 until W2) until W3)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (MATCH_MP (EV_EV_IMP_RULE) (SPECL ["W2:num->bool";
   "W3:num->bool"] T_AND2_THM)));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (SPECL [
   "W1:num->bool";"W2 And W3"] A10) thm)))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2 And W3"] A9)))));;

e(ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool" 
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_AND1_THM))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_REWRITE_EQUIV_RULE 
   T_LEM10] (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID(
      (((W2 And W3) Or (W1 And (next(W1 until (W2 And W3))))) And
         (W1 until W2)) Imp
      (W3 Or ((W1 until W2) And (next(W1 until (W2 And W3))))))")))))));;

e(IMP_RES_TAC R_UNT_INTRO);;

----------------------------------------------------------------%

let UNT_DIST_AND2 = prove_thm(`UNT_DIST_AND2`,
"!W1 W2 W3. (VALID ((W1 until (W2 And W3)) Imp ((W1 until W2) until W3)))",
REPEAT GEN_TAC
THEN ASSUME_TAC (MATCH_MP (EV_EV_IMP_RULE) (SPECL ["W2:num->bool";
   "W3:num->bool"] T_AND2_THM))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (SPECL [
   "W1:num->bool";"W2 And W3"] A10) thm))))
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2 And W3"] A9))))
THEN ASSUME_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ (SPEC "W1:num->bool" 
   T_IMP_REFL) (SPECL ["W2:num->bool";"W3:num->bool"] T_AND1_THM)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_REWRITE_EQUIV_RULE 
   T_LEM10] (MATCH_MP (T_AND_COMB) (CONJ (el 2 thms)
   (el 1 thms))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPEC_ALL (T_SIMP_THM "!W1 W2 W3. VALID(
      (((W2 And W3) Or (W1 And (next(W1 until (W2 And W3))))) And
         (W1 until W2)) Imp
      (W3 Or ((W1 until W2) And (next(W1 until (W2 And W3))))))"))))))
THEN IMP_RES_TAC R_UNT_INTRO);;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID (((W1 until W2) until W3) Imp
  ((W1 Or W2) until W3)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE[SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_OR_DIST_L] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPECL ["W2 Or W1";"W2 Or (next(W1 until W2))"] T_AND1_THM))))));;

e(ONCE_REWRITE_TAC[T_OR_SYM]);;

e(POP_ASSUM (\thm. (ACCEPT_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ thm
   (SPEC "W3:num->bool" T_IMP_REFL))))));;

----------------------------------------------------------------%

let UNT_ASSOC_THM1 = prove_thm(`UNT_ASSOC_THM1`,
"!W1 W2 W3. (VALID (((W1 until W2) until W3) Imp ((W1 Or W2) until W3)))",
REPEAT GEN_TAC
THEN ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE[SYM_RULE
   T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2:num->bool"] A9))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_OR_DIST_L] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm
   (SPECL ["W2 Or W1";"W2 Or (next(W1 until W2))"] T_AND1_THM)))))
THEN ONCE_REWRITE_TAC[T_OR_SYM]
THEN POP_ASSUM (\thm. (ACCEPT_TAC (MATCH_MP (U_U_IMP_RULE) (CONJ thm
   (SPEC "W3:num->bool" T_IMP_REFL))))));;

%----------------------------------------------------------------

set_goal([],"!W1 W2 W3. (VALID ((W1 until (W2 until W3)) Imp 
  ((W1 Or W2) until W3)))");;

e(REPEAT GEN_TAC);;

e(ASSUME_TAC (MATCH_MP (EV_EV_IMP_RULE) (SPECL ["W2:num->bool";
   "W3:num->bool"] A10)));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (SPECL [
   "W1:num->bool";"W2 until W3"] A10) (REWRITE_RULE [SYM_RULE
   EV_IDEMPOTENT_S] thm))))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W2:num->bool";"W3:num->bool"] A9)))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14b)
  (MATCH_MP (T_AND_COMB) (CONJ thm (SPEC 
  "(W1 And (next(W1 until (W2 until W3))))" T_IMP_REFL)))))));;

e(ASSUME_TAC (CONJUNCT1 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
  T_IMP_IMP_EQ_S] (SPECL ["W1:num->bool";"W2 until W3"] A9)))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 1 thms)
  (el 2 thms))))));;

e(
----------------------------------------------------------------%
%----------------------------------------------------------------
introduce a new (derived) operator
----------------------------------------------------------------%

let unless = new_infix_definition(`unless`,
"!(u v:num->bool). $unless u v = ((henceforth u) Or (u until v))");;

%----------------------------------------------------------------
unless introduction
----------------------------------------------------------------%
%----------------------------------------------------------------

set_goal([],"!U V. (VALID (U Imp (next (U Or V)))) ==>
   (VALID (U Imp (U unless V)))");;

e(REPEAT GEN_TAC);;

e(STRIP_TAC);;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [N_DIST_OR_S] thm))));;

e(ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM;A4_S] (ONCE_REWRITE_RULE
   [T_CONTRAPOS] (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
    T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] A9)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (N_N_IMP_RULE) (MATCH_MP
   (T_REWRITE_IMP_RULE T_LEM9b) (el 1 thms))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14b)
   (MATCH_MP (T_AND_COMB) (CONJ (SPEC "U:num->bool" T_IMP_REFL)
   (MATCH_MP (T_REWRITE_IMP_RULE T_LEM9a) (el 2 thms))))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_L;T_AND_SIMP;
   T_OR_F] thm))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_AND_SELF;SYM_RULE 
   T_AND_ASSOC] (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a)
   (MATCH_MP (T_AND_COMB) (CONJ (SPEC "U And (next(Not (U until V)))"
   T_IMP_REFL) (el 2 thms))))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a)
   (MATCH_MP (T_AND_COMB) (CONJ (el 5 thms) (SPEC 
   "(next(Not(U until V))) And (next(Not V))" T_IMP_REFL)))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_R] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
   (ONCE_REWRITE_RULE[T_AND_SYM] T_AND_SIMP);
   T_OR_F;T_AND_F;SYM_RULE A4_S] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;A4_S] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 2 thms)
  (el 1 thms))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;T_AND_SELF]
  (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a) (MATCH_MP
  (T_AND_COMB) (CONJ (SPEC "U:num->bool" T_IMP_REFL) thm)))))));;

e(ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms)
  (el 1 thms))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm (SPECL [
  "((U And (next U)) And (next(Not(U until V))))";"next(Not V)"]
  T_AND1_THM))))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
   SYM_RULE N_DIST_AND_S] thm))));;

e(IMP_RES_TAC T_DER_INDUCTION_RULE);;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE (T_REWRITE_EQUIV_RULE
  T_LEM2)] thm))));;

e(POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_IMP_DISJ_THM] 
  (REWRITE_RULE [SYM_RULE T_IMP_DISJ_THM;NOT_NOT_RULE] thm)))));;

e(REWRITE_TAC [unless]);;

e(POP_ASSUM (\thm. (ACCEPT_TAC (ONCE_REWRITE_RULE[T_OR_SYM] thm))));;

----------------------------------------------------------------%

let UNLESS_INTRO = prove_thm(`UNLESS_INTRO`,
"!U V. (VALID (U Imp (next (U Or V)))) ==> (VALID (U Imp (U unless V)))",
REPEAT GEN_TAC
THEN STRIP_TAC
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [N_DIST_OR_S] thm)))
THEN ASSUME_TAC (REWRITE_RULE [T_DE_MORGAN_THM;A4_S] (ONCE_REWRITE_RULE
   [T_CONTRAPOS] (CONJUNCT2 (MATCH_MP (T_AND_EXPAND) (REWRITE_RULE [SYM_RULE
    T_IMP_IMP_EQ_S] (SPECL ["U:num->bool";"V:num->bool"] A9))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (N_N_IMP_RULE) (MATCH_MP
   (T_REWRITE_IMP_RULE T_LEM9b) (el 1 thms)))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a)
   (MATCH_MP (T_AND_COMB) (CONJ (SPEC "U:num->bool" T_IMP_REFL)
   (MATCH_MP (T_REWRITE_IMP_RULE T_LEM9a) (el 2 thms)))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_L;T_AND_SIMP;
   T_OR_F] thm)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (REWRITE_RULE [T_AND_SELF;SYM_RULE 
   T_AND_ASSOC] (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a)
   (MATCH_MP (T_AND_COMB) (CONJ (SPEC "U And (next(Not (U until V)))"
   T_IMP_REFL) (el 2 thms)))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a)
    (MATCH_MP (T_AND_COMB) (CONJ (el 5 thms) (SPEC 
   "(next(Not(U until V))) And (next(Not V))" T_IMP_REFL))))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_DIST_R] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
   (ONCE_REWRITE_RULE[T_AND_SYM] T_AND_SIMP);T_OR_F;T_AND_F;SYM_RULE A4_S] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;A4_S] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (ONCE_REWRITE_RULE [T_AND_SYM] thm)))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 2 thms)
  (el 1 thms)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_AND_ASSOC;T_AND_SELF]
  (MATCH_MP (T_REWRITE_IMP_RULE T_LEM14a) (MATCH_MP
  (T_AND_COMB) (CONJ (SPEC "U:num->bool" T_IMP_REFL) thm))))))
THEN ASSUM_LIST (\thms. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ (el 4 thms)
  (el 1 thms)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (MATCH_MP (T_IMP_TRANS) (CONJ thm (SPECL [
  "((U And (next U)) And (next(Not(U until V))))";"next(Not V)"]
  T_AND1_THM)))))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE T_AND_ASSOC;
   SYM_RULE N_DIST_AND_S] thm)))
THEN IMP_RES_TAC T_DER_INDUCTION_RULE
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [SYM_RULE 
  (T_REWRITE_EQUIV_RULE T_LEM2)] thm)))
THEN POP_ASSUM (\thm. (ASSUME_TAC (REWRITE_RULE [T_IMP_DISJ_THM] 
  (REWRITE_RULE [SYM_RULE T_IMP_DISJ_THM;NOT_NOT_RULE] thm))))
THEN REWRITE_TAC [unless]
THEN POP_ASSUM (\thm. (ACCEPT_TAC (ONCE_REWRITE_RULE[T_OR_SYM] thm))));;

