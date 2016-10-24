
% Proof of theorems corresponding to the Hoare rules and axioms 
  for total correctness. %

% FORALL_AND_CONV :  "!x: t1 x /\ t2 x" -----> (!x.t1 x) /\ (!x.t2 x)	%
let FORALL_AND_CONV tm = 
    let xvar,body = dest_forall tm in
    let (p,q) = CONJ_PAIR(SPEC xvar (ASSUME tm)) in
    let imp1 = DISCH tm (CONJ (GEN xvar p) (GEN xvar q)) in
    let (P,Q) = CONJ_PAIR(ASSUME (snd(dest_imp (concl imp1)))) in
    let imp2 = DISCH_ALL (GEN xvar (CONJ (SPEC xvar P) (SPEC xvar Q))) in
    IMP_ANTISYM_RULE imp1 imp2;;

new_theory `halts_thms`;;

load_library `string`;;

new_parent `hoare_thms`;;
new_parent `halts`;;

let T_SPEC =
 new_definition
  (`T_SPEC`,
   "T_SPEC(p,c,q) = MK_SPEC(p,c,q) /\ HALTS p c");;

load_theorems `halts`;;
load_theorems `hoare_thms`;;

load_definition `halts` `HALTS`;;

load_definition `semantics` `MK_SPEC`;;

% Useful functions for interactive proof
  (should be in the system).
%

let goal tm = set_goal([],tm)
and e       = expand;;

let ASSIGN_T_THM =
 prove_thm
  (`ASSIGN_T_THM`,
   "!p x f. T_SPEC((\s. p (BND (f s) x s)), MK_ASSIGN(x,f), p)",
   REWRITE_TAC[T_SPEC;ASSIGN_THM;ASSIGN_HALTS]);;


let SEQ_T_THM =
 prove_thm
  (`SEQ_T_THM`,
   "!p q r c1 c2.
    T_SPEC(p,c1,q) /\ T_SPEC(q,c2,r) ==> T_SPEC(p,MK_SEQ(c1,c2),r)",
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SEQ_THM
    THEN IMP_RES_TAC SEQ_HALTS);;

let IF1_T_THM =
 prove_thm
  (`IF1_T_THM`,
   "!p q c b.
     T_SPEC((\s. p s /\ b s),c,q) /\ (!s. p s /\ ~(b s) ==> q s) ==>
     T_SPEC(p,MK_IF1(b,c),q)",
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC IF1_THM
    THEN IMP_RES_TAC IF1_HALTS);;

let IF2_T_THM =
 prove_thm
  (`IF2_T_THM`,
   "!p q c1 c2 b.
     T_SPEC((\s. p s /\ b s),c1,q) /\ T_SPEC((\s. p s /\ ~(b s)),c2,q) ==>
     T_SPEC(p,MK_IF2(b,c1,c2),q)",
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC IF2_THM
    THEN IMP_RES_TAC IF2_HALTS);;

let PRE_STRENGTH_T_THM =
 prove_thm
  (`PRE_STRENGTH_T_THM`,
   "!p p' q c.
     (!s. p' s ==> p s) /\ T_SPEC(p,c,q) ==> T_SPEC(p',c,q)",
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC PRE_STRENGTH_THM
    THEN IMP_RES_TAC PRE_STRENGTH_HALTS);;

let POST_WEAK_T_THM =
 prove_thm
  (`POST_WEAK_T_THM`,
   "!p q q' c.
     T_SPEC(p,c,q)/\ (!s. q s ==> q' s)  ==> T_SPEC(p,c,q')",
   REWRITE_TAC[T_SPEC]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC POST_WEAK_THM
    THEN ASM_REWRITE_TAC[]);;

let WHILE_T_LEMMA1 =
 TAC_PROOF
  (([],
    "(!n. HALTS(\s. p s /\ b s /\ (s x = n))c) ==> HALTS(\s. p s /\ b s)c"),
   REWRITE_TAC[HALTS] THEN
   BETA_TAC THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM (\th g. MATCH_MP_TAC(SPECL["(s:state)x";"s:state"] th) g) THEN
   ASM_REWRITE_TAC []);;

let WHILE_T_LEMMA2 =
 TAC_PROOF
  (([],
    "(!n. MK_SPEC((\s. p s /\ b s /\ (s x = n)),c,(\s. p s /\ (s x) < n)))
     ==>
     MK_SPEC((\s. p s /\ b s),c,p)"),
   REWRITE_TAC[MK_SPEC] THEN
   BETA_TAC THEN REPEAT STRIP_TAC THEN
   ASSUME_TAC (REFL "(s1:state) x") THEN
   RES_TAC);;

let WHILE_T_THM =
 prove_thm
  (`WHILE_T_THM`,
   "!p c b.
     (!n. T_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n))) ==> 
     T_SPEC(p,MK_WHILE(b,c),(\s. p s /\ ~(b s)))",
    REWRITE_TAC[T_SPEC]
     THEN REPEAT STRIP_TAC
     THEN POP_ASSUM(\th. STRIP_ASSUME_TAC(EQ_MP(FORALL_AND_CONV(concl th))th))
     THEN IMP_RES_TAC WHILE_T_LEMMA1
     THEN IMP_RES_TAC WHILE_HALTS
     THEN IMP_RES_TAC WHILE_T_LEMMA2
     THEN IMP_RES_TAC WHILE_THM);;

close_theory();;
