% File: mk_RCwintool1.ml

  Build basis for a theory of refinement using the window inference
  
%

load_theorem `RCcommand` `ref_prop`;;
load_theorem `RCpredicate` `implies_prop`;;

% reverse refinement relation, with reflexivity and transitivity %

let refines_DEF = new_infix_definition(`refines_DEF`,
 "$refines (c':(*s1->bool)->(*s2->bool)) c = c ref c'");;
let refines_refl  = save_thm(`refines_refl`,
  PORR[SYM (SPEC_ALL refines_DEF)] (C1 ref_prop));;
let refines_trans = save_thm(`refines_trans`,
  GEN_ALL (SPEC_ALL 
    (LPORR[SYM (SPEC_ALL refines_DEF);CONJ_SYM] (C2 (C2 ref_prop)))));;


% implication relation, with reflexivity and transitivity %

let implies_refl  = save_thm(`implies_refl`,C1 implies_prop);;
let implies_trans = save_thm(`implies_trans`,C2 (C2 implies_prop));;


% implication relation for two arguments, with reflexivity and transitivity %

let implies2_DEF = new_infix_definition(`implies2_DEF`,
 "$implies2 (P:*s1->*s2->bool) Q = !u v. P u v ==> Q u v");;
let implies2_refl = save_thm(`implies2_refl`,prove
  ("!P:*s1->*s2->bool. P implies2 P",
   PORT[implies2_DEF] THEN REPEAT STRIP_TAC));;
let implies2_trans = save_thm(`implies2_trans`,prove
  ("!P:*s1->*s2->bool.!Q R.
        P implies2 Q /\ Q implies2 R ==> P implies2 R",
   PORT[implies2_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC));;


% reverse implication relation, with reflexivity and transitivity %

let implied_by_DEF = new_infix_definition(`implied_by_DEF`,
 "$implied_by (p':*s->bool) p = p implies p'");;
let implied_by_refl  = save_thm(`implied_by_refl`,
  PORR[SYM (SPEC_ALL implied_by_DEF)] (C1 implies_prop));;
let implied_by_trans = save_thm(`implied_by_trans`,
  GEN_ALL (SPEC_ALL 
    (LPORR[SYM (SPEC_ALL implied_by_DEF);CONJ_SYM] (C2 (C2 implies_prop)))));;



