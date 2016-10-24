% File: mk_RCprocedure.ml
   procedural abstraction
%


new_theory `RCprocedure`;;
new_parent `RCrecursion`;;


let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2";;

load_library `taut`;;
let TAUT t = TAC_PROOF(([],t),TAUT_TAC);;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;
autoload_defs `RCpredicate`;;
autoload_thms `RCpredicate`;;
loadf `Predicate/RCpredicate_convs`;;

autoload_defs `RCcommand`;;
autoload_thms `RCcommand`;;

autoload_defs `RCwellf`;;
autoload_thms `RCwellf`;;

autoload_defs `RCcorrect`;;
autoload_thms `RCcorrect`;;

autoload_defs `RCrefine`;;
autoload_thms `RCrefine`;;

loadf `defs`;;


% --- The procedure call abstraction --- %

% c is procedure code, G is result parameter tuple, R is its complement %
let pcall_DEF = new_definition(`pcall_DEF`,
  "pcall c (G:*s->*sa) (R:*s->*sb) q u = 
     ?p. (!u'. p(G u') /\ (R u' = R u) ==> q u') /\ c p (G u)");;

let pcall_mono = prove
 ("!c c'.c ref c' ==> !G:*s->*s1.!R:*s->*s2.(pcall c G R) ref (pcall c' G R)",
  LPORT[ref_DEF;implies_DEF;pcall_DEF] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC "p:*s1->bool" THEN RES_TAC THEN ART[]);;

% V is value parameter function %
let xpcall_DEF = new_definition(`xpcall_DEF`,
  "xpcall c (G:*s->*sa) (R:*s->*sb) (V:*s->*) q u = 
     ?p. (!u'. p(G u') /\ (R u' = R u) ==> q u') /\ c (V u) p (G u)");;

let xpcall_mono = prove
 ("!c c'. (!a. (c a) ref (c' a))
     ==> !G:*s->*sa. !R:*s->*sb. !V:*s->*.
             (xpcall c G R V) ref (xpcall c' G R V)",
  LPORT[ref_DEF;implies_DEF;xpcall_DEF] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC "p:*sa->bool" THEN RES_TAC THEN ART[]);;

let regular_pcall = prove
 ("!G:*s->*s1. !R:*s->*s2.  regular (\x. pcall x G R)",
  LPORT[regular_DEF;pmonotonic_DEF;mono_mono_DEF;ref_DEF] THEN BETA_TAC THEN
  LPORT[monotonic_DEF;implies_DEF;pcall_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN ART[] THENL
  [EXISTS_TAC "p:*s1->bool" THEN RES_TAC THEN ART[]
  ;EXISTS_TAC "p':*s1->bool" THEN RES_TAC THEN ART[] THEN
   REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC
  ]);;


save_thm(`pcall_mono`,pcall_mono);;
save_thm(`regular_pcall`,regular_pcall);;
save_thm(`xpcall_mono`,xpcall_mono);;

close_theory();;
