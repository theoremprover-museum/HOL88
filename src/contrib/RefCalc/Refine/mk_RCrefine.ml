% File: mk_RCrefine.ml
   laws of refinement
%


new_theory `RCrefine`;;
new_parent `RCcorrect`;;

let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3"
 and estate = ":*#*s";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool"
 and pred3 = ":^state3->bool"
 and epred = ":^estate->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2"
 and ptrans13 = ":^pred1->^pred3"
 and ptrans23 = ":^pred2->^pred3"
 and eptrans = ":^epred->^epred";;


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

loadf `defs`;;
load_library `pair`;;


% --- refinement and correctness --- %

let ref_correct = prove
 ("!(c:^ptrans12) c'.
     (!p q. correct p c q ==> correct p c' q) = c ref c'",
  LPORT[ref_DEF;correct_DEF;implies_DEF] THEN REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN REPEAT GEN_TAC THEN POP_ASSUM MATCH_MP_TAC THEN RT[]
  ;REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC
  ]);;

% --- implement an assignment specification --- %

let impl_assign = 
  let lemma = prove("(q:^pred)v0 ==> (\v.v=v0) implies q",
   PORT[implies_DEF] THEN BETA_TAC THEN DISCH_TAC
   THEN CONV_TAC FORALL_1PT_CONV THEN POP_ASSUM ACCEPT_TAC)
 in prove
 ("monotonic(c:^ptrans12) /\ (!u0. correct (\u.u=u0) c (\u.u = e u0))
    ==> (assign e) ref c",
  PORT[monotonic_DEF] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  LPORT[correct_DEF;ref_DEF;true_DEF;assign_DEF;implies_DEF] THEN
  BETA_TAC THEN CONV_TAC (DEPTH_CONV FORALL_1PT_CONV) THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC lemma THEN
  UNDISCH_TAC "!u0. (c:^ptrans12)(\u. u = e u0)u0" THEN
  DISCH_THEN (ASSUME_TAC o RR[] o SPEC "u:^state2")
  THEN RES_TAC THEN POP_ASSUM (MATCH_MP_TAC o PORR[implies_DEF])
  THEN POP_ASSUM ACCEPT_TAC);;

% --- Implementing nondass specification --- %

let impl_nondass = prove
 ("monotonic(c:^ptrans12) /\ (!u0. correct (\u.u=u0) c (\v.P u0 v))
    ==> (nondass P) ref c",
  LPORT[monotonic_DEF;correct_DEF;ref_DEF;true_DEF;nondass_DEF;
        implies_DEF] THEN BETA_TAC THEN
  DISCH_THEN (MP_TAC o (CONV_RULE (DEPTH_CONV ETA_CONV) o
    CONV_RULE (DEPTH_CONV FORALL_1PT_CONV))) THEN 
  REPEAT STRIP_TAC THEN RES_TAC THEN POP_ASSUM MATCH_MP_TAC THEN ART[]);;



% ----- Rules for assertions ----- %


% --- general rule: total correctness and assertion propagation --- %

let assert_fwd = prove
 ("!p q. !c:^ptrans12.
    conjunctive c /\ correct p c q 
    ==> ((assert p) seq c) ref (c seq (assert q))",
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  IMP_RES_TAC conj_biconj THEN POP_ASSUM MP_TAC THEN
  LPORT[biconjunctive_DEF;correct_DEF;ref_DEF] THEN REPEAT STRIP_TAC THEN 
  ART[seq_DEF;assert_DEF] THEN POP_ASSUM MP_TAC THEN
  LPORT[implies_DEF;and_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

% --- weakening, splitting and removing assertion --- %
let assert_weaken = prove
 ("(p:^pred) implies q ==> (assert p) ref (assert q)",
  LPORT[ref_DEF;assert_DEF;implies_DEF;and_DEF] THEN SUPER_TAC);;
let assert_split = prove
 ("assert ((p:^pred) andd q) = (assert p) seq (assert q)",
  FUN_TAC THEN LPRT[seq_DEF;assert_DEF;and_DEF] THEN
  FUN_TAC THEN EQ_TAC THEN SUPER_TAC);;
let assert_remove = prove
 ("(assert(p:^pred)) ref skip",
  LPORT[ref_DEF;assert_DEF;skip_DEF] THEN PRED_TAUT_TAC);;

% --- special equality cases --- %

let thm1 = prove("true implies(p:^pred) = (p = true)",
  CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN LRT[true_DEF;implies_DEF] THEN
  BETA_TAC THEN EQ_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]);;
let assert_intro = prove
 ("!g. !c:^ptrans12.
    conjunctive c /\ correct true c g ==> (c = c seq (assert g))",
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  IMP_RES_TAC conj_biconj THEN POP_ASSUM MP_TAC THEN
  LPORT[biconjunctive_DEF;correct_DEF;thm1] THEN REPEAT STRIP_TAC THEN 
  FUN_TAC THEN ART[seq_DEF;assert_DEF] THEN PRED_TAUT_TAC);;

let assert_bwd = prove
 ("!p. !c:^ptrans12.
    conjunctive c ==> (c seq (assert p) = (assert (c p)) seq c)",
  REPEAT STRIP_TAC THEN IMP_RES_TAC conj_biconj THEN 
  POP_ASSUM MP_TAC THEN PORT[biconjunctive_DEF] THEN
  STRIP_TAC THEN FUN_TAC THEN ART[seq_DEF;assert_DEF]);;


% --- assertion into conditional and iteration --- %

let assert_cond = prove
 ("((assert p) seq (cond g (c1:^ptrans12) c2))
    ref ((cond g ((assert(p andd g)) seq c1)((assert(p andd(not g))) seq c2)))",
  LRT[ref_DEF;seq_DEF;cond_DEF;seq_DEF;assert_DEF] THEN 
  PRED_TAUT_TAC);;

let th1 = TAUT "t==>t'==>t'' = t/\t'==>t''";;
let th2 = prove
 ("((p:^pred) andd q) implies r ==> (p andd q = p andd q andd r)",
  LPRT[implies_DEF;and_DEF] THEN BETA_TAC THEN STRIP_TAC THEN FUN_TAC THEN
  EQ_TAC THEN SUPER_TAC);;
let th3 = prove
  ("(p:^pred) andd ((not p) or q) = p andd q",PRED_TAUT_TAC);;
let and_assoc = prove
  ("(p:^pred) andd (q andd r) = (p andd q) andd r",PRED_TAUT_TAC);;
let and_distr = prove
  ("(p:^pred) andd (q or r) = (p andd q) or (p andd r)",PRED_TAUT_TAC);;
let lemma1 = prove
 ("conjunctive(c:^ptrans) /\ (p andd g) implies (c p) 
  ==> (p andd g andd c((not p) or q) = p andd g andd (c q))",
  STRIP_TAC THEN IMP_RES_TAC conj_biconj THEN IMP_RES_TAC th2 THEN
  PORT[and_assoc] THEN POP_ASSUM SUBST1_TAC THEN PRT[SYM and_assoc] THEN
  POP_ASSUM(\th.PORT[GSYM(PORR[biconjunctive_DEF]th)]) THEN RT[th3]);;
let assert_do = prove
 ("conjunctive (c:^ptrans) /\  correct (p andd g) c p ==>
   ((assert p) seq (do g c))
    ref (do g ((assert(p andd g)) seq c))",
  LRT[ref_DEF;seq_DEF;correct_DEF;assert_DEF] THEN REPEAT STRIP_TAC THEN
  PORT[shunt] THEN MATCH_MP_TAC(PORR[th1]do_implies) THEN
  IMP_RES_TAC conj_mono THEN ART[] THEN
  SUBGOAL_THEN "monotonic((assert(p andd g)) seq(c:^ptrans))" ASSUME_TAC THENL
  [MATCH_MP_TAC mono_seq THEN ART[mono_assert]
  ;LPORT[SYM shunt;and_distr] THEN IMP_RES_TAC lemma1 THEN ART[] THEN
   IMP_RES_TAC do_unfold THEN
   FIRST_ASSUM(\th.CONV_TAC(RAND_CONV(REWR_CONV th))) THEN
   LPORT[seq_DEF;assert_DEF] THEN PRED_TAUT_TAC
  ]);;


% --- save the results --- %

save_thm(`ref_correct`,ref_correct);;
save_thm(`impl_assign`,impl_assign);;
save_thm(`impl_nondass`,impl_nondass);;
save_thm(`assert_fwd`,assert_fwd);;
save_thm(`assert_weaken`,assert_weaken);;
save_thm(`assert_split`,assert_split);;
save_thm(`assert_remove`,assert_remove);;
save_thm(`assert_intro`,assert_intro);;
save_thm(`assert_bwd`,assert_bwd);;
save_thm(`assert_cond`,assert_cond);;
save_thm(`assert_do`,assert_do);;

close_theory();;
