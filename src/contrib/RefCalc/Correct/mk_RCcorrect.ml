% File: mk_RCcorrect.ml
   total correctness reasoning
%


new_theory `RCcorrect`;;
new_parent `RCcommand`;;
new_parent `RCwellf`;;


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

loadf `defs`;;
load_library `pair`;;


% ----- correctness triple  ----- %

let correct_DEF = new_definition  
  (`correct_DEF`,
   "correct p (c:^ptrans12) q = p implies (c q)");;


% --- assign --- %

let correct_assign = snd(EQ_IMP_RULE(BETA_RULE
 (RR[assign_DEF;implies_DEF](ISPECL["p:^pred2";"assign(e:*s2->*s1)";"q:^pred1"]
   correct_DEF))));;


% --- nondass --- %

let correct_nondass = snd(EQ_IMP_RULE(BETA_RULE
 (RR[nondass_DEF;implies_DEF]
  (ISPECL["p:^pred2";"nondass(n:*s2->*s1->bool)";"q:^pred1"] correct_DEF))));;


% --- seq --- %

let correct_seq = prove
 ("!c1:^ptrans23. !c2:^ptrans12. !p q r.
    monotonic c1 /\ correct p c1 q /\ correct q c2 r
    ==> correct p (c1 seq c2) r",
  LPORT[monotonic_DEF;correct_DEF;seq_DEF] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN IMP_RES_TAC implies_prop);;


% --- cond --- %

let correct_cond = prove
 ("!g. !c1:^ptrans12. !c2:^ptrans12. !p q.
    correct (g andd p) c1 q /\ correct ((not g) andd p) c2 q
    ==> correct p (cond g c1 c2) q",
  LPORT[correct_DEF;cond_DEF;implies_DEF;and_DEF;or_DEF;not_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC "(g:^pred2)u" THEN
  RES_TAC THEN ART[]);;


% --- do: the well-founded invariant-bound theorems --- %
 
let t99 = prove
    ("(g andd((c:^ptrans)p))or((not g) andd q)=(g or q)andd((not g) or (c p))",
     PRED_TAUT_TAC);;
let do_not_guard =
 let t = TAC_PROOF
  (([],"p or ((not p) andd q) = (p:^pred) or q"),PRED_TAUT_TAC)
 in TAC_PROOF
  ((["monotonic(c:^ptrans)"],
    "do g (c:^ptrans) q = do g c ((not g) andd q)"),
   MATCH_MP_TAC (CONJUNCT1(CONJUNCT2 implies_prop)) THEN CONJ_TAC
   THEN MATCH_MP_TAC (UNDISCH(PORR[t99]do_implies)) THENL
   [PORT[UNDISCH(PORR[t99]do_unfold)] THEN
    LPORT[SYM_RULE (AP_TERM "c:^ptrans" (UNDISCH(PORR[t99]do_unfold)));t] THEN 
    MATCH_ACCEPT_TAC (CONJUNCT1 implies_prop)
   ;LPORT[t;SYM(UNDISCH(PORR[t99]do_unfold))] THEN
    MATCH_ACCEPT_TAC (CONJUNCT1 implies_prop)
   ]);; 
let lemma1 =
 let t1 = ASSUME 
  "!(y:*). po y (x:*) 
     ==> (p andd (\(u:^state). t u = y)) implies (do g c p)"
 in let t2 = BETA_RULE(LPORR[and_DEF;implies_DEF] t1)
 in let t3 = GEN "y:*" (CONV_RULE RIGHT_IMP_FORALL_CONV (SPEC_ALL t2))
 in let t4 = CONV_RULE FORALL_SWAP_CONV t3
 in let t5 = TAC_PROOF(([],"t1==>t2/\t3==>t4 = t3==>t1==>t2==>t4"),
    TAUT_TAC)
 in let t6 = PORR[t5] t4
 in let t7 = PORR[EQ_SYM_EQ] t6
 in let t8 = CONV_RULE (DEPTH_CONV FORALL_1PT_CONV) t7
 in let t9 = TAC_PROOF(([],"t1/\t2==>t3 = t1==>t2==>t3"),TAUT_TAC)
 in let t10 = PORR[SYM_RULE t9] t8
 in let t11 = BETA_CONV "(\v. po((t:^state->*)v) (x:*) /\ p v)v"
 in let t12 = PORR[SYM_RULE t11] t10
 in let t13 = PORR[SYM_RULE (SPEC_ALL implies_DEF)] t12
 in let t14 = PORR[monotonic_DEF] (ASSUME "monotonic(c:^ptrans)")
 in let t15 = MATCH_MP t14 t13
 in let t16 = TAC_PROOF
  (([],"(\v'. po((t:^state->*)v')(x:*) /\ p v') = p andd (\s.po(t s)x)"),
    PRT[and_DEF] THEN FUN_TAC THEN EQ_TAC THEN SUPER_TAC)
 in let t17 = PORR[t16] t15
 in let t18 = ASSUME "!(x:*).(p andd g andd (\(u:^state).t u = x))
     implies c(p andd (\u. po (t u) x))"
 in let t19 = MATCH_MP (CONJUNCT2(CONJUNCT2 implies_prop)) 
                       (CONJ (SPEC_ALL t18) t17)
 in let t20 = TAC_PROOF(([],
      "((p:^pred) andd (q andd r)) implies s 
       = (p andd r) implies ((q andd s) or (not q))"),
     EQ_TAC THEN LPORT[and_DEF;and_DEF;not_DEF;or_DEF;implies_DEF] THENL
     [SUPER_TAC THEN ASM_CASES_TAC "(q:^pred)u" THEN RES_TAC THEN ART[]
     ;SUPER_TAC THEN RES_TAC
     ])
 in PORR[t20] t19;;

let wellf_do_rule =
 let t1 = TAC_PROOF
  (([],"((g:^pred) or p) andd ((not g) or q) = 
        (g andd q) or ((not g) andd p)"), PRED_TAUT_TAC)
 in let t2 = PORR[t1] (UNDISCH(PORR[t99]do_unfold))
 in let t3 = TAC_PROOF
  (([],"(!(x:*). (p andd (\(u:^state).t u = x)) implies q) ==> p implies q"),
   LPORT[implies_DEF;and_DEF] THEN BETA_TAC THEN
   PORT[FORALL_SWAP_CONV "!(x:*)(u:^state). p u /\ (t u = x) ==> q u"] THEN
   DISCH_TAC THEN GEN_TAC THEN POP_ASSUM (ASSUME_TAC o
      (RR[] o SPECL["u:^state";"(t:^state->*)u"])) THEN
   POP_ASSUM ACCEPT_TAC)
 in let t4 = SPEC "do g (c:^ptrans)p" (GEN "q:^pred" t3)
 in let t5 = BETA_RULE 
  (SPEC "\(x:*). (p andd (\(u:^state).t u=x)) implies (do g c p)"
   (GEN_ALL wellf_INDUCT))
 in let t6 = IMP_TRANS t5 t4
 in let t7 = TAC_PROOF(([],
      "((p:^pred) andd q) implies (r or s) 
       = (p andd q) implies (r or (s andd p))"),
     EQ_TAC THEN LPORT[and_DEF;not_DEF;or_DEF;implies_DEF] THEN SUPER_TAC)
 in let t8 = LPORR[t7;SYM_RULE t2] lemma1
 in let t9 = UNDISCH(UNDISCH(DISCH_ALL(UNDISCH_ALL(DISCH_ALL t8))))
 in let t10 = MP t6 (GEN "x:*" t9)
 in prove
   ("monotonic (c:^ptrans) /\ wellf (po:*->*->bool) /\
    (!(x:*).(p andd g andd (\(u:^state).t u = x)) 
             implies  c(p andd (\u. po (t u) x)))
     ==> p implies (do g c p)",
   STRIP_TAC THEN ACCEPT_TAC t10);;

let correct_do_wellf =prove
 ("!g c po inv t p q. monotonic (c:^ptrans) /\
   wellf (po:*->*->bool) /\
    (p implies inv) /\
     (((not g) andd inv) implies q) /\
     (!x. correct (inv andd (g andd (\u. t u = x)))
                  c  
                  (inv andd (\u. po (t u) x)))
    ==> correct p (do g (c:^ptrans)) q",
  PORT[correct_DEF] THEN REPEAT STRIP_TAC THEN 
  IMP_RES_TAC wellf_do_rule THEN POP_ASSUM MP_TAC THEN
  SUBST_TAC[SPEC "inv:^pred" (GEN "q:^pred" do_not_guard)] THEN
  DISCH_TAC THEN IMP_RES_TAC mono_do THEN
  POP_ASSUM (ASSUME_TAC o (PORR[monotonic_DEF] o SPEC_ALL)) THEN
  RES_TAC THEN ASSUME_TAC (C2(C2 implies_prop)) THEN 
  RES_TAC THEN RES_TAC);;


% --- do: the ordinary invariant-bound theorems --- %
 
let num_do_rule = RR[num_wellf]
     (SPEC "$<" (INST_TYPE[":num",":*"] (GEN "po:*->*->bool"
      (DISCH_ALL wellf_do_rule))));;

let correct_do = prove
 ("!g c inv t p q.
       monotonic (c:^ptrans) /\
       p implies inv /\
       ((not g) andd inv) implies q /\
       (!x. correct (inv andd (g andd (\u. t u = x)))
                    c
                    (inv andd (\u. (t u) < x)))
       ==> correct p(do g c)q",
  REPEAT STRIP_TAC THEN 
  MATCH_MP_TAC (INST_TYPE[":num",":*"] correct_do_wellf) THEN ART[]
  THEN EXISTS_TAC "$<" THEN EXISTS_TAC "inv:^pred" THEN
  EXISTS_TAC "t:^state->num" THEN ART[num_wellf]);;


% --- block --- %

let correct_block = prove
 ("!p0.!c:^eptrans.!p q. correct (\(x,u).p u /\ p0(x,u)) c (\(x,u).q u)
   ==> correct p (block p0 c) q",
  LPORT[correct_DEF;block_DEF;implies_DEF] THEN PBETA_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[]);;


% --- save the results --- %

save_thm(`correct_assign`,correct_assign);;
save_thm(`correct_nondass`,correct_nondass);;
save_thm(`correct_seq`,correct_seq);;
save_thm(`correct_cond`,correct_cond);;
save_thm(`wellf_do_rule`,wellf_do_rule);;
save_thm(`correct_do_wellf`,correct_do_wellf);;
save_thm(`num_do_rule`,num_do_rule);;
save_thm(`correct_do`,correct_do);;
save_thm(`correct_block`,correct_block);;

close_theory();;
