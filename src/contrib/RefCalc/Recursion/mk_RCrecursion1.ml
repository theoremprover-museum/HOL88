% File: mk_RCrecursion1.ml

  refinement theorem for mu: recursion introduction
  corollary: loop correctness theorem
%

% --- regularity --- %

let regular_const = prove
 ("!c:^ptrans12. monotonic c ==> regular \x:^ptrans34.c",
   LRT[regular_DEF;pmonotonic_DEF;mono_mono_DEF;ref_prop] THEN
   REPEAT STRIP_TAC THEN ART[]);;

let regular_id = prove
 ("regular \x:^ptrans12.x",
   LPORT[regular_DEF;pmonotonic_DEF;mono_mono_DEF] THEN BETA_TAC THEN RT[] THEN
   REPEAT STRIP_TAC THEN ART[]);;

let regular_seq = prove
 ("!f:^ptrans12->^ptrans45. !f':^ptrans12->^ptrans34. regular f /\ regular f'
         ==>  regular (\x. (f x) seq (f' x))",
  LPORT[regular_DEF;pmonotonic_DEF;mono_mono_DEF;ref_DEF;seq_DEF] THEN
  BETA_TAC THEN LPORT[seq_DEF;monotonic_DEF] THEN REPEAT STRIP_TAC THENL
  [ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(el 5 l)
     (CONJ(el 3 l)(CONJ(el 2 l)(hd l))))) THEN 
   POP_ASSUM (ASSUME_TAC o SPEC "q:^pred3") THEN
   ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(el 8 l)
     (CONJ(el 4 l)(CONJ(el 3 l)(el 2 l))))) THEN 
   POP_ASSUM (ASSUME_TAC o SPEC "(f':^ptrans12->^ptrans34)c q") THEN
   ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(MATCH_MP(el 8 l)(el 4 l))(el 2 l))) THEN
   IMP_RES_TAC (C2(C2 implies_prop))
  ;PORT[seq_DEF] THEN
   ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(MATCH_MP(el 3 l)(el 2 l))(hd l))) THEN 
   ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(MATCH_MP(el 6 l)(el 3 l))(hd l))) THEN 
   ART[]
  ]);;

let regular_cond = prove
 ("!g. !f:^ptrans12->^ptrans34. !f'. regular f /\ regular f'
         ==>  regular (\x. cond g (f x) (f' x))",
  LPORT[regular_DEF;pmonotonic_DEF;mono_mono_DEF;ref_DEF] THEN BETA_TAC THEN
  LPORT[monotonic_DEF;cond_DEF;implies_DEF;and_DEF;or_DEF;not_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN ART[] THENL
  [ASSUM_LIST(\l.ACCEPT_TAC(MATCH_MP(MATCH_MP
      (el 9 l)(CONJ(el 5 l)(CONJ(el 4 l)(el 3 l))))(hd l)))
  ;ASSUM_LIST(\l.ACCEPT_TAC(MATCH_MP(MATCH_MP
      (el 7 l)(CONJ(el 5 l)(CONJ(el 4 l)(el 3 l))))(hd l)))
  ;ASSUM_LIST(\l.ACCEPT_TAC(MATCH_MP(MATCH_MP(MATCH_MP
      (el 7 l)(el 4 l))(el 3 l))(hd l)))
  ;ASSUM_LIST(\l.ACCEPT_TAC(MATCH_MP(MATCH_MP(MATCH_MP
      (el 5 l)(el 4 l))(el 3 l))(hd l)))
  ]);;

let Ach_least = prove
 ("!C (c:^ptrans12).(!c'. C c' ==> c' ref c) ==> (Ach C) ref c",
   LPORT[ref_DEF;Ach_DEF;lub_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT 
   STRIP_TAC THEN UNDISCH_TAC "(p:^pred2)u" THEN RES_TAC THEN ART[]);;

let thm1 = prove("t\/t'==>t'' = (t==>t'')/\(t'==>t'')",TAUT_TAC);;
let thm2 = prove
  ("(c2:^ptrans12) ref c3 ==> (c1 ref c2 ==> c1 ref c3)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC ref_prop);;
let mu_lemma = BETA_RULE(prove
 ("!C. regular(f:^ptrans12->^ptrans12) /\ (!i. monotonic (C i)) /\
   (!i. (C i) ref (Ach (\d.?j. (j<i) /\ (d = f(C j)))))
   ==> !i. (\i.(C i) ref (mu f))i",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC strong_induct THEN BETA_TAC THEN
  INDUCT_TAC THENL
  [POP_ASSUM (MP_TAC o SPEC "0") THEN 
   LRT[NOT_LESS_0;ref_DEF;Ach_DEF;lub_DEF;implies_DEF] THEN
   DISCH_TAC THEN REPEAT GEN_TAC THEN ART[]
  ;STRIP_TAC THEN ASSUM_LIST(\l.MP_TAC(SPEC "SUC n"(el 3 l))) THEN
   MATCH_MP_TAC thm2 THEN MATCH_MP_TAC Ach_least THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN
   IMP_RES_TAC(GSYM mu_fp) THEN POP_ASSUM SUBST1_TAC THEN
   ASSUME_TAC (ISPEC "f:^ptrans12->^ptrans12" mono_mu) THEN
   ASSUM_LIST(\l.ASSUME_TAC(SPEC"j:num"(el 8 l))) THEN
   IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL (PORR[pmonotonic_DEF]regular_DEF))))
  ]) );;


let C = "\i. (assert \u.t u < i) seq (c:^ptrans12)";;
let thm3 = prove("!i. (^C i) ref (^C(SUC i))",
  BETA_TAC THEN LPORT[ref_DEF;seq_DEF;assert_DEF;implies_DEF;and_DEF] THEN
  GEN_TAC THEN BETA_TAC THEN PORT[LESS_THM] THEN
  REPEAT STRIP_TAC THEN ART[]);;
let thm4 = prove("Ach(\c:^ptrans12. F) = \q.false",
  FUN_TAC THEN LRT[Ach_DEF;lub_DEF;false_DEF]);;
let thm5 = prove
 ("!C. Ach(\d:^ptrans12. ?j. j < (SUC i) /\ (d = C j))
   = (Ach(\d. ?j. (j < i) /\ (d = C j))) ach (C i)",
  GEN_TAC THEN FUN_TAC THEN LPORT[ach_DEF;Ach_DEF;lub_DEF;or_DEF] THEN
  FUN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
  [POP_ASSUM MP_TAC THEN ART[] THEN DISCH_TAC THEN
   ASSUM_LIST(\l.MP_TAC(el 4 l)) THEN PORT[LESS_THM] THEN STRIP_TAC THENL
   [DISJ2_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN ART[]
   ;DISJ1_TAC THEN EXISTS_TAC "(c:^ptrans12)f" THEN ART[] THEN
    EXISTS_TAC "(C:num->^ptrans12)j" THEN ART[] THEN
    EXISTS_TAC "j:num" THEN ART[]
   ]
  ;POP_ASSUM MP_TAC THEN ART[] THEN DISCH_TAC THEN
   EXISTS_TAC "p:^pred2" THEN ART[] THEN
   EXISTS_TAC "c:^ptrans12" THEN ART[] THEN
   EXISTS_TAC "j:num" THEN ART[LESS_THM]
  ;EXISTS_TAC "(C:num->^ptrans12)i f" THEN ART[] THEN
   EXISTS_TAC "(C:num->^ptrans12)i" THEN RT[] THEN
   EXISTS_TAC "i:num" THEN RT[LESS_SUC_REFL]
  ]);;
let thm6 = prove
 ("!C:num->^ptrans12. (!i. (C i) ref (C(SUC i)))
       ==> (!i. Ach (\d.?j. (j<i) /\ (d = C j))
            = ((i=0) => (\q.false) | C(PRE i)))",
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
  [LRT[NOT_LESS_0;thm4]
  ;LRT[NOT_SUC;PRE;thm5] THEN ART[] THEN
   MP_TAC(SPEC "i:num" num_CASES) THEN STRIP_TAC THEN ART[] THENL
   [FUN_TAC THEN LRT[ach_DEF;or_DEF;false_DEF] THEN BETA_TAC THEN
    FUN_TAC THEN REFL_TAC
   ;LRT[NOT_SUC;PRE] THEN ASSUM_LIST(\l.MP_TAC(SPEC"n:num"(el 3 l))) THEN
    CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
    LRT[ref_DEF;ach_DEF;implies_DEF;or_DEF] THEN REPEAT STRIP_TAC THEN
    FUN_TAC THEN EQ_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]
  ]]);;
let thm6a = prove
 ("monotonic(c:^ptrans12) ==> !i. monotonic(^C i)",
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC mono_seq THEN
  ART[mono_assert]);;
let thm7 =
  let th1 = PORR[pmonotonic_DEF](ASSUME"pmonotonic(f:^ptrans12->^ptrans12)") in
  let th2 = RR[UNDISCH thm6a](ISPECL["^C i";"^C(SUC i)"] th1) in
  let th3 = BETA_RULE(MATCH_MP th2 (SPEC_ALL thm3)) in
  let th4 = BETA_RULE(ISPEC "\i.(f:^ptrans12->^ptrans12)(^C i)" thm6) in
  MATCH_MP th4 (GEN "i:num" th3);;
let thm8 = prove
 ("pmonotonic(f:^ptrans12->^ptrans12) /\ monotonic(c:^ptrans12) /\
   (!i. (^C(SUC i)) ref (f(^C i)))
    ==> !i. (^C i) ref (Ach (\d.?j. (j<i) /\ (d = f(^C j))))",
  BETA_TAC THEN STRIP_TAC THEN PORT[thm7] THEN GEN_TAC THEN
  MP_TAC(SPEC "i:num" num_CASES) THEN STRIP_TAC THEN ART[] THENL
  [LRT[NOT_LESS_0;ref_DEF;seq_DEF;assert_DEF;and_DEF;false_DEF] THEN
   RT[implies_prop]
  ;LRT[NOT_SUC;PRE] THEN ART[]
  ]);;
let thm9 = BETA_RULE(prove
 ("regular(f:^ptrans12->^ptrans12) /\ monotonic(c:^ptrans12) /\ 
   (!i. (^C(SUC i)) ref (f(^C i)))
    ==> (!i. (^C i) ref (mu f))",
  PORT[regular_DEF] THEN STRIP_TAC THEN IMP_RES_TAC thm8 THEN
  IMP_RES_TAC (RR[regular_DEF]mu_lemma) THEN IMP_RES_TAC thm6a THEN
  POP_ASSUM (ASSUME_TAC o SPEC"t:*s2->num") THEN RES_TAC) );;
let thm10 = prove
 ("(!i. ((assert(\u. (t u) < i)) seq c) ref (c':^ptrans12))
   ==> c ref c'",
  LRT[ref_DEF;seq_DEF;assert_DEF;implies_DEF;and_DEF] THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN 
  ASSUM_LIST(\l.
     MP_TAC(SPECL["SUC((t:*s2->num)u)";"q:^pred1";"u:*s2"](el 2 l))) THEN
  RT[LESS_SUC_REFL] THEN STRIP_TAC THEN RES_TAC);;
let D = "\i:num. (assert \u.t u = i) seq (c:^ptrans12)";;
let thm11 = prove
 ("!i.^C(SUC i) = Ach(\d.?j. j<SUC i /\ (d = ^D j))",
  INDUCT_TAC THENL
  [PORT[thm5] THEN BETA_TAC THEN LRT[LESS_THM;NOT_LESS_0] THEN FUN_TAC THEN
   LRT[ach_DEF;Ach_DEF;lub_DEF;seq_DEF;assert_DEF;or_DEF;and_DEF;false_DEF]THEN
   FUN_TAC THEN RT[]
  ;PORT[thm5] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN BETA_TAC THEN
   FUN_TAC THEN LRT[ach_DEF;seq_DEF;assert_DEF;or_DEF;and_DEF] THEN
   FUN_TAC THEN RT[LESS_THM] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ART[]
  ]);;
let thm12 = prove
 ("!C. (!i.(C i) ref C(SUC i)) /\ (!i.(^D i) ref (C i))
   ==> (!i.(Ach(\d.?j. j<SUC i /\ (d = ^D j))) ref (C i:^ptrans12))",
  BETA_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC Ach_least THEN 
  BETA_TAC THEN SPEC_TAC("i:num","i:num") THEN INDUCT_TAC THENL
  [RT[LESS_THM;NOT_LESS_0] THEN
   CONV_TAC (DEPTH_CONV EX_1PT_CONV) THEN
   CONV_TAC FORALL_1PT_CONV THEN ART[]
  ;PORT[LESS_THM] THEN REPEAT STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN ART[] THEN DISCH_THEN SUBST1_TAC THEN ART[]
   ;RES_TAC THEN ASSUM_LIST(\l.ASSUME_TAC(SPEC"i:num"(el 6 l))) THEN
    IMP_RES_TAC ref_prop
  ]]);;
let thm13 =
  let th1 = PORR[pmonotonic_DEF](ASSUME"pmonotonic(f:^ptrans12->^ptrans12)") in
  let th2 = RR[UNDISCH thm6a](ISPECL["^C i";"^C(SUC i)"] th1) in
  MATCH_MP (BETA_RULE th2) (SPEC "i:num" (BETA_RULE thm3));;
let thm14 = prove
  ("(c2:^ptrans12) ref c1 ==> (c1 ref c3 ==> c2 ref c3)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC ref_prop);;
let thm15 = LRR[GSYM(BETA_RULE thm11);thm13] (BETA_RULE (SPEC
   "\i:num.(f:^ptrans12->^ptrans12)((assert(\u. (t u) < i)) seq c)" thm12));;
let mu_thm = prove
 ("!c. regular(f:^ptrans12->^ptrans12) /\ monotonic c /\
     (?t.!i. ((assert(\u.t u=i)) seq c) ref (f((assert(\u.(t u)<i)) seq c)))
     ==> c ref (mu f)",
  PORT[regular_DEF] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC thm10 THEN
  MATCH_MP_TAC (PORR[regular_DEF]thm9) THEN
  ART[] THEN GEN_TAC THEN IMP_RES_TAC thm15 THEN ART[]);;


% --- loop correctness derived as special case of recursion --- %

let lemma1 = prove
  ("!c:^ptrans. !p q. monotonic c ==>
     (correct p c q = ((assert p) seq (nondass \u v. q v)) ref c)",
  LPORT[monotonic_DEF;correct_DEF;ref_DEF;seq_DEF;assert_DEF;nondass_DEF;implies_DEF;
        and_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THEN 
  REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN POP_ASSUM MATCH_MP_TAC THEN RT[]);;
let lemma2 = prove
  ("!c:^ptrans. !p q q'.
     correct p c q
	   ==> ((assert p) seq (nondass \u v:*s. q' v))
	      ref (c seq (assert q) seq (nondass \u v. q' v))",
  LPRT[correct_DEF;ref_DEF;seq_DEF;assert_DEF;nondass_DEF;implies_DEF;and_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN 
  CONV_TAC(DEPTH_CONV ETA_CONV) THEN ART[]);;
let lemma3 = prove
  ("!g. !c:^ptrans. c = cond g ((assert g) seq c) ((assert(not g)) seq c)",
  REPEAT GEN_TAC THEN FUN_TAC THEN LPRT[cond_DEF;seq_DEF;assert_DEF;and_DEF;or_DEF;
     not_DEF] THEN FUN_TAC THEN ASM_CASES_TAC "(g:^pred)x" THEN ART[]);;
let lemma4 = prove
  ("!g. !c1:^ptrans. !c2 c1' c2'. c1 ref c1' /\ c2 ref c2' ==>
       (cond g c1 c2) ref (cond g c1' c2')",
  LPRT[ref_DEF;cond_DEF;implies_DEF;and_DEF;or_DEF;not_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;
let lemma5 = prove("!p:^pred. !q. (assert p) seq (assert q) = assert (p andd q)",
  REPEAT GEN_TAC THEN FUN_TAC THEN LPRT[seq_DEF;assert_DEF;and_DEF] THEN
  BETA_TAC THEN FUN_TAC THEN MATCH_ACCEPT_TAC CONJ_ASSOC);;
let lemma6 = prove
   ("!p:^pred. !q:^pred.
       (p implies q) ==> ((assert p) seq (nondass(\u v. q v))) ref skip",
  LPRT[ref_DEF;seq_DEF;assert_DEF;nondass_DEF;skip_DEF;implies_DEF;and_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ART[]);;
let th0 = prove("t==>t'==>t'' = t/\t'==>t''",TAUT_TAC);;
let thm1 = PORR[th0](DISCH_ALL
  (LPORR[GSYM do_DEF;SYM(UNDISCH(SPEC_ALL(SPEC"do g(c:^ptrans)" lemma1)))]
  (ADD_ASSUM "monotonic(do g (c:^ptrans))"(BETA_RULE 
  (ISPECL["\x:^ptrans.cond g (c seq x) skip";
     "(assert p) seq (nondass(\u:*s. \v:*s. q v))"]
    (GEN_ALL mu_thm))))));;
let th1 = BETA_RULE
  (ISPECL["g:^pred";"\x:^ptrans.(c:^ptrans) seq x";"\x:^ptrans.(skip:^ptrans)"]
        regular_cond);;
let th2 = BETA_RULE
  (ISPECL["\x:^ptrans.(c:^ptrans)";"\x:^ptrans.x"] regular_seq);;
let th3 = 
  SPECL["g:^pred";
        "(assert(\u.t u=(i:num)))seq((assert p)seq(nondass(\u:*s.\v:*s.q v)))"] lemma3;;
let th4 = AP_THM(AP_TERM "seq:^ptrans->^ptrans->^ptrans"
   (INST_TYPE[":*s",":*s1";":*s",":*s2";":*s",":*s3";":*s",":*s4"] seq_assoc))
     "c4:^ptrans";;
let and_sym = prove("!p:^pred. !q. p andd q = q andd p",PRED_TAUT_TAC);;

let lemma7 = prove
 ("!c:^ptrans. !p q p. monotonic c /\
   (!i. correct (p andd g andd (\u. t u = i)) c (p andd (\u. t u < i)))
   /\ ((not g) andd p) implies q
   ==> correct p (do g c) q",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC thm1 THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC mono_do THEN ART[]
  ;MATCH_MP_TAC th1 THEN RT[MATCH_MP regular_const mono_skip] THEN
   MATCH_MP_TAC th2 THEN RT[regular_id] THEN MATCH_MP_TAC regular_const THEN ART[]
  ;mono_TAC
  ;EXISTS_TAC "t:^state->num" THEN GEN_TAC THEN SUBST1_TAC th3 THEN
   MATCH_MP_TAC lemma4 THEN CONJ_TAC THENL
   [LPRT[seq_assoc;lemma5] THEN LPORT[SYM seq_assoc;SYM seq_assoc] THEN
    LPORT[ISPEC"assert(p:^pred)"(GEN_ALL seq_assoc);lemma5;and_sym] THEN 
    MATCH_MP_TAC lemma2 THEN FIRST_ASSUM MATCH_ACCEPT_TAC
   ;LPRT[seq_assoc;lemma5] THEN MATCH_MP_TAC lemma6 THEN POP_ASSUM MP_TAC THEN
    LPRT[implies_DEF;and_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN 
    RES_TAC THEN ART[]
  ]]);;
let lemma8 = prove
  ("!c:^ptrans. !p' p q. p' implies p /\ correct p c q ==> correct p' c q",
   LPORT[correct_DEF;implies_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;
let do_correct = prove
 ("!g (c:^ptrans) inv t p q.
    monotonic c /\
    p implies inv /\
    ((not g) andd inv) implies q /\
    (!x.
      correct
      (inv andd (g andd (\s. t s = x)))
      c
      (inv andd (\s. (t s) < x))) ==>
    correct p(do g c)q",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma8 THEN EXISTS_TAC "inv:^pred" THEN
  ART[] THEN MATCH_MP_TAC lemma7 THEN ART[]);;

save_thm(`regular_const`,regular_const);;
save_thm(`regular_id`,regular_id);;
save_thm(`regular_seq`,regular_seq);;
save_thm(`regular_cond`,regular_cond);;
save_thm(`mu_thm`,mu_thm);;
