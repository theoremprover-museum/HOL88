% File: mk_RCcommand4.ml
   junctivity properties ("healthiness")
%


% --- relating junctivities --- %

let mono_subuniconj =
 let t1 = TAC_PROOF
  ((["(P:^pred1->bool)p'"],
    "(\s. !p. P p ==> p s) implies (p':^pred1)"),
   PORT[implies_DEF] THEN SUPER_TAC)
 in prove("monotonic (c:^ptrans12) ==>
          (c (glb P)) implies (glb (\q. ?p. P p /\ (q=c p)))",
   PORT[monotonic_DEF] THEN DISCH_TAC THEN LPORT[glb_DEF;implies_DEF] 
   THEN BETA_TAC THEN REPEAT STRIP_TAC THEN ART[] THEN ASSUME_TAC t1 
   THEN RES_TAC THEN POP_ASSUM (ASSUME_TAC o PORR[implies_DEF]) THEN
   RES_TAC);;

let biconj_mono = 
 let t1 = TAC_PROOF(([],"(p:^pred1) implies q ==> (p = p andd q)"),
          RT[implies_DEF;and_DEF] THEN DISCH_TAC THEN FUN_TAC THEN 
          EQ_TAC THEN SUPER_TAC)
 and t2 = TAC_PROOF(([],"((p:^pred1) andd q) implies q"),
           RT[and_DEF;implies_DEF] THEN BETA_TAC THEN TAUT_TAC)
 in TAC_PROOF
  (([],"biconjunctive (c:^ptrans12) ==> monotonic c"),
   RT[biconjunctive_DEF;monotonic_DEF] THEN REPEAT STRIP_TAC THEN 
   PORT[UNDISCH t1] THEN ART[t2]);;

let conj_biconj = 
 let t1 = TAC_PROOF
  (([],"(\q'. ?p'. ((p' = p) \/ (p' = q)) /\ (q' = (c:^ptrans12) p')) = 
       (\p'. (p' = c p) \/ (p' = c q))"),
   FUN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ART[] THENL
   [EXISTS_TAC "p:^pred1" THEN RT[]
   ;EXISTS_TAC "q:^pred1" THEN RT[]
   ])
 in let t2 = TAC_PROOF
   (([],"?(p'':^pred1).(\p'. (p' = p) \/ (p' = q))p''"),
    BETA_TAC THEN EXISTS_TAC "p:^pred1" THEN RT[])
 in TAC_PROOF
  (([],"conjunctive (c:^ptrans12) ==> biconjunctive c"),
   LPORT[conjunctive_DEF;biconjunctive_DEF;and_glb] THEN 
   REPEAT STRIP_TAC THEN POP_ASSUM (\th. ASSUME_TAC (MATCH_MP th t2))
   THEN ART[] THEN BETA_TAC THEN RT[t1]);;

let conj_mono = IMP_TRANS conj_biconj biconj_mono;;

let uniconj_conjterm =
 let t1 = TAC_PROOF
  (([],"glb(\p:^pred.F)=true"),
   LPORT[glb_DEF;true_DEF] THEN FUN_TAC THEN EQ_TAC THEN SUPER_TAC)
 in let t2 = TAC_PROOF
  (([],"~(?(p:^pred1). P p) ==> (P=\p.F)"),
   CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THEN 
   FUN_TAC THEN ART[])
 in TAC_PROOF
  (([],"uniconjunctive (c:^ptrans12) = 
         conjunctive c /\ terminating c"),
   LPORT[uniconjunctive_DEF;conjunctive_DEF;terminating_DEF] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ART[] THENL
   [POP_ASSUM 
     (ASSUME_TAC o (RR[] o BETA_RULE o RR[t1] o SPEC "\(p:^pred1).F"))
    THEN FIRST_ASSUM ACCEPT_TAC
   ;POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o 
     (CONV_RULE LEFT_IMP_EXISTS_CONV) o SPEC_ALL)
    THEN ASM_CASES_TAC "?(p:^pred1). P p" THENL
    [POP_ASSUM CHOOSE_TAC THEN DISCH_TAC THEN RES_TAC
    ;IMP_RES_TAC t2 THEN ART[] THEN BETA_TAC THEN ART[t1]
   ]]);;

let uniconj_conj =
 DISCH_ALL (CONJUNCT1 (PORR[uniconj_conjterm] 
       (ASSUME "uniconjunctive (c:^ptrans12)")));;

let uniconj_biconj = IMP_TRANS uniconj_conj conj_biconj;;

let uniconj_mono = IMP_TRANS uniconj_biconj biconj_mono;;


% --- theorems for proving monotonicity of a command --- %

let mono_abort = prove
  ("monotonic (abort:^ptrans12)",
   LRT[monotonic_DEF;abort_DEF;implies_prop]);;
let mono_skip = prove
  ("monotonic (skip:^ptrans)",
   LPORT[monotonic_DEF;skip_DEF] THEN BETA_TAC THEN RT[]);;
let mono_assert = prove
 ("!b:^pred. monotonic (assert b)",
  LPORT[monotonic_DEF;assert_DEF;implies_DEF;and_DEF] THEN SUPER_TAC);;
let mono_assign = TAC_PROOF
 (([],"!(e:^state1->^state2). monotonic (assign e)"),
  LPORT[monotonic_DEF;assign_DEF;implies_DEF] THEN SUPER_TAC);;
let mono_nondass = prove
 ("!(p:^state1->^state2->bool). monotonic (nondass p)",
  LPORT[monotonic_DEF;nondass_DEF;implies_DEF] THEN SUPER_TAC THEN RES_TAC);;
let mono_seq = TAC_PROOF
 (([],"!(c:^ptrans23)(c':^ptrans12). monotonic c /\ monotonic c' 
         ==> monotonic (c seq c')"),
  LPORT[monotonic_DEF;seq_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC 
  THEN RES_TAC);;
let mono_cond = TAC_PROOF
 (([],"!g (c1:^ptrans12) (c2:^ptrans12). 
       monotonic c1 /\ monotonic c2 ==> monotonic (cond g c1 c2)"),
  LPORT[monotonic_DEF;cond_DEF;implies_DEF;or_DEF;not_DEF] THEN RT[and_DEF]
  THEN SUPER_TAC);;
let mono_do =
 let t = prove
  ("(p:^pred)implies q ==>
      (((g andd (c q')) or ((not g) andd q)) implies q' ==>
      ((g andd (c q')) or ((not g) andd p)) implies q')",
   LPORT[implies_DEF;or_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN REPEAT 
   STRIP_TAC THEN RES_TAC THEN RES_TAC)
 in prove
  ("!g (c:^ptrans). monotonic c  ==> monotonic (do g c)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC do_thm THEN ART[monotonic_DEF;
     fix_DEF;glb_DEF] THEN REPEAT STRIP_TAC THEN PORT[implies_DEF] THEN
   BETA_TAC THEN GEN_TAC THEN REPEAT STRIP_TAC THEN IMP_RES_TAC t THEN
   RES_TAC);;
let mono_dolib =
  let t = TAC_PROOF
    (([],"(p:^pred)implies q ==> (x or (g andd p))implies(x or (g andd q))"),
     LPORT[implies_DEF;and_DEF;or_DEF] THEN SUPER_TAC)
  in TAC_PROOF
   (([],"monotonic (c:^ptrans) ==> monotonic (dolib g c)"),
    DISCH_TAC THEN ASSUME_TAC (RR[monotonic_DEF] (ASSUME 
     "monotonic (c:^ptrans)")) THEN PORT[monotonic_DEF] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC dolib_implies THEN
    IMP_RES_TAC dolib_unfold THEN POART[] THEN
    PORT[SYM_RULE (AP_TERM "c:^ptrans" (UNDISCH_ALL dolib_unfold))] THEN
    MATCH_MP_TAC t THEN FIRST_ASSUM ACCEPT_TAC);;
let mono_block = prove
 ("!p. !c:^eptrans. monotonic c ==> monotonic (block p c)",
   LPORT[monotonic_DEF;block_DEF;implies_DEF] THEN GEN_TAC THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN
   POP_ASSUM MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   P_PGEN_TAC "y:*,u:*s" THEN PBETA_TAC THEN ART[]);;


% --- intermezzo: connection between wp and wlp --- %

let do_implies_true = 
  let t = prove
   ("((g:^pred)andd q) or ((not g)andd true) = (not g)or q",PRED_TAUT_TAC)
  in RR[t] (SPEC "true:^pred" (GEN "p:^pred" do_implies));;
let do_dolib =
  let t99 = prove
    ("(g andd((c:^ptrans)p))or((not g) andd q)=(g or q)andd((not g) or (c p))",
     PRED_TAUT_TAC) in
  let t11 = prove
     ("((p:^pred)=p') /\ (q=q') ==> ((not p) or q = (not p') or q')",
      REPEAT STRIP_TAC THEN ART[])
  in let t12 = MATCH_MP t11 (CONJ (UNDISCH_ALL (PORR[t99]dolib_unfold))
                                  (UNDISCH_ALL (PORR[t99]do_unfold)))
  in let lemma1 = TAC_PROOF
    ((["biconjunctive (c:^ptrans)"],
       "(not (dolib g (c:^ptrans) q)) or (do g c q) =
        (not g) or (not (c(dolib g c q))) or (c(do g c q))"),
     IMP_RES_TAC biconj_mono THEN PORT[t12] THEN PRED_TAUT_TAC)
  in let t21 = RR[biconjunctive_DEF] (ASSUME "biconjunctive(c:^ptrans)")
  in let t22 = SYM_RULE (SPEC_ALL t21)
  in let t23 = TAC_PROOF
       (([],"(p:^pred) andd ((not p) or q) = p andd q"),PRED_TAUT_TAC)
  in let lemma2 = TAC_PROOF
    ((["biconjunctive (c:^ptrans)"],
      "((c:^ptrans)((not p)or q)) implies ((not (c p)) or (c q))"),
     PORT[SYM_RULE shunt] THEN LPORT[t22;t23;t21] THEN PRED_TAUT_TAC)
  in let t31 = TAC_PROOF(([],"(p:^pred)implies q ==> (g or p)implies(g or q)"),
     LPORT[implies_DEF;or_DEF] THEN SUPER_TAC)
  in let lemma3 = TAC_PROOF
    ((["biconjunctive (c:^ptrans)"],
      "((dolib g(c:^ptrans)q) andd (do g c true)) implies (do g c q)"),
     PORT[shunt] THEN IMP_RES_TAC biconj_mono THEN 
     MATCH_MP_TAC (UNDISCH (PORR[t99]do_implies_true)) THEN 
     PORT[lemma1] THEN MATCH_MP_TAC t31 THEN
     PORT[SYM_RULE lemma1] THEN RT[lemma2])
  in let t = TAC_PROOF
    (([],"(p:^pred) implies q /\ p implies r ==> p implies (q andd r)"),
     LPORT[implies_DEF;and_DEF] THEN SUPER_TAC)
  in let t0 = TAC_PROOF(([],"(q:^pred) implies true"),PRED_TAUT_TAC)
  in let t1 = RR[monotonic_DEF] (UNDISCH (SPEC_ALL mono_do))
  in let t2 = UNDISCH (IMP_TRANS 
      (INST_TYPE[":*s",":*s1";":*s",":*s2"] biconj_mono)
      (DISCH_ALL (MP (SPECL["q:^pred";"true:^pred"] t1) t0)))
  in let t3 = LRR[UNDISCH gfix_fp;implies_prop]
      (SPEC "gfix(f:^ptrans)" fix_least)
  in let t4 = SPEC "\p'. (g or p) andd ((not g) or ((f:^ptrans) p'))"
      (GEN "f:^ptrans" (DISCH_ALL t3))
  in let t5 = IMP_TRANS (PORR[t99]do_mono_lemma) t4
  in let t6 = RR[SYM(UNDISCH(SPEC_ALL(PORR[t99]do_thm)));
                 SYM_RULE (SPEC_ALL(PORR[t99]dolib_DEF))]
      (UNDISCH (SPECL["c:^ptrans";"q:^pred"] (GENL["f:^ptrans";"p:^pred"] t5)))
  in let t7 = UNDISCH (IMP_TRANS 
     (INST_TYPE[":*s",":*s1";":*s",":*s2"] biconj_mono) (DISCH_ALL t6))
  in let lemma4 = MATCH_MP t (CONJ t7 t2)
 in MATCH_MP (CONJUNCT1 (CONJUNCT2 implies_prop)) (CONJ lemma4 lemma3);;


% --- theorems for proving strictness of a command --- %

let strict_abort = prove
 ("strict (abort:^ptrans12)",
  LPORT[strict_DEF;abort_DEF] THEN PRED_TAUT_TAC);;
let strict_skip = prove
 ("strict (skip:^ptrans)",
  LPORT[strict_DEF;skip_DEF] THEN PRED_TAUT_TAC);;
let strict_skip = prove
 ("strict (skip:^ptrans)",
  LPORT[strict_DEF;skip_DEF] THEN PRED_TAUT_TAC);;
let strict_assert = prove
 ("!(b:^pred). strict (assert b)",
  LPORT[strict_DEF;assert_DEF] THEN PRED_TAUT_TAC);;
let strict_assign = prove
 ("!(e:*s1->*s2). strict (assign e)",
  LPORT[strict_DEF;assign_DEF;and_DEF;false_DEF] THEN BETA_TAC THEN RT[]);;
let strict_nondass = prove
 ("strict(nondass(P:*s1->*s2->bool)) = !u.?v. P u v",
  LPORT[strict_DEF;nondass_DEF;false_DEF] THEN BETA_TAC THEN 
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN RT[] THEN
  CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN RT[NOT_CLAUSES]);;
let strict_seq = prove
 ("!(c:^ptrans23)(c':^ptrans12). 
         strict c /\ strict c' ==> strict (c seq c')",
  LPORT[strict_DEF;seq_DEF;false_DEF] THEN REPEAT STRIP_TAC THEN ART[]);;
let strict_cond = prove
 ("!b. !c1:^ptrans12. !c2:^ptrans12. strict c1 /\ strict c2
    ==> strict (cond b c1 c2)",
  LPORT[strict_DEF;cond_DEF;false_DEF;and_DEF;or_DEF;not_DEF] THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN ART[]);;
let th1 = prove("(p:^pred)implies false ==> (p = false)",
  LPORT[implies_DEF;false_DEF] THEN BETA_TAC THEN STRIP_TAC THEN
  FUN_TAC THEN EQ_TAC THEN ART[]);;
let strict_do = prove
 ("!g (c:^ptrans). monotonic c /\ strict c  ==> strict (do g c)",
   PORT[strict_DEF] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC do_thm THEN
   ART[] THEN MATCH_MP_TAC th1 THEN MATCH_MP_TAC fix_least THEN BETA_TAC THEN
   ART[] THEN PRED_TAUT_TAC);;
let strict_block = 
 let thm1 = prove("(\(x:*,v:*s).F) = (\u.F)",FUN_TAC THEN PBETA_TAC THEN RT[])
 in prove
 ("!p. !c:^eptrans. (!u.?x. p(x,u)) ==> strict c ==> strict (block p c)",
   LPORT[strict_DEF;block_DEF;false_DEF] THEN 
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN RT[] THEN
   REPEAT STRIP_TAC THEN
   ASSUM_LIST(\l.MP_TAC(SPEC "x:*s" (el 3 l))) THEN STRIP_TAC THEN
   RES_TAC THEN POP_ASSUM MP_TAC THEN ART[thm1]);;


% --- theorems for proving conjunctivity of a command --- %

let conj_abort = prove
 ("conjunctive (abort:^ptrans12)",
  LPORT[conjunctive_DEF;abort_DEF;false_DEF;glb_DEF] THEN REPEAT STRIP_TAC THEN
  FUN_TAC THEN EQ_TAC THEN RT[FALSITY] THEN CONV_TAC NOT_FORALL_CONV THEN
  EXISTS_TAC "\v:*s2. F" THEN RT[] THEN EXISTS_TAC "p:^pred1" THEN ART[]);;
let conj_skip = prove
 ("conjunctive (skip:^ptrans)",
  LPORT[conjunctive_DEF;skip_DEF;CONJ_SYM] THEN REPEAT STRIP_TAC THEN
  RHS_ORT1 EQ_SYM_EQ THEN CONV_TAC(DEPTH_CONV EX_1PT_CONV) THEN
  CONV_TAC(DEPTH_CONV ETA_CONV) THEN REFL_TAC);;
let conj_assert = prove
 ("!b:^pred. conjunctive (assert b)",
  LPORT[conjunctive_DEF;assert_DEF;and_DEF;glb_DEF] THEN REPEAT STRIP_TAC
  THEN FUN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THENL
  [BETA_TAC THEN ART[]
  ;POP_ASSUM (\t.RT[BETA_RULE(CONV_RULE FORALL_1PT_CONV t)])
  ;POP_ASSUM (\t.ALL_TAC) THEN
   POP_ASSUM (\t.RT[BETA_RULE(CONV_RULE FORALL_1PT_CONV t)])
  ]);;
let conj_assign = prove
 ("!(e:^state1->^state2). conjunctive (assign e)",
  LPORT[conjunctive_DEF;assign_DEF;and_DEF;glb_DEF] THEN REPEAT STRIP_TAC
  THEN FUN_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [RES_TAC THEN ART[]
  ;ASSUM_LIST(\[t1;t2;t3].MATCH_MP_TAC 
    (BETA_RULE (SPEC "\x.(p'((e:*s1->*s2)x):bool)"t2))) THEN
   EXISTS_TAC "p':^pred2" THEN ART[]
  ]);;
let conj_nondass = prove
 ("!(p:^state1->^state2->bool). conjunctive (nondass p)",
  LPORT[conjunctive_DEF;nondass_DEF;and_DEF;glb_DEF] THEN REPEAT STRIP_TAC
  THEN FUN_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [ART[] THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
  ;ASSUM_LIST(\[t1;t2;t3;t4].ASSUME_TAC (RR[] (BETA_RULE
    (SPEC "\x.!v'.(p:^state1->^state2->bool) x v' ==> p'' v'" t3)))) THEN
   POP_ASSUM (ASSUME_TAC o RR[] o SPEC "p'':^pred2" o
       CONV_RULE LEFT_IMP_EXISTS_CONV) THEN RES_TAC
  ]);;
let conj_seq = 
 let th1 = prove
  ("(\q.?p'. (?p. P p /\ (p' = c' p)) /\ (q = c p')) = 
        (\q.?p. P p /\ (q = (c:^ptrans23)((c':^ptrans12) p)))",
   FUN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC "p:^pred1" THEN ART[]
   ;EXISTS_TAC "(c':^ptrans12)p" THEN ART[] THEN
    EXISTS_TAC "p:^pred1" THEN ART[]
   ]) in
 prove
  ("!(c:^ptrans23)(c':^ptrans12). 
       conjunctive (c:^ptrans23) /\ conjunctive (c':^ptrans12) ==>
        conjunctive (c seq c')",
   LPORT[conjunctive_DEF;seq_DEF] THEN REPEAT STRIP_TAC THEN 
   RES_TAC THEN ART[] THEN  SUBGOAL_THEN 
      "?p':^pred2.(\q. ?p:^pred1. P p /\ (q = c' p))p'" ASSUME_TAC THENL
   [BETA_TAC THEN EXISTS_TAC "(c':^ptrans12)p" THEN
    EXISTS_TAC "p:^pred1" THEN ART[]
   ;ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(el 5 l)(hd l))) THEN
    POP_ASSUM SUBST1_TAC THEN BETA_TAC THEN RT[th1]   
   ]);;
let conj_cond = 
 let thm1 = prove
  ("cond b(c1:^ptrans12)c2 q = ((not b) or (c1 q)) andd (b or (c2 q))",
   LRT[cond_DEF] THEN PRED_TAUT_TAC) in
 let thm2 = BETA_RULE(ISPECL["\p.(not b)or((c1:^ptrans12)p)";
       "\p.b or((c2:^ptrans12)p)"] glb_and) in
 let thm3 = prove
  ("(?p'. (?p. P p /\ (p' =(c2:^ptrans12)p)) /\ (q = b or p'))
      = (?p. P p /\ (q = b or (c2 p)))",
   EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC "p:^pred1" THEN ART[]
   ;EXISTS_TAC "(c2:^ptrans12)p" THEN ART[] THEN
    EXISTS_TAC "p:^pred1" THEN ART[]
   ]) in
 prove
 ("!b. !c1:^ptrans12. !c2:^ptrans12. conjunctive c1 /\ conjunctive c2
    ==> conjunctive (cond b c1 c2)",
  LPORT[conjunctive_DEF;thm1] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
  ART[] THEN LPORT[thm2;or_into_glb] THEN BETA_TAC THEN RT[thm3]);;
let conj_dolib = 
 let th1 = prove("t\/t' = ~t==>t'",TAUT_TAC) in
 let t99 = prove
    ("(g andd((c:^ptrans)p))or((not g) andd q)=(g or q)andd((not g) or (c p))",
     PRED_TAUT_TAC) in
 prove("!g (c:^ptrans). conjunctive c ==> conjunctive (dolib g c)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC conj_mono THEN
   PORT[conjunctive_DEF] THEN REPEAT STRIP_TAC THEN
   IMP_RES_TAC mono_dolib THEN 
   POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN IMP_RES_TAC 
    (ISPEC "dolib(g:^pred)c" (GEN "c:^ptrans12"(DISCH_ALL mono_subuniconj)))
   THEN MATCH_MP_TAC (C1(C2 implies_prop)) THEN
   CONJ_TAC THEN ART[] THEN MATCH_MP_TAC(PORR[t99]dolib_implies) THEN
   SUBGOAL_THEN "?p'.(\q. ?p. P p /\ (q=dolib g (c:^ptrans) p))p'"
           ASSUME_TAC THENL
   [BETA_TAC THEN EXISTS_TAC "dolib g (c:^ptrans) p" THEN
    EXISTS_TAC "p:^pred" THEN ART[]
   ;ASSUM_LIST(\l. SUBST1_TAC (MATCH_MP
    (PORR[conjunctive_DEF](ASSUME "conjunctive(c:^ptrans)"))(hd l))) THEN
    BETA_TAC THEN CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV) THEN
    CONV_TAC (ONCE_DEPTH_CONV SWAP_EXISTS_CONV) THEN
    PORT[GSYM CONJ_ASSOC] THEN PORT[CONJ_SYM] THEN PORT[GSYM CONJ_ASSOC] THEN 
    CONV_TAC (ONCE_DEPTH_CONV EX_1PT_CONV) THEN PORT[CONJ_SYM] THEN
    CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV[UNDISCH(PORR[t99]dolib_unfold)]))
    THEN LPORT[implies_DEF;glb_DEF;and_DEF;or_DEF;not_DEF] THEN BETA_TAC THEN
    REPEAT STRIP_TAC THEN LPORT[th1;NOT_CLAUSES] THEN REPEAT STRIP_TAC THENL
    [ASSUM_LIST(\l. ASSUME_TAC(BETA_RULE
         (SPEC"\u:*s.(g u \/ p' u)/\(~g u \/ c(dolib g c p')u)"(el 3 l))))
     THEN POP_ASSUM MP_TAC THEN ART[] THEN DISCH_THEN MATCH_MP_TAC THEN
     EXISTS_TAC "p':^pred" THEN ART[]
    ;POP_ASSUM SUBST1_TAC THEN
     ASSUM_LIST(\l. ASSUME_TAC(BETA_RULE
         (SPEC"\u:*s.(g u \/ p'' u)/\(~g u \/ c(dolib g c p'')u)"(el 3 l))))
     THEN POP_ASSUM MP_TAC THEN ART[] THEN DISCH_THEN MATCH_MP_TAC THEN
     EXISTS_TAC "p'':^pred" THEN ART[]
   ]]);;
let conj_do = 
 let t1 = PORR[conjunctive_DEF] (UNDISCH (SPEC_ALL conj_dolib)) in
 prove
  ("!g (c:^ptrans). conjunctive c ==> conjunctive (do g c)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC conj_biconj THEN
   LPORT[conjunctive_DEF;do_dolib] THEN GEN_TAC THEN DISCH_TAC THEN
   ASSUM_LIST(\l.SUBST1_TAC(MATCH_MP t1 (hd l))) THEN
   LPORT[glb_DEF;and_DEF] THEN FUN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL
   [RES_TAC THEN ART[] THEN BETA_TAC THEN ART[] THEN
    POP_ASSUM (MATCH_ACCEPT_TAC o (CONV_RULE FORALL_1PT_CONV))
   ;POP_ASSUM SUBST1_TAC THEN ASSUM_LIST(\l. MP_TAC
      (SPEC "(\v. dolib g(c:^ptrans)p' v /\ do g c true v)"(el 2 l))) THEN
    BETA_TAC THEN CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
    DISCH_THEN (MP_TAC o SPEC "p':^pred") THEN ART[] THEN STRIP_TAC THEN ART[]
   ;UNDISCH_TAC "?p.(P:^pred->bool)p" THEN STRIP_TAC THEN
    ASSUM_LIST(\l. MP_TAC
      (SPEC "(\v. dolib g(c:^ptrans)p v /\ do g c true v)"(el 2 l))) THEN
    BETA_TAC THEN CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
    DISCH_THEN (MP_TAC o SPEC "p:^pred") THEN ART[] THEN STRIP_TAC THEN ART[]
   ]);;

let thm1 = prove("(\(x:*,v:*s).(f v:bool)) = (\u.f(SND u))",
    FUN_TAC THEN PBETA_TAC THEN RT[]);;
let thm2 = prove
 ("block p (c:^eptrans) =
    (nondass \u (x,u').(u'=u)/\ p(x,u')) seq c seq (assign \(x,u).u)",
  FUN_TAC THEN LPRT[block_DEF;seq_DEF;nondass_DEF;assign_DEF] THEN
  FUN_TAC THEN PBETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [ASSUM_LIST(\l.ASSUME_TAC(RR[SYM(el 2 l)](SPEC "FST(u':*#*s)"(el 3 l)))) THEN
   RES_TAC THEN POP_ASSUM MP_TAC THEN RT[thm1]
  ;ASSUM_LIST(\l.IMP_RES_TAC(RR[](SPEC "x':*,x:*s"(el 2 l)))) THEN
   POP_ASSUM MP_TAC THEN RT[thm1]
  ]);;
let conj_block = prove
 ("!p. !c:^eptrans. conjunctive c ==> conjunctive (block p c)",
  PORT[thm2] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC conj_seq THEN
  RT[conj_nondass] THEN MATCH_MP_TAC conj_seq THEN ART[conj_assign]);;

% --- nondass is normal form for universally conjunctive commands --- %

let nondass_complete =
 let lemma2 = prove
  ("uniconjunctive(c:^ptrans12) 
          ==> (c q s = (glb(\q. c q s) implies q))",
   DISCH_TAC THEN IMP_RES_TAC uniconj_mono
   THEN LPORT[uniconjunctive_DEF] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC glb_bound
    THEN BETA_TAC THEN POP_ASSUM ACCEPT_TAC
   ;POP_ASSUM (ASSUME_TAC o PORR[monotonic_DEF]) THEN DISCH_TAC THEN RES_TAC
    THEN POP_ASSUM MP_TAC THEN UNDISCH_TAC "uniconjunctive(c:^ptrans12)" 
    THEN DISCH_THEN (\th. PORT[PORR[uniconjunctive_DEF] th]) THEN
    PORT[implies_DEF] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC
    THEN PORT[glb_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN ART[]
   ])
 in prove
  ("uniconjunctive (c:^ptrans12) ==>
        (c = nondass (\u u'. glb (\q. c q u)u'))",
   DISCH_TAC THEN FUN_TAC THEN PORT[nondass_DEF] THEN BETA_TAC
   THEN FUN_TAC THEN LHS_RT1 (UNDISCH lemma2)
   THEN PORT[implies_DEF] THEN REFL_TAC);;


save_thm(`mono_subuniconj`,mono_subuniconj);;
save_thm(`biconj_mono`,biconj_mono);;
save_thm(`conj_biconj`,conj_biconj);;
save_thm(`conj_mono`,conj_mono);;
save_thm(`uniconj_conjterm`,uniconj_conjterm);;
save_thm(`uniconj_conj`,uniconj_conj);;
save_thm(`uniconj_biconj`,uniconj_biconj);;
save_thm(`uniconj_mono`,uniconj_mono);;

save_thm(`mono_abort`,mono_abort);;
save_thm(`mono_skip`,mono_skip);;
save_thm(`mono_assert`,mono_assert);;
save_thm(`mono_assign`,mono_assign);;
save_thm(`mono_nondass`,mono_nondass);;
save_thm(`mono_seq`,mono_seq);;
save_thm(`mono_cond`,mono_cond);;
save_thm(`mono_do`,mono_do);;
save_thm(`mono_dolib`,mono_dolib);;
save_thm(`mono_block`,mono_block);;

save_thm(`do_dolib`,do_dolib);;

save_thm(`strict_abort`,strict_abort);;
save_thm(`strict_skip`,strict_skip);;
save_thm(`strict_assert`,strict_assert);;
save_thm(`strict_assign`,strict_assign);;
save_thm(`strict_nondass`,strict_nondass);;
save_thm(`strict_seq`,strict_seq);;
save_thm(`strict_cond`,strict_cond);;
save_thm(`strict_do`,strict_do);;
save_thm(`strict_block`,strict_block);;

save_thm(`conj_abort`,conj_abort);;
save_thm(`conj_skip`,conj_skip);;
save_thm(`conj_assert`,conj_assert);;
save_thm(`conj_assign`,conj_assign);;
save_thm(`conj_nondass`,conj_nondass);;
save_thm(`conj_seq`,conj_seq);;
save_thm(`conj_cond`,conj_cond);;
save_thm(`conj_dolib`,conj_dolib);;
save_thm(`conj_do`,conj_do);;
save_thm(`conj_block`,conj_block);;

save_thm (`nondass_complete`,nondass_complete);;
