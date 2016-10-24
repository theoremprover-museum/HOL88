% mk_RCcommand3.ml
   general facts
%


% ------ algebraic properties of commands ------ %


% --- sequential composition is associative --- %

let seq_assoc = prove
 ("(c1:(*s3->bool)->(*s4->bool)) seq (c2 seq (c3:^ptrans12))
     = (c1 seq c2) seq c3",
  FUN_TAC THEN RT[seq_DEF]);;


% --- skip is unit of sequential composition --- %

let skip_unit = prove
 ("(skip seq (c:^ptrans12) = c) /\ (c seq skip = c)",
  CONJ_TAC THEN FUN_TAC THEN RT[seq_DEF;skip_DEF]);;


% --- properties of do1 transformed into fixpoint language --- %

let do_mono_lemma = prove
  ("monotonic (f:^ptrans) ==> 
           monotonic \p'.(g andd (f p')) or ((not g) andd p)",
   RT[monotonic_DEF] THEN BETA_TAC THEN 
   LRT[implies_DEF;or_DEF;and_DEF;not_DEF] THEN SUPER_TAC);;
let do_unfold =
  let t4 = BETA_RULE (SPEC "\p'.(g andd ((f:^ptrans) p')) or ((not g) andd p)"
    (GEN "f:^ptrans" (DISCH_ALL fix_fp)))
  in let t5 = IMP_TRANS (SPEC "c:^ptrans" (GEN "f:^ptrans" do_mono_lemma))
      (PORR[SYM(UNDISCH(SPEC_ALL do_thm))]
        (SPEC "c:^ptrans" (GEN "f:^ptrans" t4)))
  in DISCH_ALL(SYM_RULE (UNDISCH t5));;
let do_implies =
  let t1 = SPEC "\p'. (g andd ((c:^ptrans) p')) or ((not g) andd p)"
    (GEN "f:^ptrans" (DISCH_ALL fix_least))
 in DISCH_ALL (SPEC "q:^pred"
      (BETA_RULE (PORR[SYM(UNDISCH(SPEC_ALL do_thm))] t1)));;


% --- greatest fixpoint reasoning for do-loops (almost wlp) --- %

let dolib_unfold =
  let t = BETA_RULE (SPEC "\p'. (g andd ((f:^ptrans) p')) or ((not g) andd p)"
    (GEN "f:^ptrans" (DISCH_ALL gfix_fp)))
  in let t' = IMP_TRANS do_mono_lemma (RR[SYM_RULE 
       (SPEC_ALL dolib_DEF)] t)
 in SYM_RULE (SPEC "(c:^ptrans)" (GEN "f:^ptrans" t'));;
let dolib_implies =
  let t1 = SPEC "\p. (g andd ((c:^ptrans)p)) or ((not g) andd q)"
    (GEN "f:^ptrans" (DISCH_ALL gfix_greatest))
 in SPEC_ALL (BETA_RULE (PORR[SYM_RULE (SPEC_ALL dolib_DEF)] t1));;


% --- degenerate assignment --- %

let assign_skip = prove
 ("assign (\u:*s.u) = skip",
  FUN_TAC THEN LRT[assign_DEF;skip_DEF] THEN FUN_TAC THEN REFL_TAC);;

% --- degenerate conditionals --- %

let cond_true = prove
 ("cond true (c1:^ptrans12) c2 = c1",
  FUN_TAC THEN PORT[cond_DEF] THEN PRED_TAUT_TAC);;

let cond_false = prove
 ("cond false (c1:^ptrans12) c2 = c2",
  FUN_TAC THEN PORT[cond_DEF] THEN PRED_TAUT_TAC);;

let cond_same = prove
 ("cond g (c:^ptrans12) c = c",
  FUN_TAC THEN PORT[cond_DEF] THEN PRED_TAUT_TAC);;


% --- degenerate iterations --- %

let do_false = prove
 ("monotonic (c:^ptrans) ==> (do false c = skip)",
  STRIP_TAC THEN FUN_TAC THEN IMP_RES_TAC do_unfold THEN
  POART[] THEN PORT[skip_DEF] THEN PRED_TAUT_TAC);;

let do_true = 
 let thm1 = prove("((p:^pred) implies false) ==> (p = false)",
  LPORT[false_DEF;implies_DEF] THEN BETA_TAC THEN STRIP_TAC THEN
  FUN_TAC THEN RT[] THEN STRIP_TAC THEN RES_TAC) in
 prove
 ("monotonic (c:^ptrans) /\ strict c ==> (do true c = abort)",
  PORT[strict_DEF] THEN STRIP_TAC THEN FUN_TAC THEN 
  IMP_RES_TAC do_implies THEN PORT[abort_DEF] THEN MATCH_MP_TAC thm1 THEN
  POP_ASSUM MATCH_MP_TAC THEN ART[] THEN PRED_TAUT_TAC);;


% --- skip is special case of assert --- %

let skip_eq_assert = prove
 ("skip = assert (true:^pred)",
  FUN_TAC THEN LPORT[skip_DEF;assert_DEF] THEN PRED_TAUT_TAC);;


% --- assign is special case of nondass --- %

let assign_eq_nondass = prove
 ("assign(e:*s2->*s1) = nondass \u u'. u' = e u",
  FUN_TAC THEN LPORT[assign_DEF;nondass_DEF] THEN FUN_TAC THEN
  CONV_TAC (DEPTH_CONV FORALL_1PT_CONV) THEN REFL_TAC);;


% --- assignments can be merged --- %

let assign_seq = prove
 ("!e:*s1->*s2. !f:*s2->*s3. (assign e) seq (assign f) = assign \u.f(e u)",
  REPEAT GEN_TAC THEN FUN_TAC THEN LPRT[seq_DEF;assign_DEF] THEN 
  FUN_TAC THEN RT[]);;


save_thm(`seq_assoc`,seq_assoc);;
save_thm(`skip_unit`,skip_unit);;
save_thm(`do_unfold`,do_unfold);;
save_thm(`do_implies`,do_implies);;
save_thm(`dolib_unfold`,dolib_unfold);;
save_thm(`dolib_implies`,dolib_implies);;
save_thm(`assign_skip`,assign_skip);;
save_thm(`cond_true`,cond_true);;
save_thm(`cond_false`,cond_false);;
save_thm(`cond_same`,cond_same);;
save_thm(`do_false`,do_false);;
save_thm(`do_true`,do_true);;
save_thm(`skip_eq_assert`,skip_eq_assert);;
save_thm(`assign_eq_nondass`,assign_eq_nondass);;
save_thm(`assign_seq`,assign_seq);;
