% File: mk_RCcommand2.ml
   basic lemmas about fixpoints, distributivity properties of commands
%

% --- properties of the refinement relation --- %

let ref_prop = TAC_PROOF
 (([],"(!(c:^ptrans12). c ref c) /\
       (!(c:^ptrans12) c'. c ref c' /\ c' ref c ==> (c = c')) /\
       (!(c:^ptrans12) c' c''. c ref c' /\ c' ref c'' ==> c ref c'')"),
  RT[ref_DEF;CONJUNCT1 implies_prop] THEN REPEAT STRIP_TAC THENL
  [FUN_TAC THEN MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 implies_prop))
   THEN ART[]
  ;EVERY_ASSUM (ASSUME_TAC o SPEC_ALL) THEN IMP_RES_TAC
  (CONJUNCT2 (CONJUNCT2 implies_prop))
  ]);;


% ----- least fixpoint lemmas for mu and related theorems ----- %

let mono_Dch = prove
 ("(!c. C c ==> monotonic (c:^ptrans12)) ==> monotonic (Dch C)",
   LPORT[monotonic_DEF;Dch_DEF;glb_DEF;ref_DEF;implies_DEF] THEN
   BETA_TAC THEN REPEAT STRIP_TAC THEN
   POP_ASSUM (\th.PORT[th]) THEN RES_TAC THEN
   POP_ASSUM MATCH_MP_TAC THEN
   POP_ASSUM (ASSUME_TAC o (RR[] o SPEC "(c:^ptrans12)p"))
   THEN POP_ASSUM ACCEPT_TAC);;

let Dch_bound = TAC_PROOF
 ( ([],"!C (c:^ptrans12). C c ==> (Dch C) ref c"),
   LPORT[ref_DEF;Dch_DEF;glb_DEF;implies_DEF] THEN BETA_TAC THEN 
   REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN 
   DISCH_THEN (ASSUME_TAC o SPEC "(c:^ptrans12)q") THEN
   POP_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "c:^ptrans12" THEN ART[]);;

let Dch_greatest = TAC_PROOF
 ( ([],"!C (c:^ptrans12).(!c'. C c' ==> c ref c') ==> c ref (Dch C)"),
   LPORT[ref_DEF;Dch_DEF;glb_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT 
   STRIP_TAC THEN RES_TAC THEN ART[]);;

let mono_mu = prove("!f:^ptrans12->^ptrans12. monotonic(mu f)",
   PORT[mu_DEF] THEN GEN_TAC THEN MATCH_MP_TAC mono_Dch THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN ART[]);;

let mu_least = 
  let t = BETA_RULE 
    (SPECL["\(c:^ptrans12).monotonic c/\(f c) ref c";"c:^ptrans12"] Dch_bound) 
 in GEN "c:^ptrans12" (REWRITE_RULE[GEN "f:^ptrans12->^ptrans12" 
     (SYM (SPEC "f:^ptrans12->^ptrans12" mu_DEF))] t);;

let th1 = prove("t/\t'==>t'' = t==>t'==>t''",TAUT_TAC);;
let mu_fp =
  let fn = ":^ptrans12->^ptrans12"
  in let t1 = UNDISCH (fst(EQ_IMP_RULE (ISPEC "f:^fn" pmonotonic_DEF)))
  in let t2 = SPECL["mu (f:^fn)";"c:^ptrans12"] t1
  in let t2a =  SPECL["f:^fn";"c:^ptrans12"](GENL["f':^fn";"c':^ptrans12"]
      (PORR[GSYM CONJ_ASSOC] 
        (MATCH_MP (SPEC "monotonic(mu(f:^fn)) /\ monotonic(c:^ptrans12)"
                        (prove("!t.(t'==>t'') ==> t/\t'==>t/\t''",TAUT_TAC)))
                  (SPEC_ALL mu_least) ) ) )

  in let t3 = UNDISCH (IMP_TRANS t2a t2)
  in let t4 = SPECL["f(mu (f:^fn))";"(f:^fn) c";"c:^ptrans12"] 
          (CONJUNCT2 (CONJUNCT2 ref_prop))
  in let t5 = MP t4 (CONJ t3 (ASSUME "(f c) ref (c:^ptrans12)"))
  in let t6 = PORR[SYM th1]
       (DISCH "monotonic(c:^ptrans12)" (DISCH "(f c) ref (c:^ptrans12)"
         (UNDISCH_ALL(RR[th1](DISCH_ALL 
           (RR[ASSUME"(f c) ref (c:^ptrans12)"] (DISCH_ALL t5)))))))
  in let t7 = BETA_RULE (SPECL["\(c:^ptrans12).monotonic c /\ (f c)ref c"
                              ;"f(mu (f:^fn))"] 
         Dch_greatest)
  in let t8 = REWRITE_RULE[GEN "f:^fn" (SYM (SPEC "f:^fn" mu_DEF))] t7
  in let t9 = DISCH_ALL (MP t8 (GEN "c:^ptrans12" t6))
  in let t10 = MP (UNDISCH(UNDISCH(RR[th1]
                       (SPECL["f(mu (f:^fn))";"mu (f:^fn)"] t1))))
                  (UNDISCH_ALL t9)
  in let t11 = SPECL["\(c:^ptrans12).monotonic c/\(f c)ref c";"f(mu (f:^fn))"]
                    Dch_bound
  in let t12 = REWRITE_RULE [GEN "f:^fn" (SYM (SPEC "f:^fn" mu_DEF))] 
          (BETA_RULE t11)
  in let t13 = SPECL["f(mu (f:^fn))";"mu (f:^fn)"](C1 (C2 ref_prop))
  in let t14 = MP t13(CONJ(UNDISCH(UNDISCH t9))(MP (UNDISCH(RR[th1]t12))t10))
  in let t15 = UNDISCH(SPEC "mu(f:^fn)"
                        (PORR[mono_mono_DEF](ASSUME "mono_mono(f:^fn)")))
  in let t16 = RR[t15](DISCH "monotonic(f(mu(f:^fn)))" t14)
  in let t17 = RR[SYM th1] (DISCH_ALL
                    (RR[UNDISCH_ALL(RR[th1](ISPEC"f:^fn"mono_mu))]
                       (DISCH "monotonic(mu(f:^fn))" t16)))
  in PORR[GSYM regular_DEF] t17 ;;

let mu_char = prove
 ("regular (f:^ptrans12->^ptrans12) /\
    monotonic a /\ (f a) ref a /\ (!x. (f x = x) ==> a ref x) 
       ==> (a = mu f)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (C1 (C2 ref_prop)) THEN
  ASSUME_TAC mu_fp THEN RES_TAC THEN RES_TAC THEN ART[] THEN
  MATCH_MP_TAC mu_least THEN ART[]);;



% --- do g c q is least fixpoint on pred-level --- %

let do_thm =
 let t1 = prove
  ("monotonic (c:^ptrans) ==>
         monotonic (\p. (g andd (c p)) or ((not g) andd q))",
   PORT[monotonic_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
   RES_TAC THEN POP_ASSUM (ASSUME_TAC o RR[implies_DEF]) THEN
   LPORT[implies_DEF;or_DEF;and_DEF;not_DEF] THEN SUPER_TAC
   THEN RES_TAC)
 in let t2 = prove
  ("monotonic (c:^ptrans) ==> pmonotonic 
       (\(x:^ptrans). cond g (c seq x) skip)",
   LPORT[monotonic_DEF;pmonotonic_DEF;ref_DEF] THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN LPRT[cond_DEF;seq_DEF]
   THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN IMP_RES_TAC  (BETA_RULE 
      (RR[monotonic_DEF] t1)) THEN POP_ASSUM MATCH_ACCEPT_TAC)
 in let t2a = prove
  ("monotonic c ==> mono_mono 
       (\(x:^ptrans). cond g (c seq x) skip)",
   LPORT[mono_mono_DEF;monotonic_DEF] THEN BETA_TAC THEN
   LPRT[cond_DEF;seq_DEF;skip_DEF;implies_DEF;and_DEF;or_DEF;
         imp_DEF;not_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
   ART[] THEN RES_TAC THEN RES_TAC)
 in let t3 = ISPEC "\(x:^ptrans).cond g (c seq x) skip" 
   (GEN "f:^ptrans12->^ptrans12" (DISCH_ALL(PORR[regular_DEF]mu_char)))
 in let t5 = UNDISCH (SPEC 
   "\p. (g andd ((c:^ptrans) p)) or ((not g) andd q)" 
   (GEN "f:^ptrans" (DISCH_ALL fix_fp)))
 in let t6 = LPORR[cond_DEF;seq_DEF;skip_DEF] 
   (AP_THM (ASSUME "cond g (c seq x) skip = (x:^ptrans)") "q:^pred")
 in let t7 = prove
  ("monotonic (c:^ptrans)
    ==> ((\q. fix(\p. (g andd (c p)) or ((not g) andd q))) = do g c)",
   PORT[do_DEF] THEN DISCH_TAC THEN IMP_RES_TAC t2 THEN IMP_RES_TAC t2a THEN
   MATCH_MP_TAC t3 THEN ART[] THEN REPEAT CONJ_TAC THENL
   [PORT[monotonic_DEF] THEN BETA_TAC THEN
    LRT[fix_DEF;glb_DEF;implies_DEF;and_DEF;or_DEF;not_DEF] THEN
    BETA_TAC THEN REPEAT STRIP_TAC THEN
    ASSUM_LIST(\l. MATCH_MP_TAC(el 2 l)) THEN GEN_TAC THEN
    POP_ASSUM (MP_TAC o SPEC "u':*s") THEN ASM_CASES_TAC "(g:^pred)v" THEN
    ART[] THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ART[]
   ;BETA_TAC THEN LPORT[ref_DEF;cond_DEF;seq_DEF;skip_DEF] THEN
    GEN_TAC THEN BETA_TAC THEN IMP_RES_TAC t1 THEN
    POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN LRT[BETA_RULE t5;implies_prop]
   ;PORT[ref_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC fix_least THEN BETA_TAC THEN LRT[t6;implies_prop]
   ])
 in prove
  ("!c. monotonic (c:^ptrans)
        ==> (do g c q = fix(\p. (g andd (c p)) or ((not g) andd q)))",
    REPEAT STRIP_TAC THEN PORT[SYM (UNDISCH_ALL t7)] THEN
    BETA_TAC THEN REFL_TAC);;


save_thm(`ref_prop`,ref_prop);;
save_thm(`mono_Dch`,mono_Dch);;
save_thm(`Dch_bound`,Dch_bound);;
save_thm(`Dch_greatest`,Dch_greatest);;
save_thm(`mono_mu`,mono_mu);;
save_thm(`mu_least`,mu_least);;
save_thm(`mu_fp`,mu_fp);;
save_thm(`mu_char`,mu_char);;
save_thm(`do_thm`,do_thm);;
