% File: mk_RCwintool3.ml

  Refinement rules for data refinement intended for use in window inference
%


% --- Pushing data refinement through --- %

let dr_block = 
 let th1 = prove
  ("(\(x',v').q v') implies (\(a',u').!k.(r:^arel)(a',k,u')==>q u')",
   PORT[implies_DEF] THEN GEN_TAC THEN
   PORT[GSYM PAIR] THEN PBETA_TAC THEN
   REPEAT STRIP_TAC THEN ART[]) in
 let th2 = PORR[implies_DEF] (MATCH_MP
   (PORR[monotonic_DEF](ASSUME"monotonic(c:^aptrans)")) th1) in
 prove
  ("!(r:^arel) p c. monotonic(c:^aptrans) ==>
         (block (abst r p) ((abst r) seq c seq (repr r)))
         refines (block p c)",
   REPEAT GEN_TAC THEN DISCH_TAC THEN LPRT[refines_DEF;ref_DEF;block_DEF;
          seq_DEF;abst_DEF;repr_DEF;implies_DEF] THEN
   REPEAT GEN_TAC THEN PBETA_TAC THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC "a:*a" THEN RES_TAC THEN ART[] THEN
   ASSUME_TAC th2 THEN RES_TAC);;

let dr_do =
 let th1 = TAUT "t==>t'==>t'' = t/\t'==>t''" in
 let th2 = PORR[th1](DISCH_ALL(GEN_ALL
             (fst(EQ_IMP_RULE(UNDISCH_ALL dataref_alt))))) in
 let th3 = PRR[th1](DISCH_ALL(snd(EQ_IMP_RULE(UNDISCH_ALL dataref_alt)))) in
 prove("!(r:^arel) g c. monotonic c
        ==>  (!a a' k u. r(a,k,u) /\ r(a',k,u) /\ g(a',u) ==> g(a,u))
        ==>(do (abst r g) ((abst r) seq c seq (repr r)))
              refines ((abst r) seq (do g c) seq (repr r))",
 REPEAT STRIP_TAC THEN PORT[refines_DEF] THEN
 SUBGOAL_THEN "monotonic((abst(r:^arel)) seq (c seq (repr r)))"
                ASSUME_TAC THENL
 [MATCH_MP_TAC mono_seq THEN RT[mono_abst] THEN
  MATCH_MP_TAC mono_seq THEN ART[mono_repr]
 ;SUBGOAL_THEN "monotonic(do (g:^apred) c)" ASSUME_TAC THENL
  [MATCH_MP_TAC mono_do THEN ART[]
  ;SUBGOAL_THEN "monotonic(do(abst r g)((abst(r:^arel)) seq (c seq (repr r))))"
                 ASSUME_TAC THENL
   [MATCH_MP_TAC mono_do THEN ART[]
   ;ASSUM_LIST(\l.MATCH_MP_TAC(MATCH_MP th2(CONJ(el 2 l)(hd l)))) THEN
    MATCH_MP_TAC (PRR[th1](DISCH_ALL do_dataref)) THEN ART[] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC th3 THEN ART[ref_prop]
    ;PORT[abst_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC "a:*a" THEN ART[]
     ;STRIP_TAC THEN RES_TAC
 ]]]]]);;

let dr_seq =
 let th1 = LPORR[ref_DEF;seq_DEF;skip_DEF](C2(SPEC_ALL abst_repr)) in
 prove
 ("!(r:^arel) c1 c2 .monotonic c1
        ==>   (((abst r)seq c1 seq(repr r)) seq ((abst r)seq c2 seq(repr r)))
              refines  ((abst r) seq (c1 seq c2) seq (repr r))",
  LRT[monotonic_DEF;refines_DEF;ref_DEF;seq_DEF] THEN REPEAT STRIP_TAC THEN 
  MATCH_MP_TAC (PORR[monotonic_DEF]mono_abst) THEN
  POP_ASSUM MATCH_MP_TAC THEN MATCH_ACCEPT_TAC th1);;

let dr_cond =
 let th1 = prove("~t\/t' = t==>t'",TAUT_TAC) in
 prove
 ("!(r:^arel) g c1 c2 .
    (!a a' k u. r(a,k,u) /\ r(a',k,u) /\ g(a',u) ==> g(a,u))
     ==> (cond (abst r g) ((abst r)seq c1 seq(repr r))
                          ((abst r)seq c2 seq(repr r)))
         refines  ((abst r) seq (cond g c1 c2) seq (repr r))",
  LPRT[monotonic_DEF;refines_DEF;ref_DEF;seq_DEF;cond_DEF] THEN 
  LPRT[abst_DEF;repr_DEF;implies_DEF;and_DEF;or_DEF;not_DEF] THEN
  PBETA_TAC THEN REPEAT STRIP_TAC THEN
  LRT[seq_DEF;abst_DEF;repr_DEF] THEN PBETA_TAC THENL
  [DISJ1_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC "a:*a" THEN ART[]
   ;EXISTS_TAC "a:*a" THEN ART[]
   ]
  ;DISJ2_TAC THEN CONJ_TAC THENL
   [CONV_TAC NOT_EXISTS_CONV THEN PORT[DE_MORGAN_THM] THEN PORT[th1] THEN
    REPEAT STRIP_TAC THEN
    ASSUM_LIST(\l.ASSUME_TAC
      (MP(RR[](SPECL["a:*a";"a':*a";"FST(u:*c#*s)";"SND(u:*c#*s)"](el 6 l)))
         (CONJ(el 5 l)(CONJ(el 2 l)(hd l))))) THEN RES_TAC
   ;EXISTS_TAC "a:*a" THEN ART[]
  ]]);;

% --- Data refinement of basic commands --- %

let th1 = RR[mono_nondass]
           (ISPECL["nondass P:^aptrans";"nondass P':^cptrans";"r:^arel"]
              (GEN_ALL(DISCH_ALL dataref_alt)));;
let dr_nondass = prove
 ("(nondass \(k,u)(k',u'). !a. ?a'. 
                (r:^arel)(a,k,u) /\ r(a',k',u') /\ P(a,u)(a',u'))
   refines ((abst r) seq (nondass P) seq (repr r))",
   LPORT[refines_DEF;GSYM th1] THEN
   MATCH_MP_TAC nondass_dataref THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o SPEC_ALL) THEN STRIP_TAC THEN
   EXISTS_TAC "a':*a" THEN ART[]);;

let dr_nondass_rule = 
  GEN_ALL (LRR[th1;GSYM refines_DEF] nondass_dataref);;

let dr_spec = prove
 ("((assert (abst r p)) seq
   (nondass \(k,u)(k',u'). !a. ?a'. 
                (r:^arel)(a,k,u) /\ p(a,u) /\ r(a',k',u') /\ P(a,u)(a',u')))
   refines ((abst r) seq ((assert p) seq (nondass P)) seq (repr r))",
  SUBGOAL_THEN "monotonic((assert p)seq(nondass P:^aptrans))" ASSUME_TAC THENL
  [mono_TAC
  ;SUBGOAL_THEN "monotonic((assert(abst r p))seq
      (nondass \(k,u)(k',u'). !a. ?a'. 
        (r:^arel)(a,k,u) /\ p(a,u) /\ r(a',k',u') /\ P(a,u)(a',u')))"
     ASSUME_TAC THENL
   [mono_TAC
   ;PORT[refines_DEF] THEN ASSUM_LIST(\l.
      RT[MATCH_MP (GSYM dataref_alt) (CONJ(el 2 l)(hd l))]) THEN
    MATCH_MP_TAC spec_dataref THEN PORT[abst_DEF] THEN PBETA_TAC THEN
    REPEAT STRIP_TAC THENL
    [EXISTS_TAC "a:*a" THEN ART[]
    ;POP_ASSUM (MP_TAC o SPEC_ALL) THEN STRIP_TAC THEN
     EXISTS_TAC "a'':*a" THEN ART[]
  ]]]);;

let dr_spec_rule = prove
 ("(!a k u. (r:^arel)(a,k,u) /\ p(a,u) ==> q(k,u)) /\
   (!a k k' u u'.
     r(a,k,u) /\ p(a,u) /\ q(k,u) /\ Q(k,u)(k',u') ==>
     (?a'. r(a',k',u') /\ P(a,u)(a',u')))
   ==> ((assert q) seq (nondass Q))
       refines ((abst r) seq (((assert p) seq (nondass P)) seq (repr r)))",
  SUBGOAL_THEN "monotonic((assert p)seq(nondass P:^aptrans))" ASSUME_TAC THENL
  [mono_TAC
  ;SUBGOAL_THEN "monotonic((assert q)seq(nondass Q:^cptrans))" ASSUME_TAC THENL
   [mono_TAC
   ;PORT[refines_DEF] THEN ASSUM_LIST(\l.
      RT[MATCH_MP (GSYM dataref_alt) (CONJ(el 2 l)(hd l))]) THEN
    MATCH_ACCEPT_TAC spec_dataref
  ]]);;


save_thm(`dr_block`,dr_block);;
save_thm(`dr_do`,dr_do);;
save_thm(`dr_seq`,dr_seq);;
save_thm(`dr_cond`,dr_cond);;
save_thm(`dr_nondass`,dr_nondass);;
save_thm(`dr_nondass_rule`,dr_nondass_rule);;
save_thm(`dr_spec`,dr_spec);;
save_thm(`dr_spec_rule`,dr_spec_rule);;

