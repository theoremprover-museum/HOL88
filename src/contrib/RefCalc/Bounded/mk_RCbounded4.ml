% File: mk_RCbounded4.ml %

% theory of backward data refinement %


% --- backward data refinement theorems for commands --- %

% --- abort --- %
let abort_bwdref = prove
  ("(!k u. ?a. r(a,k,u)) ==> bwdref (r:^arel) abort abort",
   LRT[bwdref_DEF;ref_DEF;seq_DEF;abort_DEF;dual_abst;implies_DEF
      ;false_DEF] THEN PBETA_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  CONV_TAC NOT_FORALL_CONV THEN PORT[NOT_CLAUSES] THEN
  POP_ASSUM(ASSUME_TAC o RR[] o SPECL["FST(u:*c#*s)";"SND(u:*c#*s)"]) THEN
  FIRST_ASSUM ACCEPT_TAC);;

% --- skip --- %
let skip_bwdref = prove
  ("bwdref (r:^arel) skip skip",
   LRT[bwdref_DEF;ref_DEF;seq_DEF;skip_DEF;dual_abst;implies_DEF]);;

% --- seq --- %
let seq_bwdref = prove
  ("!c1 c1' c2 c2' (r:^arel).
     monotonic c1' /\ bwdref r c1 c1' /\ bwdref r c2 c2'
     ==> bwdref r (c1 seq c2) (c1' seq c2')",
   LPRT[bwdref_DEF;ref_DEF;monotonic_DEF;seq_DEF;dual_abst;implies_DEF] THEN
   PBETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   POP_ASSUM MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
   PBETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

% --- cond --- %
let th = TAUT "(t/\t')\/(~t/\t'') = (t==>t')/\(~t==>t'')";;
let cond_bwdref = prove
  ("!g g' c1 c1' c2 c2' (r:^arel).
     bwdref r c1 c1' /\ bwdref r c2 c2' /\ (!a k u. r(a,k,u) ==> (g(a,u) = g'(k,u)))
     ==> bwdref r (cond g c1 c2) (cond g' c1' c2')",
   LPRT[bwdref_DEF;ref_DEF;seq_DEF;cond_DEF;dual_abst;implies_DEF] THEN
   LPRT[or_DEF;and_DEF;not_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN 
   PORT[th] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM(\th. REPEAT STRIP_TAC THEN MP_TAC th) THEN 
    POP_ASSUM(\th.ASSUME_TAC th THEN  MP_TAC th) THEN
    SUBST1_TAC(SYM(ISPEC "u:*c#*s "PAIR)) THEN DISCH_TAC THEN RES_TAC THENL
    [ART[]
    ;POP_ASSUM MP_TAC THEN RT[] THEN ASSUM_LIST(\l.RT[el 4 l]) THEN
     DISCH_THEN(\th. RT[th])
    ]
   ;FIRST_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM(\th. REPEAT STRIP_TAC THEN MP_TAC th) THEN 
    POP_ASSUM(\th.ASSUME_TAC th THEN  MP_TAC th) THEN
    SUBST1_TAC(SYM(ISPEC "u:*c#*s "PAIR)) THEN DISCH_TAC THEN 
    RES_TAC THEN ART[]
   ]);;

% --- nondass --- %
let nondass_bwdref = prove
  ("(!a' c c' u u'. r(a',c',u')/\Q(c,u)(c',u') ==> ?a.r(a,c,u)/\P(a,u)(a',u'))
    ==> bwdref (r:^arel) (nondass P) (nondass Q)",
   LPORT[bwdref_DEF;ref_DEF;seq_DEF;dual_abst;implies_DEF;nondass_DEF]
   THEN PBETA_TAC THEN DISCH_TAC THEN GEN_TAC THEN
   P_PGEN_TAC "(k,u):^cstate" THEN RT[] THEN DISCH_TAC THEN
   P_PGEN_TAC "(k',u'):^cstate" THEN RT[] THEN REPEAT STRIP_TAC THEN
   RES_TAC THEN RES_TAC);;

let nondass_bwdref_eq =
 let aurel = ":(*a#*s)->(*a#*s)->bool" in
 let th1 = TAUT "t==>t'==>t'' = t/\t'==>t''" in
 prove
  ("bwdref (r:^arel) (nondass P) (nondass Q)
   =  (!a' k k' u u'. (r:^arel)(a',k',u') /\ Q(k,u)(k',u')
         ==> ?a. r(a,k,u) /\ P(a,u)(a',u'))",
  EQ_TAC THENL
  [LPRT[bwdref_DEF;ref_DEF;seq_DEF;dual_abst;nondass_DEF;
        implies_DEF;and_DEF] THEN PBETA_TAC THEN 
   CONV_TAC(DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN REPEAT STRIP_TAC THEN
   ASSUM_LIST(\l.MP_TAC
     (RR[](PBETA_RULE
       (SPECL["\(a',u').?a.r(a,k:*c,u)/\(P:^aurel)(a,u)(a',u')";
              "k:*c,u:*s";"k':*c,u':*s"](el 3 l))))) THEN
   CONV_TAC(DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN RT[th1] THEN
   STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN ART[] THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC "a:*a" THEN ART[]
  ;ACCEPT_TAC nondass_bwdref
  ]);;

% --- specification --- %
let spec_bwdref =
 let th1 = TAUT "t==>t'==>t'' = t/\t'==>t''" in
 let th2 = TAUT "t==>t'/\t'' = (t==>t')/\(t==>t'')" in
 prove
 ("(!k u. (!a. (r:^arel)(a,k,u) ==> p(a,u)) ==> q(k,u)) /\
   (!a' k k' u u'. 
      (!a. r(a,k,u) ==> p(a,u)) /\ r(a',k',u') /\ Q(k,u)(k',u')
         ==> ?a. r(a,k,u) /\ P(a,u)(a',u'))
    ==> bwdref r ((assert p) seq (nondass P)) ((assert q) seq (nondass Q))",
  STRIP_TAC THEN LPRT[bwdref_DEF;ref_DEF;seq_DEF;assert_DEF;nondass_DEF
  ;dual_abst;implies_DEF;and_DEF] THEN GEN_TAC THEN P_PGEN_TAC "k:*c,u:*s" THEN 
  PBETA_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [FIRST_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
  ;P_PGEN_TAC "k':*c,u':*s" THEN PBETA_TAC THEN
   POP_ASSUM MP_TAC THEN RT[th2] THEN CONV_TAC(DEPTH_CONV FORALL_AND_CONV) THEN
   CONV_TAC(DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN RT[th1] THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC
  ]);;

let spec_bwdref_eq =
 let aurel = ":(*a#*s)->(*a#*s)->bool" in
 let th2 = TAUT "t==>t'/\t'' = (t==>t')/\(t==>t'')" in
 prove
  ("bwdref (r:^arel) ((assert p) seq (nondass P))
                     ((assert q) seq (nondass Q))
   = (!k u. (!a. (r:^arel)(a,k,u) ==> p(a,u)) ==> q(k,u)) /\
     (!a' k k' u u'. 
      (!a. r(a,k,u) ==> p(a,u)) /\ r(a',k',u') /\ Q(k,u)(k',u')
         ==> ?a. r(a,k,u) /\ P(a,u)(a',u'))",
  EQ_TAC THENL
  [LPRT[bwdref_DEF;ref_DEF;seq_DEF;dual_abst;assert_DEF;nondass_DEF;
        implies_DEF;and_DEF] THEN PBETA_TAC THEN
   DISCH_THEN(\th.MP_TAC(RR[th2]th)) THEN 
   CONV_TAC(REDEPTH_CONV FORALL_AND_CONV) THEN
   REPEAT STRIP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ART[] THEN
    EXISTS_TAC "\u'.?a.r(a,k:*c,u)/\(P:^aurel)(a,u)u'" THEN
    PBETA_TAC THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC "a:*a" THEN ART[]
   ;ASSUM_LIST(\l.MP_TAC(el 4 l)) THEN
    CONV_TAC(REDEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN
    DISCH_THEN(MP_TAC o
      SPECL["\u'.?a.r(a,k:*c,u)/\(P:^aurel)(a,u)u'";
            "k:*c,u:*s";"k':*c,u':*s";"a':*a"]) THEN PBETA_TAC THEN 
    ART[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC "a''':*a" THEN ART[]
   ]
  ;STRIP_TAC THEN IMP_RES_TAC spec_bwdref
  ]);;


%  --- the backward data refinement theorem for iteration --- %

let lemma = prove
  ("!g c g' c' (r:^arel).
     ucontinuous c /\ ucontinuous c'
     /\ bwdref (r:^arel) c c'
     /\ (!a k u. r(a,k,u) ==> (g(a,u) = g'(k,u)))
     /\ ucontinuous (dual (abst r))
     /\ (!k u. ?a. r(a,k,u))
     ==> (!n v. (!a. r(a,v) ==> H g c n q(a,SND v))
            ==> H g' c' n(\(k,u). !a. r(a,k,u) ==> q(a,u))v)",
   LPORT[ucontinuous_DEF;bwdref_DEF;ref_DEF;seq_DEF;dual_abst;implies_DEF] THEN
   PBETA_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   IMP_RES_TAC (PORR[ucontinuous_DEF]ucont_mono) THEN INDUCT_TAC THENL
   [LPORT[H_DEF;and_DEF;not_DEF] THEN P_PGEN_TAC "(k,u):^cstate" THEN
    PBETA_TAC THEN RT[] THEN ASSUM_LIST(\l.MP_TAC(SPEC_ALL(el 3 l))) THEN 
    REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC
   ;P_PGEN_TAC "(k,u):^cstate" THEN RT[] THEN 
    LPORT[H_DEF;or_DEF;and_DEF;not_DEF] THEN PBETA_TAC THEN RT[] THEN
    ASSUM_LIST(\l.MP_TAC(SPEC_ALL(el 4 l))) THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN ART[] THENL
    [UNDISCH_TAC "(g:^apred)(a,u) = (g':^cpred)(k,u)" THEN ART[] THEN
     STRIP_TAC THEN ART[] THEN REPEAT STRIP_TAC THEN 
     ASSUM_LIST(\l. MP_TAC(MATCH_MP(el 7 l)(hd l)) THEN
                    MP_TAC(MATCH_MP(el 14 l)(hd l))) THEN ART[] THEN
     DISCH_THEN (\t.RT[t]) THEN STRIP_TAC THEN ART[]
    ;ASSUM_LIST(\l.MATCH_MP_TAC(MATCH_MP(BETA_RULE
       (SPEC"\v.!a.(r:^arel)(a,v)==>H g c n q(a,SND v)"
          (RR[monotonic_DEF;implies_DEF](el 8 l)))) (el 6 l))) THEN
     CONV_TAC(ONCE_DEPTH_CONV(PALPHA_CONV "(k,u):^cstate")) THEN RT[] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN RT[] THEN REPEAT STRIP_TAC THEN
     ASSUM_LIST(\l. MP_TAC(MATCH_MP(el 5 l)(hd l)) THEN
                    MP_TAC(MATCH_MP(el 12 l)(hd l))) THEN ART[] THEN
     DISCH_THEN (\t.RT[t]) THEN STRIP_TAC THEN ART[]
   ]]);;
let H_adjust =
 let t = prove("(p:^pred) andd (p imp q) = p andd q",PRED_TAUT_TAC)
 in prove
  ("!n. H g ((guard g) seq c) n q = H (g:^pred) c n q",
   INDUCT_TAC THEN ART[H_DEF] THEN LRT[seq_DEF;guard_DEF;t]);;
let do_bwdref =
 let t = TAUT "t==>t'==>t'' = t/\t'==>t''" in
 let t1 = prove
    ("ucontinuous(c':^cptrans) ==> ucontinuous((guard g')seq c')",
    DISCH_TAC THEN MATCH_MP_TAC ucont_seq THEN ART[ucont_guard]) in
 let t2 = RR[H_adjust](UNDISCH(RR[UNDISCH t1]
    (SPEC"(guard g')seq(c':^cptrans)"(GEN "c':^cptrans"(SPEC_ALL lemma))))) in
 prove
  ("!g c g' c' (r:^arel).
     ucontinuous c /\ ucontinuous c'
     /\  bwdref (r:^arel) c ((guard g') seq c')
     /\ (!a k u. r(a,k,u) ==> (g(a,u) = g'(k,u)))
     /\ ucontinuous (dual (abst r))
     /\ (!k u. ?a. r(a,k,u))
     ==> bwdref r (do g c) (do g' c')",
   LPORT[ucontinuous_DEF;bwdref_DEF;ref_DEF;seq_DEF;dual_abst;implies_DEF] THEN
   PBETA_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   P_PGEN_TAC "(k,u):^cstate" THEN RT[] THEN
   IMP_RES_TAC (PORR[ucontinuous_DEF]do_bounded) THEN 
   POP_ASSUM (\th.PORT[th]) THEN POP_ASSUM (\th.PORT[th]) THEN 
   IMP_RES_TAC(PORR[ucontinuous_DEF]ucont_mono) THEN IMP_RES_TAC uchain_H THEN 
   POP_ASSUM (\t.ALL_TAC) THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
   RES_TAC THEN ASSUM_LIST(\l.
     RT[PBETA_RULE(SPEC"(k,u):^cstate"(CONV_RULE FUN_EQ_CONV(el 2 l)))]) THEN
   PORT[ulimit_DEF] THEN PBETA_TAC THEN STRIP_TAC THEN
   EXISTS_TAC "n:num" THEN POP_ASSUM MP_TAC THEN RT[] THEN DISCH_TAC THEN
   MATCH_MP_TAC(RR[t](PBETA_RULE
    (LPORR[ucontinuous_DEF;bwdref_DEF;ref_DEF;seq_DEF;dual_abst;implies_DEF]
     (DISCH_ALL(SPECL["n:num";"(k,u):^cstate"] t2))))) THEN
   ART[]);;


% --- backward refinement theorem for blocks --- %
let block_bwdref =
 let thm1 = prove
  ("(!k u. ?a. (r:^arel)(a,k,u))==>
    (\(k,u). !a. r(a,k,u) ==> q u) implies (\(k,u). q u)",
   PORT[implies_DEF] THEN DISCH_TAC THEN P_PGEN_TAC "(k,u):^cstate" THEN 
   PBETA_TAC THEN POP_ASSUM (MP_TAC o SPEC_ALL) THEN RT[] THEN
   REPEAT STRIP_TAC THEN RES_TAC) in
 prove
  ("!p c p' c' (r:^arel).
         monotonic c'
      /\ (!a k u. r(a,k,u) /\ p'(k,u) ==> p(a,u))
      /\ bwdref (r:^arel) c c'
      /\ (!k u. ?a. r(a,k,u))
     ==> (block p c) ref (block p' c')",
   LPORT[bwdref_DEF;ref_DEF;block_DEF;seq_DEF;dual_abst;monotonic_DEF;
         implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   ASSUM_LIST(\l.
     ASSUME_TAC(GEN_ALL(IMP_TRANS(SPEC_ALL(hd l))(SPEC"a:*a"(el 3 l))))) THEN
   ASSUM_LIST(\l. ASSUME_TAC(PBETA_RULE(MATCH_MP(RR[]
      (SPECL["\(x':*a,v').(q:^pred)v'";"(k,v):^cstate"](el 6 l)))(hd l)))) THEN
   ASSUM_LIST(\l. ASSUME_TAC(MATCH_MP(PORR[implies_DEF]thm1)(el 6 l))) THEN
   RES_TAC);;


% --- backward refinement theorem for action systems with one action --- %
let actsys_bwdref = prove
  ("!p g c p' g' c' (r:^arel).
        ucontinuous c /\ ucontinuous c'
     /\ (!k u. ?a. r(a,k,u))
     /\ ucontinuous (dual(abst r))
     /\ (!a k u. r(a,k,u) /\ p'(k,u) ==> p(a,u))
     /\ (!a k u. r(a,k,u) ==> (g(a,u) = g'(k,u)))
     /\ bwdref r c ((guard g') seq c')
     ==> (block p (do g c)) ref (block p' (do g' c'))",
   REPEAT STRIP_TAC THEN MATCH_MP_TAC block_bwdref THEN
   EXISTS_TAC "r:^arel" THEN ART[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC mono_do THEN IMP_RES_TAC ucont_mono
   ;MATCH_MP_TAC do_bwdref THEN ART[]
   ]);;


save_thm(`abort_bwdref`,abort_bwdref);;
save_thm(`skip_bwdref`,skip_bwdref);;
save_thm(`seq_bwdref`,seq_bwdref);;
save_thm(`cond_bwdref`,cond_bwdref);;
save_thm(`nondass_bwdref`,nondass_bwdref);;
save_thm(`nondass_bwdref_eq`,nondass_bwdref_eq);;
save_thm(`spec_bwdref`,spec_bwdref);;
save_thm(`spec_bwdref_eq`,spec_bwdref_eq);;
save_thm(`do_bwdref`,do_bwdref);;
save_thm(`block_bwdref`,block_bwdref);;
save_thm(`actsys_bwdref`,actsys_bwdref);;

