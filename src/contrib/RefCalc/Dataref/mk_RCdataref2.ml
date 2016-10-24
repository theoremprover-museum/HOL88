% File: mk_RCdataref2.ml

  Basic data refinement results
%

% --- General theorems --- %

let mono_abst = prove
  ("!(r:^arel). monotonic (abst r)",
   LPORT[monotonic_DEF;abst_DEF;implies_DEF] THEN REPEAT GEN_TAC THEN
   DISCH_TAC THEN GEN_TAC THEN PORT[GSYM PAIR] THEN
   PBETA_TAC THEN PRT[FST;SND] THEN REPEAT STRIP_TAC THEN 
   EXISTS_TAC "a:*a" THEN RES_TAC THEN ART[]);;

let mono_repr = prove
  ("!(r:^arel). monotonic (repr r)",
   LPORT[monotonic_DEF;repr_DEF;implies_DEF] THEN REPEAT GEN_TAC 
   THEN DISCH_TAC THEN GEN_TAC THEN PORT[GSYM PAIR]
   THEN PBETA_TAC THEN PRT[FST;SND] THEN REPEAT STRIP_TAC
   THEN RES_TAC THEN RES_TAC);;

let abst_repr = prove
  ("!(r:^arel).
      ((abst r) seq (repr r)) ref skip /\ skip ref ((repr r) seq (abst r))",
   LPORT[ref_DEF;seq_DEF;skip_DEF;abst_DEF;repr_DEF;implies_DEF] THEN
   PBETA_TAC THEN GEN_TAC THEN CONJ_TAC THENL
   [PBETA_TAC THEN REPEAT STRIP_TAC THEN
    POP_ASSUM (ASSUME_TAC o RR[] o SPEC "FST(u:*c#*s)") THEN RES_TAC
   ;PBETA_TAC THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC "FST(u:*a#*s)" THEN ART[]
   ]);;

let dataref_alt = 
  let thm1 = PBETA_RULE(LPORR[ref_DEF;seq_DEF;abst_DEF;repr_DEF;skip_DEF] 
     (C1 (SPEC_ALL abst_repr))) in
  let thm2 = PBETA_RULE(LPORR[ref_DEF;seq_DEF;abst_DEF;repr_DEF;skip_DEF] 
     (C2 (SPEC_ALL abst_repr))) in
  prove("monotonic c /\ monotonic c' 
        ==> (dataref (r:^arel) c c' = ((abst r) seq c seq (repr r)) ref c')",
   LPRT[monotonic_DEF;dataref_DEF;ref_DEF;seq_DEF;abst_DEF;repr_DEF;
        implies_DEF] THEN PBETA_TAC THEN STRIP_TAC THEN EQ_TAC THEN
   REPEAT STRIP_TAC THENL
   [RES_TAC THEN POP_ASSUM (ASSUME_TAC o PBETA_RULE) THEN
    ASSUME_TAC (PORR[implies_DEF](SPEC_ALL  thm1)) THEN RES_TAC
   ;FIRST_ASSUM MATCH_MP_TAC THEN PBETA_TAC THEN EXISTS_TAC "a:*a" THEN
    ART[] THEN ASSUME_TAC (PORR[implies_DEF](SPEC_ALL thm2)) THEN 
    ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(el 6 l)(hd l))) THEN RES_TAC
   ]);;
let dataref_ba = prove
  ("dataref (r:^arel) c c' = c ref ((repr r) seq c' seq (abst r))",
   LPRT[dataref_DEF;ref_DEF;seq_DEF;abst_DEF;repr_DEF;
        implies_DEF] THEN PBETA_TAC THEN EQ_TAC THEN
   REPEAT STRIP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "FST(u:*a#*s)" THEN ART[]
   ;RES_TAC THEN POP_ASSUM(MATCH_MP_TAC o RR[] o SPEC"FST(u:*c#*s)") THEN ART[]
   ]);;


% --- rules for data refinement --- %

% --- abort --- %
let abort_dataref = prove
  ("dataref (r:^arel) abort abort",
   LPORT[dataref_DEF;ref_DEF;seq_DEF;abort_DEF;abst_DEF;false_DEF;implies_DEF] THEN 
   PBETA_TAC THEN RT[]);;

% --- skip --- %
let skip_dataref = prove
  ("dataref (r:^arel) skip skip",
   LPORT[dataref_DEF;ref_DEF;seq_DEF;skip_DEF;abst_DEF] THEN PBETA_TAC THEN 
   RT[implies_prop]);;

% --- nondass --- %
let nondass_dataref = prove
 ("(!a k k' u u'. 
      (r:^arel)(a,k,u) /\ Q(k,u)(k',u') ==> ?a'. r(a',k',u') /\ P(a,u)(a',u'))
      ==> dataref r (nondass P) (nondass Q)",
  STRIP_TAC THEN LPORT[dataref_DEF;ref_DEF;seq_DEF;nondass_DEF;abst_DEF
     ;implies_DEF] THEN GEN_TAC THEN P_PGEN_TAC "k:*c,u:*s" THEN PBETA_TAC THEN
  STRIP_TAC THEN P_PGEN_TAC "k':*c,u':*s" THEN PBETA_TAC THEN STRIP_TAC THEN 
  RES_TAC THEN EXISTS_TAC "a':*a" THEN ART[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ART[]);;

let nondass_dataref_eq =
 let aurel = ":(*a#*s)->(*a#*s)->bool" in
 prove
  ("dataref (r:^arel) (nondass P) (nondass Q)
   = (!a k k' u u'. (r:^arel)(a,k,u) /\ Q(k,u)(k',u')
         ==> ?a'. r(a',k',u') /\ P(a,u)(a',u'))",
  EQ_TAC THENL
  [LPRT[dataref_DEF;ref_DEF;seq_DEF;abst_DEF;nondass_DEF;
        implies_DEF;and_DEF] THEN PBETA_TAC THEN 
   CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN 
   STRIP_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   POP_ASSUM(\th.MP_TAC
     (RR[](PBETA_RULE
       (SPECL["\u'.(P:^aurel)(a,u)u'";"k:*c,u:*s";"a:*a"]th)))) THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN EXISTS_TAC "a'':*a" THEN
    POP_ASSUM MP_TAC THEN ART[]
  ;ACCEPT_TAC nondass_dataref
  ]);;

% --- specification --- %
let spec_dataref = prove
 ("(!a k u. r(a,k,u) /\ p(a,u) ==> q(k,u)) /\
   (!a k k' u u'. 
      (r:^arel)(a,k,u) /\ p(a,u) /\ Q(k,u)(k',u')
         ==> ?a'. r(a',k',u') /\ P(a,u)(a',u'))
    ==> dataref r ((assert p) seq (nondass P)) ((assert q) seq (nondass Q))",
  STRIP_TAC THEN LPRT[dataref_DEF;ref_DEF;seq_DEF;assert_DEF;nondass_DEF
  ;abst_DEF;implies_DEF;and_DEF] THEN GEN_TAC THEN P_PGEN_TAC "k:*c,u:*s" THEN 
  PBETA_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [RES_TAC
  ;P_PGEN_TAC "k':*c,u':*s" THEN PBETA_TAC THEN STRIP_TAC THEN
   ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(el 6 l)(CONJ(el 4 l)(el 3 l)))) THEN
   ASSUM_LIST(\l.ASSUME_TAC
     (MATCH_MP(el 6 l)(CONJ(el 5 l)(CONJ(el 4 l)(el 2 l))))) THEN
   POP_ASSUM MP_TAC THEN STRIP_TAC THEN EXISTS_TAC "a':*a" THEN ART[] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ART[]
  ]);;

let spec_dataref_eq =
 let aurel = ":(*a#*s)->(*a#*s)->bool" in
 prove
  ("dataref (r:^arel) ((assert p) seq (nondass P))
                     ((assert q) seq (nondass Q))
   =  (!a k u. r(a,k,u) /\ p(a,u) ==> q(k,u)) /\
      (!a k k' u u'. (r:^arel)(a,k,u) /\ p(a,u) /\ Q(k,u)(k',u')
         ==> ?a'. r(a',k',u') /\ P(a,u)(a',u'))",
  EQ_TAC THENL
  [LPRT[dataref_DEF;ref_DEF;seq_DEF;abst_DEF;assert_DEF;nondass_DEF;
        implies_DEF;and_DEF] THEN PBETA_TAC THEN 
   CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN 
   STRIP_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THENL
   [POP_ASSUM(\th.MP_TAC
     (RR[](PBETA_RULE
       (SPECL["\u'.(P:^aurel)(a,u)u'";"k:*c,u:*s";"a:*a"]th)))) THEN
    REPEAT STRIP_TAC THEN RES_TAC 
   ;POP_ASSUM(\th.MP_TAC
     (RR[](PBETA_RULE
       (SPECL["\u'.(P:^aurel)(a,u)u'";"k:*c,u:*s";"a:*a"]th)))) THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN EXISTS_TAC "a''':*a" THEN
    POP_ASSUM MP_TAC THEN ART[]
   ]
  ;STRIP_TAC THEN IMP_RES_TAC spec_dataref
  ]);;

% --- seq --- %
let seq_dataref = prove
  ("monotonic c1' /\ dataref (r:^arel) c1 c1' /\ dataref r c2 c2'
     ==> dataref r (c1 seq c2) (c1' seq c2')",
   LPRT[monotonic_DEF;dataref_DEF;ref_DEF;seq_DEF;abst_DEF;repr_DEF;
        implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   POP_ASSUM MP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN PBETA_TAC THEN ART[]);;

% --- cond --- %
let cond_dataref = prove
 ("dataref (r:^arel) c1 c1' /\ dataref r c2 c2'
    /\ (!a k u. r(a,k,u) ==> (g(a,u) = g'(k,u)))
    ==> dataref r (cond g c1 c2) (cond g' c1' c2')",
   LPORT[dataref_DEF;ref_DEF;seq_DEF;cond_DEF;abst_DEF;repr_DEF;
         implies_DEF;or_DEF;and_DEF;not_DEF] THEN PBETA_TAC THEN
   REPEAT STRIP_TAC THENL
   [ASSUM_LIST(\l.RT[RR[MATCH_MP(RR[](SPECL["a:*a";"FST(u:*c#*s)";
       "SND(u:*c#*s)"](el 4 l)))(el 3 l)](el 2 l)]) THEN RES_TAC
   ;ASSUM_LIST(\l.RT[RR[MATCH_MP(RR[](SPECL["a:*a";"FST(u:*c#*s)";
       "SND(u:*c#*s)"](el 4 l)))(el 3 l)](el 2 l)]) THEN RES_TAC
   ]);;

% --- mu --- %
let mu_dataref =
 let t1 = PORR[SYM dataref_ba]
  (SPEC "(repr(r:^arel)) seq (mu f') seq (abst r)" 
    (C1 (INST_TYPE[":^astate",":*s1";":^astate",":*s2"] ref_prop))) in
 let t2 = MATCH_MP (ASSUME "!(c:^aptrans)(c':^cptrans). 
   dataref r c c' ==> dataref r (f c) (f' c')") t1 in
 let t3 = PORR[UNDISCH (SPEC "f':^cptrans->^cptrans" 
   (INST_TYPE[":^cstate",":*s1";":^cstate",":*s2"]
    (GEN "f:^ptrans12->^ptrans12" (DISCH_ALL mu_fp))))] 
     (ADD_ASSUM "pmonotonic(f':^cptrans->^cptrans)" t2) in
 prove
  ("regular f'
    /\ (!c c'. dataref (r:^arel) c c' ==> dataref r(f c)(f' c'))
    ==> dataref r(mu f)(mu f')",
    STRIP_TAC THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL regular_DEF))) THEN
    PORT[dataref_ba] THEN MATCH_MP_TAC mu_least THEN CONJ_TAC THENL
    [MATCH_MP_TAC mono_seq THEN RT[mono_repr] THEN
     MATCH_MP_TAC mono_seq THEN RT[mono_abst;mono_mu]
    ;RT[PORR[dataref_ba]t3]
    ]);;

% --- do --- %
let do_dataref =
 let t = prove("t==>t'==>t'' = t/\t'==>t''",TAUT_TAC)
 in prove
 ("monotonic c'
    /\ dataref (r:^arel) c c'
    /\ (!a k u. r(a,k,u) ==> (g(a,u) = g'(k,u)))
    ==> dataref r (do g c ) (do  g' c')",
  STRIP_TAC THEN PORT[do_DEF] THEN MATCH_MP_TAC mu_dataref
  THEN BETA_TAC THEN SUBGOAL_THEN 
        "regular(\x:^cptrans. cond g' (c' seq x) skip)" ASSUME_TAC THENL
  [MATCH_MP_TAC(BETA_RULE
     (ISPECL["g:^cpred";"\x:^cptrans.(c':^cptrans)seq x";
                       "\x:^cptrans.(skip:^cptrans)"] regular_cond)) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC(BETA_RULE
     (ISPECL["\x:^cptrans.(c':^cptrans)";"\x:^cptrans.x"] regular_seq)) THEN
    RT[regular_id] THEN MATCH_MP_TAC regular_const THEN ART[]
   ;MATCH_MP_TAC regular_const THEN RT[mono_skip]
   ]
  ;ART[] THEN POP_ASSUM(\t.RT[PORR[regular_DEF]t]) THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC cond_dataref THEN
   ART[skip_dataref] THEN MATCH_MP_TAC seq_dataref THEN ART[]
  ]);;

% --- block --- %
let block_dataref = 
 let thm1 = prove
  ("(\(k,u). ?a. (r:^arel)(a,k,u) /\ q u) implies (\(k,u). q u)",
   PORT[implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN ART[]) in
 prove
  ("!p c p' c' (r:^arel). monotonic c'
       /\ (!k u. p'(k,u) ==> ?a. r(a,k,u) /\ p(a,u))
       /\ dataref (r:^arel) c c'
      ==> (block p c) ref (block p' c')",
   LPORT[dataref_DEF;ref_DEF;block_DEF;seq_DEF;abst_DEF;monotonic_DEF;
         implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   ASSUM_LIST(\l.ASSUME_TAC(MATCH_MP(el 4 l)(hd l))) THEN
   ASSUM_LIST(\l.IMP_RES_TAC(RR[](CONV_RULE LEFT_IMP_EXISTS_CONV
       (SPECL["\(x':*a,v':*s).(q v':bool)";"(x,v):^cstate"](el 6 l))))) THEN
   POP_ASSUM (ASSUME_TAC o PBETA_RULE) THEN
   ASSUME_TAC (PORR[implies_DEF] thm1) THEN RES_TAC);;

save_thm(`mono_abst`,mono_abst);;
save_thm(`mono_repr`,mono_repr);;
save_thm(`abst_repr`,abst_repr);;
save_thm(`dataref_alt`,dataref_alt);;
save_thm(`dataref_ba`,dataref_ba);;
save_thm(`nondass_dataref`,nondass_dataref);;
save_thm(`nondass_dataref_eq`,nondass_dataref_eq);;
save_thm(`spec_dataref`,spec_dataref);;
save_thm(`spec_dataref_eq`,spec_dataref_eq);;
save_thm(`abort_dataref`,abort_dataref);;
save_thm(`skip_dataref`,skip_dataref);;
save_thm(`seq_dataref`,seq_dataref);;
save_thm(`cond_dataref`,cond_dataref);;
save_thm(`mu_dataref`,mu_dataref);;
save_thm(`do_dataref`,do_dataref);;
save_thm(`block_dataref`,block_dataref);;

