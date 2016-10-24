% File: mk_RCbounded2.ml
   Bounded nondeterminism: basic theorems
%


% --- continuity implies monotonicity --- %
let ucont_mono =
 let t = SYM_RULE (MP (SPECL["0";"SUC n"] LESS_NOT_EQ) (SPEC "n:num" LESS_0))
 in let t1 =prove
   ("(p:^pred1) implies q ==> uchain (\n. (n=0)=>p|q)",
    DISCH_TAC THEN RT[uchain_DEF] THEN BETA_TAC THEN
    INDUCT_TAC THEN ART[implies_prop;t])
 in let t2 = prove
  ("(p:^pred1) implies q ==> (ulimit (\n. (n=0)=>p|q) = q)",
   RT[ulimit_DEF;implies_DEF] THEN DISCH_TAC THEN FUN_TAC THEN EQ_TAC THEN
   STRIP_TAC THENL
   [ASM_CASES_TAC "n=0" THEN UNDISCH_TAC "((n = 0) => (p:^pred1) | q)x"
    THEN ART[]
   ;EXISTS_TAC "SUC 0" THEN ART[SUC_ID]
   ])
 in let t3 = prove
  ("ulimit (\n. (c:^ptrans12)((n=0)=>p|q)) = (c p) or (c q)",
   RT[ulimit_DEF;or_DEF] THEN FUN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC "n=0" THEN UNDISCH_TAC "(c:^ptrans12)((n = 0) => p | q)x"
    THEN ART[] THEN DISCH_TAC THEN ART[]
   ;EXISTS_TAC "0" THEN ART[]
   ;EXISTS_TAC "SUC 0" THEN ART[SUC_ID]
   ])
 in prove
  ("ucontinuous (c:^ptrans12) ==> monotonic c",
   RT[ucontinuous_DEF;monotonic_DEF] THEN REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH t1) THEN RES_TAC THEN
   UNDISCH_TAC "(c:^ptrans12)(ulimit(\n. ((n = 0)=>p|q))) =
     ulimit(\n. c((\n. ((n = 0)=>p|q))n))" THEN BETA_TAC THEN
   RT[UNDISCH t2;t3] THEN DISCH_TAC THEN POART[] THEN
   RT[implies_DEF;or_DEF] THEN BETA_TAC THEN TAUT_TAC);;


% --- basic fact needed many times --- %

let dual_abst = prove
  ("dual (abst (r:^arel)) q = (\(k,u). !a. r(a,k,u) ==> q(a,u))",
   LPORT[dual_DEF;abst_DEF;not_DEF;not_DEF] THEN FUN_TAC THEN
   PBETA_TAC THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN 
   LPORT[DE_MORGAN_THM;NOT_CLAUSES] THEN
   PORT[TAUT "~t\/t' = t==>t'"] THEN REFL_TAC);;


% --- basic property of max --- %

let max_prop =
 let t = prove("(m<=SUC n) = (m=SUC n) \/ (m<=n)",
   LPORT[LESS_OR_EQ;LESS_THM] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ART[])
 in let t' = prove("(m<=n) /\ (n<p) ==> m<p",
    PORT[LESS_OR_EQ] THEN STRIP_TAC THEN IMP_RES_TAC LESS_TRANS THEN ART[])
 in prove
  ("i<=n ==> N i <= max N n",
   SPEC_TAC("n:num","n:num") THEN INDUCT_TAC THENL
   [LRT[LESS_OR_EQ;NOT_LESS_0] THEN DISCH_TAC THEN ART[max_DEF]
   ;LPORT[t;max_DEF] THEN STRIP_TAC THENL
    [POP_ASSUM SUBST1_TAC THEN ASM_CASES_TAC "(max N n) < (N(SUC n))" THENL
     [ART[LESS_OR_EQ]
     ;ART[] THEN POP_ASSUM (\th.RT[PORR[NOT_LESS] th;LESS_OR_EQ])
     ]
    ;RES_TAC THEN ASM_CASES_TAC "(max N n) < (N(SUC n))" THEN
     ART[] THEN IMP_RES_TAC t' THEN ART[LESS_OR_EQ]
   ]]);;


% --- chain properties --- %

let uchain_lemma = prove
 ("uchain(Q:num->^pred)
        ==> (!i j. (i<=j) ==> (Q i) implies (Q j))",
   LPORT[uchain_DEF;LESS_OR_EQ] THEN REPEAT STRIP_TAC THENL
   [POP_ASSUM (CHOOSE_TAC o MATCH_MP LESS_ADD) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN SPEC_TAC("p:num","p:num")
    THEN INDUCT_TAC THENL
    [LRT[ADD;implies_prop]
    ;EVERY_ASSUM (\th. ASSUME_TAC (SPEC "p+i" th ? th)) THEN
     PORT[ADD] THEN IMP_RES_TAC (C2(C2 implies_prop))
    ]
   ;ART[implies_prop]
   ]);;


% --- properties of the H function --- %

let mono_H = prove
 ("monotonic(c:^ptrans) ==> monotonic (H g c n)",
  LPORT[monotonic_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN SPEC_TAC("n:num","n:num") THEN INDUCT_TAC THEN
  PORT[H_DEF] THENL
  [UNDISCH_TAC "(p:^pred) implies q" THEN
   LPORT[implies_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
  ;RES_TAC THEN UNDISCH_TAC "(p:^pred) implies q" THEN
   UNDISCH_TAC "((c:^ptrans)(H g c n p)) implies (c(H g c n q))"
   THEN LPORT[implies_DEF;or_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
  ]);;

let uchain_H = prove
  ("monotonic (c:^ptrans) ==> uchain (\n. H g c n q)",
   LPORT[uchain_DEF;monotonic_DEF;implies_DEF] THEN DISCH_TAC THEN 
   BETA_TAC THEN LPORT[H_DEF;or_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN
   INDUCT_TAC THENL
   [LPORT[H_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN ART[]
   ;LPORT[H_DEF;or_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN
    REPEAT STRIP_TAC THEN ART[] THEN
    ASSUM_LIST(\l.MATCH_MP_TAC(MATCH_MP(BETA_RULE
     (SPECL["\v.H g(c:^ptrans)n q v";
        "\v.~g v/\q v\/g v/\(c:^ptrans)(H g c n q)v"](el 4 l)))(el 3 l))) THEN
    CONV_TAC(DEPTH_CONV ETA_CONV) THEN POP_ASSUM ACCEPT_TAC
   ]);;


% --- semantics of iteration: the continuuos case --- %

let do_bounded =
 let t = TAUT "t==>t'==>t'' = t/\t'==>t''" in
 let t4 = prove
  ("(g andd (ulimit(\n. c(H g c n q)))) or ((not g) andd q)
       = ulimit (\n. (H g (c:^ptrans) (SUC n) q))",
   LPORT[ulimit_DEF;H_DEF;and_DEF;or_DEF;not_DEF]
   THEN FUN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ART[]
   THEN EXISTS_TAC "n:num" THEN ART[]) in
 prove
  ("ucontinuous (c:^ptrans) ==> (do g c q = ulimit (\n. H g c n q))",
   DISCH_TAC THEN IMP_RES_TAC ucont_mono THEN 
   IMP_RES_TAC do_thm THEN POP_ASSUM (\t.RT[t]) THEN PORT[EQ_SYM_EQ] THEN 
   MATCH_MP_TAC (PORR[t] (DISCH_ALL fix_char)) THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC "monotonic(c:^ptrans)" THEN
    LPORT[monotonic_DEF;implies_DEF;and_DEF;or_DEF;not_DEF] THEN
    BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
   ;BETA_TAC THEN IMP_RES_TAC uchain_H THEN
    ASSUM_LIST(\l.SUBST1_TAC(MP(BETA_RULE(ISPEC"\n.H g c n (q:^pred)"
              (PORR[ucontinuous_DEF](el 3 l))))(SPEC_ALL(hd l)))) THEN
    SUBST1_TAC t4 THEN LPORT[implies_DEF;ulimit_DEF] THEN 
    BETA_TAC THEN REPEAT STRIP_TAC THEN EXISTS_TAC "SUC n" THEN 
    POP_ASSUM ACCEPT_TAC
   ;GEN_TAC THEN DISCH_TAC THEN LPORT[ulimit_DEF;implies_DEF]
    THEN BETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN 
    SPEC_TAC("u:^state","u:^state") THEN SPEC_TAC("n:num","n:num")
    THEN PORT[SYM(SPEC_ALL implies_DEF)] THEN INDUCT_TAC THEN PORT[H_DEF] THENL
    [POP_ASSUM (SUBST1_TAC o SYM) THEN LPORT[or_DEF;implies_DEF] THEN
     GEN_TAC THEN BETA_TAC THEN DISCH_THEN (\th.RT[th])
    ;POP_ASSUM (\th. POP_ASSUM (SUBST1_TAC o SYM) THEN ASSUME_TAC th) THEN
     REPEAT(POP_ASSUM MP_TAC) THEN LPORT[monotonic_DEF;implies_DEF;and_DEF;
     or_DEF;not_DEF]THEN BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
   ]]);;

save_thm(`ucont_mono`,ucont_mono);;
save_thm(`dual_abst`,dual_abst);;
save_thm(`max_prop`,max_prop);;
save_thm(`uchain_lemma`,uchain_lemma);;
save_thm(`mono_H`,mono_H);;
save_thm(`uchain_H`,uchain_H);;
save_thm(`do_bounded`,do_bounded);;
