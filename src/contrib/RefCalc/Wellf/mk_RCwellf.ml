% File: mk_RCwellf.ml
  A theory of well-founded types 
%

new_theory `RCwellf`;;

load_library `taut`;;
let TAUT t = prove(t,TAUT_TAC);;
loadf `defs`;;


% def of strict order po %
let order_DEF = new_definition(`order_DEF`, 
 "order (po:*->*->bool) =
  (!x y. po x y ==> ~(x=y)) /\
  (!x y z. po x y /\ po y z ==> po x z)");;

% def of minimality with respect to strict order %
let minimal_DEF = new_definition(`minimal_DEF`,
 "minimal (x:*) M po = M x /\ (!y. M y ==> ~(po y x))");;

% def of well-founded strict order %
let wellf_DEF = new_definition(`wellf_DEF`,
 "wellf (po:*->*->bool) = 
   order po /\ (!M. (?x. M x) ==> ?x. minimal x M po)");;

% the well-founded induction theorem %
let wellf_INDUCT =
  let t = TAC_PROOF(([],"~t==>~t' = t'==>t"),TAUT_TAC)
  in let t1 = BETA_RULE (SPEC "\(x:*).~P x" (CONJUNCT2 
          (RR[wellf_DEF;minimal_DEF] (ASSUME "wellf (po:*->*->bool)"))))
  in let t2 = RR[NOT_CLAUSES;DE_MORGAN_THM] 
          (CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV) (CONTRAPOS t1))
  in RR[SYM_RULE (SPEC_ALL IMP_DISJ_THM)] (LPORR[t;DISJ_SYM] t2);;
% wellf po |- (!x. (!y. po y x ==> P y) ==> P x) ==> (!x. P x) %

     
% strong induction theorem for the natural numbers %
let strong_induct =
 let t1 = TAC_PROOF(([],"t==>~t'==>t'' = t==>(t''\/t')"),TAUT_TAC)
 in let t2 = PORR[t1] LESS_SUC_IMP
 in let t3 = PORR[SYM_RULE LESS_OR_EQ] t2
 in let lemma = TAC_PROOF
     (([],"(m<=n) = (m<(SUC n))"),
      PORT[LESS_OR_EQ] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN 
      ASSUME_TAC (SPEC_ALL LESS_SUC_REFL) THENL 
      [IMP_RES_TAC LESS_TRANS 
      ;ART[LESS_SUC_REFL]
      ;IMP_RES_TAC t2 THEN OART[] THEN RT[]
      ])
 in let lemma2 = TAC_PROOF
     (([],"!P. (!n. (!m. (m<n) ==> P m) ==> P n) ==> (!n m. (m<=n) ==> P m)"),
      GEN_TAC THEN DISCH_TAC THEN (FIRST_ASSUM (ASSUME_TAC o SPEC "0"))
      THEN POP_ASSUM (ASSUME_TAC o RR[NOT_LESS_0]) THEN INDUCT_TAC THENL
      [LRT[LESS_OR_EQ;NOT_LESS_0] THEN GEN_TAC THEN 
       DISCH_THEN (\th.SUBST_TAC[th]) THEN POP_ASSUM ACCEPT_TAC
      ;GEN_TAC THEN PORT[LESS_OR_EQ] THEN STRIP_TAC THENL
       [IMP_RES_TAC t3 THEN RES_TAC
       ;POP_ASSUM (\th.SUBST_TAC[th]) THEN 
        POP_ASSUM (ASSUME_TAC o PORR[lemma]) THEN RES_TAC
      ]])
 in let t4 = RR[LESS_OR_EQ] (SPECL["n:num";"n:num"](UNDISCH (SPEC_ALL lemma2)))
 in GEN "P:num->bool" (DISCH_ALL (GEN "n:num" t4));;
%  |- !P. (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n) %

% the natural numbers are a well-founded set %
let num_wellf =
 let t1=TAC_PROOF(([],"t==>~t' = t'==>~t"),TAUT_TAC)
 and t2=TAC_PROOF(([],"t==>t' = ~t'==>~t"),TAUT_TAC)
 and t3=TAC_PROOF(([],"t\/~t' = t'==>t"),TAUT_TAC)
 and t4 = BETA_RULE (SPEC "\(x:num).~M x" strong_induct)
 in TAC_PROOF
   (([],"wellf $<"),
    LPORT[wellf_DEF;order_DEF;minimal_DEF] THEN 
    RT[LESS_NOT_EQ;LESS_TRANS] THEN LPORT[t1;t2] THEN
    CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
    LPORT[DE_MORGAN_THM;t3] THEN GEN_TAC THEN ACCEPT_TAC t4
   );;

% --- the ordering  1 < 2 < 3 < ... < 0  is well-founded --- %
let wellf_0_grt = 
 let po = "\x y. (0<x) /\ ((x<y) \/ (y=0))"
 in let t11 = RR[minimal_DEF] (CONJUNCT2 (RR[wellf_DEF] num_wellf))
 in let t12 = BETA_RULE (SPEC "\m:num. M m /\ ~(m=x)" t11)
 in let t13 = TAUT "~t\/t' = t==>t'"
 in let t14 = TAUT "~(~t==>~t') = ~t/\t'"
 in prove("wellf ^po",
   LPORT[wellf_DEF;order_DEF;minimal_DEF] THEN
   BETA_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC "0<x" THEN ART[LESS_REFL] THEN
    UNDISCH_TAC "x<y" THEN ART[LESS_REFL]
   ;REPEAT STRIP_TAC THEN ART[] THENL
    [IMP_RES_TAC LESS_TRANS THEN ART[]
    ;UNDISCH_TAC "0<y" THEN ART[LESS_REFL]
    ]
   ;REPEAT GEN_TAC THEN DISCH_TAC THEN 
    ASSUM_LIST(\l.MP_TAC(MATCH_MP t11 (hd l))) THEN STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    DISJ_CASES_TAC (LPORR[EQ_SYM_EQ] (SPEC "x:num" LESS_0_CASES)) THENL
    [ART[NOT_LESS_0] THEN ASM_CASES_TAC "?(x':num). M x' /\ ~(x'=0)" THENL
     [POP_ASSUM (MP_TAC o MATCH_MP t12) THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC "x':num" THEN ART[] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
      UNDISCH_TAC "~(y = 0) ==> ~y < x'" THEN ART[t14] THEN
      STRIP_TAC THEN UNDISCH_TAC "0<y" THEN ART[LESS_REFL]
     ;POP_ASSUM (MP_TAC o (CONV_RULE NOT_EXISTS_CONV)) THEN
      LPORT[DE_MORGAN_THM;NOT_CLAUSES;t13] THEN REPEAT STRIP_TAC THEN 
      EXISTS_TAC "0" THEN ART[] THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
      ASSUM_LIST(\l.RT[el 2 l;LESS_REFL])
     ]
    ;REPEAT STRIP_TAC THEN EXISTS_TAC "x:num" THEN ART[] THEN
     GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN RT[DE_MORGAN_THM] THEN
     IMP_RES_TAC (LPORR[EQ_SYM_EQ] LESS_NOT_EQ) THEN ART[]
   ]]);;     
%  |- wellf (\x y. 0 < x /\ (x < y \/ (y = 0))) %

save_thm(`wellf_INDUCT`,wellf_INDUCT);;
save_thm(`strong_induct`,strong_induct);;
save_thm(`num_wellf`,num_wellf);;
save_thm(`wellf_0_grt`,wellf_0_grt);;

close_theory();;
