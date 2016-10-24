% File: mk_RCpredicate2.ml

   basic lemmas about predicates and fixpoints
%


let shunt = 
  let t1 = TAC_PROOF(([],"t/\t'==>t''=t'==>t==>t''"),TAUT_TAC)
  and t2 = TAC_PROOF(([],"t'==>~t\/t''=t'==>t==>t''"),TAUT_TAC)
  in prove("((b:^pred) andd p) implies q = p implies ((not b) or q)",
      LPORT[and_DEF;implies_DEF;not_DEF;or_DEF] THEN BETA_TAC THEN
      LRT[t1;t2]);;

let implies_prop = TAC_PROOF
 (([],"(!(p:^pred). p implies p) /\
       (!(p:^pred) q. p implies q /\ q implies p ==> (p = q)) /\
       (!(p:^pred) q r. p implies q /\ q implies r ==> p implies r)"),
   RT[implies_DEF] THEN SUPER_TAC THENL
   [FUN_TAC THEN EQ_TAC THEN SUPER_TAC
   ;RES_TAC
   ]);;


% --- and as binary glb --- %

let and_glb = TAC_PROOF
 (([],"(p:^pred) andd q = glb(\p'.(p'=p)\/(p'=q))"),
  LPORT[and_DEF;glb_DEF] THEN FUN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC 
  THEN ART[] THENL
  [POP_ASSUM (ASSUME_TAC o (RR[] o SPEC "p:^pred")) THEN ART[]
  ;POP_ASSUM (ASSUME_TAC o (RR[] o SPEC "q:^pred")) THEN ART[]
  ]);;


% ----- glb and least fixpoint lemmas ----- %

let glb_bound = TAC_PROOF
 ( ([],"!P (p:^pred). P p ==> (glb P) implies p"),
   REWRITE_TAC[glb_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC
   THEN RES_TAC);;
let glb_greatest = TAC_PROOF
 ( ([],"!P (q:^pred).(!p. P p ==> q implies p) ==> q implies (glb P)"),
   REWRITE_TAC[glb_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC
   THEN RES_TAC);;
let glb_mono =
 let t1 = TAC_PROOF
  (([],"(?(x:^pred). P x /\ (x implies q)) ==> (glb P) implies q"),
   STRIP_TAC THEN IMP_RES_TAC glb_bound THEN
   IMP_RES_TAC (CONJUNCT2 (CONJUNCT2 implies_prop)))
 in TAC_PROOF
  (([],"(!p.P p ==> ((f:^ptrans) p) implies (g p)) ==>
      (glb(\q.?p.P p/\(q=f p))) implies (glb(\q.?p.P p/\(q=g p)))"),
   STRIP_TAC THEN MATCH_MP_TAC glb_greatest THEN BETA_TAC THEN 
   REPEAT STRIP_TAC THEN ART[] THEN MATCH_MP_TAC t1 THEN RES_TAC 
   THEN BETA_TAC THEN EXISTS_TAC "(f:^ptrans)p'" THEN ART[]
   THEN EXISTS_TAC "p':^pred" THEN ART[]);;
let fix_least = 
  let t = BETA_RULE 
    (SPECL["\(p:^pred).(f p) implies p";"p:^pred"] glb_bound) 
 in GEN "p:^pred" (REWRITE_RULE[GEN "f:^ptrans" 
     (SYM (SPEC "f:^ptrans" fix_DEF))] t);;
let fix_fp =
  let t1 = UNDISCH (fst(EQ_IMP_RULE (SPEC "f:^ptrans" 
             (INST_TYPE[":*s",":*s1";":*s",":*s2"] monotonic_DEF))))
  in let t2 = SPECL["fix (f:^ptrans)";"p:^pred"] t1
  in let t3 = UNDISCH (IMP_TRANS (SPEC_ALL fix_least) t2)
  in let t4 = SPECL["f(fix (f:^ptrans))";"(f:^ptrans) p";"p:^pred"] 
          (CONJUNCT2 (CONJUNCT2 implies_prop))
  in let t5 = MP t4 (CONJ t3 (ASSUME "(f p) implies (p:^pred)"))
  in let t6 = DISCH_ALL (DISCH "(f p) implies (p:^pred)" t5)
  in let t7 = BETA_RULE (SPECL ["\(p:^pred).(f p)implies p";"f(fix (f:^ptrans))"] 
         glb_greatest)
  in let t8 = REWRITE_RULE[GEN "f:^ptrans" (SYM (SPEC "f:^ptrans" fix_DEF))] t7
  in let t9 = DISCH_ALL (MP t8 (GEN "p:^pred" (UNDISCH t6)))
  in let t10 = MP (SPECL["f(fix (f:^ptrans))";"fix (f:^ptrans)"] t1) (UNDISCH t9)
  in let t11 = SPECL["\(p:^pred).(f p) implies p";"f(fix (f:^ptrans))"] glb_bound
  in let t12 = REWRITE_RULE [GEN "f:^ptrans" (SYM (SPEC "f:^ptrans" fix_DEF))] 
          (BETA_RULE t11)
  in let t13 = SPECL["f(fix (f:^ptrans))";"fix (f:^ptrans)"] 
          (CONJUNCT1 (CONJUNCT2 implies_prop))
 in DISCH_ALL(MP t13 (CONJ (UNDISCH t9) (MP t12 t10)));;
let fix_char = prove
 ("monotonic (f:^ptrans) ==>
   (f a) implies a /\ (!x. (f x = x) ==> a implies x) 
       ==> (a = fix f)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC 
  (CONJUNCT1 (CONJUNCT2 implies_prop)) THEN ASSUME_TAC (UNDISCH fix_fp) 
  THEN RES_TAC THEN ART[] THEN MATCH_MP_TAC fix_least THEN 
  FIRST_ASSUM ACCEPT_TAC);;

% ----- lub and greatest fixpoint lemmas ----- %

let lub_bound = TAC_PROOF
 ( ([],"!P (p:^pred). P p ==> p implies (lub P)"),
   RT[lub_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC "p:^pred" THEN ART[]);;
let lub_least = TAC_PROOF
 ( ([],"!P (q:^pred).(!p. P p ==> p implies q) ==> (lub P) implies q"),
   RT[lub_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC
   THEN RES_TAC);;
let lub_mono =
 let t1 = TAC_PROOF
  (([],"(?(x:^pred). P x /\ (q implies x)) ==> q implies (lub P)"),
   STRIP_TAC THEN IMP_RES_TAC lub_bound THEN
   IMP_RES_TAC (CONJUNCT2 (CONJUNCT2 implies_prop)))
 in TAC_PROOF
  (([],"(!p.P p ==> ((f:^ptrans) p) implies (g p)) ==>
      (lub(\q.?p.P p/\(q=f p))) implies (lub(\q.?p.P p/\(q=g p)))"),
   STRIP_TAC THEN MATCH_MP_TAC lub_least THEN BETA_TAC THEN 
   REPEAT STRIP_TAC THEN ART[] THEN MATCH_MP_TAC t1 THEN RES_TAC 
   THEN BETA_TAC THEN EXISTS_TAC "(g:^ptrans)p'" THEN ART[] THEN
   EXISTS_TAC "p':^pred" THEN ART[]);;
let gfix_greatest = 
  let t = BETA_RULE 
    (SPECL["\(p:^pred).p implies (f p)";"p:^pred"] lub_bound) 
 in GEN "p:^pred" (REWRITE_RULE[GEN "f:^ptrans" 
     (SYM (SPEC "f:^ptrans" gfix_DEF))] t);;
let gfix_fp =
  let t1 = UNDISCH (fst(EQ_IMP_RULE (SPEC "f:^ptrans" 
              (INST_TYPE[":*s",":*s1";":*s",":*s2"] monotonic_DEF))))
  in let t2 = SPECL["p:^pred";"gfix (f:^ptrans)"] t1
  in let t3 = UNDISCH (IMP_TRANS (SPEC_ALL gfix_greatest) t2)
  in let t4 = SPECL["p:^pred";"(f:^ptrans) p";"f(gfix (f:^ptrans))"] 
          (CONJUNCT2 (CONJUNCT2 implies_prop))
  in let t5 = MP t4 (CONJ (ASSUME "(p:^pred) implies (f p)") t3)
  in let t6 = DISCH_ALL (DISCH "(p:^pred) implies (f p)" t5)
  in let t7 = BETA_RULE (SPECL ["\(p:^pred).p implies (f p)";
                 "f(gfix (f:^ptrans))"] lub_least)
  in let t8 = REWRITE_RULE[GEN "f:^ptrans" (SYM (SPEC"f:^ptrans"gfix_DEF))] t7
  in let t9 = DISCH_ALL (MP t8 (GEN "p:^pred" (UNDISCH t6)))
  in let t10 = MP (SPECL["gfix (f:^ptrans)";"f(gfix (f:^ptrans))"] t1) (UNDISCH t9)
  in let t11 =
       SPECL["\(p:^pred).p implies (f p)";"f(gfix (f:^ptrans))"] lub_bound
  in let t12 = REWRITE_RULE [GEN "f:^ptrans"(SYM (SPEC "f:^ptrans" gfix_DEF))] 
          (BETA_RULE t11)
  in let t13 = SPECL["gfix (f:^ptrans)";"f(gfix (f:^ptrans))"] 
          (CONJUNCT1 (CONJUNCT2 implies_prop))
 in DISCH_ALL(SYM_RULE (MP t13 (CONJ (UNDISCH t9) (MP t12 t10))));;
let gfix_char = prove
 ("monotonic (f:^ptrans) ==>
   a implies (f a) /\ (!x. (f x = x) ==> x implies a) 
       ==> (a = gfix f)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC 
  (CONJUNCT1 (CONJUNCT2 implies_prop)) THEN ASSUME_TAC(UNDISCH gfix_fp) 
  THEN RES_TAC THEN ART[] THEN MATCH_MP_TAC gfix_greatest THEN 
  FIRST_ASSUM ACCEPT_TAC);;


% infinitary distributivity into glb --- %

let or_into_glb =
 let t1 = TAC_PROOF
   ((["(P:^pred->bool)p"],"?(p'':^pred).
        P p'' /\ ((\v'. q v' \/ p v') = (\v'. q v' \/ p'' v'))"),
    EXISTS_TAC "p:^pred" THEN ART[])
 in let t2 = TAC_PROOF(([],"not(not(b:^pred))=b"),PRED_TAUT_TAC)
 in TAC_PROOF
  (([],"(q:^pred) or (glb P) = glb(\p'.?p. P p /\ (p'=q or p))"),
   MATCH_MP_TAC (CONJUNCT1(CONJUNCT2 implies_prop)) THEN CONJ_TAC THENL
   [MATCH_MP_TAC glb_greatest THEN LPORT[implies_DEF;or_DEF;glb_DEF] 
    THEN BETA_TAC THEN REPEAT STRIP_TAC THEN ART[] THEN
    RES_TAC THEN BETA_TAC THEN ART[]
   ;PORT[PORR[t2](SPEC "not(b:^pred)" (GEN "b:^pred" (SYM_RULE shunt)))]
    THEN MATCH_MP_TAC glb_greatest THEN REPEAT STRIP_TAC THEN
    LPORT[shunt;t2;glb_DEF;implies_DEF;not_DEF;or_DEF;and_DEF] THEN 
    BETA_TAC THEN REPEAT STRIP_TAC THEN POP_ASSUM (ASSUME_TAC o 
     BETA_RULE o SPEC "\v'.(q:^pred) v' \/ p v'") THEN ASSUME_TAC
     t1 THEN RES_TAC THEN POP_ASSUM (\th.RT[RR[] th])
   ]);;

let glb_and = prove
 ("!f g. glb(\q:^pred2. ?p:^pred1. P p /\ (q = (f p) andd (g p)))
   = (glb (\q. ?p. P p /\ (q = f p))) andd (glb (\q. ?p. P p /\ (q = g p)))",
  REPEAT GEN_TAC THEN LRT[glb_DEF;and_DEF] THEN FUN_TAC THEN EQ_TAC THEN 
  REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN BETA_TAC THENL
  [POP_ASSUM (\t.RT[BETA_RULE(CONV_RULE FORALL_1PT_CONV t)])
  ;POP_ASSUM (\t.RT[BETA_RULE(CONV_RULE FORALL_1PT_CONV t)])
  ;POP_ASSUM (\t.RT[CONV_RULE FORALL_1PT_CONV t]) THEN
   POP_ASSUM (\t.RT[CONV_RULE FORALL_1PT_CONV t])
  ]);;


save_thm(`shunt`,shunt);;
save_thm(`implies_prop`,implies_prop);;
save_thm(`and_glb`,and_glb);;
save_thm(`glb_bound`,glb_bound);;
save_thm(`glb_greatest`,glb_greatest);;
save_thm(`glb_mono`,glb_mono);;
save_thm(`fix_least`,fix_least);;
save_thm(`fix_fp`,fix_fp);;
save_thm(`fix_char`,fix_char);;
save_thm(`gfix_greatest`,gfix_greatest);;
save_thm(`gfix_fp`,gfix_fp);;
save_thm(`gfix_char`,gfix_char);;
save_thm(`or_into_glb`,or_into_glb);;
save_thm(`glb_and`,glb_and);;
