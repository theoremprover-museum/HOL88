% mk_proof1.ml

  Theory of HOL-proofs: provability
%

new_theory `proof`;;
%
load_library `finite_sets`;;
load_library `more_lists`;;
new_parent `inference`;;
load_library `string`;;
load_library `taut`;;
loadf `defs/defs`;;
%

let proty = ":(string # num)list -> (string # Type)list -> 
              (Psequent)list -> Psequent -> bool";;
let RProvable_DEF = new_definition(`RProvable_DEF`,
 "RProvable R = 
    !Typl Conl Axil i s.
        EVERY (R Typl Conl Axil) (Inf_hyps i) /\
        OK_Inf Typl Conl Axil i /\
        (s = Inf_concl i)
        ==> R Typl Conl Axil s");;
let thm1 = prove
 ("!sl. P(R:^proty) /\ EVERY(\s. !R. P R ==> R Typl Conl Axil s)sl
        ==> EVERY(R Typl Conl Axil)sl",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN 
  RT[EVERY_DEF] THEN GEN_TAC THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ART[]);;
let RProvable_all = prove
 ("(?R. RProvable R) /\ (!R. P R ==> RProvable R)
   ==> RProvable (\Typl Conl Axil s. !R. P R ==> R Typl Conl Axil s)",
  PORT[RProvable_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  ASSUM_LIST(\thl.MATCH_MP_TAC(MATCH_MP(el 5 thl)(hd thl))) THEN
   EXISTS_TAC "i:Inference" THEN ART[] THEN
   IMP_RES_TAC thm1 THEN ART[]);;

let RProvable_inhab = prove
 ("?R. RProvable R",
  EXISTS_TAC "\Typl:(string # num)list.\Conl:(string # Type)list.
   \Axil:(Psequent)list. \s:Psequent. T" THEN
  PORT[RProvable_DEF] THEN BETA_TAC THEN RT[]);;
let RProvable_thm = prove
 ("?R. RProvable R /\ 
      (!R'. RProvable R' ==> 
            (!Typl Conl Axil s. R Typl Conl Axil s ==> R' Typl Conl Axil s))",
  EXISTS_TAC "\Typl Conl Axil s. !R. RProvable R ==> R Typl Conl Axil s"
  THEN CONJ_TAC THENL
  [MATCH_MP_TAC RProvable_all THEN CONJ_TAC THENL
   [ACCEPT_TAC RProvable_inhab
   ;GEN_TAC THEN DISCH_THEN ACCEPT_TAC
   ]
  ;BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
  ]);;

let Provable_SPEC = new_specification `Provable_SPEC` 
     [`constant`,`Provable`] RProvable_thm;;

let Provable_rules = save_thm(`Provable_rules`,
     CONV_RULE (RAND_CONV (PURE_ONCE_REWRITE_CONV[CONJ_SYM]))
     (CONJUNCT1(PORR[RProvable_DEF] Provable_SPEC)));;
% Provable_rules =
|- !Typl Conl Axil i s.
     (OK_Inf Typl Conl Axil i /\ (s = Inf_concl i)) /\
     EVERY(Provable Typl Conl Axil)(Inf_hyps i) ==>
     Provable Typl Conl Axil s
%

let Provable_induct = save_thm(`Provable_induct`,
      PORR[SPEC"EVERY(P:*->bool)l"CONJ_SYM]
      (CONJUNCT2(PORR[RProvable_DEF] Provable_SPEC)) );;
% Provable_induct =
|- !R'.
    (!Typl Conl Axil i s.
      (OK_Inf Typl Conl Axil i /\ (s = Inf_concl i)) /\
      EVERY(R' Typl Conl Axil)(Inf_hyps i) ==>
      R' Typl Conl Axil s) ==>
    (!Typl Conl Axil s.
      Provable Typl Conl Axil s ==> R' Typl Conl Axil s)
%

let TCA = ["Typl':(string # num)list";
           "Conl':(string # Type)list";
           "Axil':(Psequent)list"];;
let th1 = DISCH_ALL (SPEC_ALL (UNDISCH  (SPEC_ALL Provable_induct)));;
let th2 = INST["\a.\b.\c.\d. 
                ~(Provable a b c d ==> ((Typl=a)/\(Conl=b)/\(Axil=c)/\(s=d)))",
                "R':^proty"] th1;;
let th3 = REWRITE_RULE [DE_MORGAN_THM] (CONTRAPOS(BETA_RULE th2));;
let th4 = CONV_RULE (REDEPTH_CONV NOT_FORALL_CONV) th3;;
let th5 = REWRITE_RULE [NOT_IMP] th4;;
let lemma3 = prove
  ("!sl.EVERY(\d. Provable Typl' Conl' Axil' d /\
         ~((Typl = Typl') /\ (Conl = Conl') /\ (Axil = Axil') /\ (s = d))) sl
    ==> EVERY (Provable Typl' Conl' Axil') sl",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN RT[EVERY_DEF] THEN
   BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;
let th9 = mono_imp_rule (SPEC "Inf_hyps i" lemma3) th5;;
let lemma5 = prove
  ("((OK_Inf Typl' Conl' Axil' i /\ (s' = Inf_concl i)) /\
     EVERY(Provable Typl' Conl' Axil')(Inf_hyps i)) /\
     (Provable Typl' Conl' Axil' s' ==>
      (Typl = Typl') /\ (Conl = Conl') /\ (Axil = Axil') /\ (s = s'))
    ==> OK_Inf Typl Conl Axil i /\ (s = Inf_concl i) /\
        EVERY(Provable Typl Conl Axil)(Inf_hyps i)",
   ASSUME_TAC(SPECL(TCA @ ["i:Inference";"s':Psequent"]) Provable_rules) THEN 
   STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ART[]);;
let th11 = mono_imp_rule lemma5 th9;;
let Provable_cases1 = CONV_RULE (REDEPTH_CONV REMOVE_EXISTS_CONV) th11;;
let Provable_cases2 = prove
 ("(?i. OK_Inf Typl Conl Axil i /\ (s = Inf_concl i) /\
         EVERY(Provable Typl Conl Axil)(Inf_hyps i) )
     ==> Provable Typl Conl Axil s",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC Provable_rules THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let Provable_cases = save_thm(`Provable_cases`,
     IMP_ANTISYM_RULE Provable_cases1 Provable_cases2 );;
% Provable_cases =
|- Provable Typl Conl Axil s =
   (?i. OK_Inf Typl Conl Axil i /\
       (s = Inf_concl i) /\
       EVERY(Provable Typl Conl Axil)(Inf_hyps i))
%



