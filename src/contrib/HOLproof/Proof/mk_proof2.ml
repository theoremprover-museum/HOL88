% mk_proof2.ml

  Theory of HOL-proofs: the proofs
%


% --- definitions --- %

% proof with primitive inferences %
let Is_proof_DEF = new_list_rec_definition(`Is_proof_DEF`,
 "(Is_proof Typl Conl Axil [] = T) /\
  (Is_proof Typl Conl Axil (CONS i P) =
    OK_Inf Typl Conl Axil i /\ lmem (Inf_hyps i) (MAP Inf_concl P) /\
    Is_proof Typl Conl Axil P)");;
new_constant (`Is_Xproof`,":(Xinference)list->bool");;


% --- basic properties of proofs --- %

% Appending two proofs gives a new proof %
let Proof_APPEND = save_thm(`Proof_APPEND`,prove
  ("!P1 P2. Is_proof Typl Conl Axil P1 /\ Is_proof Typl Conl Axil P2 
               ==> Is_proof Typl Conl Axil (APPEND P1 P2)",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[APPEND;Is_proof_DEF] THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[MAP_APPEND] THEN 
   MATCH_MP_TAC lmem_APPEND1 THEN FIRST_ASSUM ACCEPT_TAC) );;

% Every conclusion in a proof is provable %
let Proof_Provable = save_thm(`Proof_Provable`,prove
 ("!P. Is_proof Typl Conl Axil P
          ==> EVERY (Provable Typl Conl Axil) (MAP Inf_concl P)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LRT[MAP;EVERY_DEF]
  ;LPRT[Is_proof_DEF;MAP;EVERY_DEF] THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN
   MATCH_MP_TAC Provable_rules THEN EXISTS_TAC "h:Inference" THEN
   ART[] THEN IMP_RES_TAC LMEM_EVERY
  ]) );;

% Provability implies existence of proof %
let thm1 = BETA_RULE (ISPECL
  ["\s P. Is_proof Typl Conl Axil P /\
             (s = Inf_concl(HD P)) /\  0 < (LENGTH P)"
  ;"sl:(Psequent)list"] EVERY_EVERYX);;
let lemma1 = prove
  ("!sl Y.(LENGTH Y = LENGTH sl)
           /\  EVERYX (\s P. Is_proof Typl Conl Axil P 
                     /\ (s = Inf_concl(HD P)) /\ 0 < (LENGTH P)) sl Y
           ==> EVERY (Is_proof Typl Conl Axil) Y",
   INDUCT_THEN list_INDUCT ASSUME_TAC THENL
   [LRT[LENGTH;LENGTH_NIL;EVERYX_DEF] THEN REPEAT STRIP_TAC THEN ART[EVERY_DEF]
   ;LRT[LENGTH;EVERYX_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC LENGTH_SUC_TL THEN RES_TAC THEN
    IMP_RES_TAC LENGTH_SUC_CONS THEN POP_ASSUM SUBST1_TAC THEN
    PORT[EVERY_DEF] THEN ART[]
   ]);;
let lemma2 = prove
 ("!sl Y. OK_Inf Typl Conl Axil i /\
    EVERYX 
      (\s P. Is_proof Typl Conl Axil P /\ (s=Inf_concl(HD P)) /\ 0<(LENGTH P))
      sl Y /\
    (LENGTH Y = LENGTH sl) ==>
    lmem sl (MAP Inf_concl(LAPPEND Y))",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN 
  LRT[EVERYX_DEF;lmem_DEF;Is_proof_DEF] THEN BETA_TAC THEN
  REPEAT GEN_TAC THEN
  POP_ASSUM (ASSUME_TAC o SPEC "TL(Y:((Inference)list)list)") THEN
  PORT[LENGTH] THEN STRIP_TAC THEN
  IMP_RES_TAC LENGTH_SUC_TL THEN RES_TAC THEN 
  IMP_RES_TAC LENGTH_SUC_CONS THEN POP_ASSUM SUBST1_TAC THEN
  LPRT[LAPPEND_DEF;MAP;mem_DEF;lmem_DEF;HD;MAP_APPEND] THEN CONJ_TAC THENL
  [MATCH_MP_TAC mem_APPEND1 THEN ART[] THEN IMP_RES_TAC LENGTH_GR0_CONS THEN
   POP_ASSUM SUBST1_TAC THEN LPRT[HD;MAP;mem_DEF] THEN RT[]
  ;MATCH_MP_TAC lmem_APPEND2 THEN POP_ASSUM ACCEPT_TAC
  ]);;
let Provable_Proof = save_thm(`Provable_Proof`,BETA_RULE (prove
 ("Provable Typl Conl Axil s ==>
   (\Typl Conl Axil s. 
       ?P. Is_proof Typl Conl Axil P /\ (s = Inf_concl(HD P))
              /\ (0 < LENGTH P)
   ) Typl Conl Axil s",
  MATCH_MP_TAC Provable_induct THEN BETA_TAC THEN RT[] THEN
  REPEAT GEN_TAC THEN PORT[thm1] THEN STRIP_TAC THEN
  EXISTS_TAC "CONS (i:Inference) (LAPPEND Y)" THEN
  LRT[LENGTH;LESS_0;HD;Is_proof_DEF] THEN ART[] THEN CONJ_TAC THENL
  [IMP_RES_TAC lemma2
  ;IMP_RES_TAC lemma1 THEN POP_ASSUM MP_TAC THEN
   REPEAT (POP_ASSUM (\t.ALL_TAC)) THEN 
   SPEC_TAC ("Y:((Inference)list)list","Y:((Inference)list)list") THEN 
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN 
   LRT[EVERY_DEF;LAPPEND_DEF;Is_proof_DEF] THEN REPEAT STRIP_TAC THEN
   RES_TAC THEN IMP_RES_TAC Proof_APPEND
  ]) ));;


% --- Conclusion: Provable means being the last step of a proof --- %

let Provable_thm = save_thm(`Provable_thm`,prove
 ("Provable Typl Conl Axil s =
    (?i P. Is_proof Typl Conl Axil (CONS i P) /\ (s = Inf_concl i))",
  EQ_TAC THEN STRIP_TAC THENL
  [IMP_RES_TAC Provable_Proof THEN
   EXISTS_TAC "HD(P:(Inference)list)" THEN
   EXISTS_TAC "TL(P:(Inference)list)" THEN ART[] THEN
   IMP_RES_TAC LENGTH_GR0_CONS THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
   FIRST_ASSUM ACCEPT_TAC
  ;IMP_RES_TAC Proof_Provable THEN POP_ASSUM MP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[MAP;EVERY_DEF] THEN
   STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC
  ]) );;

