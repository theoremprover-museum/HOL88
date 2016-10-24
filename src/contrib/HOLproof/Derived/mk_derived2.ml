% mk_derived2.ml

  HOL-proofs: derived inference rules
%



let bobo = "Tyop`fun`[Tyop`bool`[];Tyop`fun`[Tyop`bool`[];Tyop`bool`[]]]";;
let imp_fun t' t = "App(App(Const `==>` ^bobo) ^t') ^t";;


% --- tactics for the basic inference rules --- %

let IHYP_TAC (asl,gl) =
  let s = rand gl in
  (MATCH_MP_TAC Provable_rules THEN EXISTS_TAC (mk_comb("AX_inf",s)) THEN
   LPRT[OK_Inf_DEF;Inf_concl_DEF;Inf_hyps_DEF;APPEND;mem_DEF;EVERY_DEF]
   THEN RT[])(asl,gl);;
let IASSUME_TAC (asl,gl) = 
  let s = rand gl in
  let t = rand s in
  (MATCH_MP_TAC Provable_rules THEN
   EXISTS_TAC (list_mk_comb("AS_inf",[s;t])) THEN
   LRT[OK_Inf_DEF;Inf_concl_DEF;Inf_hyps_DEF;EVERY_DEF] THEN
   ART[PASSUME_DEF])(asl,gl);;
let IMP_TAC = 
  LPORT[PMP_DEF;Pseq_assum_DEF;Pseq_concl_DEF;PIMP_DEF] THEN RT[] THEN
  LPORT[INSERT_SING_UNION;UNION_EMPTY] THEN MATCH_ACCEPT_TAC UNION_COMM;;


% ---  ADD_ASSUM  --- %

let DADD_ASSUM = save_thm(`DADD_ASSUM`,prove
 ("!Typl Conl Axil G t' t.
    Pwell_typed Typl Conl t' /\ Pboolean t'
    ==> Dinf Typl Conl Axil `ADD_ASSUM` (Pseq (t' INSERT G) t) [Pseq G t]",
  REPEAT STRIP_TAC THEN LPRT[Dinf_DEF] THEN STRIP_TAC THEN
  ASM_CASES_TAC "(t':Pterm)IN G" THENL
   [IMP_RES_TAC IN_INSERT_lemma THEN ART[] THEN IHYP_TAC
   ;MATCH_MP_TAC Provable_rules THEN
    EXISTS_TAC "MP_inf (Pseq(t' INSERT G)t)
        (Pseq G ^(imp_fun "t':Pterm" "t:Pterm")) (Pseq {t':Pterm} t')" THEN
    LRT[Inf_concl_DEF;Inf_hyps_DEF;OK_Inf_DEF;EVERY_DEF] THEN 
    REPEAT CONJ_TAC THENL
    [IMP_TAC
    ;MATCH_MP_TAC Provable_rules THEN
     EXISTS_TAC "DI_inf (Pseq G ^(imp_fun "t':Pterm" "t:Pterm"))
                 t' (Pseq (G DELETE t') t)" THEN
     LRT[Inf_concl_DEF;Inf_hyps_DEF;OK_Inf_DEF;EVERY_DEF] THEN
     IMP_RES_TAC IN_DELETE_lemma THEN ART[] THEN CONJ_TAC THENL
     [LPORT[PDISCH_DEF;Pseq_assum_DEF;Pseq_concl_DEF;PIMP_DEF] THEN ART[]
     ;IHYP_TAC
     ]
    ;IASSUME_TAC
   ]]) );;


% ---  UNDISCH  --- %

let imptm12 = imp_fun "t1:Pterm" "t2:Pterm";;
let DUNDISCH = save_thm(`DUNDISCH`,prove
 ("!Typl Conl Axil G t1 t2.
     Dinf Typl Conl Axil `UNDISCH` (Pseq (t1 INSERT G) t2) [Pseq G ^imptm12]",
  REPEAT STRIP_TAC THEN PORT[Dinf_DEF] THEN
  LRT[EVERY_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC Provable_rules THEN
  EXISTS_TAC "MP_inf(Pseq(t1 INSERT G)t2)(Pseq G ^imptm12)(Pseq {t1} t1)" THEN
  LRT[Inf_concl_DEF;Inf_hyps_DEF;OK_Inf_DEF;EVERY_DEF] THEN 
  REPEAT CONJ_TAC THENL
  [IMP_TAC
  ;IHYP_TAC
  ;IASSUME_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM(\t.ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN LPRT[Pboolean_DEF;Pwell_typed_DEF;Ptype_of_DEF] THEN
   RT[Tyop_tyl_DEF;TL;HD;LENGTH] THEN
   STRIP_TAC THEN POP_ASSUM (\th.ALL_TAC) THEN ART[]
  ]) );;
