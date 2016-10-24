% mk_proof3.ml

  Facts about HOL-proofs
%

% --- standard theory --- %

let Is_standard_DEF = new_definition(`Is_standard_DEF`,
 "Is_standard (Typl,Conl,Axil) =
   EVERY (Pseq_well_typed Typl Conl) Axil /\ EVERY Pseq_boolean Axil /\
   mem1 `fun` Typl /\ (corr1 `fun` Typl = 2) /\
   mem1 `bool` Typl /\ (corr1 `bool` Typl = 0) /\
   mem1 `==>` Conl /\
    (corr1 `==>` Conl = Tyop`fun`[Tyop`bool`[];Tyop`fun`[Tyop`bool`[];Tyop`bool`[]]]) /\
   mem1 `=` Conl /\
    (corr1 `=` Conl = Tyop`fun`[Tyvar`*`;Tyop`fun`[Tyvar`*`;Tyop `bool`[]]]) /\
   mem1 `@` Conl /\
    (corr1 `@` Conl = Tyop`fun`(CONS(Tyop`fun`[Tyvar`*`;Tyop`bool`[]])(CONS(Tyvar`*`)[])))");;


let Pwty_OK = prove
 ("!t. Is_standard(Typl,Conl,Axil) /\ Pwell_typed Typl Conl t
        ==> Type_OK Typl (Ptype_of t)",
  INDUCT_THEN Pterm_induct ASSUME_TAC THEN
  LRT[Pwell_typed_DEF;Ptype_of_DEF] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THENL
  [POP_ASSUM MP_TAC THEN POP_ASSUM (\t.ALL_TAC) THEN
   NREPEAT 4 (POP_ASSUM MP_TAC) THEN
   MP_TAC (SPEC "Ptype_of t" Type_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_Tyop_DEF;Tyop_nam_DEF;Tyop_tyl_DEF] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN
   MP_TAC (ISPEC "ts:(Type)list" list_CASES) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;INV_SUC_EQ;GSYM NOT_SUC] THEN
   MP_TAC (ISPEC "t'':(Type)list" list_CASES) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;INV_SUC_EQ;GSYM NOT_SUC] THEN
   LRT[LENGTH_NIL;TL;HD;Type_OK_DEF;EVERY_DEF] THEN REPEAT STRIP_TAC
  ;ART[Type_OK_DEF;LENGTH;EVERY_DEF] THEN
   UNDISCH_TAC "Is_standard(Typl,Conl,Axil)" THEN PORT[Is_standard_DEF] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN REPEAT STRIP_TAC THEN ART[]
  ]);;


% --- All inferences yield all-boolean sequents --- %

let ASSUME_wty = prove
 ("PASSUME Typl Conl (Pseq as t) tm 
     ==> Pseq_boolean (Pseq as t) /\ Pseq_well_typed Typl Conl (Pseq as t)",
  LPORT[PASSUME_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF] THEN
  STRIP_TAC THEN ART[SEVERY_DEF]);;

let REFL_wty = prove
 ("Is_standard(Typl,Conl,Axil) /\ PREFL Typl Conl (Pseq as t) tm
     ==> Pseq_boolean (Pseq as t) /\ Pseq_well_typed Typl Conl (Pseq as t)",
  LPORT[Is_standard_DEF;PREFL_DEF;PEQ_DEF] THEN STRIP_TAC THEN ART[] THEN
  LRT[Pseq_boolean_DEF;Pseq_well_typed_DEF;SEVERY_DEF;Pwell_typed_DEF;
      Pboolean_DEF;Ptype_of_DEF;Tyop_tyl_DEF;TL;HD;Tyop_tyl_DEF;Tyop_nam_DEF;
      Is_Tyop_DEF;LENGTH;TL;HD] THEN CONV_TAC (REDEPTH_CONV num_CONV) THEN
      ART[] THEN REPEAT CONJ_TAC THENL
  [RT[Type_OK_DEF;LENGTH;EVERY_DEF] THEN ART[] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN RT[] THEN
   MATCH_MP_TAC Pwty_OK THEN ART[Is_standard_DEF]
  ;RT[Type_compat_DEF;LENGTH;EVERY2_DEF;Is_Tyop_DEF;Tyop_nam_DEF;
      Tyop_tyl_DEF;HD;TL]
  ;RT[Type_instl_DEF;Type_instlx_DEF;XMAP2_DEF;Tyop_tyl_DEF] THEN
   LRT[TL;HD;Tyop_tyl_DEF;LAPPEND_DEF;APPEND;HD;nocontr_DEF;mem2_DEF;corr2_DEF]
  ]);;

let thm1 = prove("t==>t'==>t'' = t/\t'==>t''",TAUT_TAC);;
let thm2 = GEN_ALL(RR[thm1](DISCH_ALL(C1(UNDISCH_ALL(SPEC_ALL Pbeta_wty)))));;
let thm3 = GEN_ALL(RR[thm1](DISCH_ALL(C2(UNDISCH_ALL(SPEC_ALL Palrep_wty)))));;
let BETA_CONV_wty = prove
 ("Is_standard(Typl,Conl,Axil) /\ PBETA_CONV Typl Conl (Pseq as t) tm
     ==> Pseq_boolean (Pseq as t) /\ Pseq_well_typed Typl Conl (Pseq as t)",
  LPORT[Is_standard_DEF;PBETA_CONV_DEF;PEQ_DEF] THEN STRIP_TAC THEN
  POART[] THEN LRT[Pseq_boolean_DEF;Pseq_well_typed_DEF;SEVERY_DEF;
      Pwell_typed_DEF;Pboolean_DEF;Ptype_of_DEF;Tyop_tyl_DEF;TL;HD;
      Tyop_nam_DEF;Is_Tyop_DEF;Tyop_tyl_DEF;TL;HD] THEN
  CONV_TAC (REDEPTH_CONV num_CONV) THEN RT[LENGTH] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
  [RT[Type_OK_DEF;LENGTH;EVERY_DEF] THEN ART[] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN RT[LENGTH] THEN
   MATCH_MP_TAC Pwty_OK THEN ART[Is_standard_DEF]
  ;ART[] THEN RT[Type_compat_DEF;LENGTH;EVERY2_DEF;Is_Tyop_DEF;Tyop_nam_DEF;
                 Tyop_tyl_DEF;HD;TL]
  ;ART[] THEN RT[Type_instl_DEF;Type_instlx_DEF;XMAP2_DEF;Tyop_tyl_DEF] THEN
   LRT[TL;HD;Tyop_tyl_DEF;LAPPEND_DEF;APPEND;HD;nocontr_DEF;mem2_DEF;
       corr2_DEF]
  ;POP_ASSUM MP_TAC THEN
   UNDISCH_TAC "Pwell_typed Typl Conl tm" THEN
   UNDISCH_TAC "Is_App tm" THEN UNDISCH_TAC "Is_Lam(App_fun tm)" THEN
   MP_TAC (SPEC "tm:Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_App_DEF;App_fun_DEF;App_arg_DEF] THEN
   MP_TAC (SPEC "P1:Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_Lam_DEF;Lam_bod_DEF;Lam_var_DEF] THEN
   RT[Pwell_typed_DEF;Ptype_of_DEF] THEN
   LRT[Is_Tyop_DEF;Tyop_nam_DEF;Tyop_tyl_DEF] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN RT[LENGTH;HD] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC thm2 THEN 
   EXISTS_TAC "P'':Pterm" THEN EXISTS_TAC "P2:Pterm" THEN
   EXISTS_TAC "p:string#Type" THEN ART[]
  ;PORT[EQ_SYM_EQ] THEN POP_ASSUM MP_TAC THEN PORT[Pbeta_DEF] THEN
   UNDISCH_TAC "Pwell_typed Typl Conl tm" THEN
   UNDISCH_TAC "Is_App tm" THEN UNDISCH_TAC "Is_Lam(App_fun tm)" THEN
   MP_TAC (SPEC "tm:Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_App_DEF;App_fun_DEF;App_arg_DEF] THEN
   MP_TAC (SPEC "P1:Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_Lam_DEF;Lam_bod_DEF;Lam_var_DEF] THEN
   RT[Pwell_typed_DEF;Ptype_of_DEF] THEN
   LRT[Is_Tyop_DEF;Tyop_nam_DEF;Tyop_tyl_DEF] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN RT[LENGTH;HD;TL] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC thm3 THEN
   EXISTS_TAC "Typl:(string#num)list" THEN
   EXISTS_TAC "Conl:(string#Type)list" THEN
   EXISTS_TAC "[P2:Pterm,p:string#Type]" THEN
   LRT[MAP;EVERY_DEF] THEN PBETA_TAC THEN REPEAT CONJ_TAC THEN
   TRY (FIRST_ASSUM ACCEPT_TAC) THEN FIRST_ASSUM (ACCEPT_TAC o SYM)
  ]);;

let thdlty = ":(Psequent#string#Type)list";;
let thm1 = prove("(t1/\t2)/\t3/\t4 = (t1/\t3)/\(t4/\t2)",TAUT_TAC);;
let SUBST_wty = prove
 ("Is_standard(Typl,Conl,Axil) /\ PSUBST Typl Conl (Pseq as t) thdl td th /\
   Pseq_boolean th /\ Pseq_well_typed Typl Conl th /\
   EVERY Pseq_boolean (MAP FST thdl) /\
   EVERY (Pseq_well_typed Typl Conl) (MAP FST thdl)
    ==> Pseq_boolean (Pseq as t) /\ Pseq_well_typed Typl Conl (Pseq as t)",
  MP_TAC (SPEC "th:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  LPORT[PSUBST_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF;Pboolean_DEF;
        Pseq_assum_DEF;Pseq_concl_DEF] THEN
  STRIP_TAC THEN PORT[thm1] THEN CONJ_TAC THENL
  [ART[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SEVERY_UNION THEN ART[] THEN
    UNDISCH_TAC "EVERY Pseq_boolean(MAP FST(thdl:^thdlty))" THEN
    SPEC_TAC ("thdl:^thdlty","thdl:^thdlty") THEN 
    INDUCT_THEN list_INDUCT ASSUME_TAC THEN
    LRT[MAP;LUNION_DEF;SEVERY_DEF] THEN
    P_PGEN_TAC "s0:Psequent,p:string#Type" THEN PBETA_TAC THEN
    MP_TAC (SPEC "s0:Psequent" Pseq_cases) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    LRT[EVERY_DEF;Pseq_boolean_DEF;Pseq_assum_DEF] THEN STRIP_TAC THEN
    MATCH_MP_TAC SEVERY_UNION THEN RES_TAC THEN ART[]
   ;MATCH_MP_TAC SEVERY_UNION THEN ART[] THEN
    UNDISCH_TAC "EVERY(Pseq_well_typed Typl Conl)(MAP FST(thdl:^thdlty))" THEN
    SPEC_TAC ("thdl:^thdlty","thdl:^thdlty") THEN 
    INDUCT_THEN list_INDUCT ASSUME_TAC THEN
    LRT[MAP;LUNION_DEF;SEVERY_DEF] THEN
    P_PGEN_TAC "s0:Psequent,p:string#Type" THEN PBETA_TAC THEN
    MP_TAC (SPEC "s0:Psequent" Pseq_cases) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    LRT[EVERY_DEF;Pseq_well_typed_DEF;Pseq_assum_DEF] THEN STRIP_TAC THEN
    MATCH_MP_TAC SEVERY_UNION THEN RES_TAC THEN ART[]
   ]
  ;ASSUM_LIST(\l.PORT[SYM(el 5 l)]) THEN MATCH_MP_TAC Psubst_wty THEN
   EXISTS_TAC "Psubst_newlist thdl" THEN EXISTS_TAC "td:Pterm" THEN
   ART[] THEN POP_ASSUM MP_TAC THEN
   UNDISCH_TAC "EVERY Is_EQtm(MAP Pseq_concl(MAP FST(thdl:^thdlty)))" THEN
   SPEC_TAC ("thdl:^thdlty","thdl:^thdlty") THEN PORT[o_DEF] THEN
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN
   LRT[Psubst_newlist_DEF;MAP;EVERY_DEF] THEN
   P_PGEN_TAC "s0:Psequent,p:string#Type" THEN PBETA_TAC THEN
   MP_TAC (SPEC "s0:Psequent" Pseq_cases) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   LRT[Pseq_concl_DEF;Pseq_well_typed_DEF] THEN STRIP_TAC THEN STRIP_TAC THEN
   RES_TAC THEN ART[] THEN UNDISCH_TAC "Is_EQtm P'''" THEN
   UNDISCH_TAC "Pwell_typed Typl Conl P'''" THEN
   PORT[Is_EQtm_DEF] THEN
   MP_TAC (SPEC "P''':Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_App_DEF;App_fun_DEF;App_arg_DEF] THEN
   MP_TAC (SPEC "P1:Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_App_DEF;App_fun_DEF;App_arg_DEF] THEN
   RT[Pwell_typed_DEF] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC
  ]);;

let ABS_wty = prove
 ("Is_standard(Typl,Conl,Axil) /\ PABS Typl Conl (Pseq as t) tm th/\
   Pseq_boolean th /\ Pseq_well_typed Typl Conl th
   ==> Pseq_boolean (Pseq as t) /\ Pseq_well_typed Typl Conl (Pseq as t)",
  MP_TAC (SPEC "th:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  LPORT[PABS_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF;Pseq_assum_DEF;
        Pseq_concl_DEF] THEN
  MP_TAC (SPEC "tm:Pterm" Pterm_cases) THEN STRIP_TAC THEN
  POP_ASSUM SUBST1_TAC THEN LRT[Is_Var_DEF;Var_var_DEF] THEN
  STRIP_TAC THEN ART[] THEN CONJ_TAC THENL
  [LRT[PEQ_DEF;Pboolean_DEF;Ptype_of_DEF] THEN RT[Tyop_tyl_DEF;TL;HD]
  ;POP_ASSUM MP_TAC THEN NREPEAT 6 (POP_ASSUM (\th.ALL_TAC)) THEN 
   UNDISCH_TAC "Is_EQtm P''" THEN
   LPORT[Is_EQtm_DEF;PEQ_DEF;Ptype_of_DEF] THEN
   MP_TAC (SPEC "P'':Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_App_DEF;App_arg_DEF;App_fun_DEF] THEN
   MP_TAC (SPEC "P1:Pterm" Pterm_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN LRT[Is_App_DEF;App_arg_DEF;App_fun_DEF] THEN
   DISCH_THEN SUBST1_TAC THEN LRT[Pwell_typed_DEF;Ptype_of_DEF;
     Tyop_tyl_DEF;TL;HD;Is_Tyop_DEF;Tyop_nam_DEF;Tyop_tyl_DEF;TL;HD;LENGTH] THEN
   STRIP_TAC THEN ART[] THEN REPEAT CONJ_TAC THENL
   [POP_ASSUM (\t.ALL_TAC) THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
    NREPEAT 4 (POP_ASSUM (\th.ALL_TAC)) THEN POP_ASSUM MP_TAC THEN
    RT[Type_OK_DEF;LENGTH;EVERY_DEF] THEN STRIP_TAC THEN ART[]
   ;POP_ASSUM (\t.ALL_TAC) THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
    NREPEAT 3 (POP_ASSUM (\th.ALL_TAC)) THEN POP_ASSUM MP_TAC THEN
    UNDISCH_TAC "Is_standard(Typl,Conl,Axil)" THEN PORT[Is_standard_DEF] THEN
    STRIP_TAC THEN ART[] THEN
    RT[Type_compat_DEF;Is_Tyop_DEF;Tyop_tyl_DEF;Tyop_nam_DEF;EVERY2;LENGTH]
   ;POP_ASSUM (\t.ALL_TAC) THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC "Is_standard(Typl,Conl,Axil)" THEN PORT[Is_standard_DEF] THEN
    STRIP_TAC THEN ART[] THEN
    RT[Type_instl_DEF;Type_instlx_DEF;XMAP2;LAPPEND_DEF;Tyop_tyl_DEF] THEN
    LRT[APPEND;nocontr_DEF;mem2_DEF;corr2_DEF]
  ]]);;

let INST_TYPE_wty = prove
 ("PINST_TYPE Typl (Pseq as t) tyl th /\
   Pseq_boolean th /\ Pseq_well_typed Typl Conl th
   ==> Pseq_boolean(Pseq as t) /\ Pseq_well_typed Typl Conl (Pseq as t)",
  MP_TAC (SPEC "th:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  LPORT[PINST_TYPE_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF;Pseq_assum_DEF;
        Pseq_concl_DEF;Pboolean_DEF] THEN STRIP_TAC THEN ART[] THEN
  IMP_RES_TAC Ptyinst_wty THEN ART[] THEN LRT[Type_replace_DEF;MAP]);;

let DISCH_wty = prove
 ("Is_standard(Typl,Conl,Axil) /\ PDISCH Typl Conl (Pseq as t) tm th /\
   Pseq_boolean th /\ Pseq_well_typed Typl Conl th
   ==> Pseq_boolean(Pseq as t) /\ Pseq_well_typed Typl Conl(Pseq as t)",
  MP_TAC (SPEC "th:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  LPORT[PDISCH_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF;Pseq_assum_DEF;
        Pseq_concl_DEF;Pboolean_DEF] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC SEVERY_DELETE THEN ART[] THEN
  RT[PIMP_DEF;Ptype_of_DEF;Tyop_tyl_DEF;TL;HD;Pwell_typed_DEF;LENGTH] THEN
  CONV_TAC(REDEPTH_CONV num_CONV) THEN ART[Is_Tyop_DEF;Tyop_nam_DEF] THEN
  UNDISCH_TAC "Is_standard(Typl,Conl,Axil)" THEN PORT[Is_standard_DEF] THEN
  STRIP_TAC THEN ART[] THEN REPEAT CONJ_TAC THENL
  [RT[Type_OK_DEF;LENGTH;EVERY_DEF] THEN ART[] THEN
   CONV_TAC (REDEPTH_CONV num_CONV) THEN REFL_TAC
  ;RT[Type_compat_DEF;Is_Tyop_DEF;Tyop_tyl_DEF;Tyop_nam_DEF;EVERY2;LENGTH]
  ;RT[Type_instl_DEF;Type_instlx_DEF;XMAP2;LAPPEND_DEF;Tyop_tyl_DEF] THEN
    LRT[APPEND;nocontr_DEF;mem2_DEF;corr2_DEF]
  ]);;

let MP_wty = prove
 ("Is_standard(Typl,Conl,Axil) /\ PMP (Pseq as t) th1 th2 /\
   Pseq_boolean th1 /\ Pseq_well_typed Typl Conl th1 /\
   Pseq_boolean th2 /\ Pseq_well_typed Typl Conl th2
   ==> Pseq_boolean (Pseq as t) /\ Pseq_well_typed Typl Conl(Pseq as t)",
  MP_TAC (SPEC "th1:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  MP_TAC (SPEC "th2:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
  LPORT[PMP_DEF;Pseq_boolean_DEF;Pseq_well_typed_DEF;Pseq_assum_DEF;
        Pseq_concl_DEF;Pboolean_DEF] THEN STRIP_TAC THEN ART[] THEN
  ASSUM_LIST(\l. RT[MATCH_MP SEVERY_UNION (CONJ(el 6 l)(el 2 l));
                    MATCH_MP SEVERY_UNION (CONJ(el 8 l)(el 4 l))]) THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC "Pwell_typed Typl Conl P''" THEN
  ART[PIMP_DEF] THEN LRT[Pwell_typed_DEF;Ptype_of_DEF] THEN 
  RT[Tyop_tyl_DEF;TL;HD;LENGTH] THEN
  CONV_TAC(REDEPTH_CONV num_CONV) THEN ART[Tyop_nam_DEF;Is_Tyop_DEF] THEN
  REPEAT STRIP_TAC THEN ART[]);;


% -- inferences preserve well-typedness --- %

let TAC1 th = 
  REPEAT GEN_TAC THEN MP_TAC (SPEC "P0:Psequent" Pseq_cases) THEN
  STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC th THEN ART[];;
let Inf_wty = save_thm(`Inf_wty`,prove
 ("!i.Is_standard(Typl,Conl,Axil) /\ OK_Inf Typl Conl Axil i /\
      EVERY Pseq_boolean (Inf_hyps i) /\ 
      EVERY (Pseq_well_typed Typl Conl) (Inf_hyps i)
      ==> Pseq_boolean (Inf_concl i) /\  
          Pseq_well_typed Typl Conl (Inf_concl i)",
  INDUCT_THEN Inf_induct ASSUME_TAC THEN
  LRT[OK_Inf_DEF;Inf_hyps_DEF;Inf_concl_DEF;EVERY_DEF;SEVERY_DEF] THENL
  [PORT[Is_standard_DEF] THEN
   REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_EVERY THEN ART[]
  ;TAC1 ASSUME_wty 
  ;TAC1 REFL_wty
  ;TAC1 BETA_CONV_wty
  ;REPEAT GEN_TAC THEN MP_TAC (SPEC "P0:Psequent" Pseq_cases) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC (GEN_ALL SUBST_wty) THEN
   EXISTS_TAC "Axil:(Psequent)list" THEN EXISTS_TAC "l:^thdlty" THEN
   EXISTS_TAC "P1:Pterm" THEN EXISTS_TAC "P2:Psequent" THEN ART[]
  ;TAC1 ABS_wty
  ;TAC1 INST_TYPE_wty
  ;TAC1 DISCH_wty
  ;REPEAT GEN_TAC THEN MP_TAC (SPEC "P0:Psequent" Pseq_cases) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC (GEN_ALL MP_wty) THEN EXISTS_TAC "Axil:(Psequent)list" THEN
   EXISTS_TAC "P1:Psequent" THEN EXISTS_TAC "P2:Psequent" THEN ART[]
  ]) );;

let Proof_wty = save_thm(`Proof_wty`,prove
 ("!P. Is_proof Typl Conl Axil P /\ Is_standard (Typl,Conl,Axil)
     ==> EVERY Pseq_boolean (MAP Inf_concl P) /\
         EVERY (Pseq_well_typed Typl Conl) (MAP Inf_concl P)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LRT[MAP;EVERY_DEF]
  ;GEN_TAC THEN LPORT[Is_proof_DEF;MAP;EVERY_DEF] THEN STRIP_TAC THEN
   RES_TAC THEN ART[] THEN IMP_RES_TAC LMEM_EVERY THEN
   MATCH_MP_TAC (GEN_ALL Inf_wty) THEN
   EXISTS_TAC "Axil:(Psequent)list" THEN ART[]
  ]) );;
