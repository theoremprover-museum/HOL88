%  mk_Type2.ml

  Theory of HOL-proofs: key results about Type functions
%


% --- Type_OK into Type_replace --- %

let Type_OK_replace = save_thm(`Type_OK_replace`,
 BETA_RULE(prove
 ("!ty.(\ty. !tyl. Type_OK Typl ty /\ EVERY (Type_OK Typl) (MAP FST tyl)
     ==> Type_OK Typl (Type_replace tyl ty)) ty",
  MATCH_MP_TAC Type_induct THEN BETA_TAC THEN CONJ_TAC THENL
  [LRT[Type_replace_DEF;Type_OK_DEF] THEN GEN_TAC THEN
   INDUCT_THEN list_INDUCT MP_TAC THEN
   LRT[MAP;EVERY_DEF;mem2_DEF;corr2_DEF;Type_OK_DEF] THEN
   ASM_CASES_TAC "mem2 s (tyl:(Type#string)list)" THEN ART[] THENL
   [REPEAT STRIP_TAC THEN RES_TAC THEN
    ASM_CASES_TAC "s = SND(h:Type#string)" THEN ART[]
   ;REPEAT STRIP_TAC THEN RES_TAC THEN
    ASM_CASES_TAC "s = SND(h:Type#string)" THEN ART[]
   ]
  ;LRT[Type_replace_DEF;Type_OK_DEF;LENGTH_MAP] THEN REPEAT STRIP_TAC
   THEN ART[] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
   POP_ASSUM (\th.ALL_TAC) THEN POP_ASSUM (\th.ALL_TAC) THEN 
   POP_ASSUM MP_TAC THEN 
   SPEC_TAC("ts:(Type)list","ts:(Type)list") THEN
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[MAP;EVERY_DEF] THEN
   BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
  ]) ) );;


% --- Type_compat into Type_replace --- %

let Type_compat_replace = save_thm(`Type_compat_replace`,
 BETA_RULE(prove
 ("!ty. (\ty. !ty'.Type_compat ty' ty
              ==> Type_compat (Type_replace tyl ty') ty )ty",
  MATCH_MP_TAC Type_induct THEN BETA_TAC THEN CONJ_TAC THEN
  RT[Type_compat_DEF] THEN REPEAT STRIP_TAC THENL
  [UNDISCH_TAC "Is_Tyop ty'" THEN
   MP_TAC (SPEC "ty':Type" Type_cases) THEN STRIP_TAC THEN
   ART[Type_replace_DEF;Is_Tyop_DEF]
  ;UNDISCH_TAC "Tyop_nam ty' = s" THEN UNDISCH_TAC "Is_Tyop ty'" THEN
   MP_TAC (SPEC "ty':Type" Type_cases) THEN STRIP_TAC THEN
   ART[Is_Tyop_DEF;Type_replace_DEF;Tyop_nam_DEF]
  ;UNDISCH_TAC "LENGTH(Tyop_tyl ty') = LENGTH(ts:(Type)list)" THEN
   UNDISCH_TAC "Is_Tyop ty'" THEN
   MP_TAC (SPEC "ty':Type" Type_cases) THEN STRIP_TAC THEN
   ART[Is_Tyop_DEF] THEN LRT[Type_replace_DEF;Tyop_tyl_DEF;LENGTH_MAP]
  ;POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM (\th.ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC "ty':Type" Type_cases) THEN STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN
   LRT[Is_Tyop_DEF;Type_replace_DEF;Tyop_tyl_DEF] THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC("ts':(Type)list","ts':(Type)list") THEN 
   SPEC_TAC("ts:(Type)list","ts:(Type)list") THEN 
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[EVERY_DEF] THENL
   [GEN_TAC THEN MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;MAP;EVERY2_DEF;NOT_SUC]
   ;BETA_TAC THEN REPEAT GEN_TAC THEN
    MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;GSYM NOT_SUC] THEN
    LRT[INV_SUC_EQ;MAP;EVERY2_DEF;HD;TL] THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN ART[]
  ]]) ) );;


% --- Type_instl into Type_replace --- %

let Type_instl_x = prove
  ("!ts ts'. (LENGTH ts' = LENGTH ts) ==>
    (XMAP2 Type_instlx ts ts' =  MAP2 Type_instl ts' ts)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [GEN_TAC THEN MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;NOT_SUC;XMAP2;MAP2]
  ;REPEAT GEN_TAC THEN MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;GSYM NOT_SUC] THEN
   LRT[INV_SUC_EQ;XMAP2;MAP2;CONS_11;Type_instlx_DEF] THEN ART[]
  ]);;
let Type_instl_thm = save_thm(`Type_instl_thm`,prove
  ("!s ts ty. Type_compat ty (Tyop s ts) ==>
      (Type_instl ty (Tyop s ts) =
         LAPPEND(MAP2 Type_instl (Tyop_tyl ty) ts))",
   LPORT[Type_compat_DEF;Type_instl_DEF] THEN REPEAT STRIP_TAC THEN
   IMP_RES_TAC Type_instl_x THEN ART[]) );;
let Type_instl_lemma =
   LRR[Type_compat_DEF;Tyop_tyl_DEF;Tyop_nam_DEF;Is_Tyop_DEF]
    (ISPECL["s:string";"ts:(Type)list";"Tyop s ts'"] Type_instl_thm);;
let thm1 = PORR[ASSUME "LENGTH(ts':(Type)list)= LENGTH(ts:(Type)list)"]
     (ISPECL["ts':(Type)list";"Type_replace tyl"] LENGTH_MAP);;
let thm2 = mk_thm([],
  "EVERY2 Type_compat ts' ts ==> 
    EVERY2 Type_compat (MAP (Type_replace tyl) ts') ts");;
let thm3 = prove
  ("!f:*->**. !x y. (x = y) ==> (f x = f y)",REPEAT STRIP_TAC THEN ART[]);;
let Type_instl_replace = save_thm(`Type_instl_replace`,BETA_RULE(prove
  ("!ty. (\ty. !ty' tyl. Type_compat ty' ty ==>
        (Type_instl (Type_replace tyl ty') ty 
          = MAP1 (Type_replace tyl) (Type_instl ty' ty)) )ty",
  MATCH_MP_TAC Type_induct THEN BETA_TAC THEN CONJ_TAC THENL
  [LRT[Type_instl_DEF;MAP1_DEF]
  ;REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
   PORT[Type_compat_DEF] THEN
   MP_TAC (SPEC "ty':Type" Type_cases) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   LRT[Is_Tyop_DEF;Tyop_nam_DEF;Tyop_tyl_DEF] THEN STRIP_TAC THEN
   ART[Type_replace_DEF] THEN ASSUME_TAC thm1 THEN
   IMP_RES_TAC thm2 THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
   IMP_RES_TAC Type_instl_lemma THEN ART[MAP1_LAPPEND] THEN
   MATCH_MP_TAC thm3 THEN
   NREPEAT 4 (POP_ASSUM (\th.ALL_TAC)) THEN POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN POP_ASSUM (\th.ALL_TAC) THEN POP_ASSUM MP_TAC THEN
   SPEC_TAC("ts':(Type)list","ts':(Type)list") THEN 
   SPEC_TAC("ts:(Type)list","ts:(Type)list") THEN 
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN RT[EVERY_DEF] THENL
   [GEN_TAC THEN MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;NOT_SUC;MAP;MAP2;MAP]
   ;BETA_TAC THEN REPEAT GEN_TAC THEN
    MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;GSYM NOT_SUC] THEN
    STRIP_TAC THEN LRT[INV_SUC_EQ;MAP2;MAP;MAP2;EVERY2;CONS_11] THEN
    RES_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
  ]]) ));;


% --- nocontr Type_instl  into  Type_replace --- %

let thm0 = prove
  ("!xyl. mem2 y (MAP1 (f:*->***) xyl) = mem2 (y:**) xyl",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[MAP1_DEF;mem2_DEF] THEN
   P_PGEN_TAC "x':*,y':**" THEN PBETA_TAC THEN RT[] THEN
   ASM_CASES_TAC "(y:**) = y'" THEN ART[]);;
let thm1 = prove
  ("!xyl. mem2 (y:**) xyl /\ (corr2 y xyl = x)
     ==> (corr2 y (MAP1 (f:*->***) xyl) = f x)",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[MAP1_DEF;mem2_DEF] THEN
   P_PGEN_TAC "x':*,y':**" THEN PBETA_TAC THEN RT[corr2_DEF] THEN
   ASM_CASES_TAC "(y:**) = y'" THEN ART[] THEN DISCH_TAC THEN ART[]);;
let nocontr_MAP1 = prove
  ("!xyl. nocontr (xyl:(*#**)list)
        ==> nocontr (MAP1 (f:*->***) xyl)",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[MAP1_DEF;nocontr_DEF] THEN
   P_PGEN_TAC "x:*,y:**" THEN PBETA_TAC THEN RT[] THEN
   ASM_CASES_TAC "mem2 y(xyl:(*#**)list)" THEN ART[] THEN
   ART[thm0] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
   IMP_RES_TAC thm1 THEN ART[]);;
let thm1 = PORR[LENGTH_MAP]
     (SPECL["ts:(Type)list";"MAP(Type_replace tyl)ts'"] Type_instl_x);;
let thm2 =prove
  ("!ts ts'.(LENGTH ts' = LENGTH ts) /\ EVERY2 Type_compat ts' ts ==>
      (MAP2 Type_instl(MAP (Type_replace tyl) ts')ts =
        MAP(MAP1(Type_replace tyl))(MAP2 Type_instl ts' ts))",
   INDUCT_THEN list_INDUCT ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;NOT_SUC;MAP;MAP2;MAP]
   ;REPEAT GEN_TAC THEN MP_TAC (ISPEC "ts':(Type)list" list_CASES) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN LRT[LENGTH;GSYM NOT_SUC] THEN
    LRT[INV_SUC_EQ;EVERY2;MAP;MAP2;MAP;CONS_11] THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN IMP_RES_TAC Type_instl_replace THEN ART[]
   ]);;
let thm3 = prove
  ("!ts. Tyop_tyl(Type_replace tyl(Tyop s ts)) = MAP (Type_replace tyl) ts",
   LPORT[Type_replace_DEF;Tyop_tyl_DEF] THEN GEN_TAC THEN REFL_TAC);;
let Type_nocontr_replace = save_thm(`Type_nocontr_replace`,prove
 ("!ty ty'.Type_compat ty' ty /\ nocontr (Type_instl ty' ty)
              ==>  nocontr (Type_instl(Type_replace tyl ty') ty)",
  GEN_TAC THEN MP_TAC (SPEC_ALL Type_cases) THEN STRIP_TAC THEN
  POP_ASSUM SUBST1_TAC THENL
  [LRT[Type_instl_DEF;nocontr_DEF;mem2_DEF]
  ;GEN_TAC THEN LRT[Type_instl_DEF;Type_compat_DEF] THEN
   MP_TAC (SPEC "ty':Type" Type_cases) THEN
   STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   LRT[Is_Tyop_DEF;Tyop_nam_DEF;Tyop_tyl_DEF;thm3] THEN
   STRIP_TAC THEN POP_ASSUM MP_TAC THEN 
   IMP_RES_TAC Type_instl_x THEN POP_ASSUM SUBST1_TAC THEN
   IMP_RES_TAC thm1 THEN POP_ASSUM (\th.RT[th]) THEN
   IMP_RES_TAC thm2 THEN POP_ASSUM (\th.RT[th]) THEN
   PORT[GSYM MAP1_LAPPEND] THEN MATCH_ACCEPT_TAC nocontr_MAP1
  ]) );;


