% mk_proofaux2.ml

  Auxiliary stuff needed in the proof theories: theorems
%



% --- theorems relating list functions --- %

let land_MAP = save_thm(`land_MAP`,prove
 ("!l:(*)list.land(MAP f l) = EVERY f l",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN ART[MAP;land_DEF;EVERY_DEF]) );;
let FMAP_MAP = save_thm(`FMAP_MAP`,prove
 ("!xl yl.FMAP(MAP(f:*->**->***)xl)yl = XMAP2 f xl yl",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC (ISPEC "yl:(*)list" list_CASES) THEN STRIP_TAC THEN ART[] THEN
  LRT[MAP;LENGTH;FMAP_DEF;XMAP2_DEF;NOT_SUC;GSYM NOT_SUC;INV_SUC_EQ] THEN
  ART[]) );;
let land_FMAP_MAP = save_thm(`land_FMAP_MAP`,prove
 ("!xl:(*)list.!yl:(**)list. (land(FMAP(MAP f xl)yl) = EVERY2 f xl yl)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LRT[MAP;FMAP_DEF;land_DEF;EVERY2_DEF]
  ;REPEAT GEN_TAC THEN LRT[MAP;FMAP_DEF;land_DEF;EVERY2_DEF] THEN
   MP_TAC (ISPEC "yl:(*)list" list_CASES) THEN STRIP_TAC THEN ART[]
  ]) );;


% --- Theorems about lengths of lists --- %

let LENGTH1 = save_thm(`LENGTH1`,prove
  ("(LENGTH l = 1) = (?x:*. l = [x])",
   DISJ_CASES_TAC (SPEC_ALL list_CASES) THENL
   [POP_ASSUM SUBST1_TAC THEN 
    LPORT[LENGTH;num_CONV"1";NOT_NIL_CONS;PORR[EQ_SYM_EQ]SUC_ID] THEN 
    EQ_TAC THEN STRIP_TAC
   ;POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    LPORT[LENGTH;CONS_11;num_CONV"1";INV_SUC_EQ;LENGTH_NIL] THEN
    EQ_TAC THEN STRIP_TAC THEN EXISTS_TAC "h:*" THEN ART[]
   ]) );;
let LENGTH2 = save_thm(`LENGTH2`,prove
  ("(LENGTH l = 2) = (?x:*.?y. l = [x;y])",
   DISJ_CASES_TAC (SPEC_ALL list_CASES) THENL
   [POP_ASSUM SUBST1_TAC THEN 
    LPORT[LENGTH;num_CONV"2";NOT_NIL_CONS;PORR[EQ_SYM_EQ]NOT_SUC] THEN 
    EQ_TAC THEN STRIP_TAC
   ;POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    LPORT[LENGTH;CONS_11;num_CONV"2";INV_SUC_EQ;LENGTH1] THEN
    EQ_TAC THEN STRIP_TAC THENL
    [EXISTS_TAC "h:*" THEN EXISTS_TAC "x:*" THEN ART[]
    ;EXISTS_TAC "y:*" THEN ART[]
   ]]) );;
let LENGTH_SUC_TL = save_thm(`LENGTH_SUC_TL`,prove
  ("!l:(*)list. (LENGTH l = SUC n) ==> (LENGTH(TL l) = n)",
   GEN_TAC THEN DISJ_CASES_TAC (SPEC_ALL list_CASES) THENL
   [ART[LENGTH;PORR[EQ_SYM_EQ]NOT_SUC]
   ;POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    LRT[TL;LENGTH;INV_SUC_EQ]
   ]) );;
let LENGTH_SUC_CONS = save_thm(`LENGTH_SUC_CONS`,
  IMP_TRANS (PORR[SYM(SPEC_ALL NULL_EQ_EMPTY)]
                 (SPEC_ALL LENGTH_EQ_SUC_IMP_NOT_NIL))
            (PORR[EQ_SYM_EQ](SPEC_ALL CONS)) );;
let LENGTH_GR0_CONS = save_thm(`LENGTH_GR0_CONS`,
  IMP_TRANS (PORR[SYM(SPEC_ALL NULL_EQ_EMPTY)]
                 (SPEC_ALL LENGTH_GR_0_NOT_NIL))
            (PORR[EQ_SYM_EQ](SPEC_ALL CONS)) );;


% --- lemmas about set membership --- %

let IN_INSERT_lemma = save_thm(`IN_INSERT_lemma`,prove
 ("(x:*) IN s ==> (x INSERT s = s)",
      DISCH_TAC THEN LPORT[EXTENSION;IN_INSERT] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ART[]) );;
let IN_DELETE_lemma = save_thm(`IN_DELETE_lemma`,prove
  ("~((x:*) IN s) ==> (s DELETE x = s)",
      DISCH_TAC THEN LPORT[EXTENSION;IN_DELETE] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ART[] THEN
      POP_ASSUM (\th. STRIP_TAC THEN MP_TAC th) THEN ART[]) );;


% --- lemmas about list membership --- %

let mem_lmem = save_thm(`mem_lmem`,prove
 ("!l:(*)list. mem x l /\ lmem l l' ==> mem x l'",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[mem_DEF;lmem_DEF] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ART[]) );;
let lmem_cons = prove
 ("!l:(*)list. lmem l l' ==> lmem l (CONS x l')",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN RT[lmem_DEF;mem_DEF] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;
let lmem_refl = save_thm(`lmem_refl`,prove
 ("!l:(*)list. lmem l l",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN RT[lmem_DEF;mem_DEF] THEN
  IMP_RES_TAC lmem_cons) );;


% --- Basic results about EVERY-versions --- %

let SEVERY_SING = save_thm(`SEVERY_SING`,prove
 ("!P(x:*). SEVERY P {x} = P x",RT[SEVERY_DEF]) );;
let SEVERY_DELETE = save_thm(`SEVERY_DELETE`,prove
 ("!s.!x:*.!P. SEVERY P s ==> SEVERY P (s DELETE x)",
  LPORT[SEVERY_SPEC;IN_DELETE] THEN REPEAT STRIP_TAC THEN RES_TAC) );;

let SEVERY_UNION_EQ = save_thm(`SEVERY_UNION_EQ`,prove
 ("!s1:(*)set.!s2. SEVERY P (s1:(*)set) /\ SEVERY P s2 = 
                      SEVERY P (s1 UNION s2)",
  SET_INDUCT_TAC THENL
  [LPORT[SEVERY_DEF;UNION_EMPTY] THEN RT[]
  ;GEN_TAC THEN LPORT[SEVERY_DEF;INSERT_UNION_EQ;SEVERY_DEF] THEN 
   EQ_TAC THEN STRIP_TAC THEN RES_TAC THEN ART[]
  ]) );;
let SEVERY_UNION = save_thm(`SEVERY_UNION`,
      fst(EQ_IMP_RULE(SPEC_ALL SEVERY_UNION_EQ)) );;
let SEVERY_LUNION = save_thm(`SEVERY_LUNION`,prove
 ("!xsl:((*)set)list. EVERYS P xsl ==> SEVERY P (LUNION xsl)",
  PORT[LUNION_DEF] THEN INDUCT_THEN list_INDUCT MP_TAC THENL
  [LPORT[LUNION_DEF;UNION_EMPTY] THEN RT[SEVERY_DEF]
  ;LRT[EVERYS_DEF;LUNION_DEF;SYM(SPEC_ALL SEVERY_UNION_EQ)] THEN 
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[]
  ]) );;
let EVERYS_FST0 = save_thm(`EVERY_FST0`,prove
 ("EVERYS P (MAP FST(xsl:((*)set#**)list)) /\ (0 < LENGTH xsl)
      ==> SEVERY P (FST(HD xsl))",
  DISJ_CASES_TAC (ISPEC "xsl:((*)set#**)list" list_CASES) THENL
  [ART[LENGTH;NOT_LESS_0]
  ;POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   LPORT[MAP;EVERYS_DEF;HD] THEN REPEAT STRIP_TAC THEN ART[]
  ]) );;
let EVERY_SND0 = save_thm(`EVERY_SND0`,prove
 ("EVERY P (MAP SND(xl:(*#**)list)) /\ (0 < LENGTH xl) ==> P (SND(HD xl))",
  DISJ_CASES_TAC (ISPEC "xl:(*#**)list" list_CASES) THENL
  [ART[LENGTH;NOT_LESS_0]
  ;POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   LPORT[MAP;EVERY_DEF;HD] THEN REPEAT STRIP_TAC THEN ART[]
  ]) );;


% --- Basic results about membership and EVERY-versions --- %

let MEM_EVERY = save_thm(`MEM_EVERY`,prove
 ("!l:(*)list. mem x l /\ EVERY P l ==> P x",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LPORT[mem_DEF] THEN STRIP_TAC THEN RES_TAC
  ;LPORT[mem_DEF;EVERY_DEF] THEN REPEAT STRIP_TAC THEN ART[] THEN RES_TAC
  ]) );;
let LMEM_EVERY = save_thm(`LMEM_EVERY`,prove
 ("!l:(*)list. lmem l l' /\ EVERY P l' ==> EVERY P l",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [RT[EVERY_DEF]
  ;LPORT[lmem_DEF;EVERY_DEF] THEN REPEAT STRIP_TAC THEN 
   IMP_RES_TAC MEM_EVERY THEN RES_TAC
  ]) );;
let MEM_EVERY_MAP = save_thm(`MEM_EVERY_MAP`,prove
 ("!l:(*)list. mem x l /\ EVERY P (MAP f l) ==> P(f x:**)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LPORT[mem_DEF] THEN STRIP_TAC THEN RES_TAC
  ;LPORT[mem_DEF;MAP;EVERY_DEF] THEN REPEAT STRIP_TAC THEN ART[] THEN RES_TAC
  ]) );;
let LMEM_EVERY_MAP = save_thm(`LMEM_EVERY_MAP`,prove
  ("!l:(*)list. lmem l l' /\ EVERY (P:**->bool) (MAP f l') ==> EVERY P (MAP f l)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LPORT[MAP;EVERY_DEF] THEN STRIP_TAC THEN ACCEPT_TAC TRUTH
  ;LPORT[lmem_DEF;MAP;EVERY_DEF] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MEM_EVERY_MAP THEN EXISTS_TAC "l':(*)list" THEN ART[]
   ;RES_TAC
  ]]) );;
let MEM_EVERYS_MAP = save_thm(`MEM_EVERYS_MAP`,prove
 ("!l:(*)list. mem x l /\ EVERYS(P:**->bool)(MAP f l) ==> SEVERY P (f x)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LPORT[mem_DEF] THEN STRIP_TAC THEN RES_TAC
  ;LPORT[mem_DEF;MAP;EVERYS_DEF] THEN REPEAT STRIP_TAC THEN ART[] THEN RES_TAC
  ]) );;
let LMEM_EVERYS_MAP = save_thm(`LMEM_EVERYS_MAP`,prove
 ("!l:(*set)list. lmem l l' /\ EVERYS (P:**->bool)(MAP f l') ==> EVERYS P (MAP f l)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [LPORT[MAP;EVERYS_DEF] THEN STRIP_TAC THEN ACCEPT_TAC TRUTH
  ;LPORT[lmem_DEF;MAP;EVERYS_DEF] THEN REPEAT STRIP_TAC THENL
   [IMP_RES_TAC MEM_EVERYS_MAP
   ;RES_TAC
  ]]) );;


% --- Basic results about membership and APPEND --- %

let mem_APPEND1 = save_thm(`mem_APPEND1`,prove
  ("!l:(*)list.mem x l ==> mem x (APPEND l l')",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[APPEND;mem_DEF] THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[]) );;
let mem_APPEND2 = save_thm(`mem_APPEND2`,prove
  ("!l:(*)list.mem x l' ==> mem x (APPEND l l')",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[APPEND;mem_DEF] THEN
   REPEAT STRIP_TAC THEN RES_TAC THEN ART[]) );;
let lmem_APPEND1 = save_thm(`lmem_APPEND1`,prove
  ("!xl:(*)list.lmem xl l ==> lmem xl (APPEND l l')",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[APPEND;lmem_DEF] THEN
   REPEAT STRIP_TAC THEN IMP_RES_TAC mem_APPEND1 THEN RES_TAC THEN ART[]) );;
let lmem_APPEND2 = save_thm(`lmem_APPEND2`,prove
  ("!xl:(*)list.lmem xl l' ==> lmem xl (APPEND l l')",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[APPEND;lmem_DEF] THEN
   REPEAT STRIP_TAC THEN IMP_RES_TAC mem_APPEND2 THEN RES_TAC THEN ART[]) );;


% --- a theorem about EVERY2 --- %

let EVERY_EVERY2 = save_thm(`EVERY_EVERY2`,prove
 ("!R l.EVERY (\x:*. ?y:**. R x y) l = 
   ?Y. EVERY2 R l Y /\ (LENGTH Y=LENGTH l)",
  GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN 
  LRT[EVERY_DEF;EVERY2_DEF] THEN
  BETA_TAC THEN ART[] THENL
  [EXISTS_TAC "[]:(**)list" THEN RT[LENGTH]
  ;GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC "CONS(y:**)Y" THEN ART[HD;TL;LENGTH]
   ;EXISTS_TAC "HD(Y:(**)list)" THEN ART[]
   ;EXISTS_TAC "TL(Y:(**)list)" THEN ART[] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN RT[LENGTH] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SUC_TL THEN ART[]
  ]]) );;


% --- a theorem about EVERYX --- %

let EVERY_EVERYX = save_thm(`EVERY_EVERYX`,prove
 ("!R l.EVERY (\x:*. ?y:**. R x y) l = 
   ?Y. EVERYX R l Y /\ (LENGTH Y=LENGTH l)",
  GEN_TAC THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN 
  LRT[EVERY_DEF;EVERYX_DEF] THEN
  BETA_TAC THEN ART[] THENL
  [EXISTS_TAC "[]:(**)list" THEN RT[LENGTH]
  ;GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC "CONS(y:**)Y" THEN ART[HD;TL;LENGTH]
   ;EXISTS_TAC "HD(Y:(**)list)" THEN ART[]
   ;EXISTS_TAC "TL(Y:(**)list)" THEN ART[] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN RT[LENGTH] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SUC_TL THEN ART[]
  ]]) );;


% --- distributing MAP1 over LAPPEND --- %

let MAP1_LAPPEND = save_thm(`MAP1_LAPPEND`,prove
  ("!xyll:((*#**)list)list. !f:*->***.
      MAP1 f (LAPPEND xyll) = LAPPEND (MAP(MAP1 f) xyll)",
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN LRT[MAP;LAPPEND_DEF;MAP1_DEF] THEN
  ART[] THEN INDUCT_THEN list_INDUCT ASSUME_TAC THEN ART[MAP1_DEF;APPEND]) );;

