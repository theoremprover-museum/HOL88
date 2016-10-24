% mk_Type1.ml - makes the recursive type Type by hand %


new_theory  `Type`;;
%
load_library `finite_sets`;;
load_library `more_lists`;;
new_parent `proofaux`;;
loadf `defs/defs`;;
%

load_library `string`;;
load_library `taut`;;

let UNMAP_DEF = new_list_rec_definition(`UNMAP_DEF`,
  "(UNMAP ([]:(*->**)list) = \x.[]) /\
   (UNMAP (CONS h t) = \x. (CONS (h x) ((UNMAP t) x)))");;

let IS_Type = 
     "\v:string+string.
       \tl:((string+string)ltree)list.
           ((?s. v = INL s) /\ (tl = [])) \/
           (?s. v = INR s)" ;;
let Type_TY_DEF =
  let ethm = prove("?x. TRP ^IS_Type x",
     MATCH_MP_TAC exists_TRP THEN EXISTS_TAC "INR ``:(string+string)" THEN
     BETA_TAC THEN DISJ2_TAC THEN EXISTS_TAC "``" THEN REWRITE_TAC []) in
   new_type_definition(`Type`,"TRP ^IS_Type",ethm);;
let Type_ISO_DEF =
     define_new_type_bijections `Type_ISO_DEF` `ABS_Type` `REP_Type` Type_TY_DEF;;
let Tyvar_DEF =
    new_definition
    (`Tyvar_DEF`,
     "Tyvar s = ABS_Type(Node(INL s)[])");;
let Tyop_DEF =
    new_definition
    (`Tyop_DEF`,
     "Tyop s xs = ABS_Type(Node(INR s) (MAP REP_Type xs))");;
let Type_Axiom =save_thm(`Type_Axiom`,
  let lemma1 =
    prove("!l. (MAP (f:*->**) l = []) = (l = [])",
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL;MAP]) in
  let lemma2 =
    prove("!P Q R. ((P \/ Q) ==> R) =  ((P ==> R) /\ (Q ==> R))",
     REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC ["P:bool";"Q:bool"] THEN
     ASM_REWRITE_TAC []) in
   let tm =
     "\l:(*)list. \v:string+string. \d:(Type)list.
      (ISL v => f1 (OUTL v) | f2 (OUTR v) l d):*" in
   let thm1 = BETA_RULE (MATCH_MP TY_DEF_THM Type_ISO_DEF) in
   let thm2 = PURE_REWRITE_RULE [lemma1;lemma2] thm1 in
   let thm3 = CONV_RULE (REDEPTH_CONV FORALL_AND_CONV) thm2 in
   let thm4 = CONV_RULE (TOP_DEPTH_CONV ANTE_CONJ_CONV) thm3 in
   let thm5 = CONV_RULE (DEPTH_CONV FORALL_IMP_CONV) thm4 in
   let thm6 = CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV) thm5 in
   let thm7 = CONV_RULE (ONCE_DEPTH_CONV FORALL_SWAP_CONV) thm6 in
   let thm8 = CONV_RULE (DEPTH_CONV FORALL_1PT_CONV) thm7 in
   let thm9 = REWRITE_RULE [MAP] thm8 in
   let thm10 = REWRITE_RULE[SYM(SPEC_ALL Tyvar_DEF);SYM(SPEC_ALL Tyop_DEF)]thm9 in
   let thm11 = BETA_RULE (ISPEC tm thm10) in
   let thm12 = REWRITE_RULE [ISL;OUTL;OUTR] thm11 in
   let cleanup = ONCE_DEPTH_CONV (ALPHA_CONV "ts:(Type)list") in
   GEN_ALL (CONV_RULE cleanup thm12));;

% Basic properties of the Type constructors %
let Type_11 = save_thm(`Type_11`,
 let thm1a = BETA_RULE(ISPECL
  ["\s:string.s";"\s:string.\bl:(string)list.\ts:(Type)list.``"]Type_Axiom) in
 let thm2a = CONJUNCT1(BETA_RULE(REWRITE_RULE[EXISTS_UNIQUE_DEF] thm1a)) in
 let thm1b = BETA_RULE(ISPECL["\s:string.(``,[]:(Type)list)"
   ;"\s:string.\bl:(string#(Type)list)list.\ts:(Type)list.(s,ts)"]Type_Axiom) in
 let thm2b = CONJUNCT1(BETA_RULE(REWRITE_RULE[EXISTS_UNIQUE_DEF] thm1b)) in
 prove
  ("(!s s'. (Tyvar s = Tyvar s') = (s = s')) /\
    (!s ts s' ts'. (Tyop s ts = Tyop s' ts') = (s = s') /\ (ts = ts'))",
  CONJ_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
  [DISCH_TAC THEN MP_TAC thm2a THEN STRIP_TAC THEN POP_ASSUM (\th.ALL_TAC) THEN
   POP_ASSUM (\th. ASSUME_TAC (SPEC "s':string" th) THEN 
                   MP_TAC (SPEC "s:string" th)) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN (ACCEPT_TAC o SYM)
  ;DISCH_THEN SUBST1_TAC THEN REFL_TAC
  ;DISCH_TAC THEN MP_TAC thm2b THEN STRIP_TAC THEN 
   POP_ASSUM (\th. ASSUME_TAC (SPECL["s':string";"ts':(Type)list"] th) THEN 
                   MP_TAC (SPECL["s:string";"ts:(Type)list"] th)) THEN 
   ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
  ;STRIP_TAC THEN ASM_REWRITE_TAC[]
  ]));;

let Type_distinct = save_thm(`Type_distinct`,
 let thm1 = BETA_RULE
  (ISPECL["\s:string.T";"\s:string.\bl:(bool)list.\ts:(Type)list.F"]Type_Axiom) in
 let thm2 = CONJUNCT1(BETA_RULE(REWRITE_RULE[EXISTS_UNIQUE_DEF] thm1)) in
 prove("!s s' ts'. ~(Tyvar s = Tyop s' ts')",
  REPEAT STRIP_TAC THEN MP_TAC thm2 THEN STRIP_TAC THEN
  POP_ASSUM (MP_TAC o SPECL["s':string";"ts':(Type)list"]) THEN 
  POP_ASSUM (MP_TAC o SPEC_ALL) THEN ASM_REWRITE_TAC[]));;


let thm1 = CONJUNCT2(BETA_RULE(SPEC_ALL(PORR[EXISTS_UNIQUE_DEF] Type_Axiom)));;
let thm2 = BETA_RULE(BETA_RULE(ISPECL["\x:Type.T";"P:Type->bool"] thm1));;
let thm3 = GEN_ALL(RR[](BETA_RULE(CONV_RULE (DEPTH_CONV FUN_EQ_CONV) thm2)));;
let thm4 = prove("!l:(*)list. EVERY(\x.x)(MAP f l) = EVERY f l",
            INDUCT_THEN list_INDUCT ASSUME_TAC THEN ART[MAP;EVERY_DEF] THEN
            BETA_TAC THEN RT[]);;
let thm5 = prove("!l:(*)list. EVERY(\x.T) l",
            INDUCT_THEN list_INDUCT ASSUME_TAC THEN ART[EVERY_DEF]);;
let Type_induct = save_thm(`Type_induct`,prove
 ("!P.(!s. P(Tyvar s)) /\ (!s ts. EVERY P ts ==> P(Tyop s ts)) ==> !ty. P ty",
 REPEAT STRIP_TAC THEN MATCH_MP_TAC thm3 THEN
 EXISTS_TAC "\s:string.T" THEN BETA_TAC THEN ART[] THEN
 EXISTS_TAC "\s:string.\bs:(bool)list.\ts:(Type)list.
          EVERY (\x.x) bs \/ P(Tyop s ts)" THEN BETA_TAC THEN
 PORT[thm4] THEN RT[thm5] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
 STRIP_TAC THEN RES_TAC THEN ART[]) );;

let thm1 = SPEC "ty:Type"(UNDISCH(SPEC "\z:Type.~(ty = z)" Type_induct));;
let thm2 = NOT_INTRO(DISCH_ALL(MP (BETA_RULE thm1) (REFL "ty:Type")));;
let thm3 = PORR[DE_MORGAN_THM](BETA_RULE thm2);;
let thm4 = PORR[NOT_CLAUSES](CONV_RULE (DEPTH_CONV NOT_FORALL_CONV) thm3);;
let thm5 = prove("~(t==>~t') = t/\t'",TAUT_TAC);;
let thm6 = PORR[thm5](CONV_RULE (DEPTH_CONV NOT_FORALL_CONV) thm4);;
let Type_cases = save_thm(`Type_cases`,prove
 ("!ty. (?s. ty = Tyvar s) \/ (?s ts. ty = Tyop s ts)",
  GEN_TAC THEN DISJ_CASES_TAC thm6 THEN ART[] THEN
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN DISJ2_TAC THEN
  EXISTS_TAC "s:string" THEN EXISTS_TAC "ts:(Type)list" THEN ART[]) );;

