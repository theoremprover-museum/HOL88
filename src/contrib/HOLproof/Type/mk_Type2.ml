% mk_Type2.ml

  Theory of HOL-proofs: functions over Type
%


% destructors %
let Is_Tyvar_DEF = new_Type_rec_definition(`Is_Tyvar_DEF`,
 "(Is_Tyvar (Tyvar s) = T) /\
  (Is_Tyvar (Tyop s ts) = F)");;
let Is_Tyop_DEF = new_Type_rec_definition(`Is_Tyop_DEF`,
 "(Is_Tyop (Tyvar s) = F) /\
  (Is_Tyop (Tyop s ts) = T)");;
let Tyvar_nam_DEF = new_Type_rec_definition(`Tyvar_nam_DEF`,
  "(Tyvar_nam (Tyvar s) = s) /\
   (Tyvar_nam (Tyop s ts) = @y.T)");;
let Tyop_nam_DEF = new_Type_rec_definition(`Tyop_nam_DEF`,
  "(Tyop_nam (Tyvar s) = @y.T) /\
   (Tyop_nam (Tyop s ts) = s)");;
let Tyop_tyl_DEF = new_Type_rec_definition(`Tyop_tyl_DEF`,
  "(Tyop_tyl (Tyvar s) = @y.T) /\
   (Tyop_tyl (Tyop s ts) = ts)");;

% Type_OK tyl ty holds if the type ty is OK with respect to the type list tyl
  of a theory %
let Type_OK_SPEC = new_Type_rec_definition(`Type_OK_SPEC`,
 "(Type_OK tyl (Tyvar s) = T) /\
  (Type_OK tyl (Tyop s ts) =
     mem1 s tyl /\ (LENGTH ts = corr1 s tyl) /\ land(MAP(Type_OK tyl)ts))");;
load_theorem `proofaux` `land_MAP`;;
let Type_OK_DEF = save_thm(`Type_OK_DEF`,prove
 ("(!tyl s.Type_OK tyl (Tyvar s) = T) /\
   (!tyl s ts. Type_OK tyl (Tyop s ts) =
      mem1 s tyl /\ (LENGTH ts = corr1 s tyl) /\ EVERY (Type_OK tyl) ts)",
  RT[Type_OK_SPEC;land_MAP]) );;

% Type_replace tyl ty instantiates type variables in ty according to tyl %
let Type_replace_DEF = new_Type_rec_definition(`Type_replace_DEF`,
 "(Type_replace tyl (Tyvar s) = (mem2 s tyl => corr2 s tyl | Tyvar s)) /\
  (Type_replace tyl (Tyop s ts) = Tyop s (MAP(Type_replace tyl)ts))");;

% Type_compat ty' ty holds if the structure of ty' matches that of ty %
load_definition `proofaux` `EVERY2_DEF`;;
load_theorem `proofaux` `FMAP_MAP`;;
load_theorem `proofaux` `land_FMAP_MAP`;;
let f1 = "\s:string. \ty:Type. T";;
let f2 = "\s Z (ts:(Type)list) ty. Is_Tyop ty /\ (Tyop_nam ty = s) /\
                    (LENGTH(Tyop_tyl ty) = LENGTH ts) /\
                    land(FMAP Z (Tyop_tyl ty))";;
let th1 = prove("(t==>(t'=t'')) ==> (t/\t' = t/\t'')",TAUT_TAC);;
let th2 = prove
  ("!yl xl.(LENGTH xl = LENGTH yl) ==>
         (EVERY2(\y:**.\x:*.f x y)yl xl = EVERY2 f xl yl)",
   INDUCT_THEN list_INDUCT ASSUME_TAC THEN REPEAT GEN_TAC THEN
   MP_TAC (ISPEC "xl:(*)list" list_CASES) THEN STRIP_TAC THEN
   ART[] THEN LRT[LENGTH;EVERY2_DEF;GSYM NOT_SUC;INV_SUC_EQ;NOT_SUC] THEN
   BETA_TAC THEN LRT[HD;TL] THEN STRIP_TAC THEN RES_TAC THEN ART[]);;
let thm1 = PORR[land_FMAP_MAP] (BETA_RULE (ISPECL[f1;f2] Type_Axiom));;
let thm3 = SELECT_RULE(CONJUNCT1(BETA_RULE 
               (PURE_ONCE_REWRITE_RULE[EXISTS_UNIQUE_DEF] thm1)));;
let f = rator(fst(dest_eq(snd(strip_forall(concl(CONJUNCT1 thm3))))));;
let Type_compat_SPEC = new_definition(`Type_compat_SPEC`,
  "Type_compat ty' ty = ^f ty ty'");;
let thm4 = ABS "ty:Type" (ABS "ty':Type" (SPEC_ALL Type_compat_SPEC));;
let thm5 = SYM(CONV_RULE (RHS_CONV ADHOC_CONV) thm4);;
let thm6 = PORR[MATCH_MP th1 (SPEC_ALL th2)] (BETA_RULE(PORR[thm5] thm3));;
let thm7 = BETA_RULE (CONV_RULE (REDEPTH_CONV FUN_EQ_CONV) thm6);;
let thm8 = CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV "ty:Type")) thm7;;
let Type_compat_DEF = save_thm(`Type_compat_DEF`,thm8);;

% Type_instl ty' ty is the type instantiation list needed to get ty' from ty %
let f1 = "\s:string. \ty:Type. [ty,s]";;
let f2 = "\s:string. \Z:(Type->(Type#string)list)list. \(ts:(Type)list). \ty. 
            LAPPEND(FMAP Z (Tyop_tyl ty))";;
let thm1 = RR[FMAP_MAP](BETA_RULE (ISPECL[f1;f2] Type_Axiom));;
let thm3 = SELECT_RULE(CONJUNCT1(BETA_RULE 
               (PURE_ONCE_REWRITE_RULE[EXISTS_UNIQUE_DEF] thm1)));;
let f = rator(fst(dest_eq(snd(strip_forall(concl(CONJUNCT1 thm3))))));;
let Type_instl_SPEC = new_definition(`Type_instl_SPEC`,
  "Type_instl ty' ty = ^f ty ty'");;
let thm4 = ABS "ty:Type" (ABS "ty':Type" (SPEC_ALL Type_instl_SPEC));;
let thm5 = SYM(CONV_RULE (RHS_CONV ADHOC_CONV) thm4);;
let thm6 = BETA_RULE(PORR[thm5] thm3);;
let thm7 = BETA_RULE (CONV_RULE (REDEPTH_CONV FUN_EQ_CONV) thm6);;
let thm8 = CONV_RULE (ONCE_DEPTH_CONV (ALPHA_CONV "ty:Type")) thm7;;
let Type_instlx_SPEC = new_definition(`Type_instlx_SPEC`,
 "Type_instlx = \ty'' ty'. Type_instl ty' ty''");;
let thm9 = PORR[GSYM Type_instlx_SPEC] thm8;;
let Type_instl_DEF = save_thm(`Type_instl_DEF`,thm9);;

let thm11 = GEN_ALL(BETA_RULE
   (AP_THM (AP_THM Type_instlx_SPEC "ty:Type") "ty':Type"));;
let Type_instlx_DEF = save_thm(`Type_instlx_DEF`,thm11);;


% --- function needed in type instantiation %

% Type_occurs a ty holds if tyvar a occurs in type ty %
let Type_occurs_DEF = new_Type_rec_definition(`Type_occurs_DEF`,
 "(Type_occurs s' (Tyvar s) = (s = s')) /\
  (Type_occurs s' (Tyop s ts) = lor(MAP(Type_occurs s')ts))");;

