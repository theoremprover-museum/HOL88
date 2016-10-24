% mk_proof_rules2.ml

  ml-functions that prove things: Type and Pterm %


% --- equality conversion for Type --- %

let Type_conl = ["Tyvar";"Tyop"];;
let Type_11_CONJS = CONJUNCTS Type_11;;
% equality for Type %
letrec RType_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else
    let op1,argl1 = strip_comb t1 in
    let op2,argl2 = strip_comb t2 in
    if op1 = op2 then
     if op1 = "Tyvar" then
      TRANS (SPECL (argl1@argl2) (hd Type_11_CONJS))
            (Rstring_eq [hd argl1;hd argl2])
     else % op1 = "Tyop" %
      let [ty11;ty12],[ty21;ty22] = argl1,argl2 in
      TRANS (SPECL [ty11;ty12;ty21;ty22] (hd(tl Type_11_CONJS)))
            (RRand [Rstring_eq [ty11;ty21]
                   ;Rlist_eq [ty12;ty22]
                   ])
    else
     if op1 = "Tyvar" then
       EQF_INTRO (SPECL (argl1@argl2) Type_distinct)
     else % op1 = "Tyop" %
      EQF_INTRO (SPECL (argl1@argl2) (GEN_ALL(SYM_RULE(SPEC_ALL Type_distinct)))) )
  ? REFL(mk_eq(t1,t2)) ;;
let RRType_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM (mk_comb("$=:Type->Type->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:Type->Type->bool" th1) t2b)
              (RType_eq[t1b;t2b]) )
  ? AP_TERM_LIST  "$=:Type->Type->bool" [th2;th1] ;;
Reqs := (":Type",RType_eq).Reqs;;
RReqs := (":Type",RRType_eq).RReqs;;


% --- Type destructors --- %

% Is_Tyvar %
let Is_Tyvar_CONJS = CONJUNCTS Is_Tyvar_DEF;;
letrec RIs_Tyvar [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Tyvar" then SPECL argl (hd Is_Tyvar_CONJS)
  else % op = "Tyop" % SPECL argl (el 2 Is_Tyvar_CONJS) )
  ? REFL(mk_comb("Is_Tyvar",t1)) ;;
let RRIs_Tyvar [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_Tyvar" th1) (RIs_Tyvar [t1b]) )
  ? AP_TERM  "Is_Tyvar" th1 ;;

% Is_Tyop %
let Is_Tyop_CONJS = CONJUNCTS Is_Tyop_DEF;;
letrec RIs_Tyop [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Tyvar" then SPECL argl (hd Is_Tyop_CONJS)
  else % op = "Tyop" % SPECL argl (el 2 Is_Tyop_CONJS) )
  ? REFL(mk_comb("Is_Tyop",t1)) ;;
let RRIs_Tyop [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_Tyop" th1) (RIs_Tyop [t1b]) )
  ? AP_TERM  "Is_Tyop" th1 ;;

% Tyvar_nam %
let Tyvar_nam_CONJS = CONJUNCTS Tyvar_nam_DEF;;
letrec RTyvar_nam [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Tyvar" then SPECL argl (hd Tyvar_nam_CONJS)
  else % op = "Tyop" % SPECL argl (el 2 Tyvar_nam_CONJS) )
  ? REFL(mk_comb("Tyvar_nam",t1)) ;;
let RRTyvar_nam [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Tyvar_nam" th1) (RTyvar_nam [t1b]) )
  ? AP_TERM  "Tyvar_nam" th1 ;;

% Tyop_nam %
let Tyop_nam_CONJS = CONJUNCTS Tyop_nam_DEF;;
letrec RTyop_nam [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Tyvar" then SPECL argl (hd Tyop_nam_CONJS)
  else % op = "Tyop" % SPECL argl (el 2 Tyop_nam_CONJS) )
  ? REFL(mk_comb("Tyop_nam",t1)) ;;
let RRTyop_nam [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Tyop_nam" th1) (RTyop_nam [t1b]) )
  ? AP_TERM  "Tyop_nam" th1 ;;

% Tyop_tyl %
let Tyop_tyl_CONJS = CONJUNCTS Tyop_tyl_DEF;;
letrec RTyop_tyl [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Tyvar" then SPECL argl (hd Tyop_tyl_CONJS)
  else % op = "Tyop" % SPECL argl (el 2 Tyop_tyl_CONJS) )
  ? REFL(mk_comb("Tyop_tyl",t1)) ;;
let RRTyop_tyl [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Tyop_tyl" th1) (RTyop_tyl [t1b]) )
  ? AP_TERM  "Tyop_tyl" th1 ;;


% --- functions over Type --- %

% Type_OK %
let Type_OK_CONJS = CONJUNCTS Type_OK_DEF;;
letrec RType_OK [l;t2] =
 (let op2,argl2 = strip_comb t2 in
  if op2 = "Tyvar" then 
   SPECL[l;hd argl2] (hd Type_OK_CONJS)
  else % op2 = "Tyop" %
   let [s;ts] = argl2 in
   TRANS (SPECL [l;s;ts] (el 2 Type_OK_CONJS))
     (RRand
        [Rmem1 [s;l]
        ;RRand
           [RRnum_eq [Rlength [ts];Rcorr1[s;l]]
           ;Revery (\[ts].RType_OK[l;ts]) [mk_comb("Type_OK",l);ts] ]]) )
  ? REFL(list_mk_comb("Type_OK",[l;t2]));;
let RRType_OK [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Type_OK" [th2;th1])
        (RType_OK[t1b;t2b]) )
  ? AP_TERM_LIST "Type_OK" [th2;th1];;

% Type_replace %
let Type_replace_CONJS = CONJUNCTS Type_replace_DEF;;
letrec RType_replace [l;t2] =
 (let op2,argl2 = strip_comb t2 in
  if op2 = "Tyvar" then 
   let [s] = argl2 in
   TRANS (SPECL[l;s] (hd Type_replace_CONJS))
         (RRcond [Rmem2[s;l];Rcorr2[s;l];REFL t2])
  else % op2 = "Tyop" %
   let [s;ts] = argl2 in
   TRANS (SPECL [l;s;ts] (el 2 Type_replace_CONJS))
     (AP_TERM_LIST2 "Tyop" 
        [REFL s
        ;Rmap (\[ts].RType_replace[l;ts]) [mk_comb("Type_replace",l);ts] ] ) )
  ? REFL(list_mk_comb("Type_replace",[l;t2]));;
let RRType_replace [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Type_replace" [th2;th1])
        (RType_replace[t1b;t2b]) )
  ? AP_TERM_LIST "Type_replace" [th2;th1];;

% Type_compat %
let Type_compat_CONJS = CONJUNCTS Type_compat_DEF;;
letrec RType_compat [ty;t2] =
 (let op2,argl2 = strip_comb t2 in
  if op2 = "Tyvar" then 
   let [s] = argl2 in SPECL[s;ty] (hd Type_compat_CONJS)
  else % op2 = "Tyop" %
   let [s;ts] = argl2 in
   TRANS (SPECL [s;ts;ty] (el 2 Type_compat_CONJS))
     (RRand [RIs_Tyop[ty]
            ;RRand [RRstring_eq[RTyop_nam[ty];REFL s]
                   ;RRand [RRnum_eq[RRlength[RTyop_tyl[ty]];Rlength[ts]]
                          ;RRevery2 RType_compat
                              [REFL "Type_compat" ;RTyop_tyl[ty];REFL ts]]]]) )
  ? REFL(list_mk_comb("Type_compat",[ty;t2]));;
let RRType_compat [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Type_compat" [th2;th1])
        (RType_compat[t1b;t2b]) )
  ? AP_TERM_LIST "Type_compat" [th2;th1];;

% Type_instl %
let Type_instl_CONJS = CONJUNCTS Type_instl_DEF;;
letrec (RType_instl,RType_instlx) =
 ((\[ty;t2].
   (let op2,argl2 = strip_comb t2 in
    if op2 = "Tyvar" then 
     let [s] = argl2 in SPECL[s;ty] (hd Type_instl_CONJS)
    else % op2 = "Tyop" %
     let [s;ts] = argl2 in
     TRANS (SPECL [s;ts;ty] (el 2 Type_instl_CONJS))
       (RRlappend[RRxmap2 RType_instlx
                    [REFL "Type_instlx";REFL ts;RTyop_tyl[ty]] ]))
    ? REFL(list_mk_comb("Type_instl",[ty;t2])))
 ,(\[ty;t2].
   (TRANS (ISPECL[ty;t2] Type_instlx_DEF)
          (RType_instl[t2;ty]))
   ? REFL(list_mk_comb("Type_instlx",[ty;t2])))
 );;
let RRType_instl [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Type_instl" [th2;th1])
        (RType_instl[t1b;t2b]) )
  ? AP_TERM_LIST "Type_instl" [th2;th1];;


% equality conversion for Pterm %

let Pterm_conl = ["Const";"Var";"App";"Lam"];;
let Pterm_11_CONJS = CONJUNCTS Pterm_11;;
let Pterm_dist_CONJS = CONJUNCTS Pterm_distinct;;
letrec RPterm_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else
    let op1,argl1 = strip_comb t1 in
    let op2,argl2 = strip_comb t2 in
    if op1 = op2 then
     if op1 = "Const" then
      TRANS (SPECL (argl1@argl2) (hd Pterm_11_CONJS))
            (Rprod_eq [hd argl1;hd argl2])
     else if op1 = "Var" then
      TRANS (SPECL (argl1@argl2) (el 2 Pterm_11_CONJS))
            (Rprod_eq [hd argl1;hd argl2])
     else if op1 = "App" then
      let [t11;t12],[t21;t22]=argl1,argl2 in
      TRANS (SPECL [t11;t12;t21;t22] (el 3 Pterm_11_CONJS))
            (RRand [RPterm_eq [t11;t21]
                   ;RPterm_eq [t12;t22]
                   ] )
     else % op1 = "Lam" %
      let [x1;t11],[x2;t21]=argl1,argl2 in
      TRANS (SPECL [x1;t11;x2;t21] (el 4 Pterm_11_CONJS))
            (RRand [Rprod_eq [x1;x2]
                   ;RPterm_eq [t11;t21]
                   ] )
    else
     let n1 = (position op1 Pterm_conl) - 1 in
     let n2 = (position op2 Pterm_conl) - 1 in
     if n1<n2 then
      let n = ((n1*3)+n2)-((n1*(n1+1))/2) in
      EQF_INTRO (SPECL (argl1@argl2) (el n Pterm_dist_CONJS))
     else 
      let n = ((n2*3)+n1)-((n2*(n2+1))/2) in
      let th = EQF_INTRO (SPECL (argl2@argl1) (el n Pterm_dist_CONJS)) in
      TRANS (SYM(SYM_CONV(lhs(concl th)))) th )
  ? REFL(mk_eq(t1,t2));;
let RRPterm_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM (mk_comb("$=:Pterm->Pterm->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:Pterm->Pterm->bool" th1) t2b)
              (RPterm_eq [t1b;t2b]) )
  ? AP_TERM_LIST  "$=:Pterm->Pterm->bool" [th2;th1] ;;
Reqs := (":Pterm",RPterm_eq).Reqs;;
RReqs := (":Pterm",RRPterm_eq).RReqs;;


% --- conversions for Pterm destructors --- %


% Is_Const %
let Is_Const_CONJS = CONJUNCTS Is_Const_DEF;;
letrec RIs_Const [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Is_Const_CONJS)
  else if op = "Var" then SPECL argl (el 2 Is_Const_CONJS)
  else if op = "App" then SPECL argl (el 3 Is_Const_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Is_Const_CONJS) )
  ? REFL(mk_comb("Is_Const",t1)) ;;
let RRIs_Const [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_Const" th1) (RIs_Const [t1b]) )
  ? AP_TERM  "Is_Const" th1 ;;

% Is_Var %
let Is_Var_CONJS = CONJUNCTS Is_Var_DEF;;
letrec RIs_Var [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Is_Var_CONJS)
  else if op = "Var" then SPECL argl (el 2 Is_Var_CONJS)
  else if op = "App" then SPECL argl (el 3 Is_Var_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Is_Var_CONJS) )
  ? REFL(mk_comb("Is_Var",t1)) ;;
let RRIs_Var [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_Var" th1) (RIs_Var [t1b]) )
  ? AP_TERM  "Is_Var" th1 ;;

% Is_App %
let Is_App_CONJS = CONJUNCTS Is_App_DEF;;
letrec RIs_App [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Is_App_CONJS)
  else if op = "Var" then SPECL argl (el 2 Is_App_CONJS)
  else if op = "App" then SPECL argl (el 3 Is_App_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Is_App_CONJS) )
  ? REFL(mk_comb("Is_App",t1)) ;;
let RRIs_App [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_App" th1) (RIs_App [t1b]) )
  ? AP_TERM  "Is_App" th1 ;;

% Is_Lam %
let Is_Lam_CONJS = CONJUNCTS Is_Lam_DEF;;
letrec RIs_Lam [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Is_Lam_CONJS)
  else if op = "Var" then SPECL argl (el 2 Is_Lam_CONJS)
  else if op = "App" then SPECL argl (el 3 Is_Lam_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Is_Lam_CONJS) )
  ? REFL(mk_comb("Is_Lam",t1)) ;;
let RRIs_Lam [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_Lam" th1) (RIs_Lam [t1b]) )
  ? AP_TERM  "Is_Lam" th1 ;;

% Const_nam %
let Const_nam_CONJS = CONJUNCTS Const_nam_DEF;;
letrec RConst_nam [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Const_nam_CONJS)
  else if op = "Var" then SPECL argl (el 2 Const_nam_CONJS)
  else if op = "App" then SPECL argl (el 3 Const_nam_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Const_nam_CONJS) )
  ? REFL(mk_comb("Const_nam",t1)) ;;
let RRConst_nam [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Const_nam" th1) (RConst_nam [t1b]) )
  ? AP_TERM  "Const_nam" th1 ;;

% Const_ty %
let Const_ty_CONJS = CONJUNCTS Const_ty_DEF;;
letrec RConst_ty [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Const_ty_CONJS)
  else if op = "Var" then SPECL argl (el 2 Const_ty_CONJS)
  else if op = "App" then SPECL argl (el 3 Const_ty_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Const_ty_CONJS) )
  ? REFL(mk_comb("Const_ty",t1)) ;;
let RRConst_ty [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Const_ty" th1) (RConst_ty [t1b]) )
  ? AP_TERM  "Const_ty" th1 ;;

% Var_var %
let Var_var_CONJS = CONJUNCTS Var_var_DEF;;
letrec RVar_var [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Var_var_CONJS)
  else if op = "Var" then SPECL argl (el 2 Var_var_CONJS)
  else if op = "App" then SPECL argl (el 3 Var_var_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Var_var_CONJS) )
  ? REFL(mk_comb("Var_var",t1)) ;;
let RRVar_var [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Var_var" th1) (RVar_var [t1b]) )
  ? AP_TERM  "Var_var" th1 ;;

% App_fun %
let App_fun_CONJS = CONJUNCTS App_fun_DEF;;
letrec RApp_fun [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd App_fun_CONJS)
  else if op = "Var" then SPECL argl (el 2 App_fun_CONJS)
  else if op = "App" then SPECL argl (el 3 App_fun_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 App_fun_CONJS) )
  ? REFL(mk_comb("App_fun",t1)) ;;
let RRApp_fun [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "App_fun" th1) (RApp_fun [t1b]) )
  ? AP_TERM  "App_fun" th1 ;;

% App_arg %
let App_arg_CONJS = CONJUNCTS App_arg_DEF;;
letrec RApp_arg [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd App_arg_CONJS)
  else if op = "Var" then SPECL argl (el 2 App_arg_CONJS)
  else if op = "App" then SPECL argl (el 3 App_arg_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 App_arg_CONJS) )
  ? REFL(mk_comb("App_arg",t1)) ;;
let RRApp_arg [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "App_arg" th1) (RApp_arg [t1b]) )
  ? AP_TERM  "App_arg" th1 ;;

% Lam_var %
let Lam_var_CONJS = CONJUNCTS Lam_var_DEF;;
letrec RLam_var [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Lam_var_CONJS)
  else if op = "Var" then SPECL argl (el 2 Lam_var_CONJS)
  else if op = "App" then SPECL argl (el 3 Lam_var_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Lam_var_CONJS) )
  ? REFL(mk_comb("Lam_var",t1)) ;;
let RRLam_var [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Lam_var" th1) (RLam_var [t1b]) )
  ? AP_TERM  "Lam_var" th1 ;;

% Lam_bod %
let Lam_bod_CONJS = CONJUNCTS Lam_bod_DEF;;
letrec RLam_bod [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then SPECL argl (hd Lam_bod_CONJS)
  else if op = "Var" then SPECL argl (el 2 Lam_bod_CONJS)
  else if op = "App" then SPECL argl (el 3 Lam_bod_CONJS)
  else % op = "Lam" %     SPECL argl (el 4 Lam_bod_CONJS) )
  ? REFL(mk_comb("Lam_bod",t1)) ;;
let RRLam_bod [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Lam_bod" th1) (RLam_bod [t1b]) )
  ? AP_TERM  "Lam_bod" th1 ;;


% --- conversions corresponding to a function on Pterm --- %

% Ptype_of %
let Ptype_of_CONJS = CONJUNCTS Ptype_of_DEF;;
letrec RPtype_of [t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then
   SPECL argl (hd Ptype_of_CONJS)
  else if op = "Var" then
   TRANS (SPECL argl (el 2 Ptype_of_CONJS))
         (Rsnd [hd argl])
  else if op = "App" then
   TRANS (SPECL argl (el 3 Ptype_of_CONJS))
         (RRhd[RRtl[RRTyop_tyl[RPtype_of[hd argl]]]])
  else % op = "Lam" %
   let [x;t] = argl in
   TRANS (SPECL argl (el 4 Ptype_of_CONJS))
         (AP_TERM "Tyop `fun`"
           (AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
               [Rsnd[x];AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
                           [RPtype_of[t];REFL "NIL:(Type)list"] ] ) ) )
  ? REFL(mk_comb("Ptype_of",t1)) ;;
let RRPtype_of [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Ptype_of" th1)
        (RPtype_of [t1b]) )
  ? AP_TERM  "Ptype_of" th1 ;;


% Pboolean %
let RPboolean [t] =
 (TRANS (SPEC t Pboolean_DEF)
        (RRType_eq [RPtype_of[t]; REFL "Tyop `bool` []"]))
 ? REFL(mk_comb("Pboolean",t));;
let RRPboolean [th1] =
  let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Pboolean" th1)
        (RPboolean[t1b])
 ? AP_TERM "Pboolean" th1;;

% Pwell_typed %
let Pwell_typed_CONJS = CONJUNCTS Pwell_typed_DEF;;
letrec RPwell_typed [Typl;Conl;t1] =
 (let op,argl = strip_comb t1 in
  if op = "Const" then 
   let [s;ty] = argl in
   TRANS (SPECL [Typl;Conl;s;ty] (hd Pwell_typed_CONJS))
    (RRand[Rmem1[s;Conl]
          ;RRand[RType_OK[Typl;ty]
                ;RRand[RRType_compat[REFL ty;Rcorr1[s;Conl]]
                      ;RRnocontr[RRType_instl[REFL ty;Rcorr1[s;Conl]]] ] ] ] )
  else if op = "Var" then 
   let [x] = argl in
   TRANS (SPECL [Typl;Conl;x] (el 2 Pwell_typed_CONJS))
         (RRType_OK [REFL Typl;Rsnd[x]])
  else if op = "App" then
  let [t1';t2] = argl in
  TRANS (SPECL[Typl;Conl;t1';t2] (el 3 Pwell_typed_CONJS))
     (RRand[RPwell_typed[Typl;Conl;t1']
        ;RRand[RPwell_typed[Typl;Conl;t2]
           ;RRand[RRIs_Tyop[RPtype_of[t1']]
              ;RRand[RRstring_eq[RRTyop_nam[RPtype_of[t1']];REFL"`fun`"]
                 ;RRand[RRnum_eq[RRlength[RRTyop_tyl[RPtype_of[t1']]];REFL"2"]
                    ;RRType_eq[RRhd[RRTyop_tyl[RPtype_of[t1']]];RPtype_of[t2]]
        ]  ]  ]  ]  ] )
  else % op = "Lam" %
  let [x;t] = argl in
  TRANS(SPECL [Typl;Conl;x;t] (el 4 Pwell_typed_CONJS))
       (RRand[RPwell_typed[Typl;Conl;t]
             ;RRType_OK[REFL Typl;Rsnd[x]] ]) )
  ? REFL(list_mk_comb("Pwell_typed",[Typl;Conl;t1]));;
let RRPwell_typed [th1;th2;th3] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  TRANS (AP_TERM_LIST "Pwell_typed" [th3;th2;th1])
        (RPwell_typed [t1b;t2b;t3b]) )
  ? AP_TERM_LIST "Pwell_typed" [th3;th2;th1] ;;


% Pfree %
let Pfree_CONJS = CONJUNCTS Pfree_DEF;;
letrec RPfree [t1;t2] =
 (let op2,argl2 = strip_comb t2 in
  if op2 = "Const" then SPECL ([t1]@argl2) (hd Pfree_CONJS)
  else if op2 = "Var" then
   let x = hd argl2 in
   TRANS (SPECL [t1;x] (el 2 Pfree_CONJS))
         (Rprod_eq [x;t1])
  else if op2 = "App" then
   let [t21;t22] = argl2 in
   TRANS (SPECL [t1;t21;t22] (el 3 Pfree_CONJS))
         (RRor [RPfree [t1;t21]
               ;RPfree [t1;t22]
               ] )
  else % op2 = "Lam" %
   let [x2;t21] = argl2 in
   TRANS (SPECL [t1;x2;t21] (el 4 Pfree_CONJS))
         (RRand [RRnot [Rprod_eq [x2;t1]]
                ;RPfree [t1;t21]
                ] ) )
  ? REFL(list_mk_comb("Pfree",[t1;t2]));;
let RRPfree [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Pfree" [th2;th1])
        (RPfree[t1b;t2b]) )
  ? AP_TERM_LIST "Pfree" [th2;th1];;

% Pbound %
let Pbound_CONJS = CONJUNCTS Pbound_DEF;;
letrec RPbound [t1;t2] =
 (let op2,argl2 = strip_comb t2 in
  if op2 = "Const" then SPECL ([t1]@argl2) (hd Pbound_CONJS)
  else if op2 = "Var" then SPECL ([t1]@argl2) (el 2 Pbound_CONJS)
  else if op2 = "App" then
   let [t21;t22] = argl2 in
   TRANS (SPECL [t1;t21;t22] (el 3 Pbound_CONJS))
         (RRor [RPbound [t1;t21]
               ;RPbound [t1;t22]
               ] )
  else % op2 = "Lam" %
   let [x2;t21] = argl2 in
   TRANS (SPECL [t1;x2;t21] (el 4 Pbound_CONJS))
         (RRor [Rprod_eq [x2;t1]
               ;RPbound [t1;t21]
               ] ) )
  ? REFL(list_mk_comb("Pbound",[t1;t2]));;
let RRPbound [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Pbound" [th2;th1])
        (RPbound[t1b;t2b]) )
  ? AP_TERM_LIST "Pbound" [th2;th1];;

% Poccurs %
let RPoccurs [t1;t2] =
 (TRANS (ISPECL[t1;t2] Poccurs_DEF)
        (RRor [RPfree [t1;t2]
              ;RPbound[t1;t2]
              ] ) )
 ? REFL(list_mk_comb("Poccurs",[t1;t2]));;
let RRPoccurs [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Poccurs" [th2;th1])
        (RPoccurs[t1b;t2b])
 ? AP_TERM_LIST "Poccurs" [th2;th1];;

% Plnotfree %
let Plnotfree_CONJS = CONJUNCTS Plnotfree_DEF;;
letrec RPlnotfree [t1;t] =
 (if t1 = "[]:(string#Type)list" then ISPEC t (hd Plnotfree_CONJS)
  else
   let x,xl = dest_cons t1 in
   TRANS (ISPECL[x;xl;t] (hd(tl Plnotfree_CONJS)))
         (RRand [RRnot [RPfree [x;t]]
                       ;RPlnotfree [xl;t]
                       ] ) )
 ? REFL(list_mk_comb("Plnotfree",[t1;t]));;
let RRPlnotfree [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM_LIST "Plnotfree" [th2;th1])
       (RPlnotfree[t1b;t2b])
 ? AP_TERM_LIST "Plnotfree" [th2;th1];;

% Plnotbound %
let Plnotbound_CONJS = CONJUNCTS Plnotbound_DEF;;
letrec RPlnotbound [t1;t] =
 (if t1 = "[]:(string#Type)list" then ISPEC t (hd Plnotbound_CONJS)
  else
   let x,xl = dest_cons t1 in
   TRANS (ISPECL[x;xl;t] (hd(tl Plnotbound_CONJS)))
         (RRand [RRnot [RPbound [x;t]]
                       ;RPlnotbound [xl;t]
                       ] ) )
 ? REFL(list_mk_comb("Plnotbound",[t1;t]));;
let RRPlnotbound [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM_LIST "Plnotbound" [th2;th1])
       (RPlnotbound[t1b;t2b])
 ? AP_TERM_LIST "Plnotbound" [th2;th1];;

% Plnotoccurs %
let RPlnotoccurs [t1;t2] =
 (TRANS (ISPECL[t1;t2] Plnotoccurs_DEF)
        (RRand [RPlnotfree [t1;t2]
               ;RPlnotbound[t1;t2]
               ] ) )
 ? REFL(list_mk_comb("Plnotoccurs",[t1;t2]));;
let RRPlnotoccurs [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Plnotoccurs" [th2;th1])
        (RPlnotoccurs[t1b;t2b])
 ? AP_TERM_LIST "Plnotoccurs" [th2;th1];;

% Pallnotfree %
let Pallnotfree_CONJS = CONJUNCTS Pallnotfree_DEF;;
letrec RPallnotfree [x;t2] =
 (if t2 = "{}:(Pterm)set" then SPEC x (hd Pallnotfree_CONJS)
  else
   let _,[tm;tms] = strip_comb t2 in
   TRANS (SPECL[x;tm;tms] (hd(tl Pallnotfree_CONJS)))
         (RRand [RRnot [RPfree [x;tm]]
                ;RPallnotfree [x;tms]
                ] ) )
 ? REFL(list_mk_comb("Pallnotfree",[x;t2]));;
let RRPallnotfree [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM_LIST "Pallnotfree" [th2;th1])
       (RPallnotfree[t1b;t2b])
 ? AP_TERM_LIST "Pallnotfree" [th2;th1];;

% Plallnotfree %
let Plallnotfree_CONJS = CONJUNCTS Plallnotfree_DEF;;
letrec RPlallnotfree [xl;t2] =
 (if t2 = "{}:(Pterm)set" then SPEC xl (hd Plallnotfree_CONJS)
  else
   let _,[tm;tms] = strip_comb t2 in
   TRANS (SPECL[xl;tm;tms] (hd(tl Plallnotfree_CONJS)))
         (RRand [RPlnotfree [xl;tm]
                ;RPlallnotfree [xl;tms]
                ] ) )
 ? REFL(list_mk_comb("Plallnotfree",[xl;t2]));;
let RRPlallnotfree [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM_LIST "Plallnotfree" [th2;th1])
       (RPlallnotfree[t1b;t2b])
 ? AP_TERM_LIST "Plallnotfree" [th2;th1];;

% Palreplace1 %
let Palreplace1_CONJS = CONJUNCTS Palreplace1_DEF;;
letrec RPalreplace1 [t';vvl;tvl;t] =
 (let op,argl= strip_comb t in
  if op = "Const" then 
   let [s;ty] = argl in
   TRANS (SPECL [t';vvl;tvl;s;ty] (hd Palreplace1_CONJS))
         (RPterm_eq[t';t])
  else if op = "Var" then
   let [x] = argl in
   TRANS (SPECL [t';vvl;tvl;x] (el 2 Palreplace1_CONJS))
     (RRcond[RRand[RIs_Var[t'];RRmem1[RVar_var[t'];REFL vvl]]
            ;RRprod_eq[REFL x;RRcorr1[RVar_var[t'];REFL vvl]]
            ;RRand[RRnot[Rmem1[x;vvl]]
                  ;RRcond[Rmem2[x;tvl]
                         ;RRPterm_eq[REFL t';Rcorr2[x;tvl]]
                         ;RPterm_eq[t';t] ] ] ])
  else if op = "App" then
   let [t1;t2] = argl in
   let thm1,thm2 = RApp_fun[t'],RApp_arg[t'] in
    TRANS (SUBS[thm1;thm2]
            (SPECL ([t';vvl;tvl;t1;t2]) (el 3 Palreplace1_CONJS)))
    (RRand[RIs_App[t']
          ;RRand[RPalreplace1[rhs(concl thm1);vvl;tvl;t1]
                ;RPalreplace1[rhs(concl thm2);vvl;tvl;t2] ] ] )
  else % op = "Lam" %
  let [x;t1] = argl in
  let thm1,thm2 = RLam_var[t'],RLam_bod[t'] in
   TRANS (SUBS[thm1;thm2]
            (SPECL ([t';vvl;tvl;x;t1]) (el 4 Palreplace1_CONJS)))
     (RRand[RIs_Lam[t']
           ;RRand[RRType_eq[Rsnd[rhs(concl thm1)];Rsnd[x]]
                 ;RPalreplace1[rhs(concl thm2)
                              ;mk_cons(mk_pair(rhs(concl thm1),x),vvl)
                              ;tvl;t1] ] ]) )
  ? REFL(list_mk_comb("Palreplace1",[t';vvl;tvl;t]));;
let RRPalreplace1[th1;th2;th3;th4] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "Palreplace1" [th4;th3;th2;th1])
        (RPalreplace1[t1b;t2b;t3b;t4b]) )
  ? AP_TERM_LIST "Palreplace1" [th4;th3;th2;th1];;

% Palreplace %
let RPalreplace [t';tvl;t] =
 (TRANS (ISPECL[t';tvl;t] Palreplace_DEF)
        (RPalreplace1 [t';"[]:((string#Type)#(string#Type))list";tvl;t] ) )
 ? REFL(list_mk_comb("Palreplace",[t';tvl;t]));;
let RRPalreplace [th1;th2;th3] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  TRANS (AP_TERM_LIST "Palreplace" [th3;th2;th1])
        (RPalreplace[t1b;t2b;t3b])
 ? AP_TERM_LIST "Palreplace" [th3;th2;th1];;

% Palpha %
let RPalpha [t';t] =
 (TRANS (ISPECL[t';t] Palpha_DEF)
        (RPalreplace [t';"[]:(Pterm#(string#Type))list";t] ) )
 ? REFL(list_mk_comb("Palpha",[t';t]));;
let RRPalpha [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Palpha" [th2;th1])
        (RPalpha[t1b;t2b])
 ? AP_TERM_LIST "Palpha" [th2;th1];;

% Psubst_triples %
let Psubst_triples_CONJS = CONJUNCTS Psubst_triples_DEF;;
letrec RPsubst_triples [t1] =
 (if t1 = "[]:(Pterm # (Pterm # (string # Type)))list" then
   hd Psubst_triples_CONJS
  else
   let ttv,ttvl = dest_cons t1 in
   (TRANS (SPECL[ttv;ttvl] (hd(tl Psubst_triples_CONJS)))
          (RRand [RRType_eq [RRPtype_of [Rfst [ttv]]
                            ;RRPtype_of [RRfst [Rsnd [ttv]]] ]
                 ;RRand [RRType_eq [RRPtype_of [Rfst [ttv]]
                                   ;RRsnd [RRsnd [Rsnd [ttv]]] ]
                        ;RPsubst_triples [ttvl] ] ] ) ) )
 ? REFL(mk_comb("Psubst_triples",t1));;
let RRPsubst_triples [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 TRANS (AP_TERM "Psubst_triples" th1)
       (RPsubst_triples[t1b])
 ? AP_TERM "Psubst_triples" th1;;

% list13 %
let list13_CONJS = CONJUNCTS list13_DEF;;
letrec Rlist13 [t1] =
 let ty = hd(snd(dest_type(type_of t1))) in
 let [ty1;ty2] = snd(dest_type ty) in
 let [ty2;ty3] = snd(dest_type ty2) in
 (if t1 = "[]:(^ty)list" then
   INST_TYPE[ty1,":*";ty2,":**";ty3,":***";] (hd list13_CONJS)
  else
   let xyz,xyzl = dest_cons t1 in
   (TRANS (ISPECL[xyz;xyzl] (hd(tl list13_CONJS)))
          (AP_TERM_LIST2 "CONS:(^ty1#^ty3)->(^ty1#^ty3)list->(^ty1#^ty3)list"
                         [AP_TERM_LIST2 "$,:^ty1->^ty3->(^ty1#^ty3)"
                                        [Rfst [xyz]
                                        ;RRsnd [Rsnd [xyz]] ] 
                         ;Rlist13 [xyzl] ] ) ) )
 ? REFL(mk_comb("list13:(^ty)list->(^ty1#^ty3)list",t1));;
let RRlist13 [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 let ty = hd(snd(dest_type(type_of t1b))) in
 let [ty1;ty2] = snd(dest_type ty) in
 let [ty2;ty3] = snd(dest_type ty2) in
 TRANS (AP_TERM "list13:(^ty)list->(^ty1#^ty3)list" th1)
       (Rlist13[t1b])
 ? AP_TERM "list13:(^ty)list->(^ty1#^ty3)list" th1;;

% Psubst %
let xty = ":Pterm#Pterm#string#Type->Pterm#string#Type";;
let RPsubst [Typl;Conl;t';ttvl;td;t] =
 (TRANS(ISPECL[Typl;Conl;t';ttvl;td;t] Psubst_DEF)
       (RRand[RPsubst_triples[ttvl]
         ;RRand[RPwell_typed[Typl;Conl;td]
           ;RRand[RRPlnotoccurs
                      [Rmap Rsndsnd
                         ["(SND o SND):Pterm#Pterm#string#Type->string#Type"
                         ;ttvl]
                      ;REFL t]
                   ;RRand[RRPalreplace
                            [REFL t;Rmap Rsnd["SND:^xty";ttvl];REFL td]
                         ;RRPalreplace[REFL t';Rlist13[ttvl];REFL td] ]]] ]) )
 ? REFL(list_mk_comb("Psubst",[Typl;Conl;t';ttvl;td;t]));;
let RRPsubst [th1;th2;th3;th4;th5;th6] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  let t5a,t5b = dest_eq(concl th5) in
  let t6a,t6b = dest_eq(concl th6) in
  TRANS (AP_TERM_LIST "Psubst" [th6;th5;th4;th3;th2;th1])
        (RPsubst[t1b;t2b;t3b;t4b;t5b;t6b])
 ? AP_TERM_LIST "Psubst" [th6;th5;th4;th3;th2;th1];;

let RPbeta [t';x;t1;t2] =
 (TRANS(SPECL[t';x;t1;t2] Pbeta_DEF)
   (RPalreplace[t';mk_cons(mk_pair(t2,x),"[]:(Pterm#string#Type)list");t1]) )
 ? REFL(list_mk_comb("Pbeta",[t';x;t1;t2]));;
let RRPbeta [th1;th2;th3;th4] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "Pbeta" [th4;th3;th2;th1])
        (RPbeta[t1b;t2b;t3b;t4b])
 ? AP_TERM_LIST "Pbeta" [th4;th3;th2;th1];;

% --- rules for some properties defined over Type --- %

% Type_occurs %
let Type_occurs_CONJS = CONJUNCTS Type_occurs_DEF;;
letrec RType_occurs [s';t2] =
 (let op2,argl2 = strip_comb t2 in
  if op2 = "Tyvar" then 
   let s = hd argl2 in
   TRANS (SPECL [s';s] (hd Type_occurs_CONJS))
         (Rstring_eq [s;s'])
  else % op2 = "Tyop" %
   let [s;ts] = argl2 in
   TRANS (SPECL [s';s;ts] (el 2 Type_occurs_CONJS))
         (RRlor [Rmap (\[ts].RType_occurs[s';ts])
                      [mk_comb("Type_occurs",s');ts]]) )
  ? REFL(list_mk_comb("Type_occurs",[s';t2]));;
let RRType_occurs [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Type_occurs" [th2;th1])
        (RType_occurs[t1b;t2b]) )
  ? AP_TERM_LIST "Type_occurs" [th2;th1];;

% Pty_occurs %
let Pty_occurs_CONJS = CONJUNCTS Pty_occurs_DEF;;
letrec RPty_occurs [a;tm] =
 (let op,argl= strip_comb tm in
  if op = "Const" then 
   let [s;ty] = argl in 
   TRANS (SPECL [a;s;ty] (hd Pty_occurs_CONJS))
         (RType_occurs[a;ty])
  else if op = "Var" then
   let [x] = argl in
   TRANS(SPECL[a;x] (el 2 Pty_occurs_CONJS))
        (RRType_occurs[REFL a;Rsnd[x]])
  else if op = "App" then
   let [t1;t2] = argl in
   TRANS(SPECL[a;t1;t2] (el 3 Pty_occurs_CONJS))
     (RRor[RPty_occurs[a;t1]
          ;RPty_occurs[a;t2] ]) 
  else % op = "Lam" %
   let [x;t1] = argl in
   TRANS(SPECL[a;x;t1] (el 4 Pty_occurs_CONJS))
     (RRor[RRType_occurs[REFL a;Rsnd[x]]
          ;RPty_occurs[a;t1] ]) )
  ? REFL(list_mk_comb("Pty_occurs",[a;tm]));;
let RRPty_occurs [th1;th2;th3] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Pty_occurs" [th2;th1])
        (RPty_occurs[t1b;t2b])
 ? AP_TERM_LIST "Pty_occurs" [th2;th1];;

% Pty_snotoccurs %
let Pty_snotoccurs_CONJS = CONJUNCTS Pty_snotoccurs_DEF;;
letrec RPty_snotoccurs [a;t2] =
 (if t2 = "{}:(Pterm)set" then
   SPEC a (hd Pty_snotoccurs_CONJS)
  else
   let _,[h;t] = strip_comb t2 in
   TRANS (ISPECL[a;h;t] (hd(tl Pty_snotoccurs_CONJS)))
         (RRand [RRnot [RPty_occurs [a;h]]
                ;RPty_snotoccurs [a;t] ] ) )
 ? REFL(list_mk_comb("Pty_snotoccurs",[a;t2]));;
let RRPty_snotoccurs [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = type_of t1b in
 TRANS (AP_TERM_LIST "Pty_snotoccurs" [th2;th1])
       (RPty_snotoccurs[t1b;t2b])
 ? AP_TERM_LIST "Pty_snotoccurs" [th2;th1];;

% Plty_snotoccurs %
let Plty_snotoccurs_CONJS = CONJUNCTS Plty_snotoccurs_DEF;;
letrec RPlty_snotoccurs [t1;tml] =
 (if t1 = "[]:(string)list" then
   SPEC tml (hd Plty_snotoccurs_CONJS)
  else
   let h,t = dest_cons t1 in
   TRANS (ISPECL[h;t;tml] (hd(tl Plty_snotoccurs_CONJS)))
         (RRand [RPty_snotoccurs [h;tml]
                ;RPlty_snotoccurs [t;tml] ] ) )
 ? REFL(list_mk_comb("Plty_snotoccurs",[t1;tml]));;
let RRPlty_snotoccurs [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = type_of t1b in
 TRANS (AP_TERM_LIST "Plty_snotoccurs" [th2;th1])
       (RPlty_snotoccurs[t1b;t2b])
 ? AP_TERM_LIST "Plty_snotoccurs" [th2;th1];;

% Pnewfree1 %
let Pnewfree1_CONJS = CONJUNCTS Pnewfree1_DEF;;
let ty1 = ":(string#Type)#string#Type";;
letrec RPnewfree1 [t;bl;tm] =
 (let op,argl= strip_comb tm in
  if op = "Const" then 
   let [s;ty] = argl in SPECL [t;bl;s;ty] (hd Pnewfree1_CONJS)
  else if op = "Var" then
   let [x] = argl in
   TRANS(SPECL[t;bl;x] (el 2 Pnewfree1_CONJS))
    (RRcond[RRor[Rmem[x;bl]
                ;RRstring_eq[RRfst[RVar_var[t]];Rfst[x]] ]
           ;REFL "[]:(^ty1)list"
           ;AP_TERM_LIST2 "CONS:^ty1->(^ty1)list->(^ty1)list"
              [AP_TERM_LIST2 "$,:string#Type->string#Type->^ty1"
                 [RVar_var[t];REFL x]
              ;REFL "[]:(^ty1)list" ] ])
  else if op = "App" then
   let [t1;t2] = argl in
   let thm1,thm2 = RApp_fun[t],RApp_arg[t] in
   TRANS(SUBS[thm1;thm2](SPECL[t;bl;t1;t2] (el 3 Pnewfree1_CONJS)))
     (RRappend[RPnewfree1[rhs(concl thm1);bl;t1]
              ;RPnewfree1[rhs(concl thm2);bl;t2] ]) 
  else % op = "Lam" %
   let [x;t1] = argl in
   let thm1 = RLam_bod[t] in
   TRANS(SUBS[thm1](SPECL[t;bl;x;t1] (el 4 Pnewfree1_CONJS)))
     (RPnewfree1[rhs(concl thm1);"CONS ^x ^bl";t1]) )
  ? REFL(list_mk_comb("Pnewfree1",[t;bl;tm]));;
let RRPnewfree1 [th1;th2;th3] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  TRANS (AP_TERM_LIST "Pnewfree1" [th3;th2;th1])
        (RPnewfree1[t1b;t2b;t3b])
 ? AP_TERM_LIST "Pnewfree1" [th3;th2;th1];;

% Pnewfree %
let RPnewfree [t';t] =
 (TRANS (ISPECL[t';t] Pnewfree_DEF)
        (RPnewfree1[t';"[]:(string#Type)list";t] ) )
 ? REFL(list_mk_comb("Pnewfree",[t';t]));;
let RRPnewfree [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "Pnewfree" [th2;th1])
        (RPnewfree[t1b;t2b])
 ? AP_TERM_LIST "Pnewfree" [th2;th1];;

% Ptyinst1 %
let Ptyinst1_CONJS = CONJUNCTS Ptyinst1_DEF;;
let ty1 = ":(string#Type)#string#Type";;
letrec RPtyinst1 [t;bvl;fvl;tyl;tm] =
 (let op,argl= strip_comb tm in
  if op = "Const" then
   let [s;ty] = argl in
   TRANS(SPECL [t;bvl;fvl;tyl;s;ty] (hd Ptyinst1_CONJS))
    (RRPterm_eq[REFL t
               ;AP_TERM_LIST2 "Const" [REFL s;RType_replace[tyl;ty]] ])
  else if op = "Var" then
   let [x] = argl in
   TRANS(SPECL[t;bvl;fvl;tyl;x] (el 2 Ptyinst1_CONJS))
    (RRcond[RRmem1[RVar_var[t];REFL bvl]
      ;RRand[RIs_Var[t]
        ;RRand[RRprod_eq[REFL x;RRcorr1[RVar_var[t];REFL bvl]]
          ;RRType_eq[RRsnd[RVar_var[t]];RRType_replace[REFL tyl;Rsnd[x]]] ] ]
      ;RRcond[Rmem2[x;fvl]
        ;RRPterm_eq[REFL t
                   ;AP_TERM "Var"
                     (AP_TERM_LIST2 "$,:string->Type->string#Type"
                        [RRfst[Rcorr2[x;fvl]]
                        ;RRType_replace[REFL tyl;Rsnd[x]] ] ) ]
        ;RRPterm_eq[REFL t
                   ;AP_TERM "Var"
                     (AP_TERM_LIST2 "$,:string->Type->string#Type"
                        [Rfst[x]
                        ;RRType_replace[REFL tyl;Rsnd[x]] ] ) ] ] ])
  else if op = "App" then
   let [t1;t2] = argl in
   let thm1,thm2 = RApp_fun[t],RApp_arg[t] in
   TRANS(SUBS[thm1;thm2](SPECL[t;bvl;fvl;tyl;t1;t2] (el 3 Ptyinst1_CONJS)))
    (RRand[RIs_App[t]
          ;RRand[RPtyinst1[rhs(concl thm1);bvl;fvl;tyl;t1]
                ;RPtyinst1[rhs(concl thm2);bvl;fvl;tyl;t2] ] ])
  else % op = "Lam" %
   let [x;t1] = argl in
   let thm1 = RLam_bod[t] in
   let thm2 = AP_TERM_LIST2 "CONS:^ty1->(^ty1)list->(^ty1)list"
                [AP_TERM_LIST2 "$,:string#Type->string#Type->^ty1"
                   [RLam_var[t];REFL x]
                ;REFL bvl ] in
   TRANS(SUBS[thm1;thm2](SPECL[t;bvl;fvl;tyl;x;t1] (el 4 Ptyinst1_CONJS)))
    (RRand[RIs_Lam[t] 
       ;RRand[RRnot[RRmem1[RLam_var[t];REFL fvl]]
          ;RRand[RRType_eq[RRsnd[RLam_var[t]]
                          ;RRType_replace[REFL tyl;Rsnd[x]] ]
             ;RPtyinst1[rhs(concl thm1);rhs(concl thm2);fvl;tyl;t1] ] ] ]) )
  ? REFL(list_mk_comb("Ptyinst1",[t;bvl;fvl;tyl;tm]));;
let RRPtyinst1 [th1;th2;th3;th4;th5] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  let t5a,t5b = dest_eq(concl th5) in
  TRANS (AP_TERM_LIST "Ptyinst1" [th5;th4;th3;th2;th1])
        (RPtyinst1[t1b;t2b;t3b;t4b;t5b])
 ? AP_TERM_LIST "Ptyinst1" [th5;th4;th3;th2;th1];;


% Ptyinst %
let RPtyinst [as;t';tyl;t] =
 (TRANS (ISPECL[as;t';tyl;t] Ptyinst_DEF)
    (RRand[RRPtyinst1[REFL t';REFL "[]:((string#Type)#string#Type)list"
                     ;RPnewfree[t';t];REFL tyl;REFL t]
          ;RRPlallnotfree
             [RRmap Rsnd [REFL "SND:(string#Type)#string#Type->string#Type"
                         ;RPnewfree[t';t] ]
             ;REFL as ] ]) )
 ? REFL(list_mk_comb("Ptyinst",[as;t';tyl;t]));;
let RRPtyinst [th1;th2;th3;th4] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "Ptyinst" [th4;th3;th2;th1])
        (RPtyinst[t1b;t2b;t3b;t4b])
 ? AP_TERM_LIST "Ptyinst" [th4;th3;th2;th1];;



% ---------------------------------------------------- %


% --- conversions for proof destructors --- %


% equality for Psequent %
letrec RPsequent_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else
    let _,[s1;P1] = strip_comb t1 in
    let _,[s2;P2] = strip_comb t2 in
    TRANS(SPECL[s1;P1;s2;P2] Pseq_11)
         (RRand[Rset_eq[s1;s2];RPterm_eq[P1;P2]]) )
  ? REFL(mk_eq(t1,t2)) ;;
let RRPsequent_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM (mk_comb("$=:Psequent->Psequent->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:Psequent->Psequent->bool" th1) t2b)
              (RPsequent_eq[t1b;t2b]) )
  ? AP_TERM_LIST  "$=:Psequent->Psequent->bool" [th2;th1] ;;
Reqs := (":Psequent",RPsequent_eq).Reqs;;
RReqs := (":Psequent",RRPsequent_eq).RReqs;;

% Pseq_assum %
letrec RPseq_assum [t1] =
 (let op,argl = strip_comb t1 in
  SPECL argl Pseq_assum_DEF )
  ? REFL(mk_comb("Pseq_assum",t1)) ;;
let RRPseq_assum [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Pseq_assum" th1) (RPseq_assum [t1b]) )
  ? AP_TERM  "Pseq_assum" th1 ;;

% Pseq_concl %
letrec RPseq_concl [t1] =
 (let op,argl = strip_comb t1 in
  SPECL argl Pseq_concl_DEF )
  ? REFL(mk_comb("Pseq_concl",t1)) ;;
let RRPseq_concl [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Pseq_concl" th1) (RPseq_concl [t1b]) )
  ? AP_TERM  "Pseq_concl" th1 ;;


% --- rules for primitive inferences --- %

% PEQ %
let RPEQ[t1;t2] = 
 (TRANS(SPECL[t1;t2]PEQ_DEF)
       (AP_TERM_LIST2 "App"
          [AP_TERM_LIST2 "App"
             [AP_TERM "Const `=`"
                (AP_TERM "Tyop `fun`"
                   (AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
                      [RPtype_of[t1]
                      ;AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
                         [AP_TERM "Tyop `fun`"
                            (AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
                               [RPtype_of[t1]
                               ;REFL "[Tyop `bool`[]]" ] )
                         ;REFL "NIL:(Type)list" ] ] ) )
             ;REFL t1 ]
          ;REFL t2 ] ) )
 ? REFL(list_mk_comb("PEQ",[t1;t2]));;
let RRPEQ [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "PEQ" [th2;th1]) (RPEQ[t1b;t2b])
 ? AP_TERM_LIST2 "PEQ" [th2;th1];;

% PIMP %
let RPIMP[t1;t2] = SPECL[t1;t2]PIMP_DEF;;
let RRPIMP [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "PIMP" [th2;th1]) (RPIMP[t1b;t2b])
 ? AP_TERM_LIST2 "PIMP" [th2;th1];;

% Is_EQtm %
let RIs_EQtm[t] =
 (TRANS(SPEC t Is_EQtm_DEF)
    (RRand[RIs_App[t]
       ;RRand[RRIs_App[RApp_fun[t]]
          ;RRPterm_eq[RRApp_fun[RApp_fun[t]]
             ;AP_TERM "Const `=`"
                (AP_TERM "Tyop `fun`"
                   (AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
                      [RRPtype_of[RApp_arg[t]]
                      ;AP_TERM_LIST2 "CONS:Type->(Type)list->(Type)list"
                         [AP_TERM "Tyop `fun`"
                            (AP_TERM_LIST2"CONS:Type->(Type)list->(Type)list"
                               [RRPtype_of[RApp_arg[t]]
                               ;AP_TERM_LIST2"CONS:Type->(Type)list->(Type)list"
                                  [REFL"Tyop`bool`[]";REFL"NIL:(Type)list"] ] )
                         ;REFL"NIL:(Type)list"] ] ) ) ] ] ]) )
 ? REFL(mk_comb("Is_EQtm",t));;
let RRIs_EQtm [th1] =
  let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Is_EQtm" th1) (RIs_EQtm[t1b])
 ? AP_TERM "Is_EQtm" th1;;

% Pseq_boolean %
let RPseq_boolean [th] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[as;t] Pseq_boolean_DEF)
       (RRand[Rsevery RPboolean ["Pboolean";as]
             ;RPboolean[t] ] ) )
 ? REFL(mk_comb ("Pseq_boolean",th));;
let RRPseq_boolean [th1] =
 (let t1a,t1b = dest_eq(concl th1) in
  TRANS (AP_TERM "Pseq_boolean" th1)
        (RPseq_boolean [t1b]) )
  ? AP_TERM "Pseq_boolean" th1;;

% Pseq_well_typed %
let RPseq_well_typed [Typl;Conl;th] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[Typl;Conl;as;t] Pseq_well_typed_DEF)
       (RRand[Rsevery (\[tm].RPwell_typed[Typl;Conl;tm])
                      [list_mk_comb("Pwell_typed",[Typl;Conl]);as]
             ;RPwell_typed[Typl;Conl;t] ] ) )
 ? REFL(list_mk_comb ("Pseq_well_typed",[Typl;Conl;th]));;
let RRPseq_well_typed [th1;th2;th3] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  TRANS (AP_TERM_LIST "Pseq_well_typed" [th3;th2;th1])
        (RPseq_well_typed [t1b;t2b;t3b]) )
  ? AP_TERM_LIST "Pseq_well_typed" [th3;th2;th1];;

% PASSUME %
let RPASSUME [Typl;Conl;th;tm] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[Typl;Conl;as;t;tm] PASSUME_DEF)
       (RRand[RPwell_typed[Typl;Conl;tm]
             ;RRand[RPboolean[tm]
                   ;RRand[RPterm_eq[t;tm]
                         ;Rset_eq [as;"{^tm}"] ] ] ]) )
 ? REFL(list_mk_comb ("PASSUME",[Typl;Conl;th;tm]));;
let RRPASSUME [th1;th2;th3;th4] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "PASSUME" [th4;th3;th2;th1])
        (RPASSUME [t1b;t2b;t3b;t4b]) )
  ? AP_TERM_LIST "PASSUME" [th4;th3;th2;th1] ;;

% PREFL %
let RPREFL [Typl;Conl;th;tm] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[Typl;Conl;as;t;tm] PREFL_DEF)
       (RRand[RPwell_typed[Typl;Conl;tm]
         ;RRand[Rset_eq[as;mk_const(`EMPTY`,":(Pterm)set")]
           ;RRPterm_eq[REFL t
                      ;RPEQ[tm;tm] ] ] ]) )
 ? REFL(list_mk_comb ("PREFL",[Typl;Conl;th;tm]));;
let RRPREFL [th1;th2;th3;th4] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "PREFL" [th4;th3;th2;th1])
        (RPREFL [t1b;t2b;t3b;t4b]) )
  ? AP_TERM_LIST "PREFL" [th4;th3;th2;th1] ;;

% PBETA_CONV %
let RPBETA_CONV [Typl;Conl;th;tm] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[Typl;Conl;as;t;tm] PBETA_CONV_DEF)
       (RRand[RPwell_typed[Typl;Conl;tm]
         ;RRand[Rset_eq[as;mk_const(`EMPTY`,":(Pterm)set")]
           ;RRand[RIs_App[tm]
             ;RRand[RRIs_Lam[RApp_fun[tm]]
               ;RRand[RRPterm_eq[REFL t;RRPEQ[REFL tm;RApp_arg[t]]]
                 ;RRPbeta[RApp_arg[t]
                         ;RRLam_var[RApp_fun[tm]]
                         ;RRLam_bod[RApp_fun[tm]]
                         ;RApp_arg[tm] ] ] ] ] ] ]) )
 ? REFL(list_mk_comb ("PBETA_CONV",[Typl;Conl;th;tm]));;
let RRPBETA_CONV [th1;th2;th3;th4] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "PBETA_CONV" [th4;th3;th2;th1])
        (RPBETA_CONV [t1b;t2b;t3b;t4b]) )
  ? AP_TERM_LIST "PBETA_CONV" [th4;th3;th2;th1] ;;


% PSUBST %
let Psubst_newlist_CONJS = CONJUNCTS Psubst_newlist_DEF;;
let ty1 = ":Pterm # (Pterm # (string # Type))
          -> (Pterm # (Pterm # (string # Type)))list
          -> (Pterm # (Pterm # (string # Type)))list";;
let ty2 = ":Pterm -> (Pterm # (string # Type))
          -> Pterm # (Pterm # (string # Type))";;
let ty3 = ":Pterm -> (string # Type)
          -> Pterm # (string # Type)";;
letrec RPsubst_newlist [tdl] =
 (if is_cons tdl then
   let h,t = dest_cons tdl in
   TRANS (ISPECL[h;t] (hd(tl Psubst_newlist_CONJS)))
    (AP_TERM_LIST2 "CONS:^ty1"
       [AP_TERM_LIST2 "$,:^ty2"
          [RRApp_arg[RRPseq_concl[Rfst[h]]]
          ;AP_TERM_LIST2 "$,:^ty3"
             [RRApp_arg[RRApp_fun[RRPseq_concl[Rfst[h]]]]
             ;Rsnd[h] ] ]
       ;RPsubst_newlist[t] ] )
  else (hd Psubst_newlist_CONJS) )
 ? REFL(list_mk_comb("Psubst_newlist",[tdl]));;
let RRPsubst_newlist [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 TRANS (AP_TERM "Psubst_newlist" th1)
       (RPsubst_newlist[t1b])
 ? AP_TERM "Psubst_newlist" th1;;
let ty = ":Psequent # (string # Type) -> Psequent";;
let RPSUBST[Typl;Conl;th';thdl;td;th] =
 (let [as;t] = snd(strip_comb th') in
  TRANS(SPECL[Typl;Conl;as;t;thdl;td;th] PSUBST_DEF)
    (RRand[RPwell_typed[Typl;Conl;td]
       ;RRand[RRevery RIs_EQtm
                [REFL "Is_EQtm"
                ;RRmap RPseq_concl
                   [REFL "Pseq_concl"
                   ;Rmap Rfst ["FST:^ty";thdl] ] ]
           ;RRand[RRPsubst[REFL Typl;REFL Conl;REFL t
                          ;RPsubst_newlist[thdl];REFL td;RPseq_concl[th] ]
              ;RRset_eq
                 [REFL as
                 ;RRunion[RPseq_assum[th]
                         ;RRlunion[RRmap RPseq_assum
                                     [REFL "Pseq_assum"
                                     ;Rmap Rfst ["FST:^ty";thdl] ]]]]]]]) )
 ? REFL(list_mk_comb ("PSUBST",[Typl;Conl;th';thdl;td;th]));;
let RRPSUBST [th1;th2;th3;th4;th5;th6] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  let t5a,t5b = dest_eq(concl th3) in
  let t6a,t6b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "PSUBST" [th6;th5;th4;th3;th2;th1])
        (RPSUBST [t1b;t2b;t3b;t4b;t5b;t6b]) )
  ? AP_TERM_LIST  "PSUBST" [th6;th5;th4;th3;th2;th1] ;;

% PABS %
let RPABS[Typl;Conl;th';tm;th] =
 (let [as;t] = snd(strip_comb th') in
  TRANS(SPECL[Typl;Conl;as;t;tm;th] PABS_DEF)
    (RRand[RPwell_typed[Typl;Conl;tm]
       ;RRand[RRIs_EQtm[RPseq_concl[th]]
          ;RRand[RIs_Var[tm]
             ;RRand[RRType_OK[REFL Typl;RRsnd[RVar_var[tm]]]
                ;RRand[RRPterm_eq[REFL t
                         ;RRPEQ[AP_TERM_LIST2 "Lam"
                                   [RVar_var[tm]
                                   ;RRApp_arg[RRApp_fun[RPseq_concl[th]]] ]
                               ;AP_TERM_LIST2 "Lam"
                                   [RVar_var[tm]
                                   ;RRApp_arg[RPseq_concl[th]] ] ] ]
                   ;RRand[RRset_eq[REFL as;RPseq_assum[th]]
                      ;RRPallnotfree[RVar_var[tm];REFL as] ] ] ] ] ] ]) )
 ? REFL(list_mk_comb ("PABS",[Typl;Conl;th';tm;th]));;
let RRPABS [th1;th2;th3;th4;th5;th6] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  let t5a,t5b = dest_eq(concl th5) in
  let t6a,t6b = dest_eq(concl th6) in
  TRANS (AP_TERM_LIST "PABS" [th6;th5;th4;th3;th2;th1])
        (RPABS [t1b;t2b;t3b;t4b;t5b;t6b]) )
  ? AP_TERM_LIST  "PABS" [th6;th5;th4;th3;th2;th1] ;;

% PINST_TYPE %
let RPINST_TYPE [Typl;th;tyl;th1] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[Typl;as;t;tyl;th1] PINST_TYPE_DEF)
       (RRand[RRevery (\[ty].RType_OK[Typl;ty])
                [REFL (mk_comb("Type_OK",Typl))
                ;Rmap Rfst ["FST:Type#string->Type";tyl] ]
         ;RRand[RRPtyinst[REFL as;REFL t;REFL tyl;RPseq_concl[th1]]
           ;RRand[RRPlty_snotoccurs[Rmap Rsnd ["SND:Type#string->string";tyl]
                                   ;REFL as]
             ;RRset_eq[REFL as;RPseq_assum[th1]] ] ] ]) )
 ? REFL(list_mk_comb ("PINST_TYPE",[Typl;th;tyl;th1]));;
let RRPINST_TYPE [th1;th2;th3;th4] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "PINST_TYPE" [th4;th3;th2;th1])
        (RPINST_TYPE [t1b;t2b;t3b;t4b]) )
  ? AP_TERM_LIST "PINST_TYPE" [th4;th3;th2;th1] ;;

% PDISCH %
let RPDISCH [Typl;Conl;th;tm;th1] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[Typl;Conl;as;t;tm;th1] PDISCH_DEF)
   (RRand[RPwell_typed[Typl;Conl;tm]
     ;RRand[RPboolean[tm]
       ;RRand[RRPterm_eq[REFL t;RRPIMP[REFL tm;RPseq_concl[th1]]]
         ;RRset_eq[REFL as;RRdelete[RPseq_assum[th1];REFL tm]] ] ] ]) )
 ? REFL(list_mk_comb ("PDISCH",[Typl;Conl;th;tm;th1]));;
let RRPDISCH [th1;th2;th3;th4;th5] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  let t5a,t5b = dest_eq(concl th5) in
  TRANS (AP_TERM_LIST "PDISCH" [th5;th4;th3;th2;th1])
        (RPDISCH [t1b;t2b;t3b;t4b;t5b]) )
  ? AP_TERM_LIST "PDISCH" [th5;th4;th3;th2;th1] ;;

% PMP %
let RPMP [th;th1;th2] =
 (let [as;t] = snd(strip_comb th) in
  TRANS(SPECL[as;t;th1;th2] PMP_DEF)
   (RRand[RRPterm_eq[RPseq_concl[th1]
                    ;RRPIMP[RPseq_concl[th2];REFL t] ]
         ;RRset_eq[REFL as;RRunion[RPseq_assum[th1];RPseq_assum[th2]]] ]) )
 ? REFL(list_mk_comb ("PMP",[th;th1;th2]));;
let RRPMP [th1;th2;th3] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  TRANS (AP_TERM_LIST "PMP" [th3;th2;th1])
        (RPMP [t1b;t2b;t3b]) )
  ? AP_TERM_LIST "PMP" [th3;th2;th1] ;;


% Inf_concl %
let Inf_concl_CONJS = CONJUNCTS Inf_concl_DEF;;
let RInf_concl[i] =
 (let op,argl = strip_comb i in
  if op = "AX_inf" then
    let [s] = argl in
    SPEC s (hd Inf_concl_CONJS)
  else if op = "AS_inf" then
    let [s;t] = argl in
    SPECL[s;t] (el 2 Inf_concl_CONJS)
  else if op = "RE_inf" then
    let [s;t] = argl in
    SPECL[s;t] (el 3 Inf_concl_CONJS)
  else if op = "BE_inf" then
    let [s;t] = argl in
    SPECL[s;t] (el 4 Inf_concl_CONJS)
  else if op = "SU_inf" then
    let [s;tdl;t;s1] = argl in
    SPECL[s;tdl;t;s1] (el 5 Inf_concl_CONJS)
  else if op = "AB_inf" then
    let [s;t;s1] = argl in
    SPECL[s;t;s1] (el 6 Inf_concl_CONJS)
  else if op = "IN_inf" then
    let [s;tyl;s1] = argl in
    SPECL[s;tyl;s1] (el 7 Inf_concl_CONJS)
  else if op = "DI_inf" then
    let [s;t;s1] = argl in
    SPECL[s;t;s1] (el 8 Inf_concl_CONJS)
  else if op = "MP_inf" then
    let [s;s1;s2] = argl in
    SPECL[s;s1;s2] (el 9 Inf_concl_CONJS)
  else failwith `RInf_concl` )
 ? failwith `RInf_concl`;;

% Inf_hyps %
let Inf_hyps_CONJS = CONJUNCTS Inf_hyps_DEF;;
let RInf_hyps[i] =
 (let op,argl = strip_comb i in
  if op = "AX_inf" then
    let [s] = argl in
    SPEC s (hd Inf_hyps_CONJS)
  else if op = "AS_inf" then
    let [s;t] = argl in
    SPECL[s;t] (el 2 Inf_hyps_CONJS)
  else if op = "RE_inf" then
    let [s;t] = argl in
    SPECL[s;t] (el 3 Inf_hyps_CONJS)
  else if op = "BE_inf" then
    let [s;t] = argl in
    SPECL[s;t] (el 4 Inf_hyps_CONJS)
  else if op = "SU_inf" then
    let [s;sdl;t;s1] = argl in
    TRANS(SPECL[s;sdl;t;s1] (el 5 Inf_hyps_CONJS))
         (AP_TERM_LIST2 "CONS:Psequent->(Psequent)list->(Psequent)list"
            [REFL s1
            ;Rmap Rfst ["FST:Psequent#string#Type->Psequent";sdl] ] )
  else if op = "AB_inf" then
    let [s;t;s1] = argl in
    SPECL[s;t;s1] (el 6 Inf_hyps_CONJS)
  else if op = "IN_inf" then
    let [s;tyl;s1] = argl in
    SPECL[s;tyl;s1] (el 7 Inf_hyps_CONJS)
  else if op = "DI_inf" then
    let [s;t;s1] = argl in
    SPECL[s;t;s1] (el 8 Inf_hyps_CONJS)
  else if op = "MP_inf" then
    let [s;s1;s2] = argl in
    SPECL[s;s1;s2] (el 9 Inf_hyps_CONJS)
  else failwith `RInf_hyps` )
 ? failwith `RInf_hyps`;;

% OK_Inf %
let OK_Inf_CONJS = CONJUNCTS OK_Inf_DEF;;
let ROK_Inf [Typl;Conl;Axil;i] =
 (let op,argl = strip_comb i in
  if op = "AX_inf" then
    let [s] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s] (hd OK_Inf_CONJS))
         (Rmem[s;Axil])
  else if op = "AS_inf" then
    let [s;t] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;t] (el 2 OK_Inf_CONJS))
         (RPASSUME[Typl;Conl;s;t])
  else if op = "RE_inf" then
    let [s;t] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;t] (el 3 OK_Inf_CONJS))
         (RPREFL[Typl;Conl;s;t])
  else if op = "BE_inf" then
    let [s;t] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;t] (el 4 OK_Inf_CONJS))
         (RPBETA_CONV[Typl;Conl;s;t])
  else if op = "SU_inf" then
    let [s;tdl;t;s1] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;tdl;t;s1] (el 5 OK_Inf_CONJS))
         (RPSUBST[Typl;Conl;s;tdl;t;s1])
  else if op = "AB_inf" then
    let [s;t;s1] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;t;s1] (el 6 OK_Inf_CONJS))
         (RPABS[Typl;Conl;s;t;s1])
  else if op = "IN_inf" then
    let [s;tyl;s1] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;tyl;s1] (el 7 OK_Inf_CONJS))
         (RPINST_TYPE[Typl;s;tyl;s1])
  else if op = "DI_inf" then
    let [s;t;s1] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;t;s1] (el 8 OK_Inf_CONJS))
         (RPDISCH[Typl;Conl;s;t;s1])
  else if op = "MP_inf" then
    let [s;s1;s2] = argl in
    TRANS(SPECL[Typl;Conl;Axil;s;s1;s2] (el 9 OK_Inf_CONJS))
         (RPMP[s;s1;s2])
  else failwith `ROK_Inf` )
 ? failwith `ROK_Inf`;;
let RROK_Inf[th1;th2;th3;th4] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let t4a,t4b = dest_eq(concl th4) in
  TRANS (AP_TERM_LIST "OK_Inf" [th4;th3;th2;th1])
        (ROK_Inf[t1b;t2b;t3b;t4b]) )
  ? AP_TERM_LIST "OK_Inf" [th4;th3;th2;th1];;

% Is_proof %
let Is_proof_CONJS = CONJUNCTS Is_proof_DEF;;
letrec RIs_proof [Typl;Conl;Axil;t1] =
 (if is_cons t1 then
  let i,P = dest_cons t1 in
  TRANS(SPECL[Typl;Conl;Axil;i;P] (el 2 Is_proof_CONJS))
    (RRand[ROK_Inf[Typl;Conl;Axil;i]
       ;RRand[RRlmem[RInf_hyps[i];
                    Rmap RInf_concl["Inf_concl";P]]
          ;RIs_proof[Typl;Conl;Axil;P] ] ])
  else ISPECL [Typl;Conl;Axil] (hd Is_proof_CONJS) )
  ? failwith `RIs_proof`;;

