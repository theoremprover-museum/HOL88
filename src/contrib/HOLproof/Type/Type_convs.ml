% Type_convs.ml

  theorem proving infrastructure for reasoning about Types
%


% --- Defining functions recursively over Type --- %

let mk_map(f,l) =
  let fty = type_of f in
  let dty = hd(tl(snd(dest_type fty))) in
  let mapty = mk_type(`fun`,[fty;mk_type(`fun`,[type_of l;mk_type(`list`,[dty])])]) in
  list_mk_comb(mk_const(`MAP`,mapty),[f;l]);;
letrec list_mk_funty(tyl,ty) =
    if tyl = [] then ty
    else let h.t = tyl in mk_type(`fun`,[h;list_mk_funty(t,ty)]);;
letrec mk_unmap(x,l) =
    if l = [] then x
    else let h.t = l in mk_unmap("UNMAP ^x ^h",t);;
letrec LIST_ABS l th =
    if l = [] then th
     else let h.t = l in ABS h (LIST_ABS t th);;
let UNMAP_CONV tm = 
  let u,[m0;a] = strip_comb tm in
  let m,[t0;b] = strip_comb m0 in
  let x.y.absl,t = strip_abs t0 in
  let thm = prove
      (mk_forall(b,mk_eq(tm,mk_map(list_mk_abs(x.absl,subst[a,y]t),b))),
       INDUCT_THEN list_INDUCT ASSUME_TAC THEN REWRITE_TAC[MAP;UNMAP_DEF]
       THEN REPEAT GEN_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[CONS_11]) in
  SPEC_ALL thm;;
letrec ADHOC_CONV tm = 
 (ETA_CONV tm 
  ? (let x,e = dest_abs tm in
     let thm1 = ABS x (ADHOC_CONV e) in
     TRANS thm1 (ETA_CONV (rhs(concl thm1))) ) )
 ? failwith `ADHOC_CONV`;;
let new_Type_rec_definition(thname,tm) =
 (let (l1,r1),(l2,r2) = (dest_eq # dest_eq)(dest_conj tm) in
  let nam1,(op1,v1) = (I # dest_comb)(dest_comb l1) in
  let ty = hd(tl(snd(dest_type(type_of nam1)))) in
  let fnam1,argl1 = strip_comb nam1 in
  let e1 = mk_abs(v1,list_mk_abs(argl1,r1)) in
  let nam2,(op2,[v2a;v2c]) = (I # strip_comb)(dest_comb l2) in
  let fnam2,argl2 = strip_comb nam2 in
  let v2b = genvar(mk_type(`list`,[list_mk_funty(map type_of argl2,type_of r2)])) in
  let ty1 = mk_type(`fun`,
       [type_of nam2;mk_type(`fun`,[type_of v2c;mk_type(`list`,[ty])])]) in
  let e2' = subst[mk_unmap(v2b,argl2),list_mk_comb(mk_const(`MAP`,ty1),[nam2;v2c])] r2 in
  let e2 = list_mk_abs([v2a;v2b;v2c],list_mk_abs(argl2,e2')) in
  let thm1 = BETA_RULE (ISPECL[e1;e2] Type_Axiom) in
  let thm2 = SELECT_RULE(CONJUNCT1(BETA_RULE 
               (PURE_ONCE_REWRITE_RULE[EXISTS_UNIQUE_DEF] thm1))) in
  let faux = fst(dest_comb(fst(dest_eq(snd(strip_forall(concl(CONJUNCT1 thm2))))))) in
  let vty = genvar(mk_type(`Type`,[])) in
  let defspec = new_definition(concat thname `_spec`,
    mk_eq(mk_comb(list_mk_comb(fnam1,argl1),vty),
          list_mk_comb(mk_comb(faux,vty),argl1))) in
  let vty1 = last(fst(strip_forall(concl defspec))) in
  let thm3 = ABS vty1 (LIST_ABS argl1 (SPEC_ALL defspec)) in
  let thm4 = SYM(CONV_RULE (RHS_CONV ADHOC_CONV) thm3) in
  let thm5 = BETA_RULE(PURE_ONCE_REWRITE_RULE[thm4] thm2) in
  let thm6 = BETA_RULE (CONV_RULE (REDEPTH_CONV FUN_EQ_CONV) thm5) in
  let thm7 = CONV_RULE (REDEPTH_CONV UNMAP_CONV) thm6 in
  let thm8 = CONV_RULE (DEPTH_CONV ETA_CONV) thm7 in
  let theorem = LIST_CONJ(map GEN_ALL (map SPEC_ALL (CONJUNCTS thm8))) in
  save_thm(thname,theorem) )
 ? failwith `new_Type_rec_definition`;;


% Example of a function definition
let fu_DEF = new_Type_rec_definition(`fu_DEF`,
  "(fu s' (Tyvar s) = (s'=s)) /\
   (fu s' (Tyop s ts) =  EVERY(\x.T) (MAP(fu s')ts))");;
%
