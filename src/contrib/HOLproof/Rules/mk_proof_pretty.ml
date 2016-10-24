% mk_proof_pretty

  functions for handling ugly terms
%

% mk_string turns ml string into HOL string %
let mk_string s = mk_const(concat `\`` (concat s `\``),":string");;
let dest_string t = implode(butlast(tl(explode(fst(dest_const t)))));;

% set destructors %
let is_set t = (fst(dest_type(type_of t)) = `set`) ? false;;
letrec dest_set1 t ty =
 if t = "{}:(^ty)set" then []
 else
  let _,[x;xs] = strip_comb t in
  x.dest_set1 xs ty;;
let dest_set t =
 (let ty = hd(snd(dest_type(type_of t))) in
  (dest_set1 t ty,ty) )
 ? failwith `dest_set`;;
letrec mk_set(l,ty) =
 (if l = [] then "{}:(^ty)set"
  else 
   let h.t = l in
   list_mk_comb("INSERT:^ty->(^ty)set->(^ty)set",[h;mk_set(t,ty)]) )
 ? failwith `mk_set`;;

% ty_trans - translate HOL-type into corresponding Type %
letrec ty_trans ty =
 (if is_vartype ty ? false then 
   mk_comb("Tyvar",mk_string (implode(tl(explode(dest_vartype ty)))))
  else let op,tyl = dest_type ty in
   list_mk_comb("Tyop",[mk_string op;mk_list(map ty_trans tyl,":Type")]) )
 ? failwith `ty_trans`;;

% ty_back - translate types back %
letrec ty_back ty =
 (let op,argl = strip_comb ty in
  if op = "Tyvar" then mk_vartype(concat `*` (dest_string(hd argl)))
  else % op = "Tyop" %
   let [ty0;tyl] = argl in
   mk_type(dest_string ty0,map ty_back (fst(dest_list tyl))) )
 ? failwith `ty_back`;;

% tm_trans - translate HOL-term into corresponding Pterm (basic cases) %
letrec tm_trans1 t =
 (if is_const t then
   let s,ty = dest_const t in 
   list_mk_comb("Const",[mk_string s;(ty_trans ty)])
  else if is_var t then 
   let x,ty = dest_var t in 
   mk_comb("Var",mk_pair(mk_string x,ty_trans ty))
  else if is_abs t then
   let xty,t1 = dest_abs t in
   let x,ty = dest_var xty in
   list_mk_comb("Lam",
     [mk_pair(mk_string x,ty_trans ty);tm_trans1 t1] )
  else if is_comb t then
   let t1,t2 = dest_comb t in
   list_mk_comb("App",
     [tm_trans1 t1;tm_trans1 t2])
  else fail )
 ? failwith `tm_trans1`;;
letrec tm_trans tm =
 (if is_pair tm then 
   list_mk_pair(map tm_trans (strip_pair tm))
  else if is_list tm then
   let lst = map tm_trans (fst(dest_list tm)) in
   mk_list(lst,type_of(hd lst))
  else if is_set tm then
   let lst = map tm_trans (fst(dest_set tm)) in
   mk_set(lst,type_of(hd lst))
  else if type_of tm = mk_type(`Type`,[]) then tm
  else if type_of tm = mk_type(`string`,[]) then tm
  else if type_of tm = mk_type(`num`,[]) then tm
  else tm_trans1 tm )
 ? failwith `tm_trans`;;

letrec tm_back1 t =
 (let op,argl = strip_comb t in
  if op = "Const" then 
   let [s;ty] = argl in
   mk_const(dest_string s,ty_back ty)
  else if op = "Var" then 
    let x,ty = dest_pair (hd argl) in
    mk_var(dest_string x,ty_back ty)
  else if op = "App" then
    let [t1;t2] = argl in
    mk_comb(tm_back1 t1,tm_back1 t2) 
  else if op = "Lam" then 
    let [x;t] = argl in
    mk_abs(tm_back1(mk_comb("Var",x)),tm_back1 t)
  else fail)
 ? failwith `tm_back1`;;


letref opback =
 ["Pwell_typed","\Typl:**.\Conl:***.Xwell_typed:*->bool"
 ;"Pfree","Xfree:(string#Type)->*->bool"
 ;"Pbound","Xbound:(string#Type)->*->bool"
 ;"Poccurs","Xoccurs:(string#Type)->*->bool"
 ;"Palreplace","Xalreplace:*->(**#string#Type)list->*->bool"
 ;"Palpha","Xalpha:*->*->bool"
 ;"Psubst","\Typl:**.\Conl:***.Xsubst:*->(*a#*a#string#Type)list->*->*->bool"
 ;"Pbeta","Xbeta:**->(string#Type)->**->*->bool"
 ;"Pseq","Xseq"
 ;"AX_inf","AX_Xinf"
 ;"AS_inf","AS_Xinf:Xsequent->*a->Xinference"
 ;"RE_inf","RE_Xinf:Xsequent->*b->Xinference"
 ;"BE_inf","BE_Xinf:Xsequent->*c->Xinference"
 ;"SU_inf","SU_Xinf"
 ;"AB_inf","AB_Xinf:Xsequent->*d->Xsequent->Xinference"
 ;"IN_inf","IN_Xinf"
 ;"DI_inf","DI_Xinf"
 ;"MP_inf","MP_Xinf"
 ;"Is_proof","\Typl:**.\Conl:***.\Axil:****. Is_Xproof:(Xinference)list->bool"
 ];;

% tm_back - translate Pterm into terms
  note: ":Pterm" in lists always translates into ":bool" %

let arg_inst_aux op arg =
 (let (tyop,tyl) = dest_type(type_of op) in
   if tyop = `fun` then
    let x = mk_var(`qwerty`,hd tyl) in
    snd(match x arg) 
   else [])
  ? failwith `arg_inst_aux`;;
letrec arg_inst op argl =
 (if argl = [] then []
  else 
   let arg.t = argl in
   let inst_pair = arg_inst_aux op arg in
   let inst_op = inst [] inst_pair op in
   inst_pair@(arg_inst (mk_comb(inst_op,arg)) t) )
 ? [];; 
letrec tm_back_aux ty =
  let op,argl = dest_type ty in
  if argl=[] then
   if op = `Pterm` then ":bool" 
   else if op = `Psequent` then ":Xsequent" 
   else if op = `Inference` then ":Xinference" 
   else ty
  else
   mk_type(op,map tm_back_aux argl);;
letrec tm_back tm =
 (if is_pair tm then
   let t1,t2 = dest_pair tm in
   mk_pair(tm_back t1,tm_back t2)
  else if is_list tm then
   let argl,ty = dest_list tm in
   mk_list(map tm_back argl,tm_back_aux ty)
  else if is_set tm then
   let argl,ty = dest_set tm in
   mk_set(map tm_back argl,tm_back_aux ty)
  else if is_eq tm then
   let t1,t2 = dest_eq tm in
   mk_eq(tm_back t1,tm_back t2)
  else if type_of tm = mk_type(`Pterm`,[]) then tm_back1 tm
  else if type_of tm = mk_type(`Type`,[]) then tm
  else if type_of tm = mk_type(`string`,[]) then tm
  else
   let op,argl = strip_comb tm in
   let op1 = (snd(assoc op opback) ? op) in
   let argl1 = map tm_back argl in
   let instl = arg_inst op1 argl1 in
   list_mk_comb((inst [] instl op1),argl1) )
 ? failwith `tm_back`;;

let th_back th = CONV_RULE (DEPTH_CONV(LHS_CONV BETA_CONV))
                   (mk_thm([],tm_back(concl th)));;

%
let new_print_term t = print_term(tm_back t);;
let new_print_thm th = print_thm(th_back th);;
top_print new_print_term;;
top_print new_print_thm;;

%


