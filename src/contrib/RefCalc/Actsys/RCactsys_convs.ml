% File: RCactsys_convs.ml
   
  some infrastructure for doing action system proofs
%

% --- preliminary conversion for lists --- %
letrec MAPSND_CONV l =
  let ty = hd(snd(dest_type(type_of l))) in
  let [ty1;ty2] = snd(dest_type ty) in
  if is_cons l then
    let h,t = dest_cons l in
    let g,c = dest_pair h in
    let thm1 = ISPECL[g;c] SND in
    let thm2 = ISPECL[mk_const(`SND`,mk_type(`fun`,[ty;ty2]));h;t] (C2 MAP) in
    let thm3 = MAPSND_CONV t in
    SUBS[thm1;thm3] thm2
  else ISPEC (mk_const(`SND`,mk_type(`fun`,[ty;ty2]))) (C1 MAP);;
  

% --- monotonicity provers --- %

letrec EVERY_mono_CONV l =
  let ty = hd(snd(dest_type(type_of l))) in
  if is_cons l then
    let h,t = dest_cons l in
    EQ_MP (SYM(ISPECL[mk_const(`monotonic`,mk_type(`fun`,[ty;":bool"]));h;t]
                     (C2 EVERY_DEF)))
          (CONJ (mono_CONV h) (EVERY_mono_CONV t))
  else EQT_ELIM (ISPEC (mk_const(`monotonic`,mk_type(`fun`,[ty;":bool"]))) 
                (C1 EVERY_DEF));;
let EVERY_mono_TAC:tactic (asl,w) = 
  [],\[].EVERY_mono_CONV (rand w) ? failwith `EVERY_mono_TAC`;;

let EVERY_MAPSND_mono_CONV l =
  let thm1 = MAPSND_CONV l in
  let thm2 = EVERY_mono_CONV(rhs(concl thm1)) in
  SUBS[SYM thm1] thm2;;
let EVERY_MAPSND_mono_TAC (asl,w) =
  [],\[].EVERY_MAPSND_mono_CONV(rand(rand w));;

% --- conjunctivity prover --- %

letrec conj_CONV t =
 let op,argl = strip_comb t in
 let ty = type_of op in
 let tyl = map type_of argl in
 if op = "skip:^ty" ? false then 
  INST_TYPE [hd(snd(dest_type(hd(snd(dest_type ty))))),":*s"] conj_skip
 else if op = "assign:^ty" ? false then 
  ISPEC (hd argl) conj_assign
 if op = "nondass:^ty" ? false then 
  ISPEC (hd argl) conj_nondass
 else if op = "seq:^ty" ? false then 
  let [c1;c2] = argl in
  MP (ISPECL[c1;c2]conj_seq)
     (CONJ (conj_CONV c1) (conj_CONV c2))
 else if op = "cond:^ty" ? false then 
  let [g;c1;c2] = argl in
  MP (ISPECL[g;c1;c2] conj_cond) (CONJ (conj_CONV c1) (conj_CONV c2))
 else if op = "do:^ty" ? false then 
  let [g;c] = argl in
  MP (ISPECL [g;c] conj_do) (conj_CONV c)
 else if op = "block:^ty" ? false then 
  let [p;c] = argl in
  MP (ISPECL [p;c] conj_block) (conj_CONV c)
 else failwith `conj_CONV` ;;
let conj_TAC:tactic (asl,w) = 
  [],\[].conj_CONV (rand w) ? failwith `conj_TAC`;;


% --- strictness prover --- %

letrec strict_CONV t =
 let op,argl = strip_comb t in
 let ty = type_of op in
 let tyl = map type_of argl in
 if op = "skip:^ty" ? false then 
  INST_TYPE [hd(snd(dest_type(hd(snd(dest_type ty))))),":*s"] strict_skip
 else if op = "assign:^ty" ? false then 
  ISPEC (hd argl) strict_assign
 if op = "nondass:^ty" ? false then 
  UNDISCH(ISPEC (hd argl) (GEN_ALL(snd(EQ_IMP_RULE strict_nondass))))
 else if op = "seq:^ty" ? false then 
  let [c1;c2] = argl in
  MP (ISPECL[c1;c2] strict_seq) (CONJ (strict_CONV c1) (strict_CONV c2))
 else if op = "cond:^ty" ? false then 
  let [g;c1;c2] = argl in
  MP (ISPECL[g;c1;c2] strict_cond) (CONJ (strict_CONV c1) (strict_CONV c2))
 else if op = "do:^ty" ? false then 
  let [g;c] = argl in
  MP (ISPECL [g;c] strict_do) (CONJ (mono_CONV c) (strict_CONV c))
 else if op = "block:^ty" ? false then 
  let [p;c] = argl in
  MP (UNDISCH(ISPECL [p;c] strict_block)) (strict_CONV c)
 else failwith `strict_CONV` ;;
let strict_TAC:tactic (asl,w) = 
  (let thm = DISCH_ALL(strict_CONV(rand w)) in
   (MATCH_ACCEPT_TAC thm) ORELSE (MATCH_MP_TAC thm ? ALL_TAC))(asl,w)
  ? failwith `strict_TAC`;;

