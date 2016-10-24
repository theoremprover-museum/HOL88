% File: RCcommand_convs.ml
   
  some infrastructure for doing RC-proofs
%


% --- monotonicity prover --- %

letrec mono_CONV t =
 let op,argl = strip_comb t in
 let ty = type_of op in
 let tyl = map type_of argl in
 if op = "abort:^ty" ? false then
  let ty1 = hd(snd(dest_type(hd(snd(dest_type ty))))) in
  let ty2 = hd(snd(dest_type(hd(tl(snd(dest_type ty)))))) in
  INST_TYPE [ty1,":*s1";ty2,":*s2"] mono_abort
 else if op = "skip:^ty" ? false then 
  INST_TYPE [hd(snd(dest_type(hd(snd(dest_type ty))))),":*s"] mono_skip
 else if op = "assert:^ty" ? false then 
  ISPEC (hd argl) mono_assert
 else if op = "assign:^ty" ? false then 
  ISPEC (hd argl) mono_assign
 else if op = "nondass:^ty" ? false then 
  ISPEC (hd argl) mono_nondass
 else if op = "seq:^ty" ? false then 
  let [c1;c2] = argl in
  MP (ISPECL[c1;c2] mono_seq) (CONJ (mono_CONV c1) (mono_CONV c2))
 else if op = "cond:^ty" ? false then 
  let [g;c1;c2] = argl in
  MP (ISPECL[g;c1;c2] mono_cond) (CONJ (mono_CONV c1) (mono_CONV c2))
 else if op = "do:^ty" ? false then 
  let [g;c] = argl in
  MP (ISPECL [g;c] mono_do) (mono_CONV c)
 else if op = "block:^ty" ? false then 
  let [p;c] = argl in
  MP (ISPECL [p;c] mono_block) (mono_CONV c)
 else failwith `mono_CONV` ;;
let mono_TAC:tactic (asl,w) = 
  [],\[].mono_CONV (snd(dest_comb w)) ? failwith `mono_TAC`;;


% --- conjunctivity prover --- %

letrec conj_CONV t =
 let op,argl = strip_comb t in
 let ty = type_of op in
 let tyl = map type_of argl in
 if op = "abort:^ty" ? false then
  let ty1 = hd(snd(dest_type(hd(snd(dest_type ty))))) in
  let ty2 = hd(snd(dest_type(hd(tl(snd(dest_type ty)))))) in
  INST_TYPE [ty1,":*s1";ty2,":*s2"] conj_abort
 else if op = "skip:^ty" ? false then 
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
 if op = "abort:^ty" ? false then
  let ty1 = hd(snd(dest_type(hd(snd(dest_type ty))))) in
  let ty2 = hd(snd(dest_type(hd(tl(snd(dest_type ty)))))) in
  INST_TYPE [ty1,":*s1";ty2,":*s2"] strict_abort
 else if op = "skip:^ty" ? false then 
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

