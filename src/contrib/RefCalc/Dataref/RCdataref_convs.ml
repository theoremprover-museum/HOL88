% File: RCdataref_convs.ml
   
  some infrastructure for doing data refinement proofs
%


% --- monotonicity prover --- %

letrec mono_CONV t =
 let op,argl = strip_comb t in
 let ty = type_of op in
 let tyl = map type_of argl in
 if op = "skip:^ty" ? false then 
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
 else if op = "abst:^ty" ? false then 
  ISPEC (hd argl) mono_abst
 else if op = "repr:^ty" ? false then 
  ISPEC (hd argl) mono_repr
 else failwith `mono_CONV` ;;
let mono_TAC:tactic (asl,w) = 
  [],\[].mono_CONV (snd(dest_comb w)) ? failwith `mono_TAC`;;


