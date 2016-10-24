% File: RCbounded_convs.ml
   
  some infrastructure for proofs under bounded nondeterminism
%

% --- continuity provers --- %

letrec ucont_CONV t =
 let op,argl = strip_comb t in
 let ty = type_of op in
 let tyl = map type_of argl in
 if op = "skip:^ty" ? false then 
  INST_TYPE [hd(snd(dest_type(hd(snd(dest_type ty))))),":*s"] ucont_skip
 else if op = "assert:^ty" ? false then 
  ISPEC (hd argl) (GEN_ALL ucont_assert)
 else if op = "assign:^ty" ? false then 
  ISPEC (hd argl) (GEN_ALL ucont_assign)
 else if op = "dch:^ty" ? false then 
  let [c1;c2] = argl in
  MP (ISPECL[c1;c2] (GEN_ALL ucont_dch)) (CONJ (ucont_CONV c1) (ucont_CONV c2))
 else if op = "seq:^ty" ? false then 
  let [c1;c2] = argl in
  MP (ISPECL[c1;c2] (GEN_ALL ucont_seq)) (CONJ (ucont_CONV c1) (ucont_CONV c2))
 else if op = "cond:^ty" ? false then 
  let [g;c1;c2] = argl in
  MP (ISPECL[g;c1;c2] (GEN_ALL ucont_cond)) (CONJ (ucont_CONV c1) (ucont_CONV c2))
 else if op = "do:^ty" ? false then 
  let [g;c] = argl in
  MP (ISPECL [g;c] (GEN_ALL ucont_do)) (ucont_CONV c)
 else failwith `ucont_CONV`;;
let ucont_TAC:tactic (asl,w) = 
  [],\[].ucont_CONV (snd(dest_comb w)) ? failwith `ucont_TAC`;;
