% File: RCrecursion_convs.ml

  conversions for recursion handling
%

letrec regular_CONV1 x c =
 let [ty1;ty2] = snd(dest_type(type_of x)) in
 let ty1,ty2 = hd(snd(dest_type ty1)),hd(snd(dest_type ty2)) in
 if not (mem x (frees c)) then 
   let th1 = mono_CONV c in
   MP (ISPEC c (INST_TYPE[ty1,":*s3";ty2,":*s4"] regular_const)) th1
 else if c = x ? false then 
   INST_TYPE[ty1,":*s1";ty2,":*s2"] regular_id
 else
  let op,argl = strip_comb c in
  let ty = type_of op in
  if op = "seq:^ty" ? false then 
   let [c1;c2] = argl in
   let th1 = regular_CONV1 x c1 in
   let th2 = regular_CONV1 x c2 in
   BETA_RULE (MP(ISPECL[mk_abs(x,c1);mk_abs(x,c2)]regular_seq)(CONJ th1 th2))
 else if op = "cond:^ty" ? false then 
   let [g;c1;c2] = argl in
   let th1 = regular_CONV1 x c1 in
   let th2 = regular_CONV1 x c2 in
   BETA_RULE(MP(ISPECL[g;mk_abs(x,c1);mk_abs(x,c2)]regular_cond)(CONJ th1 th2))
 else fail;;
letrec regular_CONV f =
 let x,c = dest_abs f in
 regular_CONV1 x c;;
let regular_TAC:tactic (asl,w) = 
  [],\[].regular_CONV (snd(dest_comb w)) ? failwith `regular_TAC`;;

