% proof_convs.ml

%


let CONJ_IMP = prove
 ("(t1==>t1')/\(t2==>t2')==>(t1/\t2)==>(t1'/\t2')",
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;
let DISJ_IMP = prove
 ("(t1==>t1')/\(t2==>t2')==>(t1\/t2)==>(t1'\/t2')",
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;
let IMP_IMP = prove
 ("(t2==>t2')==>(t1==>t2)==>(t1==>t2')",
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;

% Given  th=|-x==>y  produce theorem |-tm==>tm[y/x] by monotonicity %
letrec mono_imp_conv th tm =
 let ta,tb = dest_imp (concl th) in
  (let tm17 = find_term (\t.t=ta) tm in
   if tm = ta then th
   else if is_conj tm then
     let tm1,tm2 = dest_conj tm in
     let thm1 = mono_imp_conv th tm1 in
     let tm1a,tm1b = dest_imp(concl thm1) in
     let thm2 = mono_imp_conv th tm2 in
     let tm2a,tm2b = dest_imp(concl thm2) in
         MP (INST[tm1a,"t1:bool";tm1b,"t1':bool";tm2a,"t2:bool";tm2b,"t2':bool"] CONJ_IMP)
            (CONJ thm1 thm2)
   else if is_disj tm then
     let tm1,tm2 = dest_disj tm in
     let thm1 = mono_imp_conv th tm1 in
     let tm1a,tm1b = dest_imp(concl thm1) in
     let thm2 = mono_imp_conv th tm2 in
     let tm2a,tm2b = dest_imp(concl thm2) in
         MP (INST[tm1a,"t1:bool";tm1b,"t1':bool";tm2a,"t2:bool";tm2b,"t2':bool"] DISJ_IMP) 
            (CONJ thm1 thm2)
   else if is_imp tm then
     let tm1,tm2 = dest_imp tm in
     let thm2 = mono_imp_conv th tm2 in
     let tm2a,tm2b = dest_imp(concl thm2) in
         MP (INST[tm1,"t1:bool";tm2a,"t2:bool";tm2b,"t2':bool"] IMP_IMP) thm2
   else if is_forall tm then
     let x,tm1 = dest_forall tm in
     let thm1 = mono_imp_conv th tm1 in
     let thm2 = SPEC x(ASSUME(mk_forall(x,fst(dest_imp(concl thm1))))) in
         DISCH_ALL(GEN x (MP thm1 thm2))
   else if is_exists tm then
     let x,tm1 = dest_exists tm in
     let thm1 = mono_imp_conv th tm1 in
     let tm2a,tm2b = dest_imp(concl thm1) in
     let thm2 = SELECT_RULE(ASSUME(mk_exists(x,tm2a))) in
     let tm0 = fst(hd(fst(match tm2a (concl thm2)))) in
     let thm3 = MP (INST [tm0,x] thm1) thm2 in
         DISCH_ALL(EXISTS(mk_exists(x,tm2b),tm0) thm3)
   else fst(EQ_IMP_RULE(REFL tm)))
  ? fst(EQ_IMP_RULE(REFL tm));;

let mono_imp_rule th thm =
 (let thm1 = mono_imp_conv th (concl thm) in
  MP thm1 thm)
 ? failwith `mono_imp_rule`;;

let REMOVE_EXISTS_CONV tm =
 (let x,t = dest_exists tm in
  let imp1 = DISCH_ALL (EXISTS(tm,x) (ASSUME t)) in
  let imp2 = DISCH_ALL (SELECT_RULE (ASSUME tm)) in
  IMP_ANTISYM_RULE imp2 imp1)
 ? failwith `REMOVE_EXISTS_CONV`;;

letrec assoc2 x yxl =
  (let h.t = yxl in
   if x = snd h then fst h else assoc2 x t
  ) ? failwith `assoc2`;;
let ONE_EXISTS_TAC v c1 (asl,gl) =
  (let c1a,c1b = dest_eq c1 in
   let instl = fst(match c1a c1b) ? fst(match c1b c1a) in
   EXISTS_TAC (assoc2 v instl ? snd(assoc v instl)) (asl,gl)
  ) ? failwith `ONE_EXISTS_TAC`;;
letrec SIMPLE_EXISTS_TAC v c (asl,gl) =
  (if is_conj c then
    let c1,c2 = dest_conj c in
    ONE_EXISTS_TAC v c1 (asl,gl) ? SIMPLE_EXISTS_TAC v c2 (asl,gl)
   else ONE_EXISTS_TAC v c (asl,gl)
  ) ? failwith `SIMPLE_EXISTS_TAC`;;
let AUTO_EXISTS_TAC (asl,gl) =
  (let vl,c = strip_exists gl in
   SIMPLE_EXISTS_TAC (hd vl) c (asl,gl)
  ) ? failwith `AUTO_EXISTS_TAC`;;
