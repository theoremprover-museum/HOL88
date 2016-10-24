
% defs.ml - my own definitions %

let goal t = set_goal([],t);;

let REWRITE_CONV=REWR_CONV;;

% --- abbreviations for  rules and tactics --- %
let SYM_RULE = ONCE_REWRITE_RULE[EQ_SYM_EQ];;
let  PORT  = PURE_ONCE_REWRITE_TAC
 and PRT   = PURE_REWRITE_TAC
 and ORT   = ONCE_REWRITE_TAC
 and RT    = REWRITE_TAC
 and POART = PURE_ONCE_ASM_REWRITE_TAC
 and PART  = PURE_ASM_REWRITE_TAC
 and OART  = ONCE_ASM_REWRITE_TAC
 and ART   = ASM_REWRITE_TAC;;
let  PORR  = PURE_ONCE_REWRITE_RULE
 and PRR   = PURE_REWRITE_RULE
 and ORR   = ONCE_REWRITE_RULE
 and RR    = REWRITE_RULE
 and POARR = PURE_ONCE_ASM_REWRITE_RULE
 and PARR  = PURE_ASM_REWRITE_RULE
 and OARR  = ONCE_ASM_REWRITE_RULE
 and ARR   = ASM_REWRITE_RULE;;
let  C1 = CONJUNCT1
 and C2 = CONJUNCT2;;
 
% --- list versions of rewrite rules and tactics --- %
letrec LRT thl = if thl=[] then ALL_TAC
                 else RT[hd thl] THEN LRT (tl thl);;
letrec LPRT thl = if thl=[] then ALL_TAC
                 else PRT[hd thl] THEN LPRT (tl thl);;
letrec LPORT thl = if thl=[] then ALL_TAC
                 else PORT[hd thl] THEN LPORT (tl thl);;
letrec LRR thl trm = if thl=[] then trm
                 else LRR (tl thl) (RR [hd thl] trm);;
letrec LPORR thl trm = if thl=[] then trm
                 else LPORR (tl thl) (PORR [hd thl] trm);;

% --- right-hand-side rewrite rules --- %
let RHS_CONV c tm = 
  RAND_CONV c tm ? failwith `RHS_CONV: conversion failed`;;
let RHS_RR1 th = 
  CONV_RULE (RHS_CONV (DEPTH_CONV (REWRITE_CONV th)));;
letrec RHS_RRL thl th =
  if thl = [] then th
  else (RHS_RRL (tl thl)) ((RHS_RR1 (hd thl)) th);;
let RHS_ORR1 th = 
  CONV_RULE (RHS_CONV (ONCE_DEPTH_CONV (REWRITE_CONV th)));;
letrec RHS_ORRL thl th =
  if thl = [] then th
  else (RHS_ORRL (tl thl)) ((RHS_ORR1 (hd thl)) th);;

% --- right-hand-side rewrite tactics --- %
let RHS_CONV c tm = RAND_CONV c tm ? failwith `RHS_CONV: conversion failed`;;
let RHS_RT1 th = 
  CONV_TAC (RHS_CONV (DEPTH_CONV (REWRITE_CONV th)));;
let RHS_ORT1 th = 
  CONV_TAC (RHS_CONV (ONCE_DEPTH_CONV (REWRITE_CONV th)));;
letrec RHS_RTL thl =
  if thl = [] then ALL_TAC
  else RHS_RT1 (hd thl) THEN RHS_RTL (tl thl);;
let RHS_ORT1 th = 
  CONV_TAC (RHS_CONV (ONCE_DEPTH_CONV (REWRITE_CONV th)));;
letrec RHS_ORTL thl =
  if thl = [] then ALL_TAC
  else RHS_ORT1 (hd thl) THEN RHS_ORTL (tl thl);;

% --- left-hand-side rewrite rules --- %
let LHS_CONV c tm = 
  RATOR_CONV c tm ? failwith `LHS_CONV: conversion failed`;;
let LHS_RR1 th = 
  CONV_RULE (LHS_CONV (DEPTH_CONV (REWRITE_CONV th)));;
letrec LHS_RRL thl th =
  if thl = [] then th
  else (LHS_RRL (tl thl)) ((LHS_RR1 (hd thl)) th);;
let LHS_ORR1 th = 
  CONV_RULE (LHS_CONV (ONCE_DEPTH_CONV (REWRITE_CONV th)));;
letrec LHS_ORRL thl th =
  if thl = [] then th
  else (LHS_ORRL (tl thl)) ((LHS_ORR1 (hd thl)) th);;

% --- left-hand-side rewrite tactics --- %
let LHS_RT1 th = 
  CONV_TAC (LHS_CONV (DEPTH_CONV (REWRITE_CONV th)));;
letrec LHS_RTL thl =
  if thl = [] then ALL_TAC
  else LHS_RT1 (hd thl) THEN LHS_RTL (tl thl);;
let LHS_ORT1 th = 
  CONV_TAC (LHS_CONV (ONCE_DEPTH_CONV (REWRITE_CONV th)));;
letrec LHS_ORTL thl =
  if thl = [] then ALL_TAC
  else LHS_ORT1 (hd thl) THEN LHS_ORTL (tl thl);;

% ----- special tacticals ----- %
letrec NREPEAT n tac = if n=0 then ALL_TAC else (tac THEN NREPEAT (n-1) tac);;

% --- special tactics --- %
let NUM_TAC = CONV_TAC (DEPTH_CONV num_CONV);;
let FUN_TAC = CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC;;
let DEP_FUN_TAC = CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC;;
let SUPER_TAC = BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN
                ASM_REWRITE_TAC[];;
let GEN_ASM_TAC t = ASSUME_TAC (SPEC_ALL (ASSUME t));;
letrec LIST_ASSUME_TAC thl =
  if thl=[] then ALL_TAC
  else ASSUME_TAC (hd thl) THEN LIST_ASSUME_TAC (tl thl);;
letrec LIST_REWRITE_TAC thl =
  if thl=[] then REWRITE_TAC[]
  else REWRITE_TAC[hd thl] THEN LIST_REWRITE_TAC (tl thl);;
  
% --- arithmetic simplification tactics --- %
let ARITH_CMP_TAC = 
  LRT[LESS_OR_EQ;GREATER_OR_EQ;GREATER] THEN 
  CONV_TAC (REDEPTH_CONV num_CONV) THEN RT[LESS_MONO_EQ;LESS_0;NOT_LESS_0]
;;

%  "SUC `N`"  --->  |- SUC `N` = `N+1`  %
let SUC_CONV tm =
 (let suc,n = dest_comb tm in
  if not suc="SUC" then fail
  else
   let nv = int_of_string(fst(dest_const n))+1 in
   SYM (num_CONV (mk_const(string_of_int nv,":num")))
 ) ? failwith `SUC_CONV`
;;

%  "PRE `N`"  --->  |- SPRE `N` = `N-1`  %
let PRE_CONV tm =
 (let pre,m = dest_comb tm in
  if not pre = "PRE" then fail
  else
   if m="0" then CONJUNCT1 PRE
   else
    PORR[PRE] (RHS_ORR1 (num_CONV m) (REFL tm))
 ) ? failwith `PRE_CONV`
;;

% --- rewriting-tactic using rewritten popped assumptions  --- %
let RART thl = POP_ASSUM_LIST (RT o (map (RR thl)));;
let ROART thl = POP_ASSUM_LIST (RT o (map (ORR thl)));;
let RART1 thl = POP_ASSUM ((\th.RT[th]) o (RR thl));;
let ROART1 thl = POP_ASSUM ((\th.RT[th]) o (ORR thl));;


% --- disjunction tactics: choose one disjunct from goal --- %
let DISJ1_TAC:tactic (asl,gl) =
  (let l,r = dest_disj gl in
     [(asl,l)], \[th1]. DISJ1 th1 r
  ) ? failwith `DISJ1_TAC`;;
let DISJ2_TAC:tactic (asl,gl) =
  (let l,r = dest_disj gl in
     [(asl,r)], \[th2]. DISJ2 l th2
  ) ? failwith `DISJ2_TAC`;;



% ----- conversions ----- %

% "N" --->  |- i<N = (i=N-1) \/ ... \/ (i=0) %
let LESS_CONV tm = 
  let LESS_CONV_X tm =
       PORR[LESS_THM] 
        (CONV_RULE(RHS_CONV (DEPTH_CONV num_CONV)) (REFL "i<^tm"))
  in letrec LESS_RULE tm =
       if tm = "0" then LESS_CONV_X "0"
          else let thm = LESS_CONV_X tm
               in SUBS [LESS_RULE (snd(dest_comb(snd(dest_comb(snd
                                    (dest_eq(snd(dest_thm thm))))))))]
                       thm
     in RR[NOT_LESS_0] (LESS_RULE tm)
;;

% "?x.(x=y) /\ P" ---> |- (?x.(x=y) /\ P) = P[y/x] %
let EX_1PT_CONV tm =
 let v,eq,P = (I # dest_conj) (dest_exists tm) in
 let l,r = dest_eq eq in
 let [thm1;thm2] = CONJUNCTS(SELECT_RULE (ASSUME tm)) in
 let imp1 = DISCH tm (SUBST[thm1,v] P thm2) in
 let asm = subst[r,l] P in
 let imp2 = DISCH asm (EXISTS (tm,r) (CONJ (REFL r) (ASSUME asm))) in
   IMP_ANTISYM_RULE imp1 imp2
;;

% "?x.P /\ (x=y)" ---> |- (?x.P /\ (x=y)) = P[y/x] %
let EX_1PT_RIGHT_CONV tm =
 let v,P,eq = (I # dest_conj) (dest_exists tm) in
 let l,r = dest_eq eq in
 let [thm1;thm2] = CONJUNCTS(SELECT_RULE (ASSUME tm)) in
 let imp1 = DISCH tm (SUBST[thm2,v] P thm1) in
 let asm = subst[r,l] P in
 let imp2 = DISCH asm (EXISTS (tm,r) (CONJ (ASSUME asm) (REFL r))) in
   IMP_ANTISYM_RULE imp1 imp2
;;

% "!x.(x=y) ==> P" ---> |- (!x.(x=y) ==> P) = P[y/x] %
let FORALL_1PT_CONV tm =
    let v,eq,P = (I # dest_imp) (dest_forall tm) in
    let l,r = dest_eq eq in
    let imp1 = DISCH tm (MP (SPEC r (ASSUME tm)) (REFL r)) in
    let asm = rand(concl imp1) in
    let th1 = SUBST [SYM(ASSUME eq),v] P (ASSUME asm) in
    let imp2 = DISCH asm (GEN v (DISCH eq th1)) in
        IMP_ANTISYM_RULE imp1 imp2
;;

% "!x y. P" ---> |- (!x y. P) = (!y x. P)  %
let FORALL_SWAP_CONV tm =
    let v1,v2,P = (I # dest_forall) (dest_forall tm) in
    let th1 = SPEC v2 (SPEC v1 (ASSUME tm)) in
    let imp1 = DISCH tm (GEN v2 (GEN v1 th1)) in
    let tm' = snd(dest_imp(concl imp1)) in
    let th2 = SPEC v1 (SPEC v2 (ASSUME tm')) in
    let imp2 = DISCH tm' (GEN v1 (GEN v2 th2)) in
        IMP_ANTISYM_RULE imp1 imp2
;;

% "?x y. P" ---> |- (?x y. P) = (?y x. P)  %
let EXISTS_SWAP_CONV tm =
  let x,rest = dest_exists tm in
  let y,rest = dest_exists rest in
  let rhs = mk_exists(y,mk_exists(x,rest)) in
  let TAC =
    EQ_TAC THEN STRIP_TAC THENL
    [EXISTS_TAC y THEN EXISTS_TAC x THEN POP_ASSUM ACCEPT_TAC
    ;EXISTS_TAC x THEN EXISTS_TAC y THEN POP_ASSUM ACCEPT_TAC
    ]
  in TAC_PROOF(([],mk_eq(tm,rhs)),TAC)
;;

let INDIRECT_TAC2 = PURE_ONCE_REWRITE_TAC[GSYM NOT_CLAUSES] THEN DISCH_TAC;;

