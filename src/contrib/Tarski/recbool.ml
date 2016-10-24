%----- -*- Emacs Mode: fundamental -*- -------------------------------

  File:		recbool.ml

  Authors:	(c) Flemming Andersen & Kim Dam Petersen
  Date:		26/7-1991.
  Last Updated:	29/10-1992.

  Description:
		Defines operations for constructing recursive predicates.
  Dependicies:
		tarski
  Usage:
		loadt`recbool`;;
---------------------------------------------------------------------%

loadt`curry`;;
loadt`tarski`;;

let FORALL_PAIR_EQ = TAC_PROOF(([],
  "(!P. (!p. P p) = (!(x:*) (y:**). P (x,y)))"),
  GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [ ASM_REWRITE_TAC[]
  ; POP_ASSUM(\thm.
      ACCEPT_TAC (ONCE_REWRITE_RULE[PAIR]
         (SPECL["FST(p:*#**)";"SND(p:*#**)"]thm)))
  ]);;

%<
  FORALL_PAIR_CONV "(x1:*,..,xn:*n)" "!(p:*#...#*n). P p" -->
     |- (!(p:*#...#*n). P p) = (!(x1:*) ... (xn:*n). P(x1,...,xn))
>%
let FORALL_PAIR_CONV xp tm =
  let
    (p,Pp) = dest_forall tm and
    xv = strip_pair xp
  in letrec pairs xp =
    if is_pair xp then
      ((\p. "FST ^p") .
       (map (\fn p. fn "SND ^p") (pairs (snd(dest_pair xp)))))
    else
      [\p. p]
  in let
    thm1 = DISCH_ALL(GENL xv (SPEC xp (ASSUME tm)))
  in let
    thm2 = DISCH_ALL (PURE_REWRITE_RULE[PAIR](GEN p (SPECL 
      (map (\fn. fn p) (pairs xp))
      (ASSUME (list_mk_forall (xv, (subst[(xp,p)]Pp)))))))
  in
    if is_pair xp then
      IMP_ANTISYM_RULE thm1 thm2
    else
      failwith `FORALL_PAIR_CONV`;;

%<
  EquationToAbstraction "!x1 ... xn. f (x1,...,xn) = t"
                     --> "\f (x1,...,xn). t"
>%
let EquationToAbstraction =
  set_fail_prefix `EquationToAbstraction`
  (\tm.
     let
       (fxv, t) = dest_eq (snd(strip_forall tm))
     in let
       (f,xv)   = strip_comb fxv
     in
       mk_abs (f, list_mk_uncurry_abs (xv,t)));;

%<
   PURE_CONV conv tm --> if conv tm = |- tm = tm then fail
>%
let PURE_CONV conv =
  set_fail_prefix `PURE_CONV`
  (\tm.
    let thm = conv tm
    in
       if aconv tm (concl thm) then fail`identity conversion`
       else thm);;
%<
  MonoThmToTactic mono_thm --> Initial tactic

>%
let MonoThmToTactic eqn =
  let
    xp = snd(dest_comb(fst(dest_eq(eqn))))
  in
    (REWRITE_TAC[IsMono;Leq] THEN
     BETA_TAC THEN
     CONV_TAC(DEPTH_CONV (FORALL_PAIR_CONV xp)) THEN
     UNCURRY_BETA_TAC);;
    
%<
  CurryEquationToAbstraction "!x1 ... xn. f x1 ... xn = t"
                     --> "\f'. (\f (x1,...,xn). t)(\x1 ... xn. g(x1,...,xn))"
>%
let CurryEquationToAbstraction =
  set_fail_prefix `NewEquationToAbstraction`
  (\tm.
     let    (fxv, t) = dest_eq (snd(strip_forall tm))
     in let (f,xv)   = strip_comb fxv
     in let tpg      = type_of(list_mk_pair xv)
     in let g = variant (frees t)
                   (mk_var(fst(dest_var f),
                           mk_type(`fun`,[tpg;":bool"])))
     in let fabs = mk_abs(f, mk_uncurry_abs (list_mk_pair xv,t)) and
            gabs = list_mk_abs(xv, mk_comb(g,list_mk_pair xv))
     in
       mk_abs (g, mk_comb(fabs, gabs)));;

%<
  set_monotonic_goal "f (x1,...,xn) = Body[f,x1,...,xn]" -->
    set_goal([],"IsMono (\f. \(x1,...,xn). Body[f,x1,...,xn])")
>%

let set_monotonic_goal =
  set_fail_prefix `set_monotonic_goal`
  (\tm.
    let
      tm' = "IsMono ^(EquationToAbstraction tm)"
    in
      (set_goal([],tm');
       e(MonoThmToTactic tm)));;

%<       e(REWRITE_TAC[IsMono;Leq])));; >%

%<
  curry_set_monotonic_goal "f (x1,...,xn) = Body[f,x1,...,xn]" -->
    curry_set_goal([],"IsMono (\f. \(x1,...,xn). Body[f,x1,...,xn])")
>%

let curry_set_monotonic_goal =
  set_fail_prefix `curry_set_monotonic_goal`
  (\tm.
    let
      tm' = "IsMono ^(CurryEquationToAbstraction tm)" and
      xp = list_mk_pair(snd(strip_comb(fst(dest_eq (snd(strip_forall tm))))))
    in
      (set_goal([],tm');
       e(REWRITE_TAC[IsMono;Leq] THEN
         BETA_TAC THEN
         BETA_TAC THEN
         CONV_TAC (DEPTH_CONV UNCURRY_BETA_CONV) THEN
         CONV_TAC (DEPTH_CONV (FORALL_PAIR_CONV xp)) THEN
         CONV_TAC (DEPTH_CONV UNCURRY_BETA_CONV) )));;

%<
  prove_monotonic_thm "f (x1,...,xn) = Body[f,x1,...,xn]" tactic -->
    |- IsMono (\f. \(x1,...,xn). Body[f,x1,...,xn])
>%

let prove_monotonic_thm =
  set_fail_prefix `prove_monotonic_thm`
  (\ (str,tm,tactic). 
    let
      tm' = "IsMono ^(EquationToAbstraction tm)"
    in
      (prove_thm(str, tm', (MonoThmToTactic tm THEN tactic))));;

%<
  new_min_recursive_relation_definition name
       |- IsMono (\f. \(x1,...,xn). Body[f,x1,...,xn]) -->
    |- f = MinFix (\f. \(x1,...,xn). Body[f,x1,...,xn])
>%

let new_min_recursive_relation_definition =
  set_fail_prefix `new_min_recursive_relation_definition`
  (\(name,mono).
     let
       (r,a) = dest_abs(snd(dest_comb(snd(dest_thm mono))))
     in let
       b     = mk_abs (r,a)
     in
       new_definition (name, "^r = MinFix ^b"));;

%<
  new_max_recursive_relation_definition name
       |- IsMono (\f. \(x1,...,xn). Body[f,x1,...,xn]) -->
    |- f = MaxFix (\f. \(x1,...,xn). Body[f,x1,...,xn])
>%

let new_max_recursive_relation_definition =
  set_fail_prefix `new_max_recursive_relation_definition`
  (\(name,mono).
     let
       (r,a) = dest_abs(snd(dest_comb(snd(dest_thm mono))))
     in let
       b     = mk_abs (r,a)
     in
       new_definition (name, "^r = MaxFix ^b"));;

%<
  prove_fix_thm
       fail_str
       FixEQThm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_fix_thm fail_str FixEQThm =
  set_fail_prefix fail_str
  (\ (name,def,mono). 
    let
      thm= BETA_RULE(ONCE_REWRITE_RULE[SYM def](MATCH_MP FixEQThm mono))
    in let
      x = fst(dest_uncurry_abs(fst(dest_eq(snd(dest_thm thm)))))
    in let
      thm = AP_THM thm x
    in letrec
      curry_beta_rule (x,thm) =
        if is_pair x then
          curry_beta_rule
           (snd(dest_pair x),
            BETA_RULE(PURE_ONCE_REWRITE_RULE[UNCURRY_DEF]thm))
        else
          BETA_RULE(PURE_ONCE_REWRITE_RULE[UNCURRY_DEF]thm)
    in
      save_thm(name, GEN_ALL(SYM(curry_beta_rule(x,thm)))));;

%<
  prove_min_fix_thm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_min_fix_thm =
 prove_fix_thm `prove_min_fix_thm` MinFixEQThm;;

%<
  prove_max_fix_thm
       name
       (|- f = MaxFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_max_fix_thm =
 prove_fix_thm `prove_max_fix_thm` MaxFixEQThm;;

%<
  prove_min_min_thm name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !R. ((\ (x1,...,xn). Body[R]) = R) ==>
             (!x1 ... xn. f (x1,...,xn) = R(x1,...,xn))   
>%
let prove_min_min_thm =
  set_fail_prefix `prove_min_min_thm`
  (\ (name,def,mono). 
    let Fn = el 1 (snd (strip_comb (concl mono))) in
    let
      thm1 = BETA_RULE(ONCE_REWRITE_RULE[SYM def]
                (ISPEC Fn Min_MinFixThm))
    in let
      thm2 = ONCE_REWRITE_RULE[Leq]thm1
    in let
      x = el 2 (fst(strip_uncurry_abs
                 (snd(dest_comb(snd(dest_eq(snd(dest_thm def))))))))
    in letrec rule (x,thm) =
         if is_pair x then
            rule(snd(dest_pair x),
                 BETA_RULE(ONCE_REWRITE_RULE[UNCURRY_DEF]
                   (CONV_RULE (DEPTH_CONV (FORALL_PAIR_CONV x)) thm)))
         else
            thm
    in
      save_thm(name, rule(x,thm2)));;

%<
  prove_max_max_thm name
       (|- f = MaxFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !R. ((\ (x1,...,xn). Body[R]) = R) ==>
             (!x1 ... xn. f (x1,...,xn) = R(x1,...,xn))   
>%
let prove_max_max_thm =
  set_fail_prefix `prove_max_max_thm`
  (\ (name,def,mono). 
    let Fn = el 1 (snd (strip_comb (concl mono))) in
    let
      thm1 = BETA_RULE(ONCE_REWRITE_RULE[SYM def]
                        (ISPEC Fn Max_MaxFixThm))
    in let
      thm2 = ONCE_REWRITE_RULE[Leq]thm1
    in let
      x = el 2 (fst(strip_uncurry_abs
                 (snd(dest_comb(snd(dest_eq(snd(dest_thm def))))))))
    in letrec rule (x,thm) =
         if is_pair x then
            rule(snd(dest_pair x),
                 BETA_RULE(ONCE_REWRITE_RULE[UNCURRY_DEF]
                   (CONV_RULE (DEPTH_CONV (FORALL_PAIR_CONV x)) thm)))
         else
            thm
    in
      save_thm(name, rule(x,thm2)));;

let OR_IMP = TAC_PROOF(([],
  "!t1 t2 t. ((t1 \/ t2) ==> t) = ((t1 ==> t) /\ (t2 ==> t))"),
  REPEAT GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN
  RES_TAC);;

%<
   FORALL_CONJ_CONV "!x1 ... xn. P1 /\ ... /\ Pm" -->
     |- (!x1...xn. P1  /\ ... /\ Pm) =
        (!x1...xk1. P1) /\ ... /\ (!x1...xkm. Pm)
   , where x1...xki = intersect [x1...xn] (frees Pi)
>%

let FORALL_CONJ_CONV tm =
  letrec
     conjs tm =
       if can dest_conj tm then
          (let (x,tm') = dest_conj tm in (x.(conjs tm')))
       else
          [tm]
  in let
    (xv,PC) = strip_forall tm
  in let
    Pv      = conjs PC
  in if (length Pv) < 2 or (length xv) < 1 then
            failwith `FORALL_CONJ_CONV` else
  let
    fPv     = map (\tm. intersect xv (frees tm)) Pv
  in let
    thm1 = LIST_CONJ (map
                       (\ (fv,thm). GENL fv thm)
                       (combine (fPv,
                          (CONJ_LIST (length Pv) (SPECL xv (ASSUME tm)))))) and
    thm2 = GENL xv (LIST_CONJ(map (\ (fv,thm). SPECL fv thm)
     (combine (fPv,
       (CONJ_LIST (length Pv) (ASSUME (list_mk_conj
         (map (\ (fv,tm). list_mk_forall(fv,tm)) (combine (fPv,Pv))))))))))
  in
   IMP_ANTISYM_RULE (DISCH_ALL thm1) (DISCH_ALL thm2);;


%<
  prove_intro_thm
       fail_str
       IntroThm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_intro_thm fail_str IntroThm =
  set_fail_prefix fail_str
  (\ (name,def,mono). 
    let Fn = el 1 (snd (strip_comb (concl mono))) in
    let
      thm1 = ONCE_REWRITE_RULE [mono] (BETA_RULE(ONCE_REWRITE_RULE[SYM def]
               (ISPEC Fn IntroThm)))
    in let
      thm2 = REWRITE_RULE[Leq]thm1
    in let
      x = el 2 (fst(strip_uncurry_abs
                 (snd(dest_comb(snd(dest_eq(snd(dest_thm def))))))))
    in letrec rule (x,thm) =
         if is_pair x then
            rule(snd(dest_pair x),
                 BETA_RULE(ONCE_REWRITE_RULE[UNCURRY_DEF]
                   (CONV_RULE (DEPTH_CONV (FORALL_PAIR_CONV x)) thm)))
         else
            thm
    in let
      thm3 = PURE_REWRITE_RULE[OR_IMP](rule(x,thm2))
    in let
      thm4 = CONV_RULE (DEPTH_CONV FORALL_CONJ_CONV) thm3
    in let
      thm5 = BETA_RULE (REWRITE_RULE[And;Or]thm4)
    in
      save_thm(name, thm5));;

%<
  prove_min_intro_thm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_min_intro_thm =
  prove_intro_thm `prove_min_intro_thm` MinFixIntroductThm;;

%<
  prove_extended_min_intro_thm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%

let prove_extended_min_intro_thm =
  prove_intro_thm `prove_extended_min_intro_thm` ExtMinFixIntroductThm;;

%<
  prove_max_intro_thm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_max_intro_thm =
  prove_intro_thm `prove_max_intro_thm` MaxFixIntroductThm;;

%<
  prove_extended_max_intro_thm
       name
       (|- f = MinFix (\f. \ (x1,...,xn). Body[f,x1,...,xn]))
       (|- IsMono (\f...))
    |- !x1 ... xn. f (x1,...,xn) = Body[f,x1,...,xn]
>%
let prove_extended_max_intro_thm =
  prove_intro_thm `prove_extended_max_intro_thm` ExtMaxFixIntroductThm;;
