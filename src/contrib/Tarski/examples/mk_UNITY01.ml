%----- -*- Emacs Mode: fundamental -*- -------------------------------

  File:		mk_UNITY01.ml

  Authors:	(c) Flemming Andersen & Kim Dam Petersen
  Date:		26/7-1991.
  Last Updated:	28/10-1992.

  Description:
	This theory defines (a small part of) the UNITY theory.

	The definition is based on the theory presented in:

		Parallel Program Design, A Foundation
		K. Mani Chandy
		Jayadev Misra

	The theory includes one of the "leadsto" induction principles
	used in Chandy and Misra's book.  The induction principle is
	automatically derived from the fixed point definition.

  Dependencies:
	The theory is dependent on the theory `tarski` which introduces
	recursively defined boolean functions.

  Make:		The theory is created by executing:
			# loadt`mk_UNITY01`;;

  Usage:	The theory is loaded by executing:
			# load_theory`UNITY01`;;

---------------------------------------------------------------------%

system`/bin/rm UNITY01.th`;;
loadt`recbool`;;

new_theory`UNITY01`;;

%< The unity theory is based on the following definitions:

   (1)    Predicate := any element of type (*->bool)
   (2)    Program   := ((*->bool) # ((*->*) list))

   (1.1)  InList x [] = FALSE
   (1.2)  InList x (CONS y l) = (x = y) \/ (InList x l)

   (2.1)  Step p st := \s. p (st s)
   (2.2)  Unless (p, q, (Init,Stmts)) :=
	     (!st. st InList Stmts ==> ((p And (Not q)) Leq Step (p Or q) st))
   (2.3)  Stable (p, Pr) :=
	     Unless (p, FALSE, Pr)
   (2.4)  Invariant (p, (Init,Stmts)) :=
	     Stable (p, (Init,Stmts)) /\ (Init ==>* p)
   (2.5)  Ensures (p, q, (Init,Stmts)) :=
	     Unless (p, q, Pr) /\
	     (?st. st InList Pr ==> ((p And (Not q)) leq Step q st))
   (2.6)  Leadsto (p, q, Pr) := MinFix(\L.
	     Ensures (p, q, Pr) \/
	     (?r. L (p,q,Pr) /\ L (q,r,Pr)) \/
	     (?P. (LUB P = p) /\ (!r. P r ==> L (r,q,Pr))))

   The main theorems are:

>%

let InList = new_recursive_definition true list_Axiom `InList`
  "($InList (x:*) [] = F) /\
   ($InList x (CONS y l) = (x = y) \/ ($InList x l))";;

let Step = new_definition(`Step`,
  "Step (p:*->bool) (st:*->*) = \s. p (st s)");;

let True =
 new_definition(`True`,
  "True (x:*) = T");;

let False =
 new_definition(`False`,
  "False (x:*) = F");;

let Not =
 new_definition(`Not`,
  "Not R = \x:*. ~R x");;

let Imply =
 new_infix_definition(`Imply`,
  "$Imply R R' = \x:*. R x ==> R' x");;

let Unless = new_definition(`Unless`,
  "Unless (p, q, (Init:(*->bool),Stmts:(*->*)list)) =
     (!st. st InList Stmts ==>
        ((p And (Not q)) Leq (Step (p Or q) st)))");;

let Stable = new_definition(`Stable`,
  "Stable (p:*->bool, Pr) = Unless (p, False, Pr)");;

let Invariant = new_definition(`Invariant`,
  "Invariant (p:*->bool, (Init, Stmts)) =
     (Init Leq p) /\ 
     (Stable (p, (Init, Stmts)))");;

let Ensures = new_definition(`Ensures`,
  "Ensures (p, q, (Init:*->bool, Stmts:(*->*)list)) =
     Unless (p, q, (Init,Stmts)) /\
     (?st. st InList Stmts /\ ((p And (Not q)) Leq (Step q st)))");;

%<
  Mono:

  |- Mono (\Leadsto. \ (p,q,Pr).
                   Ensures (p,q,Pr) \/
                   (?r. Leadsto(p,r,Pr) /\ Leadsto(r,q,Pr)) \/
                   (?P. (LUB P = p) /\ (!r. P r ==> Leadsto(r,q,Pr))))
>%
let MonoLeadsto = prove_monotonic_thm(`MonoLeadsto`,
  "Leadsto (p:*->bool, q, Pr) =
       Ensures (p, q, Pr) \/
       (?r. Leadsto(p,r,Pr) /\ Leadsto(r,q,Pr)) \/
       (?P. (LUB P = p) /\ (!r. P r ==> Leadsto(r,q,Pr)))",
  REPEAT STRIP_TAC THENL
  [ ASM_REWRITE_TAC[]
  ; DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC"r:*->bool" THEN
    RES_TAC THEN
    ASM_REWRITE_TAC[]
  ; DISJ2_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC "P:(*->bool)->bool" THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC THEN
    RES_TAC
  ]);;

%
|- Leadsto =
   MinFix
   (\Leadsto' (p,q,Pr).
     Ensures(p,q,Pr) \/
     (?r. Leadsto'(p,r,Pr) /\ Leadsto'(r,q,Pr)) \/
     (?P. (LUB P = p) /\ (!r. P r ==> Leadsto'(r,q,Pr))))
%
let Leadsto =
  new_min_recursive_relation_definition(`Leadsto`, MonoLeadsto);;

close_theory();;

%< Substitution >%

let PrExp_THM = prove_thm(`PrExp_THM`,
  "!Form:((*->bool)#((*->*)list))->bool.
     (!Pr. Form Pr) = (!Init Stmts. Form (Init,Stmts))",
  GEN_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [ ASM_REWRITE_TAC[]
  ; POP_ASSUM (\thm.
       REWRITE_TAC[REWRITE_RULE [PAIR]
        (SPECL ["FST(Pr:((*->bool)#(*->*)list))";
                "SND(Pr:((*->bool)#(*->*)list))"] thm)])
  ]);;

%<
   EXT_TAC        f = g
             ===============
             (!x. f x = g x)
>%
let EXT_TAC (g:goal) =
  let (ls,rs) = dest_eq(snd g) in
  let tp = type_of ls in
  let (`fun`,[tp1;tp2]) = dest_type tp in
  let x = variant (freesl ((snd g).(fst g))) (mk_var(`x`,tp1))
  in
    ([(fst g),(mk_forall(x, mk_eq(mk_comb(ls,x), mk_comb(rs,x))))],
     \ [thm]. EXT thm);;

let Not_False_THM = prove_thm(`Not_False_THM`,
  "!p:*->bool. (!s. Not p s) = (p = False)",
  GEN_TAC THEN
  REWRITE_TAC[Not] THEN
  BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
  [ EXT_TAC THEN
    ASM_REWRITE_TAC[False]
  ; UNDISCH_TAC "(p:*->bool)s" THEN
    ASM_REWRITE_TAC[False]
  ]);;

%<
  FixLeadsto :

  |- !p q Pr. Leadsto (p,q,Pr) =
                Ensures (p,q,Pr) \/
                (?r. Leadsto (p,r,Pr) /\ Leadsto (r,q,Pr)) \/
                (?P. (LUB P = p) /\ (!r. P r ==> Leadsto (r,q,Pr)))
>%
let FixLeadsto =
  prove_min_fix_thm (`FixLeadsto`,Leadsto,MonoLeadsto);;

%<
  MinLeadsto:

  |- !R. ((\(p,q,Pr).
         Ensures(p,q,Pr) \/
         (?r. R(p,r,Pr) /\ R(r,q,Pr)) \/
         (?P. (LUB P = p) /\ (!r. P r ==> R(r,q,Pr)))) =
       R) ==>
      (!p q Pr. Leadsto(p,q,Pr) ==> R(p,q,Pr))

>%
let MinLeadsto =
  prove_min_min_thm (`MinLeadsto`,Leadsto,MonoLeadsto);;

%<
  IntroLeadsto :

  |- !R.
      ((!p q Pr. Ensures (p,q,Pr)
                 ==> R (p,q,Pr)) /\
       (!p q Pr. (?r. Leadsto (p,r,Pr) /\ Leadsto (r,q,Pr))
                 ==> R (p,q,Pr)) /\
       (!p q Pr. (?P. (LUB P = p) /\ (!r. P r ==> Leadsto (r,q,Pr)))
                 ==> R (p,q,Pr)))
      ==>
      (!p q Pr. Leadsto(p,q,Pr) ==> R(p,q,Pr))
>%
let IntroLeadsto =
  prove_min_intro_thm (`IntroLeadsto`,Leadsto,MonoLeadsto);;


%<
  ExtIntroLeadsto :

  |- !x.
    (!p q Pr. Ensures(p,q,Pr) ==> x(p,q,Pr)) /\
    (!p q Pr.
      (?r.
        (x(p,r,Pr) /\ Leadsto(p,r,Pr)) /\ x(r,q,Pr) /\ Leadsto(r,q,Pr)) ==>
      x(p,q,Pr)) /\
    (!p q Pr.
      (?P. (LUB P = p) /\ (!r. P r ==> x(r,q,Pr) /\ Leadsto(r,q,Pr))) ==>
      x(p,q,Pr)) ==>
    (!p q Pr. Leadsto(p,q,Pr) ==> x(p,q,Pr))
>%
let ChandyMisraLeadstoInduction1_THM =
  prove_extended_min_intro_thm (`ChandyMisraLeadstoInduction1_THM`,
                                 Leadsto,MonoLeadsto);;

%<
  Ensures_Impossibility:

  |- !p,Pr. Ensures (p,False,Pr) ==> (!s. Not p s)
>%
let Ensures_Impossibility_THM = prove_thm(`Ensures_Impossibility_THM`,
  "!p Pr. Ensures (p, False, Pr) ==> (!s:*. Not p s)",
  GEN_TAC THEN
  REWRITE_TAC[
    BETA_RULE(SPEC"\Pr. Ensures(p,False,Pr) ==> (!s:*. Not p s)"PrExp_THM)
    ] THEN
  REWRITE_TAC[Ensures;Unless;Leq;Step;Not;False;And;Or] THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC);;

let Leadsto_Impossibility_Lemma1 = TAC_PROOF(([],
  "!(p:*->bool) q Pr. Ensures(p,q,Pr) ==> (q = False) ==> (!s. Not p s)"),
  REPEAT STRIP_TAC THEN
  POP_ASSUM(\thm1. POP_ASSUM(\thm2.
    ASSUME_TAC (PURE_ONCE_REWRITE_RULE[thm1]thm2))) THEN
  IMP_RES_TAC Ensures_Impossibility_THM THEN
  POP_ASSUM(\thm. ACCEPT_TAC (SPEC_ALL thm)));;

let Leadsto_Impossibility_Lemma2 = TAC_PROOF(([],
  "!(p:*->bool) (q:*->bool) (Pr:(*->bool)#((*->*)list)).
         (?r:*->bool.
           ((r = False) ==> (!s. Not p s)) /\
           ((q = False) ==> (!s. Not r s))) ==>
         (q = False) ==>
         (!s. Not p s)"),
  REWRITE_TAC[Not_False_THM] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM(\thm1. POP_ASSUM(\thm2. POP_ASSUM(\thm3.
    ACCEPT_TAC (MP thm3 (MP thm2 thm1))))));;

let Leadsto_Impossibility_Lemma3 = TAC_PROOF(([],
  "!(p:*->bool) (q:*->bool) (Pr:(*->bool)#((*->*)list)).
         (?P.
           (LUB P = p) /\ (!r. P r ==> (q = False) ==> (!s. Not r s))) ==>
         (q = False) ==> (!s. Not p s)"),
  REWRITE_TAC[Not_False_THM] THEN
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (REWRITE_RULE[ASSUME "(q:*->bool) = False"]
   (ASSUME "!r:*->bool. P r ==> ((q:*->bool) = False) ==> (r = False)")) THEN
  REWRITE_TAC[SYM (ASSUME "LUB P = (p:*->bool)")] THEN
  REWRITE_TAC[SYM(SPEC_ALL Not_False_THM);Not] THEN
  REWRITE_TAC[LUB] THEN
  BETA_TAC THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  ASSUME_TAC (REWRITE_RULE[In] (ASSUME "(x:*->bool) In P")) THEN
  RES_TAC THEN
  STRIP_ASSUME_TAC (REWRITE_RULE[ASSUME "(x:*->bool) = False";False]
   (ASSUME "(x:*->bool)s")));;

%<
  Leadsto_Impossibility :

  |- !p Pr. Leadsto(p,False,Pr) ==> (!s. Not p s)
>%
let Leadsto_Impossibility_THM = prove_thm(`Leadsto_Impossibility_THM`,
  "!(p:*->bool) Pr. Leadsto(p,False,Pr) ==> (!s. Not p s)",
  REPEAT STRIP_TAC THEN
  ASSUME_TAC
   (REWRITE_RULE[Leadsto_Impossibility_Lemma1;
                 Leadsto_Impossibility_Lemma2;
                 Leadsto_Impossibility_Lemma3]
    (BETA_RULE(REWRITE_RULE[UNCURRY_DEF](ONCE_REWRITE_RULE[SYM(SPEC_ALL PAIR)]
    (BETA_RULE(REWRITE_RULE[UNCURRY_DEF](ONCE_REWRITE_RULE[SYM(SPEC_ALL PAIR)]
    (SPEC
       "\(p:*->bool,q:*->bool,Pr:((*->bool)#((*->*)list))).
             (q = False) ==> (!s. Not p s)" IntroLeadsto)))))))) THEN
  RES_TAC THEN
  POP_ASSUM(\thm. REWRITE_TAC[REWRITE_RULE[]thm]));;

$$$;;
