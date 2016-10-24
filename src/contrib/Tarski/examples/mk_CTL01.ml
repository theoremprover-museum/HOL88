%----- -*- Emacs Mode: fundamental -*- -------------------------------

  File:          mk_CTL01.ml:

  Author:        (c) Flemming Andersen
  Date:          March 7, 1992
  Last Updated:  28/10-1992.

  Description:

        This file defines a HOL theory for a Branching Time Temporal Logic.

        It is a formalization of the CTL temporal logic proof system
        as proposed by J.R.Burch, E.M. Clarke and K.L.McMillan in:

           Sequential Curcuit Verification Using Symbolic Model Checking

  Dependencies:
	The theory is dependent on the theory `tarski` which introduces
	recursively defined boolean functions.

  Make:		The theory is created by executing:
			# loadt`mk_CTL01`;;

  Usage:	The theory is loaded by executing:
			# load_theory`CTL01`;;
---------------------------------------------------------------------%

%
   The CTL theory is based on the following definitions:

   N is the basic next transition relation of a CTL model (program).

   EX(N,p,u)   = ?v. p v /\ N(u,v)
   EG(N,p,u)   = p u /\ EX(N,(\u. EG(N,p,u)),u)
   EU(N,p,q,u) = q u \/ (p u /\ EX(N,(\u. EU(N,p,q,u)),u))


   The rest of the predicates are all defined in terms of EX, EG, EU:

   EF(N,p,u)   = EU(N,(\u. T),p, u)
   AX(N,p,u)   = ~EX(N,(\u. ~p u),u)
   AF(N,p,u)   = ~EG(N,(\u. ~p u),u)
   AG(N,p,u)   = ~EF(N,(\u. ~p u),u)
   AU(N,p,q,u) = (~EU(N,(\u. ~q u),(\u. ~p u /\ ~q u),u)) /\ AF(N,q,u)

   The fixed point definitions use the Tarski fixed point tool developed
   for HOL mechanized support of fixed points presented in the paper:

	Recursive Boolean Functions in HOL
	Flemming Andersen & Kim Dam Petersen
%

system`/bin/rm CTL01.th`;;

loadt`recbool`;;

new_theory`CTL01`;;

let EX = new_definition
  (`EX`, "EX (N, p, (u:*)) = ?v:*. p v /\ N(u,v)");;

%
  |- Mono (\EG. \(N,p,u). p u /\ EX (N, (\u:*. EG(N,p,u)), u)
%
let MonoEG = prove_monotonic_thm
  (`MonoEG`, "EG(N,p,u) = p u /\ EX(N,(\u:*. EG(N, p, u)),u)",
   REWRITE_TAC[EX] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THENL
   [
    ASM_REWRITE_TAC[]
   ;
    RES_TAC THEN
    EXISTS_TAC "v:*" THEN
    ASM_REWRITE_TAC[]]);;

%
  |- EG = MaxFix(\EG' (N,p,u). p u /\ EX(N,(\u'. EG'(N,p,u')),u))
%
let EG = new_max_recursive_relation_definition(`EG`, MonoEG);;

%
  |- !N p u. EG(N,p,u) = p u /\ EX(N,(\u'. EG(N,p,u')),u)
%
let FixEG = prove_max_fix_thm (`FixEG`,EG,MonoEG);;

%
  |- !R. ((\(N,p,u). p u /\ EX(N,(\u'. R(N,p,u')),u)) = R) ==>
           (!N p u. R(N,p,u) ==> EG(N,p,u))
%
let MaxEG = prove_max_max_thm (`MaxEG`,EG,MonoEG);;

%
  |- !R.
    (!N p u. R(N,p,u) ==> p u /\ EX(N,(\u'. R(N,p,u')),u)) ==>
    (!N p u. R(N,p,u) ==> EG(N,p,u))

%
let IntroEG = prove_max_intro_thm (`IntroEG`,EG,MonoEG);;


%
  |- !x.
    (!N p u. x(N,p,u) ==> p u /\ EX(N,(\u'. (x Or EG)(N,p,u')),u)) ==>
    (!N p u. x(N,p,u) ==> EG(N,p,u))

%
let ExtIntroEG = prove_extended_max_intro_thm (`ExtIntroEG`,EG,MonoEG);;


%
  |- Mono(\EU (N,p,q,u). q u \/ p u /\ EX(N,(\u. EU(N,p,q,u)),u))
%
let MonoEU = prove_monotonic_thm
  (`MonoEU`, "EU(N,p,q,u) = q u \/ (p u /\ EX(N,(\u:*. EU(N,p,q,u)),u))",
   REWRITE_TAC[EX] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ASM_REWRITE_TAC[]
    ;
     DISJ2_TAC THEN
     ASM_REWRITE_TAC[] THEN
     RES_TAC THEN
     EXISTS_TAC "v:*" THEN
     ASM_REWRITE_TAC[]
    ]);;

%
  |- EU = MinFix(\EU' (N,p,q,u). q u \/ p u /\ EX(N,(\u'. EU'(N,p,q,u')),u))
%
let EU = new_min_recursive_relation_definition(`EU`, MonoEU);;

%
  |- !N p q u. EU(N,p,q,u) = q u \/ p u /\ EX(N,(\u'. EU(N,p,q,u')),u)
%
let FixEU = prove_min_fix_thm (`FixEU`,EU,MonoEU);;

%
  |- !R.
    ((\(N,p,q,u). q u \/ p u /\ EX(N,(\u'. R(N,p,q,u')),u)) = R) ==>
    (!N p q u. EU(N,p,q,u) ==> R(N,p,q,u))

%
let MaxEU = prove_min_min_thm (`MinEU`,EU,MonoEU);;

%
  |- !R.
    (!N p q u. q u ==> R(N,p,q,u)) /\
    (!N p q u. p u /\ EX(N,(\u'. R(N,p,q,u')),u) ==> R(N,p,q,u)) ==>
    (!N p q u. EU(N,p,q,u) ==> R(N,p,q,u))
%
let IntroEU = prove_min_intro_thm (`IntroEU`,EU,MonoEU);;

%
  |- !x.

        (!N p q u. q u ==> x(N,p,q,u))
      /\
        (!N p q u. p u /\ EX(N,(\u'. (x And EU)(N,p,q,u')),u) ==> x(N,p,q,u))
      ==>
        (!N p q u. EU(N,p,q,u) ==> x(N,p,q,u))
%
let ExtIntroEU = prove_extended_min_intro_thm (`ExtIntroEU`,EU,MonoEU);;

%
   Derived properties:
%
let EF = new_definition
  (`EF`, "EF(N,p,u:*) =  EU(N,(\u. T),p, u)");;
let AX = new_definition
  (`AX`, "AX(N,p,u:*) = ~EX(N,(\u. ~p u),u)");;
let AF = new_definition
  (`AF`, "AF(N,p,u:*) = ~EG(N,(\u. ~p u),u)");;
let AG = new_definition
  (`AG`, "AG(N,p,u:*) = ~EF(N,(\u. ~p u),u)");;
let AU = new_definition
  (`AU`,
   "AU(N,p,q,u:*) = (~EU(N,(\u. ~q u),(\u. ~p u /\ ~q u),u)) /\ AF(N,q,u)");;
