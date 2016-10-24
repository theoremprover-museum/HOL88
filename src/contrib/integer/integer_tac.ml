% FILE		: integer_tactics.ml					%
% DESCRIPTION   : defines the rules and tactics for various arguements  %
%                 special to the  integers.  Contains the rule and	%
%		  tactic that were previously in int_cases_tac.ml.	%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.7.17						%
%									%
%-----------------------------------------------------------------------%

loadf (library_pathname() ^ `/group/start_groups`);;



% INT_CASES = |- !P. (!m. P(INT m)) /\ (!m. P(neg(INT m))) ==> (!M. P M) %

% INT_CASES_RULE : thm -> thm -> thm

  A1 |- !n1:num. P(INT n1)   A2 |- !n2:num. P(neg(INT n2))
------------------------------------------------------------
                  A1 u A2 |- !M:integer. P M
%

let INT_CASES_RULE thm1 thm2 =
(let (var1,prop1) = dest_forall (concl thm1) in
 let (var2,prop2) = dest_forall (concl thm2) in
 let M = variant ((var1.(frees prop1))@(var2.(frees prop2))) "M:integer" in
 let P = subst [(M,"INT ^var1")] prop1 in
  MP (BETA_RULE (SPEC "\^M.^P" (theorem `integer` `INT_CASES`)))
     (CONJ thm1 thm2)
)?failwith `INT_CASES_RULE`;;



% INT_CASES_TAC : tactic

                   [A] !n:integer. P n
============================================================================
 [A] !n1:num. P (INT n1)   [A;!n1:num. P (INT n1)] !n2:num. P (neg(INT n2))

  INT_CASES_TAC allows a reduction of a problem about all integers to
  two problems about natural numbers.  After making this reduction one
  can proceed by induction on the natural numbers.
%


let INT_CASES_TAC (asl,gl) =
(let (V,prop) = dest_forall gl in
 let n1 = variant (V.(frees prop)) "n1:num" in
 let n2 = variant (V.(frees prop)) "n2:num" in
 let fst_gl = "!^n1.^(subst [("INT ^n1",V)] prop)" in
 ([(asl,fst_gl);(fst_gl.asl,"!^n2.^(subst [("neg(INT ^n2)",V)] prop)")],
 (\[thm1;thm2]. CONV_RULE (GEN_ALPHA_CONV V)
     (INT_CASES_RULE thm1 (MP (DISCH (concl thm1) thm2) thm1))))
)?failwith `INT_CASES_TAC`;;

%**************************************************************************%
% SIMPLE_INT_CASES_RULE and SIMPLE_INT_CASES_TAC allow a reduction of a
  problem about all integers to the three cases where the integer is
  positive, where it is negative, and where it is zero.
%

% SIMPLE_INT_CASES_RULE : thm -> thm -> thm

      A1 |- !N:integer. POS N ==> P N 
      A2 |- !N:integer. NEG N ==> P N
              A3 |- P (INT 0)
     ---------------------------------
      A1 u A2 u A3 |- !N:integer. P N
%

let SIMPLE_INT_CASES_RULE thm1 thm2 thm3 =
(let N = variant
  ((frees (concl thm1))@(freesl ((hyp thm1)@(hyp thm2)@(hyp thm3))))
  "N:integer" in
 let (V,prop) =
      (\ (v,p).(v,(snd (dest_imp p)))) (dest_forall (concl thm1)) in
 let PN = subst [(N,V)] prop in
 let Thm3 = DISCH "^N = (INT 0)"
     (EQ_MP (SYM (BETA_RULE (AP_TERM "\^N.^PN" (ASSUME "^N = (INT 0)"))))
            thm3) in
 let thm4 = (DISCH "NEG ^N \/ (^N = (INT 0))"
  (MP (MP (MP (SPECL [PN;"NEG ^N";"^N = (INT 0)"] OR_ELIM_THM)
   (ASSUME "NEG ^N \/ (^N = (INT 0))")) (SPEC N thm2)) Thm3)) in
 
  (GEN N (MP (MP (MP
   (SPECL [PN;"POS ^N";"NEG ^N \/ (^N = (INT 0))"] OR_ELIM_THM)
    (CONJUNCT1 (SPEC N (theorem `integer` `TRICHOTOMY`))))
    (SPEC N thm1)) thm4))

)?failwith `SIMPLE_INT_CASES_RULE`;;


% SIMPLE_INT_CASES_TAC : tactic

                   [A] !N:integer. P N
==============================================================================
 [A] !N. POS N ==> P N  [A;!N. POS N ==> P N] !N. NEG N ==> P N  [A] P(INT 0)

%


let SIMPLE_INT_CASES_TAC (asl,gl) =
(let N = variant (frees gl) "N:integer" in
 let (V,prop) = dest_forall gl in
 let PN = subst [(N,V)] prop in
 let fst_gl = "!^N.POS ^N ==> ^PN" in
 let snd_gl = "!^N.NEG ^N ==> ^PN" in
 let trd_gl = subst [("INT 0",V)] prop in
 ([(asl,fst_gl);(fst_gl.asl,snd_gl);(asl,trd_gl)],
 (\[thm1;thm2;thm3]. CONV_RULE (GEN_ALPHA_CONV V)
   (SIMPLE_INT_CASES_RULE thm1 (MP (DISCH (concl thm1) thm2) thm1) thm3)))
)?failwith `SIMPLE_INT_CASES_TAC`;;



%**************************************************************************%

% INT_MIN_RULE, INT_MAX_RULE, INT_MIN_TAC, and INT_MAX_TAC are for
  showing that minimum and maximun elements for bounded subsets of
  the integers exist.
%

% INT_MIN_RULE : thm -> thm -> thm

  A1 |- ?M:integer. S1 M    A2 |- ?K1. !N. N below K1 ==> ~S1 N
  -------------------------------------------------------------
     A1 u A2 |- ?MIN. S1 MIN /\ (!N1. N1 below MIN ==> ~S1 N1)

%

let INT_MIN_RULE thm1 thm2 =
(let (var1,prop1) = dest_exists (concl thm1) in
 let (var21,(var22,prop2)) = 
  ((\ (v21,prop).(v21,(dest_forall prop)))(dest_exists (concl thm2))) in
 let MIN = variant ((var1.(frees prop1))@(var21.(var22.(frees prop2))))
         "MIN:integer" in
 let SMIN = subst [(MIN,var1)] prop1 in
  (MP (CONJUNCT1 (MP (BETA_RULE
     (SPEC "\^MIN.^SMIN" (theorem `integer` `DISCRETE`))) thm1)) thm2)
)?failwith `INT_MIN_RULE`;;


% INT_MIN_TAC : term -> tactic
                 S1

                   [A] Goal
   =============================================
     [A, S1 MIN, !N. N below MIN ==> ~S1 N] Goal
     [A] ?M:integer. S1 M
     [A, S1 M] ?LB. !N. N below LB ==> ~S1 N
%

let INT_MIN_TAC S1 = set_fail `INT_MIN_TAC`
\ (asl,gl) .
(if not (type_of S1 = ":integer -> bool")
 then failwith `Term is not a predicate over the integers.`
 else
 let varlist = ((frees S1)@(frees gl)@(freesl asl)) in
 let M = variant varlist "M:integer" in
 let N = variant varlist "N:integer" in
 let MIN = variant varlist "MIN:integer" in
 let LB = variant varlist "LB:integer" in
 let SM = rhs (concl (DEPTH_CONV BETA_CONV "^S1 ^M")) in
 let SMIN = subst [(MIN,M)] SM in
 let SN = subst [(N,M)] SM in
 ([(SMIN.("!^N.^N below ^MIN ==> ~^SN".asl),gl);
   (asl,"?^M.^SM");
   (SM.asl,"?^LB.!^N. ^N below ^LB ==> ~^SN")],
  (\[thm1;thm2;thm3].
    let thm4 = SELECT_RULE
     (INT_MIN_RULE 
      thm2 
      (MP (SPEC "@^M.^SM" (GEN M (DISCH SM thm3))) (SELECT_RULE thm2))) in
    let thm5 = ASSUME "^SMIN /\ !^N.^N below ^MIN ==> ~^SN" in 
    MP (SPEC "@^MIN.^(concl thm5)" (GEN MIN (DISCH (concl thm5)
           (PROVE_HYP (CONJUNCT2 thm5) (PROVE_HYP (CONJUNCT1 thm5) thm1)))))
       thm4)));;



% INT_MAX_RULE : thm -> thm -> thm

  A1 |- ?M:integer. S1 M    A2 |- ?K1. !N. K1 below N ==> ~S1 N
  -------------------------------------------------------------
     A1 u A2 |- ?MAX. S1 MAX /\ (!N1. MAX below N1 ==> ~S1 N1)
%

let INT_MAX_RULE thm1 thm2 =
(let (var1,prop1) = dest_exists (concl thm1) in
 let (var21,(var22,prop2)) = 
  ((\ (v21,prop).(v21,(dest_forall prop)))(dest_exists (concl thm2))) in
 let MAX = variant ((var1.(frees prop1))@(var21.(var22.(frees prop2))))
         "MAX:integer" in
 let SMAX = subst [(MAX,var1)] prop1 in
  (MP (CONJUNCT2 (MP (BETA_RULE
     (SPEC "\^MAX.^SMAX" (theorem `integer` `DISCRETE`))) thm1)) thm2)
)?failwith `INT_MAX_RULE`;;


% INT_MAX_TAC : tactic

                   [A] Goal
   =============================================
     [A, S1 MAX. !N. MAX below N ==> ~S1 N] Goal
     [A] ?M:integer. S1 M
     [A, S1 M] ?UB. !N. UB below N ==> ~S1 N
%

let INT_MAX_TAC S1 = set_fail `INT_MAX_TAC` 
\ (asl,gl).
(if not (type_of S1 = ":integer -> bool")
 then failwith `Term is not a predicate over the integers.`
 else
 let varlist = ((frees S1)@(frees gl)@(freesl asl)) in
 let M = variant varlist "M:integer" in
 let N = variant varlist "N:integer" in
 let MAX = variant varlist "MAX:integer" in
 let UB = variant varlist "UB:integer" in
 let SM = rhs (concl (DEPTH_CONV BETA_CONV "^S1 ^M")) in
 let SMAX = subst [(MAX,M)] SM in
 let SN = subst [(N,M)] SM in
 ([(SMAX.("!^N. ^MAX below ^N ==> ~^SN".asl),gl);
   (asl,"?^M.^SM");
   (SM.asl,"?^UB.!^N. ^UB below ^N ==> ~^SN")],
  (\[thm1;thm2;thm3].
    let thm4 = SELECT_RULE
     (INT_MAX_RULE
      thm2
      (MP (SPEC "@^M.^SM" (GEN M (DISCH SM thm3))) (SELECT_RULE thm2))) in
    let thm5 = ASSUME "^SMAX /\ !^N. ^MAX below ^N ==> ~^SN" in
    MP (SPEC "@^MAX.^(concl thm5)" (GEN MAX (DISCH (concl thm5)
           (PROVE_HYP (CONJUNCT2 thm5) (PROVE_HYP (CONJUNCT1 thm5) thm1)))))
       thm4)));;

%**************************************************************************%


% INT_RIGHT_ASSOC_TAC : term -> tactic  (term = (a plus b) plus c)

   A |-  t((a plus b) plus c)
---------------------------------
   A |-  t(a plus (b plus c))

%

let INT_RIGHT_ASSOC_TAC tm =
 set_fail_prefix `INT_RIGHT_ASSOC_TAC`
 (\ (asl,gl).
  let plus = rator (rator tm) in
   if not((rator (rator tm)) = "$plus") or
      not((rator(rator(rand (rator tm))))= "$plus")
   then failwith `Term not of form "(a plus b) plus c".`
   else
  let a = (rand(rator(rand (rator tm)))) in
  let b = (rand(rand (rator tm))) in
  let c = rand tm in
   NEW_SUBST1_TAC (SPECL [a;b;c] 
     (theorem `integer` `PLUS_GROUP_ASSOC`)) (asl,gl));;


% INT_LEFT_ASSOC_TAC : term -> tactic  (term = a plus (b plus c))

   A |-  t(a plus (b plus c))
---------------------------------
   A |-  t((a plus b) plus c)

%

let INT_LEFT_ASSOC_TAC tm =
 set_fail_prefix `INT_LEFT_ASSOC_TAC`
 (\ (asl,gl).
  let plus = rator (rator tm) in
   if not((rator (rator tm)) = "$plus") or
      not((rator(rator (rand tm)))= "$plus")
   then failwith `Term not of form "a plus (b plus c)".`
   else
  let a = (rand(rator tm)) in
  let b = (rand(rator (rand tm))) in
  let c = (rand (rand tm)) in
   NEW_SUBST1_TAC (SYM (SPECL [a;b;c]
    (theorem `integer` `PLUS_GROUP_ASSOC`))) (asl,gl));;
