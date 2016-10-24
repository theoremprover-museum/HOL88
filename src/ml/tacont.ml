%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        tacont.ml                                             %
%                                                                             %
%     DESCRIPTION:      Theorem continuations                                 %
%     AUTHOR:           Larry Paulson                                         %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml      %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: Revised for HOL by MJCG                               %
%=============================================================================%

% Many inference rules, particularly those involving disjunction and    %
% existential quantifiers, produce intermediate results that are needed %
% only briefly.  One approach is to treat the assumption list like a    %
% stack, pushing and popping theorems from it.  However, it is          %
% traditional to regard the assumptions as unordered;  also, stack      %
% operations are crude.                                                 %
%                                                                       %
% Instead, we adopt a continuation approach:  a continuation is a       %
% function that maps theorems to tactics.  It can put the theorem on    %
% the assumption list, produce a case split, throw it away, etc.  The   %
% text of a large theorem continuation should be a readable description %
% of the flow of inference.                                             %
%                                                                       %


% Must be compiled in the presence of the hol parser/pretty printer     %
% This loads genfns.ml and hol-syn.ml too.                              %
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml            %

if compiling then  (loadf `ml/hol-in-out`;
                    loadf `ml/hol-rule`;
                    loadf `ml/hol-drule`;
                    loadf `ml/drul`;
                    loadf `ml/tacticals`);;


lettype thm_tactic = thm -> tactic;;
lettype thm_tactical = thm_tactic -> thm_tactic;;

ml_curried_infix `THEN_TCL`;;
ml_curried_infix `ORELSE_TCL`;;

let $THEN_TCL (ttcl1: thm_tactical) (ttcl2: thm_tactical) ttac =
    ttcl1 (ttcl2 ttac) ;;

let $ORELSE_TCL (ttcl1: thm_tactical) (ttcl2: thm_tactical) ttac th =
    (ttcl1 ttac th) ? (ttcl2 ttac th);;

letrec REPEAT_TCL (ttcl: thm_tactical) ttac th =
    ((ttcl  THEN_TCL  (REPEAT_TCL ttcl))  ORELSE_TCL  I) ttac th;;

% --------------------------------------------------------------------- %
% New version of REPEAT for ttcl's.  Designed for use with IMP_RES_THEN.%
% TFM 91.01.20.                                                         %
% --------------------------------------------------------------------- %
letrec REPEAT_GTCL (ttcl: thm_tactical) ttac th (A,g) =
    ttcl (REPEAT_GTCL ttcl ttac) th (A,g) ? ttac th (A,g);;

let ALL_THEN : thm_tactical = I;;
let NO_THEN : thm_tactical = \ttac th. failwith `NO_THEN`;;

%
Uses every theorem tactical.
EVERY_TCL [ttcl1;...;ttcln] =  ttcl1  THEN_TCL  ...  THEN_TCL  ttcln
%

let EVERY_TCL ttcll = itlist $THEN_TCL ttcll ALL_THEN;;

%
Uses first successful theorem tactical.
FIRST_TCL [ttcl1;...;ttcln] =  ttcl1  ORELSE_TCL  ...  ORELSE_TCL  ttcln
%

let FIRST_TCL ttcll = itlist $ORELSE_TCL ttcll NO_THEN;;

%
Conjunction elimination

        C
   ==============       |- A1 /\ A2
        C
      ===== ttac1 |-A1
       ...
      ===== ttac2 |-A2
       ...
%

let CONJUNCTS_THEN2 (ttac1: thm_tactic) ttac2 cth : tactic =
    let th1,th2 = CONJ_PAIR cth ? failwith `CONJUNCTS_THEN2` in
    ttac1 th1  THEN  ttac2 th2;;

let CONJUNCTS_THEN ttac = CONJUNCTS_THEN2 ttac ttac;;

%
Disjunction elimination

                 C
   =============================       |- A1 \/ A2
      C                     C
    ===== ttac1 A1|-A1    ===== ttac2 A2|-A2
     ...                   ...

%

% -------------------------------------------------------------------------- %
% REVISED 22 Oct 1992 by TFM. Bugfix.					     %
%									     %
% The problem was, for example:						     %
%									     %
%  th = |- ?n. ((?n. n = SUC 0) \/ F) /\ (n = 0)			     %
%  set_goal ([], "F");;						             %
%  expandf (STRIP_ASSUME_TAC th);;				 	     %
%  OK..									     %
%  "F"									     %
%     [ "n = SUC 0" ] (n.b. should be n')				     %
%     [ "n = 0" ]						             %
% 								             %
% let DISJ_CASES_THEN2 ttac1 ttac2 disth :tactic  =			     %
%     let a1,a2 = dest_disj (concl disth) ? failwith `DISJ_CASES_THEN2` in   %
%     \(asl,w).								     %
%      let gl1,prf1 = ttac1 (ASSUME a1) (asl,w)				     %
%      and gl2,prf2 = ttac2 (ASSUME a2) (asl,w)			    	     %
%      in							             %
%      gl1 @ gl2,							     %
%      \thl. let thl1,thl2 = chop_list (length gl1) thl in		     %
%            DISJ_CASES disth (prf1 thl1) (prf2 thl2);;			     %
% -------------------------------------------------------------------------- %

let DISJ_CASES_THEN2 ttac1 ttac2 disth :tactic  =
    let a1,a2 = dest_disj (concl disth) ? failwith `DISJ_CASES_THEN2` in
    \(asl,w).
     let gl1,prf1 = ttac1 (itlist ADD_ASSUM (hyp disth) (ASSUME a1)) (asl,w)
     and gl2,prf2 = ttac2 (itlist ADD_ASSUM (hyp disth) (ASSUME a2)) (asl,w)
     in
     gl1 @ gl2, 
     \thl. let thl1,thl2 = chop_list (length gl1) thl in
	   DISJ_CASES disth (prf1 thl1) (prf2 thl2);;

%Single-, multi-tactic versions%

let DISJ_CASES_THEN ttac = DISJ_CASES_THEN2 ttac ttac;;
let DISJ_CASES_THENL = end_itlist DISJ_CASES_THEN2;;

%
Implication introduction

        A ==> B
    ==============
          B
    ==============  ttac |-A
        . . .
%

% DISCH changed to NEG_DISCH for HOL %

% Deleted: TFM 88.03.31                                                 %
%                                                                       %
% let DISCH_THEN ttac :tactic (asl,w) =                                 %
%     let ante,conc = dest_imp w ? failwith `DISCH_THEN` in             %
%     let gl,prf = ttac (ASSUME ante) (asl,conc) in                     %
%     gl, (NEG_DISCH ante) o prf;;                                      %

% Added: TFM 88.03.31  (bug fix)                                        %

let DISCH_THEN ttac :tactic (asl,w) =
    let ante,conc = dest_neg_imp w ? failwith `DISCH_THEN` in
    let gl,prf = ttac (ASSUME ante) (asl,conc) in
    gl, (if is_neg w then NEG_DISCH ante else DISCH ante) o prf;;

% --------------------------------------------------------------------- %
% If-and-only-iff elimination                    DELETED [TFM 91.01.20] %
%                                                                       %
%       C                                                               %
%    ==============       |- A1 <=> A2                                  %
%       C                                                               %
%       ===== ttac1 |-A1==>A2                                           %
%        ...                                                            %
%       ===== ttac2 |-A2==>A1                                           %
%        ...                                                            %
%                                                                       %
% let IFF_THEN2 (ttac1: thm_tactic) ttac2 iffth : tactic =              %
%  let th1,th2 = CONJ_PAIR (IFF_CONJ iffth) ? failwith `IFF_THEN2` in   %
%  ttac1 th1  THEN  ttac2 th2;;                                         %
%                                                                       %
% let IFF_THEN ttac = IFF_THEN2 ttac ttac;;                             %
% --------------------------------------------------------------------- %

%
Existential elimination

            B
    ==================   |- ?x. A(x)
            B
    ==================    ttac A(y)
           ...
explicit version for tactic programming
%

let X_CHOOSE_THEN y ttac xth :tactic =
    let x,body = dest_exists (concl xth) ? failwith `X_CHOOSE_THEN` in
    \(asl,w).
        let th = itlist ADD_ASSUM (hyp xth) (ASSUME (subst [y,x] body)) in
        let gl,prf = ttac th (asl,w) in
        gl, (CHOOSE (y, xth)) o prf;;

% chooses a variant for the user %

let CHOOSE_THEN ttac xth :tactic =
    let x,body = dest_exists (concl xth) ? failwith `CHOOSE_THEN` in
    \(asl,w).
     let y = variant ((thm_frees xth) @ (freesl (w.asl))) x in
     X_CHOOSE_THEN y ttac xth (asl,w);;

%Cases tactics%

%for a generalized disjunction  |-(?xl1.B1(xl1))  \/...\/  (?xln.Bn(xln))
where the xl1...xln are vectors of zero or more variables,
and the variables in each of yl1...yln have the same types as the
corresponding xli do

                        A
=============================================
   A                                    A
======= ttac1 |-B1(yl1)     ...      ======= ttacn |-Bn(yln)
  ...                                  ...
%

let X_CASES_THENL varsl ttacl =
    DISJ_CASES_THENL
       (map (\(vars,ttac). EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
        (varsl com ttacl));;

%needed??? = X_CASES_THENL varsl (map (K ttac) varsl) %

let X_CASES_THEN varsl ttac =
    DISJ_CASES_THENL
       (map (\vars. EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);;

%Version that chooses the y's as variants of the x's%

let CASES_THENL ttacl =
    DISJ_CASES_THENL (map (REPEAT_TCL CHOOSE_THEN) ttacl);;

%Tactical to strip off ONE disjunction, conjunction, or existential%

let STRIP_THM_THEN =
    FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN; CHOOSE_THEN];;
