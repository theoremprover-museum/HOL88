%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        tactics.ml                                            %
%                                                                             %
%     DESCRIPTION:      tactics inverting the inference rules, and other basic%
%                       tactics                                               %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml,     %
%                       tacont.ml                                             %
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
%     REVISION HISTORY: (none)                                                %
%=============================================================================%


% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml,tacont.ml	%
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`;
		    loadf `ml/hol-rule`;
		    loadf `ml/hol-drule`;
		    loadf `ml/drul`;
		    loadf `ml/tacticals`;
		    loadf `ml/tacont`);;

%
Accepts a theorem that satisfies the goal

	A
    =========	ACCEPT_TAC "|-A"
	-
%

% --------------------------------------------------------------------- %
% Revised to return a theorem alpha-identical to goal.  [TFM 93.07.22]  %
% OLD CODE:                                                             %
%                                                                       %
% let ACCEPT_TAC th :tactic (asl,w) =                                   %
%     if aconv (concl th) w then [], \[].th                             %
%     else failwith `ACCEPT_TAC`;;                                      %
% --------------------------------------------------------------------- %

let ACCEPT_TAC th :tactic (asl,w) =
    if aconv (concl th) w then 
       [], \[]. EQ_MP (ALPHA (concl th) w) th
    else failwith `ACCEPT_TAC`;;

% --------------------------------------------------------------------- %
% DISCARD_TAC: checks that a theorem is useless, then ignores it.	%
% Revised: 90.06.15 TFM.						%
% --------------------------------------------------------------------- %

let DISCARD_TAC : thm -> tactic = 
    let truth = mk_const(`T`,mk_type(`bool`,[])) in		  % "T" %
    \th. \(asl,w). if exists (aconv (concl th)) (truth . asl)
                      then ALL_TAC (asl,w)
                      else failwith `DISCARD_TAC`;;

%
Contradiction rule

	 A
    ===========  CONTR_TAC "|- FALSITY ()"
	 -
%

let CONTR_TAC cth :tactic (asl,w) =
    (let th = CONTR w cth in [], \[].th)
    ? failwith `CONTR_TAC`;;

%
Put a theorem onto the assumption list.
Note:  since an assumption B denotes a theorem B|-B, 
you cannot instantiate types or variables in assumptions.

	A
   ===========	|- B
      [B] A
%

let ASSUME_TAC bth :tactic (asl,w) =
      [ ((concl bth) . asl) , w],
      \[th]. PROVE_HYP bth th;;

%"Freeze" a theorem to prevent instantiation 

	A
   ===========	ttac "B|-B"
       ...
%

let FREEZE_THEN ttac bth :tactic =
    \g. let gl,prf = ttac (ASSUME (concl bth)) g in
	gl, PROVE_HYP bth o prf;;

%
Conjunction introduction

	A /\ B
    ===============
      A        B
%

let CONJ_TAC :tactic (asl,w) =
   (let l,r = dest_conj w in
    [(asl,l); (asl,r)], \[th1;th2]. CONJ th1 th2
   ) ? failwith `CONJ_TAC`;;



%
Disjunction introduction

	A \/ B
    ==============
	  A
%

let DISJ1_TAC : tactic (asl,w) =
   (let a,b = dest_disj w in  [(asl,a)], \[tha]. DISJ1 tha b)
   ? failwith `DISJ1_TAC`;;


%	A \/ B
    ==============
	  B
%

let DISJ2_TAC :tactic (asl,w) =
   (let a,b = dest_disj w in  [(asl,b)], \[thb]. DISJ2 a thb)
   ? failwith `DISJ2_TAC`;;

%Implication elimination

	   A
    ================  |- B
        B ==> A   
%

let MP_TAC thb :tactic (asl,wa) =
    [asl, mk_imp(concl thb, wa)], \[thimp]. MP thimp thb;;

% --------------------------------------------------------------------- %
% If-and-only-if introduction			 DELETED [TFM 91.01.20]	%
% 									%
%	A <=> B 							%
%    ================ 							%
%    A==>B      B==>A 							%
%									%
% let IFF_TAC : tactic (asl,w) = 					%
%   (let a,b = dest_iff w in 						%
%    [(asl, "^a==>^b"); (asl, "^b==>^a")], 				%
%    \[thab;thba]. CONJ_IFF (CONJ thab thba) 				%
%   ) ? failwith `IFF_TAC`;; 						%
% --------------------------------------------------------------------- %

%
           t1 = t2
  =========================
  t1 ==> t2       t2 ==> t1
%

% MJCG 17/11/88 for HOL88 
  Recoded to use mk_imp to eliminate mk_comb failure 
  and hence spurious error messages %

let EQ_TAC:tactic (asl,t) =
 (let t1,t2 = dest_eq t
  in
  ([(asl, mk_imp(t1,t2)); (asl, mk_imp(t2,t1))],
   \[th1;th2]. IMP_ANTISYM_RULE th1 th2)
   ) ? failwith `EQ_TAC`;;

% Universal quantifier							%

%	!x.A(x)
    ==============
	 A(x')

 explicit version for tactic programming;  proof fails if x' is free in hyps

%

% let X_GEN_TAC x' :tactic (asl,w) =			%
%   (let x,body = dest_forall w in			%
%    [ (asl, subst[x',x]body) ], (\[th]. GEN x' th) 	%
%   ) ? failwith `X_GEN_TAC`;;				%

% T. Melham. X_GEN_TAC rewritten 88.09.17				%
%									%
% 1)  X_GEN_TAC x'    now fails if x' is not a variable.		%
%									%
% 2) rewritten so that the proof yields the same quantified var as the  %
%    goal.								%
%									%
%  let X_GEN_TAC x' :tactic =						%
%   if not(is_var x') then failwith `X_GEN_TAC` else			%
%   \(asl,w).((let x,body = dest_forall w in				%
%               [(asl,subst[x',x]body)],				%
%                (\[th]. GEN x (INST [(x,x')] th)))			%
%              ? failwith `X_GEN_TAC`);;				%

% Bugfix for HOL88.1.05, MJCG, 4 April 1989				%
% Instantiation before GEN replaced by alpha-conversion after it to 	%
% prevent spurious failures due to bound variable problems when 	%
% quantified variable is free in assumptions.				%
% Optimization for the x=x' case added.					%

let X_GEN_TAC x' :tactic =		
 if not(is_var x') 
  then failwith `X_GEN_TAC` 
  else
   \(asl,w).((let x,body = dest_forall w 
              in
              if x=x'
               then
                ([(asl,body)], \[th]. GEN x' th)
               else
                ([(asl,subst[x',x]body)],
                  \[th]. let th' = GEN x' th
                         in
                         EQ_MP (GEN_ALPHA_CONV x (concl th')) th'))
             ? failwith `X_GEN_TAC`);;


% chooses a variant for the user;  for interactive proof		%
% informative error string added			[TFM 90.06.02]  %

let GEN_TAC :tactic (A,g) =
    let x,b = dest_forall g ? 
              failwith `GEN_TAC: goal not universally quantified`  in
    X_GEN_TAC (variant (freesl(g.A)) x) (A,g);;

%	A(t)
    ============  t,x
       !x.A(x)

example of use:  generalizing a goal before attempting an inductive proof
as with Boyer and Moore

valid only if x is not free in A(UU), but this test is slow
%

let SPEC_TAC (t,x) :tactic (asl,w) =
    ([ asl, mk_forall(x, subst [x,t] w)], \[th]. SPEC t th)
    ? failwith `SPEC_TAC` ;;


%
Existential introduction

	?x.A(x)
    ==============   t
	 A(t)
%

let EXISTS_TAC t :tactic (asl,w) =
   (let x,body = dest_exists w in
    [asl, subst [t,x]body], \[th]. EXISTS (w,t) th
   ) ? failwith `EXISTS_TAC` ;;

%Substitution%

%
These substitute in the goal;  thus they DO NOT invert the rules SUBS and
SUBS_OCCS, despite superficial similarities.  In fact, SUBS and SUBS_OCCS
are not invertible;  only SUBST is.
%

let GSUBST_TAC substfn ths :tactic (asl,w) =
     let ls,rs = split (map (dest_eq o concl) ths) in
     let vars = map (genvar o type_of) ls in
     let base = substfn (combine(vars,ls)) w   in
     [ asl, subst (combine(rs,vars)) base],
     \[th]. SUBST (combine(map SYM ths, vars)) base th  ;;

%	A(ti)
    ==============   |- ti == ui
	A(ui)
%

let SUBST_TAC ths =
  set_fail_prefix `SUBST_TAC` (GSUBST_TAC subst ths);;


let SUBST_OCCS_TAC nlths =
  set_fail_prefix `SUBST_OCCS_TAC`
    (let nll,ths = split nlths in  GSUBST_TAC (subst_occs nll) ths);;


%	 A(t)
    ===============   |- t==u
	 A(u)

works nicely with tacticals 
%

let SUBST1_TAC rthm = SUBST_TAC [rthm];;

%Map an inference rule over the assumptions, replacing them%

let RULE_ASSUM_TAC rule =
    POP_ASSUM_LIST (\asl. MAP_EVERY ASSUME_TAC (rev (map rule asl)));;

%Substitute throughout the goal and its assumptions%

let SUBST_ALL_TAC rth =
    SUBST1_TAC rth  THEN
    RULE_ASSUM_TAC (SUBS [rth]);;

let CHECK_ASSUME_TAC gth = 
    FIRST [CONTR_TAC gth;  ACCEPT_TAC gth;
	  DISCARD_TAC gth; ASSUME_TAC gth];;

let STRIP_ASSUME_TAC =
    (REPEAT_TCL STRIP_THM_THEN) CHECK_ASSUME_TAC;;

%
given a theorem:

|- (?y1. (x=t1(y1)) /\ B1(x,y1))  \/ ... \/  (?yn. (x=tn(yn)) /\ Bn(x,yn))

where each y is a vector of zero or more variables
and each Bi is a conjunction (Ci1 /\ ... /\ Cin)

		        A(x)
    ===============================================
    [Ci1(tm,y1')] A(t1)  . . .  [Cin(tm,yn')] A(tn)

such definitions specify a structure as having n different possible
constructions (the ti) from subcomponents (the yi) that satisfy various 
constraints (the Cij)
%

let STRUCT_CASES_TAC =
    REPEAT_TCL STRIP_THM_THEN
     (\th. SUBST1_TAC th  ORELSE  ASSUME_TAC th);;



% --------------------------------------------------------------------- %
% COND_CASES_TAC: tactic for doing a case split on the condition p	%
%                 in a conditional (p => u | v).			%
%									%
% Find a conditional "p => u | v" that is free in the goal and whose 	%
% condition p is not a constant. Perform a case split on the condition. %
%                                                                       %
%									%
%	t[p=>u|v]							%
%    =================	 COND_CASES_TAC					%
%       {p}  t[u]							%
%      {~p}  t[v]							%
%									%
% 						[Revised: TFM 90.05.11] %
% --------------------------------------------------------------------- %

let COND_CASES_TAC :tactic =
    let is_good_cond tm =  not(is_const(fst(dest_cond tm))) ? false  in
    \(asl,w). let cond = find_term (\tm. is_good_cond tm & free_in tm w) w
                         ? failwith `COND_CASES_TAC` in
              let p,t,u = dest_cond cond in
	      let inst = INST_TYPE [type_of t, ":*"] COND_CLAUSES in
              let (ct,cf) = CONJ_PAIR (SPEC u (SPEC t inst)) in
              DISJ_CASES_THEN2
                 (\th. SUBST1_TAC (EQT_INTRO th) THEN 
		       SUBST1_TAC ct THEN ASSUME_TAC th)
                 (\th. SUBST1_TAC (EQF_INTRO th) THEN 
		       SUBST1_TAC cf THEN ASSUME_TAC th)
         	 (SPEC p EXCLUDED_MIDDLE)
                 (asl,w) ;;

%Cases on  |- p=T  \/  p=F %

let BOOL_CASES_TAC p = STRUCT_CASES_TAC (SPEC p BOOL_CASES_AX);;

%Strip one outer !, /\, ==> from the goal%

let STRIP_GOAL_THEN ttac =  FIRST [GEN_TAC; CONJ_TAC; DISCH_THEN ttac];;

% Like GEN_TAC but fails if the term equals the quantified variable %

let FILTER_GEN_TAC tm : tactic (asl,w) =
    if is_forall w & not (tm = fst(dest_forall w)) then 
	GEN_TAC (asl,w)
    else failwith `FILTER_GEN_TAC`;;

%Like DISCH_THEN but fails if the antecedent mentions the term%

let FILTER_DISCH_THEN ttac tm : tactic (asl,w) =
    if is_neg_imp w  &  not (free_in tm (fst(dest_neg_imp w))) then
	DISCH_THEN ttac (asl,w)
    else failwith `FILTER_DISCH_THEN`;;

%Like STRIP_THEN but preserves any part of the goal that mentions the term%

let FILTER_STRIP_THEN ttac tm =
    FIRST [
	FILTER_GEN_TAC tm;
	FILTER_DISCH_THEN ttac tm;
	CONJ_TAC];;

let DISCH_TAC = \g. DISCH_THEN ASSUME_TAC g ? failwith `DISCH_TAC`;;

let DISJ_CASES_TAC = DISJ_CASES_THEN ASSUME_TAC;;

let CHOOSE_TAC = CHOOSE_THEN ASSUME_TAC;;

let X_CHOOSE_TAC x = X_CHOOSE_THEN  x  ASSUME_TAC;;

let STRIP_TAC = 
    \g. STRIP_GOAL_THEN STRIP_ASSUME_TAC g ? failwith `STRIP_TAC`;;

let FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC;;

let FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC;;


% Cases on  |- t \/ ~t %

let ASM_CASES_TAC t = DISJ_CASES_TAC(SPEC t EXCLUDED_MIDDLE);;


% --------------------------------------------------------------------- %
% A tactic inverting REFL (from tfm).	 				%
%									%
%     A = A								%
% ==============							%
%									%
% Revised to work if lhs is alpha-equivalent to rhs      [TFM 91.02.02]	%
% Also revised to retain assumptions.					%
% --------------------------------------------------------------------- %

let REFL_TAC:tactic (asl,g) =
    let (l,r) = dest_eq g ? failwith `REFL_TAC: not an equation` in
    let asms = itlist ADD_ASSUM asl in 
    if (l=r) then [], K (asms (REFL l)) else
    if (aconv l r) then [], K (asms (ALPHA l r)) else
       failwith `REFL_TAC: lhs and rhs not alpha-equivalent`;;

%
UNDISCH_TAC - tactic, moves one of the assumptions as LHS of an implication
                      to the goal (fails if named assumption not in
                      assumptions)

UNDISCH_TAC: term -> tactic
              tm

         [ t1;t2;...;tm;tn;...tz ]  t
   ======================================
        [ t1;t2;...;tn;...tz ]  tm ==> t
%

let UNDISCH_TAC tm (asl,t) =
 if mem tm asl 
 then ([subtract asl [tm], mk_imp(tm,t)], UNDISCH o hd)
 else failwith `UNDISCH_TAC`;;

% --------------------------------------------------------------------- %
% AP_TERM_TAC: Strips a function application off the lhs and rhs of an	%
% equation.  If the function is not one-to-one, does not preserve 	%
% equivalence of the goal and subgoal.					%
%									%
%   f x = f y								%
% =============								%
%     x = y								%
%									%
% Added: TFM 88.03.31							%
% Revised: TFM 91.02.02							%
% --------------------------------------------------------------------- %

let AP_TERM_TAC:tactic (asl,gl) =
    let l,r = dest_eq gl ? failwith `AP_TERM_TAC: not an equation` in
    let g,x = dest_comb l ? failwith `AP_TERM_TAC: lhs not an application` in
    let f,y = dest_comb r ? failwith `AP_TERM_TAC: rhs not an application` in
    if not(f=g) 
       then failwith `AP_TERM_TAC: functions on lhs and rhs differ` 
       else ([asl, mk_eq(x,y)], (AP_TERM f o hd));;


% --------------------------------------------------------------------- %
% AP_THM_TAC: inverts the AP_THM inference rule.			%
%									%
%   f x = g x								%
% =============								%
%     f = g								%
%									%
% Added: TFM 91.02.02							%
% --------------------------------------------------------------------- %

let AP_THM_TAC:tactic (asl,gl) =
    let l,r = dest_eq gl ? failwith `AP_THM_TAC: not an equation` in
    let g,x = dest_comb l ? failwith `AP_THM_TAC: lhs not an application` in
    let f,y = dest_comb r ? failwith `AP_THM_TAC: rhs not an application` in
    if not(x=y) 
       then failwith `AP_THM_TAC: arguments on lhs and rhs differ` 
       else ([asl, mk_eq(g,f)], (C AP_THM x o hd));;

% ===================================================================== %
% EXISTS_REFL_TAC 							%
%									%
% A, ?x1...xn. tm[t1'...tn'] = tm[x1....xn]				%
% -----------------------------------------				%
%		-							%
%									%
% Added: TFM 88.03.31							%
%									%
% Temporarily deleted, pending reimplementation.  The tactic should	%
% really unify lhs and rhs!				 [TFM 91.02.05] %
% ===================================================================== %
%									%
% let EXISTS_REFL_TAC (A,g) = 						%
%     (let v,(l,r) = (I # dest_eq)(strip_exists g) in			%
%      let m = (fst(match l r)) in					%
%((MAP_EVERY (\v. EXISTS_TAC (snd(assoc v m))) v) THEN			%
%   REFL_TAC) (A,g)) ? 							%
%      failwith `EXISTS_REFL_TAC`;;					%
% --------------------------------------------------------------------- %
