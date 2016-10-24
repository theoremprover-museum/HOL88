% FILE		: start_groups.ml					%
% DESCRIPTION   : defines a collection of general purpose functions,	%
%                 rules, and tactics which are used throughout this	%
%                 library entry and the library entry, integer.		%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.20						%
%									%
%-----------------------------------------------------------------------%


% The four funtions listed below, each with prefix "include", load and  %
% bind to names with which they were stored the definitions, axioms,    %
% etc. of the named theory.						%

let include_definitions thy =
 (map
   ((\name.autoload_theory (`definition`,thy,name)) o fst)
   (definitions thy);());;

let include_axioms thy =
 (map
   ((\name.autoload_theory (`axiom`,thy,name)) o fst)
   (axioms thy);());;

let include_theorems thy =
 (map
   ((\name.autoload_theory (`theorem`,thy,name)) o fst)
   (theorems thy);());;

let include_theory thy=(include_definitions thy);(include_axioms thy);
     (include_theorems thy);;


% The following function is like expand, except that it fails if the    %
% tactic is not valid.  It is extremely inefficient, and should only    %
% be used for debugging purposes					%

let check_expand (tactic:tactic) =
  if check_valid (top_goal()) (tactic (top_goal()))
  then expand tactic
  else failwith `Invalid tactic`;;


% general purpose functions %

let cont l1 l2 = itlist (\x.\y.(x & y)) 
    (map (\x.(exists (\y.(aconv x y))l2)) l1) true;;

letrec zip fun_list =
 (fun []. (if null fun_list then [] else fail) 
   |  (h.t) . (((hd fun_list) h).(zip (tl fun_list) t))) ?failwith `zip`;;

ml_curried_infix `and_then`;;
let x and_then f = f x;;


%The following are derived proof rules and tactics which I found useful
 in developing group theory and the integers.%

%proof rules%

%AUTO_SPEC : term -> thm -> thm   (term = t)
(Automatically tries to instantiate the type of x to that of t)

    A |- !x.u
------------------  
    A |- u[t/x]
%

let AUTO_SPEC thisterm theorem =
(let types = snd(match (fst(dest_forall(concl(theorem)))) thisterm) in
  SPEC thisterm (INST_TYPE types theorem) )?failwith `AUTO_SPEC`;;


%AUTO_SPECL : term_list -> thm -> thm  (term_list = [t1;...;tn])

   A |- !x1 ... xn. t(x1,...,xn)
-----------------------------------
     A |- t(t1,...,tn)
%

let AUTO_SPECL = rev_itlist AUTO_SPEC;;


% EQF_INTRO : thm -> thm

    A |- ~t
  ------------
   A |- t = F
%

let EQF_INTRO (thisthm:thm) =
(EQ_MP
  (SYM(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC(dest_neg(concl(thisthm)))
    EQ_CLAUSES)))))
  thisthm
 )? failwith `EQF_INTRO`;;


%FALSITY_INTRO : thm -> thm -> thm

 A1 |- t  A2 |- ~t            A1 |- ~t  A2 |- t
--------------------    or   --------------------
   A1 u A2 |- F                 A1 u A2 |- F
%

let FALSITY_INTRO (thm1:thm) (thm2:thm)=
(let P1,P2=
  if is_neg(concl(thm2)) & (concl(thm1))=(dest_neg(concl thm2))
  then thm1,thm2
  else thm2,thm1  in
 MP (SUBST
  [((BETA_CONV "^(rand(concl(NOT_DEF)))^(concl(P1))"),"X:bool")] "X:bool"
            (SUBST[(NOT_DEF,"f:bool->bool")]
   "(f:bool->bool)^(concl(P1))" P2)) P1
)?failwith `FALSITY_INTRO`;;


let NORMALIZE rewrite_list thm = REWRITE_RULE rewrite_list (BETA_RULE thm);;


% STRONG_INST_TY_TERM and STRONG_INST are like INST_TY_TERM and INST,   %
% except that they instantiate free variables in the hypotheses, rather %
% than failing.	  (Definitions replaced by ELG 89.9.12)			%

letrec COUNT_UNDISCH n thm =
 if n = 0 then thm else COUNT_UNDISCH (n -1) (UNDISCH thm);;

let STRONG_INST_TY_TERM (inst_list,inst_ty_list) thm =
  let n = (length (hyp thm))
   and (value_list,var_list) = split inst_list in
   COUNT_UNDISCH n
    (SPECL value_list
     (GENL var_list (INST_TYPE inst_ty_list (DISCH_ALL thm))));;

let STRONG_INST inst_list thm =
  let n = (length (hyp thm))
   and (value_list,var_list) = split inst_list in
   COUNT_UNDISCH n (SPECL value_list (GENL var_list (DISCH_ALL thm)));;

%let STRONG_INST_TY_TERM (inst_list,inst_ty_list) thm =                      %
%  let n = (length (hyp thm)) in                                             %
%   COUNT_UNDISCH n (INST_TY_TERM (inst_list,inst_ty_list) (DISCH_ALL thm));;%

%let STRONG_INST inst_list thm =                                             %
%  let n = (length (hyp thm)) in                                             %
%   COUNT_UNDISCH n (INST inst_list (DISCH_ALL thm));;                       %


let MATCH_TERM_SUBS_RULE thm tm =
  set_fail_prefix `MATCH_TERM_SUBS_RULE`
  (let strip_thm = hd (IMP_CANON thm) in
   SUBS [(STRONG_INST_TY_TERM (match (lhs(concl strip_thm)) tm) strip_thm)]);;

%tactics%

%SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A;t] t1    [A] t
%

let SUPPOSE_TAC thisterm thisgoal =
(if type_of thisterm = ":bool"
 then [((thisterm.(fst thisgoal)),(snd thisgoal));((fst thisgoal),thisterm)],
      (\[goalthm;termthm].MP (DISCH thisterm goalthm) termthm)
 else fail)?failwith `SUPPOSE_TAC`;;


%REV_SUPPOSE_TAC : term -> tactic  (term = t)

            [A] t1
    =======================
       [A] t    [A;t] t1
%

let REV_SUPPOSE_TAC thisterm thisgoal =
(if type_of thisterm = ":bool"
 then [((fst thisgoal),thisterm);((thisterm.(fst thisgoal)),(snd thisgoal))],
      (\[termthm;goalthm].MP (DISCH thisterm goalthm) termthm)
 else fail)?failwith `REV_SUPPOSE_TAC`;;


% ADD_ASSUMS_THEN : term list -> tactic -> tactic                       %
%                                                                       %
% For adding assumptions to the goal to be used by the given tactic.    %
% Returns the result of applying the tactic to the augmented goal,      %
% together with a new subgoal for each new assumption added.            %

letrec ADD_ASSUMS_THEN asmlist tactic (asms,goal) =
 if null asmlist then tactic  (asms,goal) else
 if (exists (aconv (hd asmlist)) asms)
 then (ADD_ASSUMS_THEN (tl asmlist) tactic (asms,goal))
 else
  ((SUPPOSE_TAC (hd asmlist)) THENL
   [(ADD_ASSUMS_THEN (tl asmlist) tactic);ALL_TAC])
  (asms,goal);;

% ADD_STRIP_ASSUMS_THEN : term list -> tactic -> tactic                 %
%                                                                       %
% Like ADD_ASSUMS_THEN except it srtips the new assumptions before      %
% adding them to the assumptions.                                       %

letrec ADD_STRIP_ASSUMS_THEN asmlist tactic (asms,goal) =
 if null asmlist then tactic  (asms,goal) else
 if (exists (aconv (hd asmlist)) asms)
 then (ADD_STRIP_ASSUMS_THEN (tl asmlist) tactic (asms,goal))
 else
  ((SUPPOSE_TAC (hd asmlist)) THENL
   [((POP_ASSUM STRIP_ASSUME_TAC) THEN
     (ADD_STRIP_ASSUMS_THEN (tl asmlist) tactic));
    ALL_TAC])
  (asms,goal);;


% use_thm : thm -> (thm -> tactic) -> tactic                            %
%                                                                       %
% For adding the hypotheses of a theorem to the assumptions fo a goal   %
% before applying the tactic resulting from applying a thm_tactic to    %
% the given theorem.                                                    %

let use_thm thm tactic =
 ADD_STRIP_ASSUMS_THEN (hyp thm) (tactic thm);;


let NEW_SUBST1_TAC thm = set_fail_prefix `NEW_SUBST1_TAC`
  (use_thm thm SUBST1_TAC);;

let SUBST_MATCH_TAC thm =
  set_fail_prefix `SUBST_MATCH_TAC`
  \(asl,gl).
     (let strip_thm = hd (IMP_CANON thm) in
      let subst_thm =
        STRONG_INST_TY_TERM (find_match (lhs(concl strip_thm)) gl) strip_thm in
      NEW_SUBST1_TAC subst_thm (asl,gl));;


let MATCH_TERM_SUBST_TAC thm tm =
  set_fail_prefix `MATCH_TERM_SUBST_TAC`
  \(asl,gl).
     (let strip_thm = hd (IMP_CANON thm) in
      let subst_thm =
        STRONG_INST_TY_TERM (match (lhs(concl strip_thm)) tm) strip_thm in
      NEW_SUBST1_TAC subst_thm (asl,gl));;


letrec ASSUME_LIST_TAC thmlist (asms,gl)=
 let more_asms = (flat (map hyp thmlist)) in
 ADD_ASSUMS_THEN more_asms
  (itlist
    (\thm tac.(if ((exists (aconv (concl thm)) asms) or
                   (exists (aconv (concl thm)) more_asms))
               then ALL_TAC
               else (ASSUME_TAC thm) THEN tac))
    thmlist
    ALL_TAC)
  (asms,gl);;


% SELECT_TAC : term -> tactic   ( term = @x.P(x) )

    [A] P[@x.P(x)]
======================
     [A] ?x.P(x)
%

let SELECT_TAC (thisterm:term) (thisgoal:goal) =
(let t1,t2=dest_select thisterm in
 if (snd thisgoal)= subst[(thisterm,t1)]t2
 then [((fst thisgoal),(mk_exists (t1,t2)))], (\[thm].(SELECT_RULE thm))
 else fail
)?failwith `SELECT_TAC`;;


%ASM_CONJ1_TAC : tactic

     [A] T1 /\ T2
======================
  [A] T1   [A;T1] T2
%

let ASM_CONJ1_TAC (asl,goal) =
 if is_conj goal
 then ((REV_SUPPOSE_TAC (rand(rator goal)) THENL
  [ALL_TAC;(CONJ_TAC THENL [(ACCEPT_TAC(ASSUME (rand(rator goal))));ALL_TAC])])
   (asl,goal))
  else failwith `ASM_CONJ1_TAC failed; goal not a conjuct.`;;

%ASM_CONJ2_TAC : tactic

     [A] T1 /\ T2
======================
  [A;T2] T1   [A] T2
%

let ASM_CONJ2_TAC (asl,goal) =
 if is_conj goal
 then ((SUPPOSE_TAC (rand goal)) THENL
  [(CONJ_TAC THENL 
    [ALL_TAC;(ACCEPT_TAC(ASSUME (rand goal)))]); ALL_TAC]) (asl,goal)
  else failwith `ASM_CONJ2_TAC failed; goal not a conjuct.`;;


% MP_IMP_TAC : thm -> tactic  ( thm = [A1] |- t2 ==> t1 )

      [A] t1
    ==========
      [A] t2

%

let MP_IMP_TAC thisthm (thisgoal:goal)=
 if (is_imp(concl(thisthm)))
 then
  (if (aconv (snd(dest_imp(concl(thisthm)))) (snd thisgoal))
   then (use_thm thisthm
     (\imp_thm.(\goal.(
       [(fst goal),(fst(dest_imp(concl imp_thm)))],
       (\[thm].(MP imp_thm thm)))))) thisgoal
    else failwith `MP_IMP_TAC failed; theorem doesn't imply goal.`)
 else failwith `MP_IMP_TAC failed; theorem is not an implication.`;;


% MATCH_THM_TAC : (term -> term) -> thm_tactic -> thm_tactic            %
%                                                                       %
% Used to create a version of a theorem tactic that will do matching   %
% against the given theorem.                                            %

let MATCH_THM_TAC pat_fun thm_tac =
  let sub_tac thm (asl,gl) =
    let inst_thm = STRONG_INST_TY_TERM (match (pat_fun (concl thm)) gl) thm in
    ((thm_tac inst_thm) ORELSE (thm_tac (BETA_RULE inst_thm))) (asl,gl) in
  \thm. ((REPEAT GEN_TAC) THEN (sub_tac (SPEC_ALL thm)));;


% NEW_MATCH_ACCEPT_TAC : thm -> tactic                                  %
%                                                                       %
% Same as MATCH_ACCEPT_TAC, except that if the instantiated version of  %
% the theorem has hypotheses that are not among the goal assumptions,   %
% then it creates new subgoals for these, rather than failing.          %

let NEW_MATCH_ACCEPT_TAC =
  set_fail_prefix `NEW_MATCH_ACCEPT_TAC` (MATCH_THM_TAC (\x.x) 
   (\thm. (use_thm thm ACCEPT_TAC)));;


% MATCH_MP_IMP_TAC : thm -> tactic  ( thm = [A1] |- t2 ==> t1 )

      [A] t1'
    ==========
      [A] t2'

 where t2' ==> t1' is an instance of t2 ==> t1
%

let MATCH_MP_IMP_TAC =
  set_fail_prefix `MATCH_MP_IMP_TAC`
   (MATCH_THM_TAC (\tm.(snd(dest_imp tm)))MP_IMP_TAC);;


% REDUCE_TAC : thm_list -> tactic                                        %
% Reduces a goal by stripping and using modus ponens and any theorem     %
% which is an implication and whose implication conclusion matches the   %
% goal statement.  It also solves those subgoals which match any of the  %
% given theorems, or which are included among the assumptions.           %
%									 %

let REDUCE_TAC thm_list =
  let new_thm_list = map UNDISCH_ALL (flat (map IMP_CANON thm_list)) in
  let tac_list = map 
   (\thm. (NEW_MATCH_ACCEPT_TAC thm) ORELSE (MATCH_MP_IMP_TAC thm))
   new_thm_list in
  letrec core_reduce_tac gl=
   ((FIRST_ASSUM ACCEPT_TAC) ORELSE
    ((REPEAT STRIP_TAC) THEN
     ((FIRST_ASSUM ACCEPT_TAC) ORELSE
      ((\gl.tryfind (\f. f gl) tac_list) THEN
       core_reduce_tac) ORELSE
      ALL_TAC))) gl in
  core_reduce_tac;;


% EXT_TAC : term -> tactic  ( term = x )

         [A] t1 = t2
    =======================
      [A] !x. t1 x = t2 x

 x should not be free in t1, t2, or [A].
%

let EXT_TAC (thisterm:term) (thisgoal:goal) =
 if is_eq(snd(thisgoal))
 then
  if (fst(dest_type(type_of(rand(snd(thisgoal))))))=`fun`
  then
   if (type_of thisterm)=
      (hd(snd(dest_type(type_of(rand(snd(thisgoal)))))))
   then
    if (is_var thisterm)
    then
     if (not(free_in thisterm (snd thisgoal)))
     then ([((fst(thisgoal)), mk_forall(thisterm,
                    (mk_eq((mk_comb((rand(rator(snd(thisgoal)))),thisterm)),
                          (mk_comb((rand(snd(thisgoal))),thisterm))))))],
      (\[thm].(EXT thm)))
     else failwith `EXT_TAC failed; term free in goal.`
    else failwith `EXT_TAC failed; term not a varialbe.`
   else failwith `EXT_TAC failed; term type not function domain type.`
  else failwith `EXT_TAC failed; terms in goal are not functions.`
 else failwith `EXT_TAC failed; goal is not an equation.`;;

% AP_THM_TAC : tactic

   [A] t1(t) = t2(t)
=======================
     [A] t1 = t2
%

let AP_THM_TAC (thisgoal:goal) =
(let (firstterm,secondterm)=(dest_eq(snd(thisgoal))) in
 if (aconv (snd(dest_comb(firstterm))) (snd(dest_comb(secondterm))))
 then
  ([(fst thisgoal),
    (mk_eq((fst(dest_comb(firstterm))),(fst(dest_comb(secondterm)))))],
   (\[thm].(AP_THM thm (fst(dest_comb(firstterm))))))
 else fail
)?failwith `AP_THM_TAC`;;


% The tactic AP_TERM_TAC now exists as part of the system.
! 
!  AP_TERM_TAC : tactic
! 
!    [A] t(t1) = t(t2)
! =======================
!      [A] t1 = t2
! 
! 
! let AP_TERM_TAC (thisgoal:goal) =
! (let (firstterm,secondterm)=(dest_eq(snd(thisgoal))) in
!   ([(fst thisgoal),
!     (mk_eq((snd(dest_comb(firstterm))),(snd(dest_comb(secondterm)))))],
!    (\[thm].(AP_TERM (fst(dest_comb(firstterm))) thm)))
! )?failwith `AP_TERM_TAC`;;
%


%NEW_COND_CASES_TAC : tactic

      [A] t[p=>u|v]
===========================
 [A;p] t[u]    [A;~p] t[v]
%


let NEW_COND_CASES_TAC (thisgoal:goal)=
(let is_good_cond tm = not(is_const(fst(dest_cond tm))) ? false in
 let cond =
  fst(dest_cond
   (find_term (\tm. is_good_cond tm & free_in tm (snd thisgoal)) 
    (snd thisgoal))) in
 DISJ_CASES_THEN2
 (\th.((ASSUME_TAC th) THEN
  (REPEAT (\goal:goal.(
   let t,u =
    (snd(dest_cond
     (find_term(\tm.(is_cond tm)&
        (aconv (fst(dest_cond tm)) cond))(snd goal))))
   in
   let v = genvar ":bool" in
   let thm = SUBST [((SYM(EQT_INTRO th)),v)] (mk_eq ((mk_cond (v,t,u)),t))
    (CONJUNCT1 (AUTO_SPECL [t;u] COND_CLAUSES))
   in
   (SUBST1_TAC thm goal) )))))
 (\th.((ASSUME_TAC th) THEN
  (REPEAT (\goal:goal.(
   let t,u =
    (snd(dest_cond
     (find_term(\tm.(is_cond tm)&
        (aconv (fst(dest_cond tm)) cond))(snd goal))))
   in
   let v = genvar ":bool" in
   let thm = SUBST [((SYM(EQF_INTRO th)),v)] (mk_eq ((mk_cond (v,t,u)),u))
    (CONJUNCT2 (AUTO_SPECL [t;u] COND_CLAUSES))
   in
   (SUBST1_TAC thm goal) )))))
  (SPEC cond EXCLUDED_MIDDLE) thisgoal
)?failwith `NEW_COND_CASES_TAC`;;


%FILTER_COND_CASES_TAC : term -> tactic  (term = p)

      [A] t[p=>u|v]
==========================
 [A;p] t[u]   [A;~p] t[v]
%

let FILTER_COND_CASES_TAC (cond:term) (thisgoal:goal)=
(DISJ_CASES_THEN2
 (\th.((ASSUME_TAC th) THEN
  (REPEAT (\goal:goal.(
   let t,u =
    (snd(dest_cond
     (find_term(\tm.(is_cond tm)&
        (aconv (fst(dest_cond tm)) cond))(snd goal))))
   in
   let v = genvar ":bool" in
   let thm = SUBST [((SYM(EQT_INTRO th)),v)] (mk_eq ((mk_cond (v,t,u)),t))
    (CONJUNCT1 (AUTO_SPECL [t;u] COND_CLAUSES))
   in
   (SUBST1_TAC thm goal) )))))
 (\th.((ASSUME_TAC th) THEN
  (REPEAT (\goal:goal.(
   let t,u =
    (snd(dest_cond
     (find_term(\tm.(is_cond tm)&
         (aconv (fst(dest_cond tm)) cond))(snd goal))))
   in
   let v = genvar ":bool" in
   let thm = SUBST [((SYM(EQF_INTRO th)),v)] (mk_eq ((mk_cond (v,t,u)),u))
    (CONJUNCT2 (AUTO_SPECL [t;u] COND_CLAUSES))
   in
   (SUBST1_TAC thm goal) )))))
  (SPEC cond EXCLUDED_MIDDLE) thisgoal
)?failwith `FILTER_COND_CASES_TAC`;;

