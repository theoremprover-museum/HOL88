% --------------------------------------------------------------------- %
%       Copyright (c) Jim Grundy 1992                                   %
%       All rights reserved                                             %
%                                                                       %
% Jim Grundy, hereafter referred to as `the Author', retains the        %
% copyright and all other legal rights to the Software contained in     %
% this file, hereafter referred to as `the Software'.                   %
%                                                                       %
% The Software is made available free of charge on an `as is' basis.    %
% No guarantee, either express or implied, of maintenance, reliability, %
% merchantability or suitability for any purpose is made by the Author. %
%                                                                       %
% The user is granted the right to make personal or internal use        %
% of the Software provided that both:                                   %
% 1. The Software is not used for commercial gain.                      %
% 2. The user shall not hold the Author liable for any consequences     %
%    arising from use of the Software.                                  %
%                                                                       %
% The user is granted the right to further distribute the Software      %
% provided that both:                                                   %
% 1. The Software and this statement of rights is not modified.         %
% 2. The Software does not form part or the whole of a system           %
%    distributed for commercial gain.                                   %
%                                                                       %
% The user is granted the right to modify the Software for personal or  %
% internal use provided that all of the following conditions are        %
% observed:                                                             %
% 1. The user does not distribute the modified software.                %
% 2. The modified software is not used for commercial gain.             %
% 3. The Author retains all rights to the modified software.            %
%                                                                       %
% Anyone seeking a licence to use this software for commercial purposes %
% is invited to contact the Author.                                     %
% --------------------------------------------------------------------- %
%============================================================================%
% CONTENTS: miscelaneous HOL utility functions                               %
%============================================================================%
%$Id: hol_ext.ml,v 3.1 1993/12/07 14:15:19 jg Exp $%

% goal_frees gl = the set of variables which occur free in gl.              %
let goal_frees (as, cn) = (freesl as) @ (frees cn);;

% (term_mem tm tms) = tm mem tms.                                           %
let term_mem tm tms = exists (\t. aconv t tm) tms;;

% (term_subset l1 l2) = (!x. (x mem l1) ==> (x mem l2))                     %
let term_subset (l1 : term list) (l2 : term list) = 
    forall (\t. exists (aconv t) l2) l1;;   

% (term_setify tl) = the subset of tl with all the distinct terms.          %
letrec term_setify =
    fun []      . []
     |  (h.t)   . h.(term_setify (filter (\a.not (aconv h a)) t));;

% (term_intersect l1 l2) = l1 intersection l2.                              %
let term_intersect l1 l2 = 
    term_setify (filter (\t. exists (aconv t) l2) l1);;

% (term_union l1 l2) = l1 union l2.                                         %
let term_union l1 l2 = term_setify (l1 @ l2);;

% better_thm t1 t2 = true, iff t1 t2 share the same conclusion and t1's     %
%   hyptheses are a subset of those of t2.                                  %
let better_thm t1 t2 =  (aconv (concl t1) (concl t2)) &
                        (term_subset (hyp t1) (hyp t2));;

% better_goal c1 c2 = true, iff c1 c2 share the same conclusion and c1's    %
%   hypotheses are a subset of those of c2.                                 %
let better_goal c1 c2 = (aconv (snd c1) (snd c2)) &
                        (term_subset (fst c1) (fst c2));;

% (thm_subset l1 l2) = (!x. (x mem l1) ==> (x mem l2))                      %
let thm_subset (l1 : thm list) (l2 : thm list) = 
    forall (\t1. exists (\t2. better_thm t2 t1) l2) l1;;    

% Check to see if two theorem sets are equal.                               %
let  thm_set_equal l1 l2 = (thm_subset l1 l2) & (thm_subset l2 l1);;

% (goal_subset l1 l2) = (!x. (x mem l1) ==> (x mem l2))                     %
let goal_subset (l1 : goal list) (l2 : goal list) = 
    forall (\c1. exists (\c2. better_goal c2 c1) l2) l1;;   

% Check to see if two goal sets are equal.                                  %
let  goal_set_equal l1 l2 = (goal_subset l1 l2) & (goal_subset l2 l1);;

% Crush out all the redundant theorems in a set.                            %
letrec thm_setify = fun []  .   []
                    |  (h.t).   if (exists (\u.better_thm u h) t) then
                                    thm_setify t
                                else
                                    h.(thm_setify
                                        (filter (\u.not (better_thm h u)) t));;

% Crush out all the redundant conjectures in a set.                         %
letrec goal_setify = fun [] .   []
                    |  (h.t).   if (exists (\u.better_goal u h) t) then
                                    goal_setify t
                                else
                                    h.(goal_setify
                                        (filter (\u.not (better_goal h u)) t));;
                                        
% is_fun t = true, iff t is a function.                                     %
let is_fun tm =
    (not is_vartype (type_of tm)) &
    (let (name, _) = dest_type (type_of tm) in
        name = `fun`);;

% dom f = the domain of f                                                   %
let dom fn =
    let (name, ty._) = dest_type (type_of fn) in
        if name = `fun` then
            ty
        else
            failwith `dom`;;

% ran f = the range of f                                                    %
let ran fn =
    let (name, _.ty._) = dest_type (type_of fn) in
        if name = `fun` then
            ty
        else
            failwith `ran`;;

% (is_trueimp t) = true, iff t = "t ==> u".                                 %
let is_trueimp t =  (is_imp t) & (not (is_neg t));;

% (is_pmi t) = true, iff t = "t <== u".                                     %
let is_pmi t =  (is_comb t) &
                (is_comb (rator t)) &
                ((rator (rator t)) = "<==");;

% (dest_pmi "a ==> b") = ("a", "b")                                         %
let dest_pmi t =
    if is_pmi t then
         (rand (rator t), rand t)
    else
         failwith `dest_pmi`;;

% IMP_PMI_CONV "A ==> B" = (|- (A ==> B) = (B <== A))                      %
let IMP_PMI_CONV tm =
    let (a,b) = dest_imp tm in
    SYM (SPECL [b;a] PMI_DEF);;

%  (|- t ==> u)                                                             %
% --------------    IMP_PMI                                                 %
%  (|- u <== t)                                                             %
let IMP_PMI = CONV_RULE IMP_PMI_CONV;;

% PMI_IMP_CONV "A <== B" = (|- (A <== B) = (B ==> A))                       %
let PMI_IMP_CONV tm =
    let (a,b) = dest_pmi tm in
    SPECL [a;b] PMI_DEF;;

%  (|- u <== t)                                                             %
% --------------    PMI_IMP                                                 %
%  (|- t ==> u)                                                             %
let PMI_IMP = CONV_RULE PMI_IMP_CONV;;

%                                                                           %
% --------------    IMP_REFL "t"                                            %
%  (|- t ==> t)                                                             %
let IMP_REFL = DISCH_ALL o ASSUME;;

%                                                                           %
% --------------    PMI_REFL "t"                                            %
%  (|- t <== t)                                                             %
let PMI_REFL = IMP_PMI o IMP_REFL;;

%  (|- t <== u /\ u <== v)                                                  %
% -------------------------                                                 %
%       (|- t <== v)                                                        %
let PMI_TRANS t1 t2 = IMP_PMI (IMP_TRANS (PMI_IMP t2) (PMI_IMP t1));;

%       A |- t1 ==> t2                                                      %
% --------------------------  EXISTS_PMI "x"   [where x is not free in A]   %
%  A |- (?x.t1) ==> (?x.t2)                                                 %
let EXISTS_PMI x th = IMP_PMI (EXISTS_IMP x (PMI_IMP th));;

% Smashes a theorem into lots of little theorems.                           %
% SMASH is based on CONJUNCTS, but as well as smashing                      %
%   (H |- A1 /\ A2) into [(H |- A1); (H |- H2)],                            %
%   SMASH also smashes                                                      %
%   (H |- ~(A1 \/ A2) into [(H |- ~A1); (H |- ~A2)]                         %
%   and                                                                     %
%   (H |- ~(A ==> B) into [(H |- A); (H |- ~B)]                             %
%   and                                                                     %
%   (H |- ~(A <== B) into [(H |- ~A); (H |- B)]                             %
%   and                                                                     %
%   (H |- A => B | F) into [(H |- A); (H |- B)]                             %
begin_section smash_section;;
let DNEG_THM = CONJUNCT1 NOT_CLAUSES;;
let NOT_DISJ_THM = GENL ["t1:bool"; "t2:bool"]
              (CONJUNCT2 (SPEC_ALL DE_MORGAN_THM));;
let NOT_IMP_THM = prove ("!t1 t2. ~(t1 ==> t2) = t1 /\ ~t2",
             (REWRITE_TAC [IMP_DISJ_THM; NOT_DISJ_THM]));;
let NOT_PMI_THM = prove("!t1 t2. ~(t1 <== t2) = ~t1 /\ t2",
                    (REPEAT STRIP_TAC) THEN
                    (BOOL_CASES_TAC "t1:bool") THEN
                    (REWRITE_TAC [PMI_DEF]));;
let COND_F_THM = prove ("!t1 t2. (t1 => t2 | F) = (t1 /\ t2)", 
            (REPEAT STRIP_TAC) THEN
            (BOOL_CASES_TAC "t1:bool") THEN
            (REWRITE_TAC [COND_CLAUSES]));;

let SMASH =
    letrec  ((BREAK : thm -> thm list), (TWEAK : thm -> thm list)) =
                (
                    (\t:thm. flat (map TWEAK (CONJUNCTS t)))
                ,
                    (\t:thm. 
                        let c = concl t in
                        let negc = is_neg c in
                            if  (negc & (is_neg (rand c))) then
                BREAK (EQ_MP (SPEC (rand (rand c)) DNEG_THM) t)
                            else if (negc & (is_disj (rand c))) then
                let th = SPECL [rand (rator (rand c));
                            rand (rand c)]
                           NOT_DISJ_THM
                in
                                    BREAK (EQ_MP th t)
                            else if (negc & (is_imp (rand c))) then
                let th = SPECL [rand (rator (rand c));
                        rand (rand c)]
                           NOT_IMP_THM
                in
                                    BREAK (EQ_MP th t)
                            else if (negc & (is_pmi (rand c))) then
                let th = SPECL [rand (rator (rand c));
                        rand (rand c)]
                           NOT_PMI_THM
                in
                                    BREAK (EQ_MP th t)
                            else if ((is_cond c) & (rand c = "F")) then
                let th = SPECL [rand (rator (rator c));
                        rand (rator c)]
                           COND_F_THM
                in
                                    BREAK (EQ_MP th t)
                            else
                                [t])
                ) in
        BREAK;;

SMASH;;
end_section smash_section;;
let SMASH = it;;

% smash breaks a term into lots of little terms.                            %
% smash is to SMASH as conjuncts is to CONJUNCTS.                           %
let smash (t : term) = map concl (SMASH (ASSUME t));;

%  (H1 ?- t)   (H2 ?- u)                                                    %
% ----------------------- prove_hyp                                         %
%  (H1 u (H2 - {t}) ?- u)                                                   %
let prove_hyp (H1, t:term) (H2, u:term) =
    (term_setify (filter (\h. not (aconv h t)) (H1 @ H2)), u);;

let true_tm = "T"
and false_tm = "F"
and imp_tm = "==>"
and pmi_tm = "<=="
and equiv_tm = "=:bool->bool->bool";;
