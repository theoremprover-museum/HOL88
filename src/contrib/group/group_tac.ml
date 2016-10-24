% FILE		: group_tac.ml						%
% DESCRIPTION   : defines tactics for solving routine group membership  %
%                 goals, and rules and tactics for reassociating        %
%                 subexpresions to the left or to the right. 	        %
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.20						%
%									%
%-----------------------------------------------------------------------%

loadf `start_groups`;;

% --------------------------------------------------------------------- %
% Internal function: mapshape						%
% 									%
% Applies the functions in fl to argument lists obtained by splitting   %
% the list l into sublists of lengths given by nl.			%
% --------------------------------------------------------------------- %

letrec mapshape nl fl l =  
   if null nl then [] else 
      (let m,l = chop_list (hd nl) l in 
       (hd fl)m . mapshape(tl nl)(tl fl)l) ;;

% GROUP_TAC : thm list -> tactic					%
% Like GROUP_ELT_TAC, accept you can add aditional theorems to be used  %
% in reducing goals.							%

let GROUP_TAC thm_list =
 set_fail_prefix `GROUP_TAC`
 (let prod_thm = (theorem `elt_gp` `CLOSURE`) in
  let inv_thm =  (theorem `elt_gp` `INV_CLOSURE`) in
  let id_thm = (CONJUNCT1 (UNDISCH (theorem `elt_gp` `ID_LEMMA`))) in
   REDUCE_TAC (thm_list@[prod_thm;inv_thm;id_thm;]));;

% GROUP_ELT_TAC : tactic						%
% Used to solved routine goals of group membership.			%

let GROUP_ELT_TAC =  set_fail_prefix `GROUP_ELT_TAC` (GROUP_TAC []);;


% GROUP_RIGHT_ASSOC_TAC : term -> tactic  (term = prod (prod a b) c)

   A |-  t(prod (prod a b) c)
---------------------------------
   A |-  t(prod a (prod b c))

 provided there is an assumption of the form GROUP(G,prod).
 GROUP_RIGHT_ASSOC_TAC uses GROUP_ELT_TAC to handle the group membership
 requirements which arise.
%

let GROUP_RIGHT_ASSOC_TAC tm =
 set_fail_prefix `GROUP_RIGHT_ASSOC_TAC`
 (\(asl,gl).
  let prod = rator (rator tm) in
  let first_inst_thm = UNDISCH_ALL (STRONG_INST_TY_TERM
   (tryfind
     (\asm. (if (aconv (rand (rand asm)) prod) then
      match "GROUP((G:* -> bool),(prod:* -> * -> *))" asm
      else fail)) (rev asl))
   (hd (IMP_CANON (theorem `elt_gp` `GROUP_ASSOC`)))) in
  let (subgl,pf) = NEW_SUBST1_TAC 
    (STRONG_INST (fst (match (lhs(concl first_inst_thm)) tm)) first_inst_thm)
    (asl,gl) in
  let goallist = (ALL_TAC (hd subgl).(map GROUP_ELT_TAC (tl subgl))) in
  let (subgl_list,pf_list) = split goallist in
  let num_list = map length subgl_list in
 ((flat subgl_list), (pf o (mapshape num_list pf_list))));;


% GROUP_LEFT_ASSOC_TAC : term -> tactic  (term = prod a (prod b c))

   A |-  t(prod a (prod b c))
---------------------------------
   A |-  t(prod (prod a b) c)

 provided there is an assumption of the form GROUP(G,prod).
 GROUP_LEFT_ASSOC_TAC uses GROUP_ELT_TAC to handle the group membership
 requirements which arise.
%

let GROUP_LEFT_ASSOC_TAC tm =
 set_fail_prefix `GROUP_LEFT_ASSOC_TAC`
 (\(asl,gl).
  let prod = rator (rator tm) in
  let first_inst_thm = SYM (UNDISCH_ALL (STRONG_INST_TY_TERM
   (tryfind
     (\asm. (if (aconv (rand (rand asm)) prod) then
      match "GROUP((G:* -> bool),(prod:* -> * -> *))" asm
      else fail)) (rev asl))
   (hd (IMP_CANON (theorem `elt_gp` `GROUP_ASSOC`))))) in
  let (subgl,pf) = NEW_SUBST1_TAC 
    (STRONG_INST (fst (match (lhs(concl first_inst_thm)) tm)) first_inst_thm)
    (asl,gl) in
  let goallist = (ALL_TAC (hd subgl).(map GROUP_ELT_TAC (tl subgl))) in
  let (subgl_list,pf_list) = split goallist in
  let num_list = map length subgl_list in
 ((flat subgl_list), (pf o (mapshape num_list pf_list))));;

