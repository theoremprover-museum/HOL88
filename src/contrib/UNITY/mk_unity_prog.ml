% -*- Emacs Mode: fundamental -*- %


%----------------------------------------------------------------

   File:         mk_unity_prog.ml
   Description:  

   A representation of UNITY programs for the HOL-UNITY proof system

   Author:       Copyright by Flemming Andersen 1990
   Date:         May 11, 1990

   Usage:        To allow for defining UNITY programs for the corresponding
                 logic specifications in the HOL-UNITY proof system.

----------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
autoload_defs_and_thms `gen_induct`;;
autoload_defs_and_thms `leadsto`;;
autoload_defs_and_thms `comp_unity`;;
%

system `/bin/rm unity_prog.th`;;

%set_flag(`timing`,true);; %

new_theory`unity_prog`;;

%
  To allow for expressing the update of a given state s to a state s' by a set
  of state transforming assignments, we define a primitive recursive function
  STr, which takes a start state s, an intermediate state s', and a list of
  assignments stl as parameters.

  The state s' represents the updated state when the list stl is the empty
  list. For a non-empty list (CONS st stl) the assignment st of the list is
  the lambda expression, which represents the updated state. The assignment
  st itself is a pair, in which the first part (FST st) is the variable to be
  updated, and the second part is the expression which represents the new
  value in the state s.

  Nottice that the state argument s is needed since every right handside
  expression (SND st) of an assignment represents a value in the state s.

%
let STr = new_recursive_definition false list_Axiom `STr`
   "(STr (s:*->**) s' [] = s') /\
    (STr s s' (CONS (st:*#**) stl) =
               (STr s (\nm:*. ((nm = (FST st)) => (SND st) | s' nm)) stl))";;


%
  A conditional update MK_COND takes a pair (c, stl), and a state s as
  parameter. The first part c of the pair is the boolean guard. The second part
  stl is the set of assignments to update when c is true in the given state s.
  If c is false in the state s, the state s represents the result of the
  update.

  Nottice that in states s for which c is false, MK_COND represents the
  identity function according to the semantic definition of a UNITY assignment.
%
let MK_COND = new_definition (`MK_COND`,
   "MK_COND (c, stl) (s:*->**) = ((c s) => (STr s s stl) | s)");;


% close_theory( );; %
