%-----------------------------------------------------------------------------%
%
   File:         mk_until.ml
   Description:  

   This file defines the theorems for the UNTIL definition.

   Author:       Copyright by Flemming Andersen 1990
   Date:         May 7, 1990
%
%-----------------------------------------------------------------------------%

loadf`aux_definitions`;;

%
autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
autoload_defs_and_thms `gen_induct`;;
autoload_defs_and_thms `leadsto`;;
%

system `/bin/rm until.th`;;

new_theory`until`;;

%-----------------------------------------------------------------------------%
% The definition of UNTIL is based on the definition:

      p until q in Pr = (p unless q in Pr /\ p --> q in Pr)

%
let UNTIL = new_infix_definition
  (`UNTIL`,
   "UNTIL (P:*->bool) (Q:*->bool) (Pr:(*->*)list) =
      ((P UNLESS Q) Pr) /\ ((P LEADSTO Q) Pr)");;

%-----------------------------------------------------------------------------%
%
  Lemmas
%
%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
%
  Theorems about UNTIL
%
%-----------------------------------------------------------------------------%

%

               p ensures q in Pr
              -------------------
               p until q in Pr
%


%

               p until q in Pr, q ==> r
              -------------------------
                   p until r in Pr
%


%

               p until false in Pr
              ---------------------
                       ~p
%


%

               p until q in Pr, p' until q' in Pr
              ------------------------------------
                   p \/ p' until q \/ q' in Pr
%


close_theory();;

