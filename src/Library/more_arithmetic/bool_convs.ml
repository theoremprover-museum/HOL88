%****************************************************************************%
%									     %
% File:         bool_convs.ml						     %
%									     %
% Author:       Wim Ploegaerts  (ploegaer@imec.be)			     %
%									     %
% Date:         Sun Mar 24 1991						     %
%									     %
% Organization: Imec vzw.						     %
%               Kapeldreef 75						     %
%               3001 Leuven - Belgium					     %
%									     %
% Description:  conversions for boolean stuff				     %
%									     %
%****************************************************************************%


%*********************************  HISTORY  ********************************%
%									     %
% 2/5/91 PC                                                                  %
%        EQ_TO_EXISTS has been moved to this file and not saved              %
%*****************************  END OF HISTORY  *****************************%


%<WP>%

%									     %
%  A conversion that introduces an internal variable, according to the	     %
%  following theorem							     %
%									     %

let EQ_TO_EXIST = prove(
  "!t1 t2:* . (t1 = t2) = (?t3 . (t3 = t1) /\ (t3 = t2))",
 REPEAT GEN_TAC THEN EQ_TAC THENL
  [
   DISCH_THEN SUBST1_TAC THEN EXISTS_TAC "t2:*" THEN
   REWRITE_TAC []
  ;
   STRIP_TAC THEN
   EVERY_ASSUM (SUBST1_TAC o SYM) THEN
   REFL_TAC
  ]
);;


%									     %
% EQ_INT_VAR_CONV "t1:*" "t2:* = t3";;					     %
% |- (t2 = t3) = (?t1. (t1 = t2) /\ (t1 = t3))				     %
%									     %
%									     %
% EQ_INT_VAR_CONV "l:num" "t = n + m";;					     %
% |- (t = n + m) = (?l. (l = t) /\ (l = n + m))				     %
%									     %
% EQ_INT_VAR_CONV "l:*" "t = n + m";;					     %
%									     %


% REQUIRES BINDER_CONV --> LOAD AUXILIARY !! %
let EQ_INT_VAR_CONV t term = 
     let (tv,tty) = dest_var t ? failwith `not a variable` in
     let theorem  = INST_TYPE [tty,":*"] EQ_TO_EXIST in
     let t1,t2 = dest_eq term ? failwith `not an equality` in
   CONV_RULE (ONCE_DEPTH_CONV (RAND_CONV (GEN_ALPHA_CONV t)))
            ( SPECL [t1;t2] theorem );;







