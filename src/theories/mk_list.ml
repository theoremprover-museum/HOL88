%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_list.ml                                            %
%                                                                             %
%     DESCRIPTION:      Creates the theory "list.th" containing the logical   %
%                       definition of the list type operator.  The type is    %
%                       defined and the following "axiomatization" is proven  %
%                       from the definition of the type:                      %
%                                                                             %
%                       |- !x. !f. ?!fn. (fn NIL = x) /\                      %
%                                        (!h t. fn (CONS h t) = f (fn t) h t) %
%                                                                             %
%     AUTHOR:           T. F. Melham (86.11.24)                               %
%                                                                             %
%     PARENTS:          arithmetic.th                                         %
%     WRITES FILES:     list.th                                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1987                                     %
%                                                                             %
%     REVISION HISTORY: 97.03.14                                              %
%=============================================================================%


% Define the new theory..						%
new_theory `list`;;

% Parents are arithmetic.						%
new_parent `arithmetic`;;

% fetch theorems from prim_rec.th					%
let NOT_LESS_0 = theorem `prim_rec` `NOT_LESS_0`;;
let PRIM_REC_THM = theorem `prim_rec` `PRIM_REC_THM`;;
let PRE = theorem `prim_rec` `PRE`;;
let LESS_0 = theorem `prim_rec` `LESS_0`;;

% Fetch theorems from num.th						%
let NOT_SUC = theorem `num` `NOT_SUC`;;
let INDUCTION = theorem `num` `INDUCTION`;;

% Fetch theorems from arithmetic.th					%
let ADD_CLAUSES = theorem `arithmetic` `ADD_CLAUSES`;;
let LESS_ADD_1 = theorem `arithmetic` `LESS_ADD_1`;;
let LESS_EQ = theorem `arithmetic` `LESS_EQ`;;
let NOT_LESS = theorem `arithmetic` `NOT_LESS`;;
let LESS_EQ_ADD = theorem `arithmetic` `LESS_EQ_ADD`;;
let num_CASES = theorem `arithmetic` `num_CASES`;;
let LESS_MONO_EQ = theorem `arithmetic` `LESS_MONO_EQ`;;

% ------------------------------------------------------------- %
% We need to load in the induction tactic.  It's in ml/ind.ml	%
% but it is part of hol rather than basic hol, so it's loaded   %
% in uncompiled (since it may not have been recompiled since    %
% basic-hol was last rebuilt.					%
%								%
% TFM 88.04.02							%
% ------------------------------------------------------------- %

loadt (concat ml_dir_pathname `ind.ml`);;


% And create an induction tactic 				%
% Added: TFM 88.03.31						%
let INDUCT_TAC = INDUCT_THEN INDUCTION ASSUME_TAC;;

% Load the (uncompiled) axiom scheme for numerals.		%

loadt (concat ml_dir_pathname `numconv.ml`);;

% Define the subset predicate for lists.				%
let IS_list_REP = 
    new_definition
     (`IS_list_REP`,
      "IS_list_REP r = ?f n. r = ((\m.(m<n => f m | @x:*.T)),n)");;

% Show that the representation subset is nonempty.			%
let EXISTS_list_REP =
    TAC_PROOF(([], "?p. IS_list_REP (p:(num->*) # num)"),
	      EXISTS_TAC "(\n:num.@e:*.T),0" THEN
	      PURE_REWRITE_TAC [IS_list_REP] THEN
	      MAP_EVERY EXISTS_TAC ["\n:num.@e:*.T";"0"] THEN
	      REWRITE_TAC [NOT_LESS_0]);;

% Define the new type.							%
let list_TY_DEF = 
    new_type_definition 
     (`list`, "IS_list_REP:((num->*) # num) -> bool", EXISTS_list_REP);;

% --------------------------------------------------------------------- %
% Define a representation function, REP_list, from the type (*)list to 	%
% the representing type and the inverse abstraction function ABS_list, 	%
% and prove some trivial lemmas about them.				%
% --------------------------------------------------------------------- %

let list_ISO_DEF = 
    define_new_type_bijections
        `list_ISO_DEF` `ABS_list` `REP_list` list_TY_DEF;;

let R_ONTO = prove_rep_fn_onto list_ISO_DEF     and
    A_11   = prove_abs_fn_one_one list_ISO_DEF  and
    A_R = CONJUNCT1 list_ISO_DEF                and
    R_A = CONJUNCT2 list_ISO_DEF;;

% --------------------------------------------------------------------- %
% Definitions of NIL and CONS.						%
% --------------------------------------------------------------------- %

let NIL_DEF = 
    new_definition
     (`NIL_DEF`, "NIL = ABS_list ((\n:num.@e:*.T),0)");;

let CONS_DEF =
    new_definition
     (`CONS_DEF`,
      "CONS (h:*) (t:(*)list) = 
        (ABS_list ((\m. ((m=0) => h | (FST(REP_list t)) (PRE m))),
		  (SUC(SND(REP_list t)))))");;

close_theory();;

% ---------------------------------------------------------------------	%
% Now, prove the axiomatization of lists.				%
% --------------------------------------------------------------------- %

let lemma1 = 
    TAC_PROOF(
    ([],"!x:**. !f:(**->*->(*)list->**).
	 ?fn:(((num->*)#num)->**).
	 (!g.   fn(g,0)   = x) /\
	 (!g n. fn(g,n+1) = 
	        f (fn ((\i.g(i+1)),n)) (g 0) (ABS_list((\i.g(i+1)),n)))"),
   REPEAT STRIP_TAC THEN
   EXISTS_TAC 
   "\p:((num->*)#num). 
   (PRIM_REC (\g.x:**) 
	     (\b m g. f (b (\i.g(i+1))) (g 0) (ABS_list((\i.g(i+1)),m))))
   (SND p)
   (FST p)" THEN
   CONV_TAC (DEPTH_CONV (BETA_CONV ORELSEC num_CONV)) THEN
   REWRITE_TAC [PRIM_REC_THM;ADD_CLAUSES] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[]);;

let NIL_lemma = 
    TAC_PROOF(([], "REP_list NIL = ((\n:num.@x:*.T), 0)"),
              REWRITE_TAC [NIL_DEF;(SYM(SPEC_ALL R_A));IS_list_REP] THEN
	      MAP_EVERY EXISTS_TAC ["\n:num.@x:*.T";"0"] THEN
	      REWRITE_TAC [NOT_LESS_0]);;

let REP_lemma = 
    TAC_PROOF(([], "IS_list_REP (REP_list (l:(*)list))"),
              REWRITE_TAC [R_ONTO] THEN
	      EXISTS_TAC "l:(*)list" THEN
	      REFL_TAC);;

let CONS_lemma = 
    TAC_PROOF(([], 
	      "REP_list (CONS (h:*) t) = 
              ((\m.((m=0)=>h|FST(REP_list t)(PRE m))),SUC(SND(REP_list t)))"),
              REWRITE_TAC [CONS_DEF;(SYM(SPEC_ALL R_A));IS_list_REP] THEN
	      EXISTS_TAC "\n.((n=0) => (h:*) | (FST(REP_list t)(PRE n)))" THEN
	      EXISTS_TAC "SUC(SND(REP_list (t:(*)list)))" THEN
	      REWRITE_TAC [PAIR_EQ] THEN
	      CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
	      STRIP_TAC THEN 
              ASM_CASES_TAC "n < (SUC(SND(REP_list (t:(*)list))))" THEN
	      ASM_REWRITE_TAC [] THEN
	      STRIP_ASSUME_TAC 
	        (REWRITE_RULE [IS_list_REP] 
		  (SPEC "t:(*)list" (GEN_ALL REP_lemma))) THEN
	      POP_ASSUM SUBST_ALL_TAC THEN
	      POP_ASSUM MP_TAC THEN
	      REWRITE_TAC [FST;SND;NOT_LESS;(SYM(SPEC_ALL LESS_EQ))] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      DISCH_THEN
		 ((STRIP_THM_THEN SUBST1_TAC) o MATCH_MP LESS_ADD_1) THEN
	      REWRITE_TAC [num_CONV "1";PRE;ADD_CLAUSES;NOT_SUC] THEN
	      REWRITE_TAC[REWRITE_RULE[SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD]);;

let exists_lemma = 
    TAC_PROOF(
    ([], "!x:**. !f:(**->*->(*)list->**).?fn:(*)list->**.
	  (fn NIL = x) /\ (!h t. fn (CONS h t) = f (fn t) h t)"),
    REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC (REWRITE_RULE [num_CONV "1";ADD_CLAUSES]
		   (SPECL ["x:**";"f:**->*->(*)list->**"] lemma1)) THEN
    EXISTS_TAC "\x:(*)list.(fn (REP_list x):**)" THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC [NIL_lemma;CONS_lemma] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [NOT_SUC;PRE;PAIR;ETA_AX;A_R]);;

let A_11_lemma = 
    REWRITE_RULE [SYM (ANTE_CONJ_CONV "(A /\ B) ==> C")]
    (DISCH_ALL(snd(EQ_IMP_RULE (UNDISCH_ALL (SPEC_ALL A_11)))));;

let R_A_lemma = 
    TAC_PROOF(([],
	     "REP_list(ABS_list((\m.((m<n) => f(SUC m) | @x:*.T)),n)) = 
	      ((\m.((m<n) => f(SUC m) | @x:*.T)),n)"),
	     REWRITE_TAC [SYM(SPEC_ALL R_A);IS_list_REP] THEN
	     MAP_EVERY EXISTS_TAC ["\n.f(SUC n):*";"n:num"] THEN
	     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	     REFL_TAC);;

let cons_lemma = 
    TAC_PROOF(([], 
	     "ABS_list((\m.(m < SUC n) => f m | (@x:*.T)), (SUC n)) = 
              (CONS(f 0)(ABS_list ((\m.((m<n) => f(SUC m) | @x:*.T)), n)))"),
	      REWRITE_TAC [CONS_DEF] THEN
	      MATCH_MP_TAC (GEN_ALL A_11_lemma) THEN
	      REPEAT STRIP_TAC THENL
	      [REWRITE_TAC [R_ONTO] THEN
	       EXISTS_TAC 
	        "CONS (f 0)(ABS_list((\m.((m<n) => f(SUC m)|@x:*.T)),n))" THEN
	       REWRITE_TAC [CONS_lemma];
	       REWRITE_TAC [IS_list_REP] THEN
	       MAP_EVERY EXISTS_TAC ["f:num->*";"SUC n"] THEN REFL_TAC;
	       REWRITE_TAC [PAIR_EQ;R_A_lemma] THEN 
	       CONV_TAC FUN_EQ_CONV THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	       STRIP_TAC THEN
	       STRIP_ASSUME_TAC (SPEC "n':num" num_CASES) THEN
	       POP_ASSUM SUBST1_TAC THENL
	       [REWRITE_TAC [PRE;LESS_0];
	        REWRITE_TAC [PRE;NOT_SUC;LESS_MONO_EQ]]]);;

let list_Axiom =
   prove_thm(`list_Axiom`,
	     "!x:**. !f:(**->*->(*)list->**).
	      ?!fn:(*)list->**.
	      (fn NIL = x) /\
	      (!h t. fn (CONS h t) = f (fn t) h t)",
	     PURE_REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
	     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
	     REWRITE_TAC [exists_lemma] THEN
	     REWRITE_TAC [NIL_DEF] THEN
	     REPEAT STRIP_TAC THEN
	     CONV_TAC FUN_EQ_CONV THEN
             CONV_TAC (ONCE_DEPTH_CONV(REWR_CONV(SYM (SPEC_ALL A_R)))) THEN
	     X_GEN_TAC "l:(*)list" THEN
  	     STRIP_ASSUME_TAC 
	        (REWRITE_RULE [IS_list_REP] 
		  (SPEC "l:(*)list" (GEN_ALL REP_lemma))) THEN
	     POP_ASSUM SUBST_ALL_TAC THEN
	     SPEC_TAC ("f':num->*","f':num->*") THEN
	     SPEC_TAC ("n:num","n:num") THEN
	     INDUCT_TAC THENL
	     [ASM_REWRITE_TAC [NOT_LESS_0];
	      STRIP_TAC THEN
	      POP_ASSUM (ASSUME_TAC o (CONV_RULE (DEPTH_CONV BETA_CONV)) o
	        	 (SPEC "\n.f'(SUC n):*")) THEN
	      ASM_REWRITE_TAC [cons_lemma]]);;

quit();;
