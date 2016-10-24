%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_tree.ml                                            %
%                                                                             %
%     DESCRIPTION:      Creates the theory "tree.th" containing the           %
%                       definition of a type of (bare) trees.                 %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.07.27)                               %
%                                                                             %
%     PARENTS:          list.th                                               %
%     WRITES FILES:     tree.th                                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1988                                     %
%                                                                             %
%     REVISION HISTORY: Mike Gordon and John Carroll (26 August 1989)         %
%=============================================================================%


% Create the new theory "tree.th".					%
new_theory `tree`;;

% The theory of lists is a parent theory.				%
new_parent `list`;;

% fetch theorems from list.th						%
let list_Axiom		 = theorem `list` `list_Axiom` 
and list_INDUCT		 = theorem `list` `list_INDUCT` 
and CONS_11      	 = theorem `list` `CONS_11` 
and NULL		 = theorem `list` `NULL`
and NOT_CONS_NIL	 = theorem `list` `NOT_CONS_NIL` 
and NOT_NIL_CONS	 = theorem `list` `NOT_NIL_CONS` 
and ALL_EL_CONJ 	 = theorem `list` `ALL_EL_CONJ`;;

% theorem changed to definition for HOL88				%
let ALL_EL  		 = definition `list` `ALL_EL`
and MAP 		 = definition `list` `MAP`
and HD 			 = definition `list` `HD` 
and TL			 = definition `list` `TL`;;


% Need arithmetic definitions.						%
let LESS_OR_EQ		= definition `arithmetic` `LESS_OR_EQ`;;

% theorem changed to definition for HOL88				%
let EXP   	        = definition `arithmetic` `EXP`;;

% Need various arithmetic theorems.					%
let LESS_ADD_1 		= theorem `arithmetic` `LESS_ADD_1` and
    ADD_SYM		= theorem `arithmetic` `ADD_SYM` and
    EXP_ADD		= theorem `arithmetic` `EXP_ADD` and
    MULT_ASSOC		= theorem `arithmetic` `MULT_ASSOC` and
    MULT_EXP_MONO	= theorem `arithmetic` `MULT_EXP_MONO` and
    MULT_CLAUSES	= theorem `arithmetic` `MULT_CLAUSES` and
    ADD_CLAUSES		= theorem `arithmetic` `ADD_CLAUSES` and
    NOT_ODD_EQ_EVEN	= theorem `arithmetic` `NOT_ODD_EQ_EVEN` and
    LESS_CASES		= theorem `arithmetic` `LESS_CASES` and
    WOP			= theorem `arithmetic` `WOP` and
    num_CASES		= theorem `arithmetic` `num_CASES` and
    NOT_LESS		= theorem `arithmetic` `NOT_LESS` and
    LESS_IMP_LESS_OR_EQ	= theorem `arithmetic` `LESS_IMP_LESS_OR_EQ` and
    LESS_EQ_TRANS	= theorem `arithmetic` `LESS_EQ_TRANS` and
    LESS_EQ_ADD		= theorem `arithmetic` `LESS_EQ_ADD` and
    LESS_TRANS		= theorem `arithmetic` `LESS_TRANS` and
    LESS_EQ_ANTISYM	= theorem `arithmetic` `LESS_EQ_ANTISYM` and
    LESS_EQ 		= theorem `arithmetic` `LESS_EQ`;;


% Need theorems from prim_rec.th					%
let INV_SUC_EQ		= theorem `prim_rec` `INV_SUC_EQ` and
    PRIM_REC_THM	= theorem `prim_rec` `PRIM_REC_THM` and
    LESS_0		= theorem `prim_rec` `LESS_0` and
    LESS_SUC_REFL 	= theorem `prim_rec` `LESS_SUC_REFL` and
    LESS_THM		= theorem `prim_rec` `LESS_THM` and
    LESS_SUC		= theorem `prim_rec` `LESS_SUC` and
    NOT_LESS_0 		= theorem `prim_rec` `NOT_LESS_0` and
    LESS_REFL 		= theorem `prim_rec` `LESS_REFL`;;

% Need theorems from num.th						%
let NOT_SUC		= theorem `num` `NOT_SUC` and 
    INDUCTION 		= theorem `num` `INDUCTION`;;

% ---------------------------------------------------------------------	%
% Load code needed							%
% ---------------------------------------------------------------------	%

% Load the axiom scheme for numerals (NB: uncompiled!).			%
loadt (concat ml_dir_pathname `numconv.ml`);;

% We need to load in the induction tactic.  It's in ml/ind.ml		%
% but it is part of hol rather than basic hol, so it's loaded   	%
% in uncompiled.							%
%									%
% TFM 88.04.02								%
loadt (concat ml_dir_pathname `ind.ml`);;

% Note that prim_rec_ml.o must be recompiled if basic-hol has been.	%
% So we just load prim_rec.ml uncompiled.				%
%									%
% TFM 88.04.02								%

loadt (concat ml_dir_pathname `prim_rec.ml`);;

% Create an induction tactic for :num					%
let INDUCT_TAC = INDUCT_THEN (theorem `num` `INDUCTION`) ASSUME_TAC;;

% Create a tactic for list induction.					%
let LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Define a one-to-one coding function from (num)list -> num:		%
%									%
% The coding function used will be iteration of (2n + 1) (2 ^ p)...	%
% --------------------------------------------------------------------- %

% First a few arithmetic lemmas:					%
let arith_lemma = 
    TAC_PROOF(
    ([], "!p q n m.
           p < q ==>
 	   ~(((SUC(n + n)) * (2 EXP p)) = ((SUC(m + m)) * (2 EXP q)))"),
    REPEAT GEN_TAC THEN
    DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    CONV_TAC (REDEPTH_CONV num_CONV) THEN
    MAP_EVERY ONCE_REWRITE_TAC [[ADD_SYM];[EXP_ADD]] THEN
    REWRITE_TAC [MULT_ASSOC;MULT_EXP_MONO] THEN
    REWRITE_TAC [EXP_ADD;MULT_ASSOC;EXP] THEN 
    REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES] THEN
    MATCH_ACCEPT_TAC NOT_ODD_EQ_EVEN);;

% The next two theorems state that the function (2n + 1)(2 ^ p) is 1-1	%
let fun_11_1 = 
    TAC_PROOF(
     ([], "!p q n m. 
           ((SUC(n + n)) * (2 EXP p) = (SUC(m + m)) * (2 EXP q)) ==>
     	   (p = q)"),
     REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o SYM) THEN
     IMP_RES_TAC (REWRITE_RULE [] 
		  ((CONV_RULE CONTRAPOS_CONV) (SPEC_ALL arith_lemma))) THEN
     STRIP_ASSUME_TAC 
       (REWRITE_RULE [LESS_OR_EQ] (SPECL ["q:num";"p:num"] LESS_CASES)) THEN
     RES_TAC);;

let fun_11_2 = 
    TAC_PROOF(
     ([], "!p q n m. ((SUC(n + n)) * (2 EXP p) = (SUC(m + m)) * (2 EXP q)) ==>
     		     (n = m)"),
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN SUBST_ALL_TAC fun_11_1 THEN
     POP_ASSUM (MP_TAC o (CONV_RULE (DEPTH_CONV num_CONV))) THEN
     REWRITE_TAC [MULT_EXP_MONO;INV_SUC_EQ] THEN
     MAP_EVERY SPEC_TAC ["m:num","m:num";"n:num","n:num"] THEN
     REPEAT (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES]) THENL
     [REWRITE_TAC [NOT_EQ_SYM(SPEC_ALL NOT_SUC)];
      REWRITE_TAC [NOT_SUC];
      ASM_REWRITE_TAC [INV_SUC_EQ]]);;

% --------------------------------------------------------------------- %
% Representation of trees  ---- :num.					%
% ---------------------------------------------------------------------	%

% The representation type for trees is:  ":num".			%
let ty = ":num";;

% node_REP: makes a tree representation from a tree representation list.%
% The idea is that the term "node [t1;t2;t3;t4...]" represents the tree %
% with branches represented by t1, t2, ... etc.				%
% node_REP is defined using the coding function above...		%
let node_REP = 
    new_recursive_definition false list_Axiom `node_REP`
      "(node_REP NIL = 0) /\
       (node_REP (CONS h t) = ((SUC(h+h)) * (2 EXP (node_REP t))))";;

% Prove that node_REP is one-to-one:					%
let node_REP_one_one = 
    TAC_PROOF(([], "!l1 l2. (node_REP l1 = node_REP l2) = (l1 = l2)"),
    	      LIST_INDUCT_TAC THENL
	      [LIST_INDUCT_TAC THEN
	       REWRITE_TAC [node_REP;NOT_NIL_CONS] THEN
	       CONV_TAC (DEPTH_CONV num_CONV) THEN
	       REWRITE_TAC [REWRITE_RULE [MULT_CLAUSES] 
			 (SPECL ["p:num";"q:num";"0"] MULT_EXP_MONO)] THEN
	       REWRITE_TAC [NOT_EQ_SYM (SPEC_ALL NOT_SUC)];
	       GEN_TAC THEN LIST_INDUCT_TAC THENL
	       [REWRITE_TAC [node_REP;NOT_CONS_NIL] THEN
 	        CONV_TAC (DEPTH_CONV num_CONV) THEN
	        REWRITE_TAC [REWRITE_RULE [MULT_CLAUSES] 
	 	  (SPECL ["p:num";"q:num";"n:num";"0"] MULT_EXP_MONO)] THEN
 	        REWRITE_TAC [NOT_SUC];
		REWRITE_TAC [node_REP;CONS_11] THEN
		MAP_EVERY POP_ASSUM [K ALL_TAC;
				     SUBST1_TAC o SYM o SPEC_ALL] THEN
		REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
		[IMP_RES_TAC fun_11_2;
		 IMP_RES_TAC fun_11_1;
		 ASM_REWRITE_TAC []]]]);;

% ---------------------------------------------------------------------	%
% DEFINITION of the subset of ":num" that will represent trees...	%
% .... and related theorems.						%
% ---------------------------------------------------------------------	%

% Definition of valid tree representations.  Is_tree_REP is true of 	%
% anything constructed by "node_REP".					%
let Is_tree_REP = 
    new_definition
    (`Is_tree_REP`,
     "Is_tree_REP = 
	\t:^ty. !P. (!tl. ALL_EL P tl ==> P(node_REP tl)) ==> P t");;

% A little lemma about ALL_EL and Is_tree_REP.				%
let ALL_EL_Is_tree_REP = 
    TAC_PROOF(
    ([], "!trl.
	  ALL_EL Is_tree_REP trl = 
	  !P. ALL_EL (\t.(!tl. ALL_EL P tl ==> P(node_REP tl)) ==> P t) trl"),
    REWRITE_TAC [Is_tree_REP] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [ALL_EL] THEN
    CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    RES_TAC THEN ASM_REWRITE_TAC[]);;

% Show that if ALL_EL Is_tree_REP trl then Is_tree_REP (node_REP v trl).	%
let Is_tree_lemma1 = 
    TAC_PROOF
    (([], "!trl. ALL_EL Is_tree_REP trl ==>  Is_tree_REP (node_REP trl)"),
     REWRITE_TAC [Is_tree_REP;ALL_EL_Is_tree_REP] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     GEN_TAC THEN 
     DISCH_THEN (\thm. REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL thm)) THEN
     ASM_REWRITE_TAC [ETA_AX]);;

% A little propositional tautology:					%
let taut1 = 
    TAC_PROOF(([], "!a b. ~(a ==> b) = (a /\ ~b)"),
    	      REWRITE_TAC [IMP_DISJ_THM;DE_MORGAN_THM]);;

% Show that if t is a tree then it must be of the form "node_REP tl" for%
% some v:* and tl (where each object in tl staifies Is_tree_REP).	%
let Is_tree_lemma2 = 
    TAC_PROOF(
    ([], "!t. Is_tree_REP t ==> 
          ?trl. ALL_EL Is_tree_REP trl /\ (t = node_REP trl)"),
     GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
     SUBST1_TAC (RIGHT_BETA (AP_THM Is_tree_REP "t:^ty")) THEN
     CONV_TAC (REDEPTH_CONV NOT_EXISTS_CONV) THEN
     CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
     DISCH_TAC THEN
     EXISTS_TAC "\x:^ty. ?tl. ALL_EL Is_tree_REP tl /\ (x = node_REP tl)" THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [taut1] THEN
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC "tl:^ty list" THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC) THEN
      SPEC_TAC ("tl:^ty list","tl:^ty list") THEN
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [ALL_EL] THEN
      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
      REPEAT STRIP_TAC THENL
      [IMP_RES_TAC Is_tree_lemma1 THEN
       RES_TAC THEN ASM_REWRITE_TAC[];
       RES_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      RES_TAC]);;

% Show that Is_tree_REP(node_REP tl) ==> ALL_EL Is_tree_REP tl		%
let Is_tree_lemma3 = 
    let spec = SPEC "node_REP tl" Is_tree_lemma2 in
    let rew1 = REWRITE_RULE [node_REP_one_one] spec in
    let [t1;t2] = CONJUNCTS (SELECT_RULE (UNDISCH rew1)) in
    GEN_ALL(DISCH_ALL (SUBS [SYM t2] t1));;

% Main result... of the past few lemmas.				%
% Show that !v tl. Is_tree_REP (node_REP v tl) = ALL_EL Is_tree_REP tl	%
let Is_tree_lemma4 = 
    TAC_PROOF(([], "!tl. Is_tree_REP (node_REP tl) = ALL_EL Is_tree_REP tl"), 
              REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
	      [IMP_RES_TAC Is_tree_lemma3;
	       IMP_RES_TAC Is_tree_lemma1 THEN
	       POP_ASSUM MATCH_ACCEPT_TAC]);;

% Show that a tree representation exists.				%
let Exists_tree_REP = 
    TAC_PROOF(([], "?t:^ty. Is_tree_REP t"),
              EXISTS_TAC "node_REP NIL" THEN
	      REWRITE_TAC [Is_tree_REP] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
	      REWRITE_TAC [ALL_EL]);;

% ---------------------------------------------------------------------	%
% Introduction of the new type of trees.				%
% ---------------------------------------------------------------------	%

% Define the new type.							%

let tree_TY_DEF = 
   new_type_definition 
     (`tree`, 
      rator(snd(dest_exists(concl Exists_tree_REP))),
      Exists_tree_REP);;

% --------------------------------------------------------------------- %
% Define a representation function, REP_tree, from the type tree to 	%
% the representing type, and the inverse abstraction 			%
% function ABS_tree, and prove some trivial lemmas about them.		%
% --------------------------------------------------------------------- %

let tree_ISO_DEF = 
    define_new_type_bijections
        `tree_ISO_DEF` `ABS_tree` `REP_tree` tree_TY_DEF;;

let R_11   = prove_rep_fn_one_one tree_ISO_DEF  and
    R_ONTO = prove_rep_fn_onto tree_ISO_DEF     and
    A_11   = prove_abs_fn_one_one tree_ISO_DEF  and
    A_ONTO = prove_abs_fn_onto tree_ISO_DEF     and
    A_R = CONJUNCT1 tree_ISO_DEF                and
    R_A = CONJUNCT2 tree_ISO_DEF;;

% Definition of node -- the constructor for trees.			%
let node = 
    new_definition
     (`node`,
      "node tl = (ABS_tree (node_REP (MAP REP_tree tl)))");;

% Definition of dest_node: inverse of node.				%
let dest_node = 
    new_definition
      (`dest_node`, "!t. dest_node t = @p. t = node p");;

% ---------------------------------------------------------------------	%
% Several lemmas about ABS and REP follow...				%
% ---------------------------------------------------------------------	%

let IS_REP_lemma = 
    TAC_PROOF(([], "!tl.ALL_EL Is_tree_REP (MAP REP_tree (tl:(tree)list))"),
	      LIST_INDUCT_TAC THEN
	      ASM_REWRITE_TAC [MAP;ALL_EL;R_ONTO] THEN
	      STRIP_TAC THEN EXISTS_TAC "h:tree" THEN REFL_TAC);;

% Prove that REP(ABS x) = x.						%
let REP_ABS_lemma = 
    TAC_PROOF(
    ([], "!tl. REP_tree(node tl) = (node_REP (MAP REP_tree tl))"),
    REWRITE_TAC [node;SYM(SPEC_ALL R_A)] THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC [Is_tree_lemma4] THEN
    SPEC_TAC ("tl:(tree)list","tl:(tree)list") THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP;ALL_EL;R_ONTO] THEN
    GEN_TAC THEN EXISTS_TAC "h:tree" THEN REFL_TAC);;

let ABS_REP = 
    TAC_PROOF(
    ([], "!tl. Is_tree_REP (node_REP (MAP REP_tree tl))"),
    REWRITE_TAC [Is_tree_lemma4] THEN
    MATCH_ACCEPT_TAC IS_REP_lemma);;
    
let ABS_11_lemma = 
    let a11 = SPECL ["node_REP (MAP REP_tree tl1)";
		     "node_REP (MAP REP_tree tl2)"] A_11 in
    REWRITE_RULE [ABS_REP] a11;;

% Prove that node is one-to-one... save this theorem.			%
let node_11 = 
    prove_thm
    (`node_11`,
     "!tl1 tl2. (node tl1 = node tl2) = (tl1 = tl2)",
    REWRITE_TAC [node;ABS_11_lemma;node_REP_one_one] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN 
    MAP_EVERY SPEC_TAC [("tl1:(tree)list","tl1:(tree)list");
                        ("tl2:(tree)list","tl2:(tree)list")] THEN
    LIST_INDUCT_TAC THENL
    [LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;NOT_CONS_NIL];
     GEN_TAC THEN LIST_INDUCT_TAC THENL
     [REWRITE_TAC [MAP;NOT_EQ_SYM(SPEC_ALL NOT_CONS_NIL)];
      ASM_REWRITE_TAC [MAP;CONS_11;R_11] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

% Some more lemmas about ABS and REP....				%

let A_R_list = 
    TAC_PROOF(([], "!tl:(tree)list. tl = MAP ABS_tree (MAP REP_tree tl)"),
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [MAP;A_R;CONS_11] THEN
    POP_ASSUM ACCEPT_TAC);;

let R_A_R = 
    TAC_PROOF(([], "REP_tree(ABS_tree(REP_tree (t:tree))) = (REP_tree t)"),
              REWRITE_TAC [SYM(SPEC_ALL R_A)] THEN
	      REWRITE_TAC [R_ONTO] THEN
	      EXISTS_TAC "t:tree" THEN REFL_TAC);;

let Is_R = 
    TAC_PROOF(([], "Is_tree_REP (REP_tree (t:tree))"),
    	      REWRITE_TAC [R_ONTO] THEN
	      EXISTS_TAC "t:tree" THEN REFL_TAC);;

let R_A_R_list = 
    TAC_PROOF(
    ([], "!tl:(tree)list.
          MAP REP_tree (MAP ABS_tree (MAP REP_tree tl)) = (MAP REP_tree tl)"),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;R_A_R]);;

let A_ONTO_list = 
    TAC_PROOF(([], "!tl:(tree)list. ?trl.
	            ((tl = MAP ABS_tree trl) /\ (ALL_EL Is_tree_REP trl))"),
    LIST_INDUCT_TAC THENL
    [EXISTS_TAC "NIL:(^ty)list" THEN REWRITE_TAC [MAP;ALL_EL];
     POP_ASSUM STRIP_ASSUME_TAC THEN
     STRIP_TAC THEN
     STRIP_ASSUME_TAC (SPEC "h:tree" A_ONTO) THEN
     EXISTS_TAC "CONS (r:^ty) trl" THEN
     ASM_REWRITE_TAC [CONS_11;MAP;ALL_EL]]);;

let R_ONTO_list = 
    TAC_PROOF(
    ([], "!trl:(^ty)list.
	  ALL_EL Is_tree_REP trl ==> ?tl. trl = MAP REP_tree tl"),
    LIST_INDUCT_TAC THENL
    [DISCH_TAC THEN EXISTS_TAC "NIL:(tree)list" THEN REWRITE_TAC [MAP];
     REWRITE_TAC [ALL_EL;R_ONTO] THEN
     REPEAT STRIP_TAC THEN
     RES_THEN STRIP_ASSUME_TAC THEN
     EXISTS_TAC "CONS (a:tree) tl" THEN
     ASM_REWRITE_TAC [MAP]]);;
    
let R_A_list = 
    TAC_PROOF(
    ([], "!trl. ALL_EL Is_tree_REP (trl:(^ty)list) ==>
                (MAP REP_tree (MAP ABS_tree trl) = trl)"),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ALL_EL;MAP;R_A] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC THEN ASM_REWRITE_TAC[]);;


% Two lemmas showing how induction on trees relates to induction on	%
% tree representations....						%
let induct_lemma1 = 
    TAC_PROOF(
    ([], "(!tl. ALL_EL P tl ==> (P(node tl))) =
    	  (!trl. ALL_EL Is_tree_REP trl ==>
	  	 ALL_EL (\x.P(ABS_tree x)) trl ==>
		 ((\x.P(ABS_tree x)) (node_REP trl)))"),
    let ALL_EL_MAP = TAC_PROOF(([],
    	 "!l P f.ALL_EL P (MAP (f:*->**) (l:(*)list)) = ALL_EL (\x.P(f x)) l"),
        LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;ALL_EL] THEN
    	CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THEN REFL_TAC) in
    EQ_TAC THENL
    [DISCH_TAC THEN GEN_TAC THEN
     DISCH_THEN ((STRIP_THM_THEN SUBST1_TAC) o (MATCH_MP R_ONTO_list)) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [SYM(SPEC_ALL ALL_EL_MAP);SYM(SPEC_ALL A_R_list)] THEN
     ASM_REWRITE_TAC [SYM(SPEC_ALL node)];
     DISCH_TAC THEN GEN_TAC THEN
     STRIP_ASSUME_TAC (SPEC_ALL A_ONTO_list) THEN
     FIRST_ASSUM SUBST_ALL_TAC THEN
     REWRITE_TAC [node;ALL_EL_MAP] THEN
     IMP_RES_TAC R_A_list THEN 
     REPEAT STRIP_TAC THEN RES_TAC THEN
     POP_ASSUM (MP_TAC o CONV_RULE BETA_CONV) THEN
     ASM_REWRITE_TAC []]);;

let induct_lemma2 = 
    TAC_PROOF(
     ([], "(!t:tree. P t:bool) = 
	   (!rep. Is_tree_REP rep ==> 
	         (\r. Is_tree_REP r /\ ((\x.P(ABS_tree x)) r)) rep)"),
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      EQ_TAC THENL
      [CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC [R_ONTO] THEN
       REPEAT STRIP_TAC THENL
       [EXISTS_TAC "a:tree" THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC [A_R]];
       CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THEN
       STRIP_ASSUME_TAC (SPEC "t:tree" A_ONTO) THEN
       RES_TAC THEN ASM_REWRITE_TAC[]]);;

% Induction on trees.							%
let tree_Induct = 
    prove_thm
    (`tree_Induct`,
     "!P. (!tl. ALL_EL P tl ==> P (node tl)) ==> !t. P t",
    REWRITE_TAC [induct_lemma1;induct_lemma2] THEN
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    let is_thm = RIGHT_BETA (AP_THM Is_tree_REP "trep:^ty") in
    DISCH_THEN (MATCH_MP_TAC o (REWRITE_RULE [is_thm])) THEN
    REWRITE_TAC [ALL_EL_CONJ] THEN
    REPEAT STRIP_TAC THEN CONV_TAC BETA_CONV THEN
    RES_TAC THEN ASM_REWRITE_TAC [Is_tree_lemma4]);;

% ---------------------------------------------------------------------	%
%   tree_INDUCT: thm  -> thm						%
%									%
%     A |- !tl. ALL_EL \t.P[t] tl ==> P[node tl]				%
% =======================================================		%
%               A |- !t. P[t]						%
%									%
% ---------------------------------------------------------------------	%

let tree_INDUCT th =
 (let (tl,body) = dest_forall(concl th) in
  let (asm,con) = (dest_imp body) in
  let ALL_EL,[P;tll] = strip_comb asm in
  let b = genvar bool_ty in
  let concth = SYM(RIGHT_BETA(REFL "^P(node ^tl)")) and
      IND    = SPEC P tree_Induct and
      th'    = (SPEC tl th) in
  let th1 = SUBST [concth,b]
                  "^(concl th') = (ALL_EL ^P ^tl ==> ^b)"
                  (REFL (concl th')) in
  let th2 = GEN tl (EQ_MP th1 th') in
  CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND th2)?failwith `tree_INDUCT`);;

% ---------------------------------------------------------------------	%
%									%
% tree_INDUCT_TAC							%
%									%
%             [A] !t.P[t]						%
%  ================================					%
%    [A,ALL_EL \t.P[t] trl] |- P[node trl]				%
%									%
% ---------------------------------------------------------------------	%

let tree_INDUCT_TAC (A,term) =
 (let t,body = dest_forall term in
  let t' = variant ((frees term) @ (freesl A)) t in
  let body' = subst [t',t] body in
  let trl = variant ((frees body') @ (freesl A)) "trl:(tree)list" in
  let asm = "ALL_EL (\^t'.^body') trl" in
 ([ (asm.A, subst["node ^trl",t']body')],
  \[thm]. tree_INDUCT (GEN trl (DISCH asm thm)))
 ) ? failwith `tree_INDUCT_TAC`;;

% ---------------------------------------------------------------------	%
% Definition of a height function on trees...				%
%									%
% ---------------------------------------------------------------------	%

% First, define a relation "bht n tr" which is true if tr has height 	%
% bounded by n.  I.e. bht n tr = height of tr <= n.			%
let bht = 
    new_definition
    (`bht`,
     "bht = PRIM_REC 
            (\tr. tr = node NIL) 
	    (\res n. \tr. ?trl. (tr = node trl) /\ ALL_EL res trl)");;

% show that bht has the following recursive definition:			%
let bht_thm = 
    TAC_PROOF(
    ([], "(bht 0 tr = (tr = node NIL)) /\
          (bht (SUC n) tr = ?trl. (tr = node trl) /\ ALL_EL (bht n) trl)"),
    PURE_REWRITE_TAC [bht;PRIM_REC_THM] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN REFL_TAC);;

% Show that if height t <= n then height t <= (SUC n)			%
let bht_lemma1 = 
    TAC_PROOF(([], "!n. !tr:tree. bht n tr ==> bht (SUC n) tr"),
	      INDUCT_TAC THENL
	      [REWRITE_TAC [bht_thm] THEN
	       REPEAT STRIP_TAC THEN
	       EXISTS_TAC "NIL:(tree)list" THEN
	       ASM_REWRITE_TAC [ALL_EL];
	       ONCE_REWRITE_TAC [bht_thm] THEN
	       REPEAT STRIP_TAC THEN
	       EXISTS_TAC "trl:(tree)list" THEN
	       ASM_REWRITE_TAC [] THEN
	       MAP_EVERY POP_ASSUM [MP_TAC;K ALL_TAC] THEN
	       SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
	       LIST_INDUCT_TAC THEN
	       REWRITE_TAC [ALL_EL] THEN
	       REPEAT STRIP_TAC THEN RES_TAC]);;

% show that if height tr <= n then height tr <= n+m			%
let bht_lemma2 = 
    (GEN_ALL o DISCH_ALL o GEN "m:num" o UNDISCH o SPEC_ALL)
    (TAC_PROOF(([], "!m n. !tr:tree. bht n tr ==>  bht (n+m) tr"),
    	       INDUCT_TAC THEN
	       REWRITE_TAC [ADD_CLAUSES] THEN 
	       REPEAT STRIP_TAC THEN
	       RES_TAC THEN IMP_RES_TAC bht_lemma1));;

% show that height bounds for all the trees in a list implies a single	%
% bound for all the trees in the list.					%
let bht_lemma3 = 
    TAC_PROOF(
     ([],"!trl.ALL_EL (\tr:tree.?n.bht n tr) trl ==> ?n. ALL_EL (bht n) trl"),
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [ALL_EL] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     POP_ASSUM STRIP_ASSUME_TAC THEN
     EXISTS_TAC "n+n'" THEN
     STRIP_TAC THENL
     [IMP_RES_TAC bht_lemma2 THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      POP_ASSUM MP_TAC THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN
      SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [ALL_EL] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      IMP_RES_TAC bht_lemma2 THEN
      POP_ASSUM MATCH_ACCEPT_TAC]);;

% show that there always exists an n such that height tr <= n.		%
let exists_bht = 
    TAC_PROOF(([], "!tr:tree. ?n. bht n tr"),
    	      tree_INDUCT_TAC THEN
	      POP_ASSUM (STRIP_ASSUME_TAC o MATCH_MP bht_lemma3) THEN
	      EXISTS_TAC "SUC n" THEN
	      REWRITE_TAC [bht_thm] THEN
	      EXISTS_TAC "trl:(tree)list" THEN
	      ASM_REWRITE_TAC[]);;

% Show that there is always a minimum bound on the height of a tree.	%
let min_bht = 
    CONV_RULE (DEPTH_CONV BETA_CONV)
    (TAC_PROOF(
     ([], "!t:tree.?n.(\n. bht n t)n /\ (!m. m < n ==> ~((\n. bht n t)m))"),
     GEN_TAC THEN
     MATCH_MP_TAC WOP THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     MATCH_ACCEPT_TAC exists_bht));;
	      
% We can now define our hieght function as follows:			%
let HT = 
    new_definition
     (`HT`,
      "HT (t:tree) = @n.  bht n t /\ (!m. m < n ==> ~bht m t)");;

% A number of theorems about HT follow:					%
% The main thing is to show that:					%
% 1) !tl. ALL_EL (\t. HT t < HT(node tl)) tl				% 
% 2) !trl. (HT (node trl) = 0) = (trl = NIL)				%

let HT_thm1 = 
    TAC_PROOF(([], "!tr:tree. bht (HT tr) tr"),
    	      REWRITE_TAC [HT] THEN
	      GEN_TAC THEN
	      STRIP_ASSUME_TAC (SELECT_RULE (SPEC "tr:tree" min_bht)));;

let HT_thm2 = 
    TAC_PROOF(([], "!tr:tree.!m. m < (HT tr) ==> ~bht m tr"),
    	      REWRITE_TAC [HT] THEN
	      GEN_TAC THEN
	      STRIP_ASSUME_TAC (SELECT_RULE (SPEC "tr:tree" min_bht)));;

% A Key result about HT.						%
let HT_leaf =
    TAC_PROOF(([], "!trl. (HT (node trl) = 0) = (trl = NIL)"),
    	      REPEAT STRIP_TAC THEN EQ_TAC THENL
	      [DISCH_TAC THEN MP_TAC (SPEC "node trl" HT_thm1) THEN
	       POP_ASSUM SUBST1_TAC THEN
	       REWRITE_TAC [bht_thm;node_11] THEN
	       STRIP_TAC;
	       DISCH_THEN SUBST1_TAC THEN
	       STRIP_ASSUME_TAC (SPEC "HT(node NIL)" num_CASES) THEN
	       MP_TAC (SPEC "node NIL" HT_thm2) THEN
	       POP_ASSUM SUBST1_TAC THEN
	       REWRITE_TAC [NOT_SUC] THEN
	       CONV_TAC NOT_FORALL_CONV THEN
	       REWRITE_TAC [taut1] THEN
	       EXISTS_TAC "0" THEN
	       REWRITE_TAC [bht_thm;LESS_0]]);;

let HT_thm3 = 
    TAC_PROOF(([], "!m. !tr:tree. (~bht m tr) ==> m < (HT tr)"),
    	      CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
	      REWRITE_TAC [NOT_LESS;LESS_OR_EQ] THEN
	      REPEAT STRIP_TAC THENL
	      [POP_ASSUM 
		((STRIP_THM_THEN SUBST1_TAC) o MATCH_MP LESS_ADD_1) THEN
	       STRIP_ASSUME_TAC (SPEC "tr:tree" HT_thm1) THEN
	       IMP_RES_TAC bht_lemma2 THEN POP_ASSUM MATCH_ACCEPT_TAC;
	       POP_ASSUM (SUBST1_TAC o SYM) THEN
	       MATCH_ACCEPT_TAC HT_thm1]);;

let HT_thm4 = 
    TAC_PROOF(([], "!tr:tree. !m. m < (HT tr) = ~bht m tr"),
              REPEAT STRIP_TAC THEN EQ_TAC THENL
	      (map MATCH_ACCEPT_TAC [HT_thm2;HT_thm3]));;

% TFM: fixed error "tl" for "trl" after quantifier. 88.11.17	%
let HT_thm5 = 
    TAC_PROOF(
     ([], "!n tl h. ~bht n (node tl) ==> ~bht n (node (CONS h tl))"),
    CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
    GEN_TAC THEN STRIP_ASSUME_TAC (SPEC "n:num" num_CASES) THEN
    ASM_REWRITE_TAC [bht_thm] THEN
    POP_ASSUM (K ALL_TAC) THENL
    [REWRITE_TAC [node_11] THEN
     REPEAT STRIP_TAC THEN
     POP_ASSUM (MP_TAC o (AP_TERM "NULL:(tree)list->bool")) THEN
     REWRITE_TAC [NULL];
     REWRITE_TAC [node_11] THEN
     REPEAT STRIP_TAC THEN
     MAP_EVERY POP_ASSUM [MP_TAC;SUBST1_TAC o SYM] THEN
     REWRITE_TAC [ALL_EL] THEN STRIP_TAC THEN
     EXISTS_TAC "tl:tree list" THEN
     ASM_REWRITE_TAC []]);;

let HT_thm6 = 
    TAC_PROOF(
     ([], "!trl tl. !t:tree.
	    ALL_EL (\t. ~bht (HT t) (node tl)) trl ==>
            ALL_EL (\t. ~bht (HT t) (node (CONS h tl))) trl"),
     LIST_INDUCT_TAC THEN
     REWRITE_TAC [ALL_EL] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC HT_thm5;RES_TAC]);;
    
% A Key result about HT.						%
let HT_node = 
    TAC_PROOF(([], "!tl. ALL_EL (\t. HT t < HT(node tl)) tl"),
              REWRITE_TAC [HT_thm4] THEN
              LIST_INDUCT_TAC THEN
	      REWRITE_TAC [ALL_EL] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT GEN_TAC THEN STRIP_TAC THENL
	      [STRIP_ASSUME_TAC (SPEC "HT (h:tree)" num_CASES) THENL
	       [ASM_REWRITE_TAC [bht_thm;node_11;CONS_11] THEN
		DISCH_THEN (MP_TAC o AP_TERM "NULL:(tree)list->bool") THEN
	        REWRITE_TAC [NULL];
	        MP_TAC (SPEC "h:tree" HT_thm2) THEN
	        ASM_REWRITE_TAC [bht_thm;ALL_EL;node_11] THEN
	        DISCH_TAC THEN
	        CONV_TAC (REDEPTH_CONV NOT_EXISTS_CONV) THEN
	        ONCE_REWRITE_TAC [DE_MORGAN_THM] THEN
	        ONCE_REWRITE_TAC [SYM(SPEC_ALL IMP_DISJ_THM)] THEN
	        REPEAT GEN_TAC THEN 
	        DISCH_THEN (SUBST1_TAC o SYM) THEN
	        REWRITE_TAC [ALL_EL;DE_MORGAN_THM] THEN
	        DISJ1_TAC THEN 
	        FIRST_ASSUM MATCH_MP_TAC THEN
	        MATCH_ACCEPT_TAC LESS_SUC_REFL];
	       IMP_RES_THEN MATCH_ACCEPT_TAC HT_thm6]);; 

% The following lemmas are used in the proof of approx_lemma below:	%

let Less_lemma = 
    TAC_PROOF(([], "!n m. (n < SUC m) = (n <= m)"),
    	      REWRITE_TAC [LESS_OR_EQ] THEN
	      CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV DISJ_SYM)) THEN
	      MATCH_ACCEPT_TAC LESS_THM);;

let less_HT = 
    TAC_PROOF(([], "!trl m n.
		    (m <= n) ==> 
		    ALL_EL (\t. HT t < m) trl ==>
		    ALL_EL (\t:tree. HT t <= n) trl"),
	      LIST_INDUCT_TAC THEN
	      REWRITE_TAC [ALL_EL] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT STRIP_TAC THENL
	      [IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
	       IMP_RES_TAC LESS_EQ_TRANS;
	       RES_TAC]);;

let less_HT2 = 
     TAC_PROOF(
     ([], "!trl n. HT(node trl) < n ==> ALL_EL (\t. HT t < n) trl"),
          REPEAT GEN_TAC THEN
	  DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
	  MP_TAC (SPEC "trl:(tree)list" HT_node) THEN
	  SPEC_TAC ("HT(node trl)","n:num") THEN
	  REWRITE_TAC [ADD_CLAUSES;num_CONV "1"] THEN
	  SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
	  LIST_INDUCT_TAC THEN
	  REWRITE_TAC [ALL_EL] THEN
	  CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
	  REPEAT STRIP_TAC THEN RES_TAC THEN
	  STRIP_ASSUME_TAC (REWRITE_RULE [LESS_OR_EQ] 
			      (SPECL ["n:num";"p:num"] LESS_EQ_ADD)) THENL
	  [IMP_RES_TAC LESS_TRANS;
	   POP_ASSUM (SUBST1_TAC o SYM)] THEN
	   IMP_RES_TAC LESS_SUC);;
	  
let less_HT3  = 
    TAC_PROOF(
    ([],"!trl.
      (HT(node trl) <= HT(node (CONS (node trl) NIL)))"),
    REPEAT STRIP_TAC THEN
    MP_TAC (SPEC "CONS (node trl) NIL" HT_node) THEN
    REWRITE_TAC [ALL_EL] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    STRIP_TAC THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ);;

% Following proof revised for version 1.12 resolution. 	 [TFM 91.01.18] %

let less_HT4 = 
    TAC_PROOF
     (([], "!trl m n. (m <= n) ==> 
 		      ALL_EL (\t. HT t < m) trl ==>
		      ALL_EL (\t:tree. HT t < n) trl"),
      PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN
      REPEAT GEN_TAC THEN
      DISCH_THEN (STRIP_THM_THEN (\th g. SUBST1_TAC th g ? MP_TAC th g)) THENL
      [MAP_EVERY (\t. SPEC_TAC(t,t)) ["n:num";"m:num";"trl:(tree)list"] THEN
       LIST_INDUCT_TAC THEN REWRITE_TAC [ALL_EL] THEN
       CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THENL [IMP_RES_TAC LESS_TRANS; RES_TAC];
       DISCH_THEN ACCEPT_TAC]);;

let less_HT5 = 
    let spec = SPEC "CONS (h:tree) NIL" HT_node in
    let rew = CONV_RULE (DEPTH_CONV BETA_CONV) 
    	                (REWRITE_RULE [ALL_EL] spec) in
    GEN_ALL rew;;

let less_HT6 = 
    let spec = SPEC "CONS (h:tree) trl" HT_node in
    let rew = CONV_RULE (DEPTH_CONV BETA_CONV)
    	      (REWRITE_RULE [ALL_EL] spec) in
    let less1 = CONJUNCT1(SPEC_ALL rew) in
    let spec2 = SPEC "node (CONS h trl)" (GEN_ALL less_HT5) in
    GEN_ALL(MATCH_MP LESS_TRANS (CONJ less1 spec2));;

let less_HT7 = 
    let less1 = (SPEC_ALL HT_node) in
    let less2 = (SPEC_ALL less_HT3) in
     (MATCH_MP (GEN_ALL(MATCH_MP less_HT4 less2)) less1);;

let less_HT8 = 
    let sp = REWRITE_RULE [ALL_EL]
            (SPEC "CONS (h:tree) trl" (GEN_ALL less_HT7)) in
      (CONJUNCT2 sp);;


% Show that dest is the destructor for node.				%
let dest_node_thm = 
     TAC_PROOF(([], "!tl. dest_node (node tl) = tl"),
               REWRITE_TAC [dest_node;node_11] THEN
	       REPEAT STRIP_TAC THEN
	       CONV_TAC SYM_CONV THEN
	       CONV_TAC SELECT_CONV THEN
	       EXISTS_TAC "tl:(tree)list" THEN REFL_TAC);;

% we now show that for all n there is a recursive function that works	%
% as desired for trees of height <= n.					%
let approx_lemma = 
    TAC_PROOF
    (([], "!f. !n. ?fn. !trl.
           (HT(node trl) <= n) ==>
	   (fn (node trl) = f (MAP fn trl):**)"),
     GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [NOT_LESS_0;LESS_OR_EQ;HT_leaf] THEN
      EXISTS_TAC "\t:tree. f (NIL:(**)list):**" THEN
      REPEAT (STRIP_GOAL_THEN SUBST1_TAC)  THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [MAP];
      POP_ASSUM STRIP_ASSUME_TAC THEN
      REWRITE_TAC [LESS_OR_EQ] THEN REWRITE_TAC [Less_lemma] THEN
      EXISTS_TAC 
      "\t:tree. ((HT t) <= n) => (fn t:**) | f(MAP fn (dest_node t))" THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [dest_node_thm] THEN
      REPEAT STRIP_TAC THENL
      [RES_TAC THEN ASM_REWRITE_TAC [] THEN
       ASSUME_TAC (SPEC "trl:(tree)list" HT_node) THEN
       IMP_RES_TAC less_HT THEN
       POP_ASSUM MP_TAC THEN POP_ASSUM_LIST (K ALL_TAC) THEN
       DISCH_THEN (\th. AP_TERM_TAC THEN MP_TAC th) THEN
       SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
       LIST_INDUCT_TAC THEN
       REWRITE_TAC [ALL_EL;MAP] THEN
       CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[];
       MP_TAC (SPEC "trl:(tree)list" HT_node) THEN
       ASM_REWRITE_TAC [Less_lemma;SYM(SPEC_ALL LESS_EQ);LESS_REFL] THEN
       POP_ASSUM_LIST (K ALL_TAC) THEN
       DISCH_THEN (\th. AP_TERM_TAC THEN MP_TAC th) THEN
       SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
       LIST_INDUCT_TAC THEN
       REWRITE_TAC [ALL_EL;MAP] THEN
       CONV_TAC (DEPTH_CONV BETA_CONV) THEN
       REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);;

% Now, define tree_rec_fun n f to be the function that works for trees	%
% shorter than n.							%
let trf = 
    new_definition
     (`trf`,
      "trf n f = @fn. !trl.
      	         (HT(node trl)) <= n ==>
		 (fn(node trl):** = f(MAP fn trl))");;

% Prove that trf has the appropriate property.				%
let trf_thm = 
    TAC_PROOF(([], "!f n trl.
    		    (HT (node trl)) <= n ==>
		    (trf n f (node trl):** = f(MAP (trf n f) trl))"),
	      REWRITE_TAC [trf] THEN
	      CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
	      MATCH_ACCEPT_TAC approx_lemma);;

% show that trf n f = trf m f for trees shorter than n amd m.		%
let trf_EQ_thm = 
    TAC_PROOF(([], "!t:tree. !n m f. HT(t) < n /\ HT(t) < m ==>
	                  (trf n f t:** = trf m f t)"),
	      tree_INDUCT_TAC THEN
	      REPEAT STRIP_TAC THEN
	      IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
	      IMP_RES_THEN (SUBST1_TAC o SPEC_ALL) trf_thm THEN
	      AP_TERM_TAC THEN 
	      MAP_EVERY POP_ASSUM [K ALL_TAC;K ALL_TAC] THEN
	      REPEAT (POP_ASSUM (MP_TAC o MATCH_MP less_HT2)) THEN
	      POP_ASSUM MP_TAC THEN 
              SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
	      LIST_INDUCT_TAC THEN REWRITE_TAC [MAP;ALL_EL] THEN
	      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
   	      GEN_TAC THEN CONV_TAC ANTE_CONJ_CONV THEN
	      DISCH_THEN 
	      (\th. ASSUME_TAC th THEN REPEAT STRIP_TAC THEN
	            MP_TAC (SPECL ["n:num";"m:num";"f:(**)list->**"] th)) THEN
	      RES_TAC THEN POP_ASSUM SUBST1_TAC THEN
	      REWRITE_TAC [CONS_11] THEN
	      STRIP_TAC THEN RES_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

% extend the above result for lists of trees.				%
let trf_EQ_thm2 = 
    TAC_PROOF(
    ([], "!trl:(tree)list. 
	  !n m f. (ALL_EL (\t. HT t < n) trl  /\  ALL_EL (\t. HT t < m) trl) ==>
	 	   (MAP (trf n f) trl:(**)list = MAP(trf m f) trl)"),
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [MAP;ALL_EL] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) trf_EQ_thm THEN RES_TAC THEN
    REWRITE_TAC [CONS_11] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;


% Now, by taking "\t. trf (HT (node [t])) f t" we have a function that	%
% works for all trees t.						%
let FN_EXISTS = 
    TAC_PROOF(
    ([], "!f. ?fn. !trl. (fn (node trl):** = f (MAP fn trl))"),
    STRIP_TAC THEN
    EXISTS_TAC 
     "\t. trf (HT(node (CONS t NIL))) (f:(**)list->**) t" THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN   
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPEC "trl:(tree)list" less_HT3) THEN
    IMP_RES_THEN (SUBST1_TAC o SPEC_ALL) trf_thm THEN
    POP_ASSUM (K ALL_TAC) THEN
    AP_TERM_TAC THEN 
    SPEC_TAC ("trl:(tree)list","trl:(tree)list") THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [ALL_EL;MAP] THEN
    REPEAT STRIP_TAC THEN 
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [CONS_11] THEN STRIP_TAC THENL
    [MATCH_MP_TAC trf_EQ_thm THEN STRIP_TAC THENL
     [MATCH_ACCEPT_TAC less_HT6;
      MATCH_ACCEPT_TAC less_HT5];
     FIRST_ASSUM (SUBST1_TAC o SYM) THEN
     MATCH_MP_TAC trf_EQ_thm2 THEN
     STRIP_TAC THENL
     [ACCEPT_TAC less_HT8;
      MATCH_ACCEPT_TAC (GEN_ALL less_HT7)]]);;

% Now show that there is a function that produces the desired tree	%
% recursive function, given f.						%
let FN_thm = 
    TAC_PROOF
    (([], "?FN. !f. !trl. ((FN f) (node trl) = f (MAP (FN f) trl):**)"),
     EXISTS_TAC "\f.  @fn. !trl. (fn(node trl):** = f(MAP fn trl))" THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
     MATCH_ACCEPT_TAC FN_EXISTS);;

% Prove the existence of a certain function AP.				%
let AP = 
    prove_rec_fn_exists list_Axiom 
      "(!l. AP NIL l = NIL) /\
       (!h t l. AP (CONS h t) l = CONS (h (HD l:*):**) (AP t (TL l)))";;

% Got to have the types just right for use of AP below.			%
let AP = INST_TYPE [":tree",":*"] AP;;
let AP_DEF = conjuncts(snd(dest_exists(concl AP)));;

% A lemma about AP and MAP.						%
let AP_MAP = 
    TAC_PROOF((AP_DEF, 
    	      "!l. AP (MAP (f:tree->tree->**) l) l = MAP (\x. f x x) l"),
              LIST_INDUCT_TAC THEN
	      ASM_REWRITE_TAC [MAP;HD;TL] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      STRIP_TAC THEN REFL_TAC);;

% Now, prove the existence of the recursively defined functions.	%
let EXISTS_THM = 
    TAC_PROOF(
     ([], "!f. ?fn. !tl. fn (node tl):** = f (MAP fn tl) tl"),
     STRIP_TAC THEN
     STRIP_ASSUME_TAC (INST_TYPE [":tree->**",":**"] FN_thm) THEN
     STRIP_ASSUME_TAC AP THEN
     let fn = 
        "\n:tree. ((FN (\fnl:(tree->**)list.\n:tree.
		       f (AP fnl (dest_node n):(**)list) 
    	    	         (dest_node n):**)) (n:tree) (n:tree):**)" in
     EXISTS_TAC fn THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC [] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [dest_node_thm;AP_MAP]);;

% A little lemma...							%
let lemma = 
    TAC_PROOF(([],"!l. ALL_EL (\x:*. f x:** = g x) l ==> (MAP f l = MAP g l)"),
              LIST_INDUCT_TAC THEN
	      REWRITE_TAC [MAP;ALL_EL] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT STRIP_TAC THEN RES_TAC THEN
	      ASM_REWRITE_TAC[]);;

% Finally, prove the theorem for trees!					%
let tree_Axiom = 
    prove_thm
    (`tree_Axiom`,
     "!f. ?!fn. !tl. fn (node tl):** = f (MAP fn tl) tl",
     GEN_TAC THEN 
     CONV_TAC EXISTS_UNIQUE_CONV THEN
     STRIP_TAC THENL
     [MATCH_ACCEPT_TAC EXISTS_THM;
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
      tree_INDUCT_TAC THEN
      IMP_RES_TAC lemma THEN
      ASM_REWRITE_TAC []]);;

% Close the theory.                                                     %
close_theory();;

quit();;
