%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        ltree.ml                                              %
%                                                                             %
%     DESCRIPTION:      Creates the theory "ltree.th" containing the          %
%                       definition of a type (*)ltree of labelled trees.      %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.07.27)                               %
%                                                                             %
%     PARENTS:          tree.th, combin.th                                    %
%     WRITES FILES:     ltree.th                                              %
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
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% Create the new theory "ltree.th".					%
new_theory `ltree`;;

% tree.th is a parent.							%
new_parent `tree`;;

% theory of combinators is also a parent.				%
new_parent `combin`;;
 
% Fetch theorems from tree.th						%
let node_11	 = theorem `tree` `node_11` and
    tree_Induct  = theorem `tree` `tree_Induct` and
    tree_Axiom   = theorem `tree` `tree_Axiom`;;

% theorem changed to definition for HOL88				%
let SUM			 = definition `list` `SUM` and
    LENGTH 		 = definition `list` `LENGTH` and
    MAP			 = definition `list` `MAP` and
    FLAT	 	 = definition `list` `FLAT` and
    APPEND 		 = definition `list` `APPEND` and
    HD		         = definition `list` `HD` and
    TL			 = definition `list` `TL` and
    ALL_EL		 = definition `list` `ALL_EL`;;

% Fetch theorems from list.th						%
let list_Axiom		 = theorem `list` `list_Axiom` and
    list_INDUCT		 = theorem `list` `list_INDUCT` and
    LENGTH_APPEND 	 = theorem `list` `LENGTH_APPEND` and
    LENGTH_NIL		 = theorem `list` `LENGTH_NIL` and
    LENGTH_CONS		 = theorem `list` `LENGTH_CONS` ;;


% Fetch theorems from combin.th						%
let o_THM = theorem `combin` `o_THM`;;

% Fetch theorems from arithmetic.th					%
let ADD_CLAUSES 	= theorem `arithmetic` `ADD_CLAUSES` and
    ADD_EQ_0 		= theorem `arithmetic` `ADD_EQ_0`;;


% fetch theorems from prim_rec.th					%
let num_Axiom 		= theorem `prim_rec` `num_Axiom` and
    INV_SUC_EQ		= theorem `prim_rec` `INV_SUC_EQ`;;

% fetch theorems from num.th						%
let INDUCTION 		= theorem `num` `INDUCTION`;;

% ---------------------------------------------------------------------	%
% Load/define code needed.						%
% ---------------------------------------------------------------------	%

% We need to load in the induction tactic.  It's in ml/ind.ml		%
% but it is part of hol rather than basic hol, so it's loaded   	%
% in uncompiled.							%
%									%
% TFM 88.04.02								%
loadt (concat ml_dir_pathname `ind.ml`);;

% Note that prim_rec_ml.o must be recompiled if basic-hol has been.	%
% So, load prim_rec.ml uncompiled.					%
%									%
% TFM 88.04.02								%

loadt (concat ml_dir_pathname `prim_rec.ml`);;

% ---------------------------------------------------------------------	%
%   tree_INDUCT: thm  -> thm						%
%									%
%     A |- !tl. ALL_EL \t.P[t] tl ==> P[node tl]				%
% ----------------------------------------------------------		%
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

% Create a tactic for list induction.					%
let LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;;

% Create an induction tactic for :num					%
let INDUCT_TAC = INDUCT_THEN (theorem `num` `INDUCTION`) ASSUME_TAC;;


% Define a function Size on trees that gives the number of nodes in 	%
% a tree.								%
let Size = 
    new_definition
     (`Size`,
      "Size = @fn. (!tl. fn (node tl:tree) = SUC(SUM (MAP fn tl)))");;

% Show that Size has the desired prim rec defn.				%
let Size_thm = 
    TAC_PROOF(([], "!tl. Size (node tl:tree) = SUC(SUM (MAP Size tl))"),
              REWRITE_TAC [Size] THEN
	      CONV_TAC SELECT_CONV THEN
              MP_TAC (SPEC "\n. \tl:(tree)list. (SUC(SUM n))" 
			   (INST_TYPE [":num",":**"] tree_Axiom)) THEN
	      REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
	      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
	      DISCH_THEN (STRIP_THM_THEN CHECK_ASSUME_TAC));;

% ---------------------------------------------------------------------	%
% Subset predicate for (*)ltree and introduction of the new type.	%
% ---------------------------------------------------------------------	%

let Is_ltree = 
    new_definition
      (`Is_ltree`,
       "Is_ltree (t,l) = (Size (t:tree) = LENGTH (l:(*)list))");;

% (*)ltree is represented by :(tree # (*)list				%
let ty = ":(tree # (*)list)";;

% Show that a ltree representation exists.				%
let Exists_ltree_REP = 
    TAC_PROOF(([], "?t:^ty. Is_ltree t"),
              EXISTS_TAC "node NIL:tree,CONS (@v:*.T) NIL " THEN
	      REWRITE_TAC [Is_ltree;LENGTH;Size_thm;MAP;SUM]);;

% Define the new type.							%
let ltree_TY_DEF = 
     new_type_definition 
      (`ltree`, 
       rator(snd(dest_exists(concl Exists_ltree_REP))),
       Exists_ltree_REP);;

% --------------------------------------------------------------------- %
% Define a representation function, REP_tree, from the type tree to 	%
% the representing type, and the inverse abstraction 			%
% function ABS_tree, and prove some trivial lemmas about them.		%
% --------------------------------------------------------------------- %

let ltree_ISO_DEF = 
    define_new_type_bijections
        `ltree_ISO_DEF` `ABS_ltree` `REP_ltree` ltree_TY_DEF;;

let R_11   = prove_rep_fn_one_one ltree_ISO_DEF  and
    R_ONTO = prove_rep_fn_onto ltree_ISO_DEF     and
    A_11   = prove_abs_fn_one_one ltree_ISO_DEF  and
    A_ONTO = prove_abs_fn_onto ltree_ISO_DEF     and
    A_R = CONJUNCT1 ltree_ISO_DEF                and
    R_A = CONJUNCT2 ltree_ISO_DEF;;

% Definition of Node.							%
let Node = 
    new_definition
     (`Node`,
      "Node (v:*) (tl:((*)ltree)list) = 
      (ABS_ltree ((node (MAP (FST o REP_ltree) tl)), 
		 ((CONS v (FLAT (MAP (SND o REP_ltree) tl))))))");;

% A lemma about Rep_ltree(Node v tl)					%
let REP_Node = 
    TAC_PROOF(
    ([], 
    "!tl.REP_ltree (Node (v:*) tl) = 
        (node(MAP(FST o REP_ltree)tl), CONS v(FLAT(MAP(SND o REP_ltree)tl)))"),
    REWRITE_TAC [Node;SYM(SPEC_ALL R_A);Is_ltree] THEN
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [Size_thm;MAP;LENGTH;FLAT;SUM];
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [Size_thm;MAP;LENGTH;FLAT;SUM;LENGTH_APPEND] THEN
     REWRITE_TAC [SYM (el 4 (CONJUNCTS ADD_CLAUSES))] THEN
     DISCH_THEN SUBST1_TAC THEN 
     STRIP_TAC THEN STRIP_ASSUME_TAC (SPEC "h:(*)ltree" A_ONTO) THEN
     MP_TAC (SPEC "r:^ty" R_A) THEN
     ASM_REWRITE_TAC [o_THM] THEN
     DISCH_THEN SUBST1_TAC THEN
     MAP_EVERY POP_ASSUM [MP_TAC;K ALL_TAC] THEN
     ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
     REWRITE_TAC [Is_ltree] THEN
     DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

% A lemma about Size and LENGTH of the components of REP_ltree t	%
let Size_LENGTH_lemma = 
    TAC_PROOF(
    ([], "!t:(*)ltree. Size (FST (REP_ltree t)) = LENGTH (SND (REP_ltree t))"),
    GEN_TAC THEN STRIP_ASSUME_TAC (SPEC "t:(*)ltree" A_ONTO) THEN
    MP_TAC (SPEC_ALL R_A) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY POP_ASSUM [MP_TAC;K ALL_TAC] THEN
    ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
    REWRITE_TAC [Is_ltree]);;

% Extend the above thm to lists of REP_ltree				%
let MAP_Size_LENGTH = 
    TAC_PROOF(
    ([], "!tl:((*)ltree)list. 
	  MAP Size (MAP (FST o REP_ltree) tl) = 
          MAP LENGTH (MAP (SND o REP_ltree) tl)"),
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP;Size_thm;LENGTH;Size_LENGTH_lemma;o_THM]);;

% ---------------------------------------------------------------------	%
% In what follows, we define a few list processing functions.  These	%
% are rather special purpose.  But they are defined constants here,	%
% for convenience of use.  In a later version of HOL, these could be 	%
% defined by use of the assumption list to introduce "local" 		%
% definitions, so as not to clutter up the built-in theories		%
% with constants that will be only used locally here.			%
% ---------------------------------------------------------------------	%

let AP = 
    new_recursive_definition false list_Axiom `AP`
      "(!l. AP NIL l = NIL) /\
       (!h t l. AP (CONS h t) l = CONS (h (HD l:*):**) (AP t (TL l)))";;

let SPLIT = 
    new_recursive_definition false num_Axiom `SPLIT`
     "(SPLIT 0 l = (NIL,l:(*)list)) /\
      (SPLIT (SUC n) l = (CONS (HD l) (FST(SPLIT n (TL l))), 
			  SND(SPLIT n (TL l))))";;

let PART = 
    new_recursive_definition false list_Axiom `PART`
     "(PART NIL (l:(*)list) = NIL) /\
      (PART (CONS n t) l = 
           (CONS (FST (SPLIT n l)) (PART t (SND (SPLIT n l)))))";;

% ---------------------------------------------------------------------	%
% Some theorems about SPLIT, PART, etc.					%
% ---------------------------------------------------------------------	%

let SPLIT_APPEND = 
    TAC_PROOF
    (([], "!l:(*)list. !l'. SPLIT (LENGTH l) (APPEND l l') = (l,l')"),
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [APPEND;SPLIT;LENGTH;HD;TL]);;

let PART_FLAT = 
    TAC_PROOF
    (([],  "!l:((*)list)list. PART (MAP LENGTH l) (FLAT l) = l"),
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [PART;LENGTH;MAP;FLAT;SPLIT_APPEND]);;

let LENGTH_SND_SPLIT = 
    TAC_PROOF
    (([],"!l:(*)list.!n m.(LENGTH l = n+m) ==> (LENGTH(SND(SPLIT n l)) = m)"),
      LIST_INDUCT_TAC THENL 
      [ONCE_REWRITE_TAC [INST_TYPE [":num",":*"] EQ_SYM_EQ] THEN
       REWRITE_TAC [LENGTH;ADD_EQ_0] THEN
       REPEAT (STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC)) THEN
       REWRITE_TAC [SPLIT;LENGTH];
       REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
       INDUCT_TAC THENL
       [REWRITE_TAC [ADD_CLAUSES;SPLIT;LENGTH];
        REWRITE_TAC [ADD_CLAUSES;INV_SUC_EQ] THEN
	REPEAT STRIP_TAC THEN RES_TAC THEN
	ASM_REWRITE_TAC [SPLIT;TL]]]);;

let LENGTH_FST_SPLIT = 
    TAC_PROOF
    (([],"!l:(*)list.!n m.(LENGTH l = n+m) ==> (LENGTH(FST(SPLIT n l)) = n)"),
      LIST_INDUCT_TAC THENL 
      [ONCE_REWRITE_TAC [INST_TYPE [":num",":*"] EQ_SYM_EQ] THEN
       REWRITE_TAC [LENGTH;ADD_EQ_0] THEN
       REPEAT (STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC)) THEN
       REWRITE_TAC [SPLIT;LENGTH];
       REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
       INDUCT_TAC THENL
       [REWRITE_TAC [ADD_CLAUSES;SPLIT;LENGTH];
        REWRITE_TAC [ADD_CLAUSES;INV_SUC_EQ] THEN 
	REPEAT STRIP_TAC THEN RES_TAC THEN
	ASM_REWRITE_TAC [SPLIT;HD;TL;LENGTH]]]);;

let APPEND_SPLIT = 
    TAC_PROOF
    (([],  "!l:(*)list. !n m.
      (LENGTH l = n + m) ==> 
      (APPEND (FST(SPLIT n l)) (SND (SPLIT n l)) = l)"),
     LIST_INDUCT_TAC THENL 
     [ONCE_REWRITE_TAC [INST_TYPE [":num",":*"] EQ_SYM_EQ] THEN
      REWRITE_TAC [LENGTH;ADD_EQ_0] THEN
      REPEAT (STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC)) THEN
      REWRITE_TAC [SPLIT;APPEND];
      REWRITE_TAC [LENGTH] THEN STRIP_TAC THEN
      INDUCT_TAC THENL
      [REWRITE_TAC [ADD_CLAUSES;SPLIT;APPEND];
       REWRITE_TAC [ADD_CLAUSES;INV_SUC_EQ] THEN 
       REPEAT STRIP_TAC THEN RES_TAC THEN
       ASM_REWRITE_TAC [SPLIT;HD;TL;APPEND]]]);;

% Recursive functions on the REPRESENTATION type...(MAJOR THM)		%
let REP_REC_lemma = 
    TAC_PROOF
    (([], "!f. ?!fn. !tl. !l:(*)list. 
           fn(node tl,l):** = 
              f (AP (MAP (\t e.fn(t,e)) tl)(PART (MAP Size tl)(TL l)))
                (HD l:*) 
                (MAP ABS_ltree 
                     (AP (MAP $, tl) (PART (MAP Size tl) (TL l))))"),
     STRIP_TAC THEN
     MP_TAC (SPEC "\rl:((*)list->**)list. \tl:(tree)list. \l:(*)list.
                    f (AP rl (PART (MAP Size tl) (TL l))) 
		      (HD l:*)
       	              (MAP ABS_ltree 
     	      		   (AP (MAP $, tl) 
		               (PART (MAP Size tl) (TL l)))):**"
      	          (INST_TYPE [":(*)list->**",":**"] tree_Axiom)) THEN
     REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC "\p. fn (FST p:tree) (SND p:(*)list):**" THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN 
      ASM_REWRITE_TAC [ETA_AX] THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC;
      REPEAT GEN_TAC THEN
      POP_ASSUM 
      (MP_TAC o 
        SPECL ["\t:tree. \e:(*)list.x(t,e):**";
               "\(t:tree) (e:(*)list).y(t,e):**"]) THEN
      CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
      POP_ASSUM MATCH_ACCEPT_TAC]);;

% A little simplifying lemma						%
let lemma1 = 
    TAC_PROOF(
    ([], "!tl:((*)ltree)list. 
          (MAP ABS_ltree 
    	       (AP (MAP $,(MAP(FST o REP_ltree)tl))
                   (PART (MAP Size(MAP(FST o REP_ltree)tl))
		              (FLAT(MAP(SND o REP_ltree)tl))))) = tl"),
    REWRITE_TAC [MAP_Size_LENGTH;PART_FLAT] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [o_THM;MAP;AP;A_R;HD;TL]);;

% Another								%
let lemma2 = 
    TAC_PROOF(
    ([], "!tl:((*)ltree)list. 
          (AP (MAP(\t e. fn(t,e))(MAP(FST o REP_ltree)tl))
              (PART (MAP Size(MAP(FST o REP_ltree)tl))
		         (FLAT(MAP(SND o REP_ltree)tl)))) = 
	  (MAP (fn o REP_ltree) tl:(**)list)"),
    REWRITE_TAC [MAP_Size_LENGTH;PART_FLAT] THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MAP;AP;o_THM;TL;HD] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [PAIR]);;

% Another								%
let lemma3 = 
    TAC_PROOF(
    ([], "!trl:(tree)list. !l:(*)list. 
          (LENGTH l = SUM(MAP Size trl)) ==>
          (FLAT (MAP (SND o REP_ltree) 
                (MAP ABS_ltree (AP (MAP $, trl)
				  (PART(MAP Size trl)l)))) = l)"),
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [SUM;MAP;LENGTH_NIL] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PART;AP;MAP;FLAT];
     REWRITE_TAC [MAP;SUM;PART] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SND_SPLIT THEN RES_TAC THEN
     IMP_RES_TAC LENGTH_FST_SPLIT THEN
     ASM_REWRITE_TAC [AP;MAP;FLAT;HD;TL;o_THM] THEN
     MP_TAC (SPEC "(h:tree),(FST(SPLIT(Size h)(l:(*)list)))" R_A) THEN
     REWRITE_TAC [Is_ltree] THEN 
     POP_ASSUM (ASSUME_TAC o SYM) THEN
     DISCH_THEN 
       (\th1. FIRST_ASSUM (\th. (SUBST1_TAC (EQ_MP th1 th)) ? NO_TAC)) THEN
     IMP_RES_TAC APPEND_SPLIT THEN
     REWRITE_TAC [] THEN POP_ASSUM ACCEPT_TAC]);;

% Another								%
let lemma4 = 
    TAC_PROOF(
    ([], "!trl:(tree)list. !l:(*)list. 
          (LENGTH l = SUM(MAP Size trl)) ==>
          (node (MAP (FST o REP_ltree) 
                (MAP ABS_ltree (AP (MAP $, trl) 
				  (PART(MAP Size trl)l)))) = node trl)"),
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [SUM;MAP;LENGTH_NIL] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PART;AP;MAP];
     REWRITE_TAC [MAP;SUM;PART] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SND_SPLIT THEN RES_TAC THEN
     IMP_RES_TAC LENGTH_FST_SPLIT THEN
     ASM_REWRITE_TAC [AP;MAP;FLAT;HD;TL;o_THM] THEN
     MP_TAC (SPEC "(h:tree),(FST(SPLIT(Size h)(l:(*)list)))" R_A) THEN
     REWRITE_TAC [Is_ltree] THEN 
     POP_ASSUM (ASSUME_TAC o SYM) THEN
     DISCH_THEN 
       (\th1. FIRST_ASSUM (\th. (SUBST1_TAC (EQ_MP th1 th)) ? NO_TAC)) THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [node_11] THEN
     DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

% Another								%
let lemma5 = 
    TAC_PROOF(
    ([], "!trl l.
     (Size (node trl) = LENGTH l) ==>
     (ABS_ltree(node trl,l) = 
       Node (HD l:*) 
            (MAP ABS_ltree 
    	         (AP (MAP $, trl)
                     (PART (MAP Size trl) (TL l)))))"),
     ONCE_REWRITE_TAC [INST_TYPE [":num",":*"] EQ_SYM_EQ] THEN
     REWRITE_TAC [Size_thm;LENGTH_CONS] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [HD;TL;Node] THEN
     IMP_RES_TAC lemma3 THEN
     POP_ASSUM SUBST1_TAC THEN
     IMP_RES_TAC lemma4 THEN
     POP_ASSUM SUBST1_TAC THEN
     REFL_TAC);;

% Another								%
let lemma6 = 
    TAC_PROOF(
    ([], "!trl. !l:(*)list.
     (Size (node trl) = LENGTH l) ==>
     ALL_EL (\p. Size(FST p) = LENGTH(SND p))
           (AP(MAP $, trl)(PART(MAP Size trl)(TL l)))"),
     ONCE_REWRITE_TAC [INST_TYPE [":num",":*"] EQ_SYM_EQ] THEN
     REWRITE_TAC [Size_thm;LENGTH_CONS] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [HD;TL] THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     MAP_EVERY SPEC_TAC [("l':(*)list","l:(*)list");
                         ("trl:(tree)list","trl:(tree)list")] THEN
     LIST_INDUCT_TAC THENL
     [REWRITE_TAC [MAP;AP;PART;ALL_EL];
     REWRITE_TAC [MAP;SUM;PART] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC LENGTH_SND_SPLIT THEN RES_TAC THEN
     ASM_REWRITE_TAC [ALL_EL;AP;HD;TL] THEN
     CONV_TAC BETA_CONV THEN
     REWRITE_TAC [] THEN IMP_RES_TAC LENGTH_FST_SPLIT]);;

% Another								%
let lemma7 = 
    TAC_PROOF(
     ([], "!trl. 
           ALL_EL (\t.!l. (Size t = LENGTH l) ==> 
		 (x(ABS_ltree(t,l)) = y(ABS_ltree(t,l)))) trl ==>
           (!l:((*)list)list.
            ALL_EL (\p. Size(FST p) = LENGTH(SND p)) (AP(MAP $, trl)l) ==>
           (MAP x(MAP ABS_ltree(AP(MAP $, trl)l)):(**)list =
            MAP y(MAP ABS_ltree(AP(MAP $, trl)l))))"),
     LIST_INDUCT_TAC THENL
     [REWRITE_TAC [ALL_EL;MAP;AP];
      REWRITE_TAC [ALL_EL;MAP;AP] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      ASM_REWRITE_TAC []]);; 

% Prove the axiom for (*)ltree						%
let ltree_Axiom = 
    prove_thm
    (`ltree_Axiom`,
     "!f. ?!fn. !v tl. fn(Node (v:*) tl):** = f (MAP fn tl) v tl",
     GEN_TAC THEN MP_TAC (SPEC_ALL REP_REC_lemma) THEN
     PURE_REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
     STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC "(fn:^ty->**) o REP_ltree" THEN
      ASM_REWRITE_TAC [REP_Node;o_THM;TL;HD;lemma1;lemma2];
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
      STRIP_ASSUME_TAC (SPEC "l:(*)ltree" A_ONTO) THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM SUBST1_TAC THEN
      PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL PAIR)] THEN
      PURE_REWRITE_TAC [Is_ltree] THEN
      SPEC_TAC ("SND (r:tree # (*)list)","l:(*)list") THEN
      SPEC_TAC ("FST (r:tree # (*)list)", "t:tree") THEN
      tree_INDUCT_TAC THEN 
      REPEAT STRIP_TAC THEN 
      IMP_RES_THEN SUBST1_TAC lemma5 THEN
      ASM_REWRITE_TAC [] THEN
      IMP_RES_TAC lemma6 THEN
      IMP_RES_TAC lemma7 THEN
      POP_ASSUM SUBST1_TAC THEN REFL_TAC]);;

% get uniqueness part of ltree_Axiom					%
let unique_lemma = 
     GEN_ALL(CONJUNCT2(CONV_RULE EXISTS_UNIQUE_CONV (SPEC_ALL ltree_Axiom)));;

% Prove induction thm for (*)ltree					%
let ltree_Induct = 
     save_thm
     (`ltree_Induct`,
      let unique = CONV_RULE (DEPTH_CONV BETA_CONV) unique_lemma in
      let spec = 
               SPECL ["\b v tl.(ALL_EL (\x.x:bool) b \/ P (Node (v:*) tl))";
	              "\t:(*)ltree.T";"P:(*)ltree -> bool"]
		 (INST_TYPE [":bool",":**"] (GEN_ALL unique)) in
      let conv = CONV_RULE(REDEPTH_CONV(BETA_CONV ORELSEC FUN_EQ_CONV))spec in
      let rew1 = TAC_PROOF(([], "(X = Y \/ X) = (Y ==> X)"),
			  ASM_CASES_TAC "X:bool" THEN ASM_REWRITE_TAC[]) in
      let rew2 = TAC_PROOF(([], "(!h:*. !t. ALL_EL P t ==> P(Node h t)) = 
			         (!t. ALL_EL P t ==> !h. P(Node h t))"),
			   REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
			   RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC) in
      let rew3 = 
       TAC_PROOF(([], "!l:(*)list. ALL_EL (\x.x) (MAP (\x.T) l)"),
                 LIST_INDUCT_TAC THEN
		 ASM_REWRITE_TAC [MAP;ALL_EL] THEN
                 CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
		 REPEAT GEN_TAC THEN REFL_TAC) in
      let rew4 = 
       TAC_PROOF(([], "!l:(*)list. ALL_EL (\x.x) (MAP P l) = ALL_EL P l"),
                 LIST_INDUCT_TAC THEN
		 ASM_REWRITE_TAC [MAP;ALL_EL] THEN
                 CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
		 REPEAT GEN_TAC THEN REFL_TAC) in
      GEN_ALL(REWRITE_RULE [rew1;rew3;rew2;rew4] conv));;

let exists_lemma = 
     GEN_ALL(CONJUNCT1(CONV_RULE EXISTS_UNIQUE_CONV (SPEC_ALL ltree_Axiom)));;

let Node_11 = 
    prove_thm
    (`Node_11`,
     "!v1:*. !v2 trl1 trl2. 
           ((Node v1 trl1) = (Node v2 trl2)) = ((v1 = v2) /\ (trl1 = trl2))",
    MP_TAC (SPEC "\l:(*)list. \v:*. \trl:((*)ltree)list. v"
	   (INST_TYPE [":*",":**"] exists_lemma)) THEN
    MP_TAC (SPEC "\l:(((*)ltree)list)list. \v:*.\trl:((*)ltree)list. trl"
	   (INST_TYPE [":((*)ltree)list",":**"] (GEN_ALL exists_lemma))) THEN
    CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
    [POP_ASSUM (MP_TAC o AP_TERM "fn':(*)ltree->*") THEN ASM_REWRITE_TAC[];
     POP_ASSUM (MP_TAC o AP_TERM "fn:(*)ltree->((*)ltree)list") THEN
     ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[]]);;

% ---------------------------------------------------------------------	%
%   ltree_INDUCT: thm  -> thm						%
%									%
%     A |- !tl. ALL_EL \t.P[t] tl ==> !v. P[Node v tl]			%
% ----------------------------------------------------------		%
%               A |- !t. P[t]						%
%									%
% ---------------------------------------------------------------------	%

let ltree_INDUCT th =
 (let (tl,body) = dest_forall(concl th) in
  let (asm,v,con) = (I # dest_forall) (dest_imp body) in
  let ALL_EL,[P;tll] = strip_comb asm in
  let b = genvar bool_ty in
  let concth = SYM(RIGHT_BETA(REFL "^P(Node ^v ^tl)")) and
      IND    = SPEC P (INST_TYPE [type_of v,":*"] ltree_Induct) and
      th'    = DISCH asm (SPEC v (UNDISCH(SPEC tl th))) in
  let th1 = SUBST [concth,b]
                  "^(concl th') = (ALL_EL ^P ^tl ==> ^b)"
                  (REFL (concl th')) in
  let th2 = GEN tl (DISCH asm (GEN v(UNDISCH (EQ_MP th1 th')))) in
  CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND th2)?failwith `ltree_INDUCT`);;


% ---------------------------------------------------------------------	%
%									%
% ltree_INDUCT_TAC							%
%									%
%             [A] !t.P[t]						%
%  ================================					%
%    [A,ALL_EL \t.P[t] trl] |- !v. P[Node v trl]				%
%									%
% ---------------------------------------------------------------------	%

let ltree_INDUCT_TAC (A,term) =
 (let t,body = dest_forall term in
  let t' = variant ((frees term) @ (freesl A)) t in
  let t_ty = hd(snd(dest_type(type_of t))) in
  let body' = subst [t',t] body in
  let v' = variant ((frees body') @ (freesl A)) "v:^t_ty" in
  let trl = variant ((frees body') @ (freesl A)) "trl:((^t_ty)ltree)list" in
  let asm = "ALL_EL (\^t'.^body') trl" in
 ([ (asm.A, mk_forall (v',subst["Node (^v') ^trl",t']body'))],
  \[thm]. ltree_INDUCT (GEN trl (DISCH asm thm)))
 ) ? failwith `ltree_INDUCT_TAC`;;

% Need this theorem						%
let Node_onto = 
    prove_thm
    (`Node_onto`,
     "!t:(*)ltree. ?v:*. ?trl. t = Node v trl",
       ltree_INDUCT_TAC THEN STRIP_TAC THEN 
       MAP_EVERY EXISTS_TAC ["v:*";"trl:((*)ltree)list"] THEN REFL_TAC);;

close_theory();;

quit();;
