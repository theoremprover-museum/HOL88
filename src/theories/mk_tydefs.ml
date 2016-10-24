%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_tydefs.ml                                          %
%                                                                             %
%     DESCRIPTION:      Creates the theory "tydefs.th" containing the master  %
%                       theorem for axiomatizing all recursive types.         %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.07.27)                               %
%                                                                             %
%     PARENTS:          ltree.th                                              %
%     WRITES FILES:     tydefs.th                                             %
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
%     REVISION HISTORY: 90.04.11                                              %
%=============================================================================%

% Create the new theory							%
new_theory `tydefs`;;

% Parent theories							%
map new_parent [`ltree`];;

% Fetch theorems from combin.th						%
let o_THM = theorem `combin` `o_THM`;;

% load list induction theorem						%
let list_INDUCT 	= theorem `list` `list_INDUCT`;;
let MAP_o = theorem `list` `MAP_o`;;

% load thms from ltree.th						%
let ltree_Axiom  =  theorem `ltree` `ltree_Axiom` and
    ltree_Induct =  theorem `ltree` `ltree_Induct`;;

% Load theorems from list.th.						%
let ALL_EL		 = definition `list` `ALL_EL` and
    MAP			 = definition `list` `MAP`;;

% ---------------------------------------------------------------------	%
% Load/define code needed.						%
% ---------------------------------------------------------------------	%

% We need to load in the induction tactic.  It's in ml/ind.ml		%
% but it is part of hol rather than basic hol, so it's loaded   	%
% in uncompiled.							%
%									%
% TFM 88.04.02								%
loadt (concat ml_dir_pathname `ind.ml`);;

% Create a tactic for list induction.					%
let LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;;

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
  CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) (MP IND th2) ?
  failwith `ltree_INDUCT`);;


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


% First, a little lemma about Node.					%
let Node_onto = 
     TAC_PROOF(([], "!t:(*)ltree. ?v:*. ?trl. t = Node v trl"),
	  ltree_INDUCT_TAC THEN STRIP_TAC THEN 
          MAP_EVERY EXISTS_TAC ["v:*";"trl:((*)ltree)list"] THEN REFL_TAC);;

% A little lemma about ALL_EL and MAP					%
let ALL_EL_MAP_lemma = 
    TAC_PROOF (([], "!l:(*)list. ALL_EL (\x.x) (MAP P l) = ALL_EL P l"),
               LIST_INDUCT_TAC THEN
	       REWRITE_TAC [ALL_EL;MAP] THEN
	       CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	       REPEAT STRIP_TAC THEN RES_TAC THEN
	       ASM_REWRITE_TAC[]);;

% Existence part of ltree_Axiom.					%
let exists_lemma = 
     GEN_ALL(CONJUNCT1(CONV_RULE EXISTS_UNIQUE_CONV (SPEC_ALL ltree_Axiom)));;

% Show that for every predicate P on Nodes of a (*)ltree, there is a	%
% predicate TRP that holds of a (*)ltree if P holds of every node in	%
% the tree.								%
let TRP_thm = 
    TAC_PROOF(
     ([], "!P. ?TRP. !v:*. !tl. TRP(Node v tl) = P v tl /\ ALL_EL TRP tl"),
     STRIP_TAC THEN
     MP_TAC (SPEC "\rl:(bool)list. \v:*. \tl:((*)ltree)list. 
		    P v tl /\ ALL_EL (\x.x) rl"
  	     (INST_TYPE [":bool",":**"] exists_lemma)) THEN
     CONV_TAC (REDEPTH_CONV BETA_CONV) THEN 
     REWRITE_TAC [ALL_EL_MAP_lemma] THEN STRIP_TAC THEN
     EXISTS_TAC "fn:(*)ltree->bool" THEN 
     POP_ASSUM ACCEPT_TAC);;

% A lemma 								%
let lemma1 = 
    TAC_PROOF(
     ([], "!l:(*)list. !x y. 
           (ALL_EL P l /\ ALL_EL (\e. P e ==> (x e:** = y e)) l) ==>
	   (MAP x l = MAP y l)"),
     LIST_INDUCT_TAC THEN REWRITE_TAC [ALL_EL;MAP] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

% There is a unique function on trees all of whose nodes satisfy P	%
% Following proof revised for version 1.12 resolution. 	 [TFM 91.01.18] %
let TRP_EU = 
    TAC_PROOF(
     ([], 
    "!TRP:(*)ltree->bool. !P.
     (!v:*. !tl. TRP(Node v tl) = P v tl /\ ALL_EL TRP tl) ==>
     !f. (?fn. !v tl. TRP(Node v tl) ==> 
     		      (fn(Node v tl):** = f (MAP fn tl) v tl)) /\
         !x y. (!v tl. TRP(Node v tl) ==>
 		       (x(Node v tl) = f (MAP x tl) v tl)) ==>
               (!v tl. TRP(Node v tl) ==> 
		       (y(Node v tl) = f (MAP y tl) v tl)) ==>
	       (!t. TRP t  ==> (x t = y t))"),
     REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CONJ_TAC THENL
     [STRIP_ASSUME_TAC 
         (SPEC "f:(**)list->*->((*)ltree)list->**" exists_lemma) THEN
      EXISTS_TAC "fn:(*)ltree->**" THEN ASM_REWRITE_TAC [];
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ltree_INDUCT_TAC THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN
      IMP_RES_TAC lemma1 THEN ASM_REWRITE_TAC []]);;

% define a function TRP P t = P holds of every node in t		%
let TRP_DEF = 
    new_definition
     (`TRP_DEF`, 
       "TRP P = @trp. !v:*. !tl. trp(Node v tl) = P v tl /\ ALL_EL trp tl");;

let TRP = 
    prove_thm
    (`TRP`,
     "!P v tl.(TRP P) (Node v tl) = P (v:*) tl /\ ALL_EL (TRP P)tl",
      REWRITE_TAC [TRP_DEF] THEN 
      CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
      MATCH_ACCEPT_TAC TRP_thm);;

% There is a unique recursive function on TRP-subsets of (*)ltree	%
%									%
% |- !P f.								%
%    (?fn. !v tl. TRP P(Node v tl) ==> 					%
%  	          (fn(Node v tl) = f(MAP fn tl)v tl)) /\		%
%    (!x y. (!v tl. TRP P(Node v tl) ==> 				%
%		    (x(Node v tl) = f(MAP x tl)v tl)) ==>		%
%           (!v tl. TRP P(Node v tl) ==> 				%
%		    (y(Node v tl) = f(MAP y tl)v tl)) ==>		%
%           (!x. TRP P x ==> (x x = y x)))				%
 
let TRP_EU_thm = 
    GEN_ALL (MATCH_MP TRP_EU (SPEC "P:*->((*)ltree)list->bool" TRP));;

% Some lemmas about ABS and REP						%
let AR_lemma1 = 
    TAC_PROOF(([],"(!a:**.ABS(REP a:(*)ltree) = a) ==>
		   (!r:(*)ltree. TRP P r = (REP(ABS r:**) = r)) ==>
       		   !tl. ALL_EL (TRP P) (MAP REP tl)"),
              REPEAT DISCH_TAC THEN LIST_INDUCT_TAC THEN
	      ASM_REWRITE_TAC [MAP;ALL_EL]);;

let AR_lemma2 = 
    TAC_PROOF(([],"(!a:**.ABS(REP a:(*)ltree) = a) ==>
		   (!r:(*)ltree. TRP P r = (REP(ABS r:**) = r)) ==>
                   !tl v. P v (MAP REP tl) ==> 
	           (REP(ABS(Node v (MAP REP tl))) = Node v (MAP REP tl))"),
     DISCH_TAC THEN 
     DISCH_THEN (\th. REWRITE_TAC [SYM(SPEC_ALL th)] THEN
		      ASSUME_TAC th) THEN
     IMP_RES_TAC AR_lemma1 THEN 
     REWRITE_TAC [TRP] THEN
     ASM_REWRITE_TAC[]);;
	      
let AR_lemma3 = 
    TAC_PROOF(([], "(!a:**.ABS(REP a:(*)ltree) = a) ==>
		    (!r:(*)ltree. TRP P r = (REP(ABS r:**) = r)) ==>
                    !trl. ALL_EL (TRP P) trl ==> ?tl. trl = MAP REP tl"),
    REPEAT DISCH_TAC THEN LIST_INDUCT_TAC THENL
    [REWRITE_TAC[ALL_EL] THEN 
     EXISTS_TAC "NIL:(**)list" THEN REWRITE_TAC [MAP];
     ASM_REWRITE_TAC [ALL_EL] THEN REPEAT STRIP_TAC THEN 
     RES_THEN STRIP_ASSUME_TAC THEN
     EXISTS_TAC "CONS (ABS (h:(*)ltree):**) tl" THEN
     ASM_REWRITE_TAC [MAP]]);;

let AR_lemma4 = 
    TAC_PROOF(([], "(!a:**.ABS(REP a:(*)ltree) = a) ==>
                    (!al. MAP ABS (MAP REP al) = al)"),
  	      STRIP_TAC THEN
	      LIST_INDUCT_TAC THEN
	      ASM_REWRITE_TAC [MAP]);;

let AR_lemma5 = 
    (GEN_ALL o UNDISCH_ALL o hd o IMP_CANON o DISCH_ALL o prove_abs_fn_onto)
    (ASSUME "(!a:**.ABS(REP a:(*)ltree) = a) /\
	     (!r:(*)ltree. TRP P r = (REP(ABS r:**) = r))");;

%< Moved to the theory list (file mk_list_thm2.ml) by WW 5 Jan 94
let MAP_o = 
    prove_thm
     (`MAP_o`,
      "!f:**->***. !g:*->**.  MAP (f o g) = (MAP f) o (MAP g)",
      REPEAT GEN_TAC THEN
      CONV_TAC FUN_EQ_CONV THEN
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [MAP;o_THM]);; >%
	
% ===================================================================== %
% NOW... the main theorem....						%
% Following proof revised for version 1.12 resolution. 	 [TFM 91.01.18] %
% ===================================================================== %

let TY_DEF_THM = 
    prove_thm
    (`TY_DEF_THM`,
     "!REP. !ABS. !P.
      ((!a:**.ABS(REP a:(*)ltree) = a) /\ 
       (!r:(*)ltree. TRP P r = (REP(ABS r:**) = r))) ==>
      !f. ?!fn. !v:*. !tl. 
      P v (MAP REP tl) ==> 
      (fn(ABS(Node v (MAP REP tl)):**):*** = f (MAP fn tl) v tl)",
    REPEAT GEN_TAC THEN 
    CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN 
    CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
    REPEAT STRIP_TAC THENL
    [MP_TAC (CONJUNCT1 
          (SPECL ["P:*->((*)ltree)list->bool";
                  "\l:(***)list.\v:*.\tl:((*)ltree)list.
		    f l v (MAP ABS tl:(**)list):***"]
                   (INST_TYPE [":***",":**"] TRP_EU_thm))) THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     PURE_ONCE_REWRITE_TAC [TRP] THEN
     REPEAT STRIP_TAC THEN 
     EXISTS_TAC "((fn:(*)ltree->***) o REP):(**)->***" THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     ASSUME_TAC (SPEC_ALL (UNDISCH_ALL AR_lemma1)) THEN
     IMP_RES_TAC AR_lemma2 THEN 
     IMP_RES_TAC AR_lemma4 THEN
     RES_TAC THEN ASM_REWRITE_TAC [MAP_o;o_THM];
     REPEAT_TCL STRIP_THM_THEN (\th g. SUBST1_TAC th g ? MP_TAC th g)
     	        (SPEC "x:**" AR_lemma5) THEN
     SPEC_TAC ("r:(*)ltree","r:(*)ltree") THEN
     MP_TAC (CONJUNCT2 
          (SPECL ["P:*->((*)ltree)list->bool";
                  "\l:(***)list.\v:*.\tl:((*)ltree)list.
		    f l v (MAP ABS tl:(**)list):***"]
                   (INST_TYPE [":***",":**"] TRP_EU_thm))) THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     DISCH_THEN 
        (MP_TAC o (REWRITE_RULE [SYM(ANTE_CONJ_CONV "A /\ B ==> C")])) THEN
     DISCH_THEN (MP_TAC o (SPECL["((fn:**->***) o ABS):(*)ltree->***";
				 "((fn':**->***) o ABS):(*)ltree->***"])) THEN
     REWRITE_TAC [o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
     REWRITE_TAC [TRP] THEN
     CONJ_TAC THEN REPEAT GEN_TAC THEN 
     CONV_TAC ANTE_CONJ_CONV THEN
     DISCH_THEN (\t. STRIP_TAC THEN MP_TAC t) THEN
     IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) (UNDISCH_ALL AR_lemma3) THEN 
     IMP_RES_TAC AR_lemma4 THEN ASM_REWRITE_TAC [MAP_o;o_THM]]);;

% For use in type definition package...					%
let exists_TRP = 
    prove_thm
    (`exists_TRP`,
     "!P. (?v:*. P v NIL) ==> ?t:(*)ltree. TRP P t",
     GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC "Node (v:*) NIL" THEN
     ASM_REWRITE_TAC [TRP;ALL_EL]);;

close_theory();;

quit();;

