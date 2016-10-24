%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_list_thms.ml                                       %
%                                                                             %
%     DESCRIPTION:      Extends the theory list.th with some theorems         %
%                       Definitions have been moved to mk_list_defs.ml        %
%                                                                             %
%     AUTHORS:          T. F. Melham (86.11.24)                               %
%                       W. Wong (2 Jan 94)                                    %
%                                                                             %
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
%                       W. Wong 1994                                          %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% --------------------------------------------------------------------- %
% Reopen the theory							%
% --------------------------------------------------------------------- %
load_theory `list`;;

% --------------------------------------------------------------------- %
% fetch axiom and definitions for lists.				%
% --------------------------------------------------------------------- %
let list_Axiom = theorem `list` `list_Axiom`;;
let NULL_DEF   = definition `list` `NULL_DEF`;;
let HD         = definition `list` `HD`;;
let TL         = definition `list` `TL`;;
let SNOC       = definition `list` `SNOC`;;
let FOLDR      = definition `list` `FOLDR`;;
let FOLDL      = definition `list` `FOLDL`;;
let FILTER     = definition `list` `FILTER`;;
let MAP        = definition `list` `MAP`;;
let MAP2       = definition `list` `MAP2`;;
let SCANR      = definition `list` `SCANR`;;
let SCANL      = definition `list` `SCANL`;;
let SEG        = definition `list` `SEG`;;
let REVERSE    = definition `list` `REVERSE`;;
let APPEND     = definition `list` `APPEND`;;
let FLAT       = definition `list` `FLAT`;;
let LENGTH     = definition `list` `LENGTH`;;
let ALL_EL     = definition `list` `ALL_EL`;;
let SOME_EL    = definition `list` `SOME_EL`;;
let IS_EL_DEF  = definition `list` `IS_EL_DEF`;;
let AND_EL_DEF = definition `list` `AND_EL_DEF`;;
let OR_EL_DEF  = definition `list` `OR_EL_DEF`;;
let FIRSTN     = definition `list` `FIRSTN`;;
let BUTFIRSTN  = definition `list` `BUTFIRSTN`;;
let LASTN      = definition `list` `LASTN`;;
let BUTLASTN   = definition `list` `BUTLASTN`;;
let LAST_DEF   = definition `list` `LAST_DEF`;;
let BUTLAST_DEF = definition `list` `BUTLAST_DEF`;;
let EL         = definition `list` `EL`;;
let ELL	       = definition `list` `ELL`;;
let IS_PREFIX  = definition `list` `IS_PREFIX`;;
let IS_SUFFIX  = definition `list` `IS_SUFFIX`;;
let IS_SUBLIST = definition `list` `IS_SUBLIST`;;
let SPLITP     = definition `list` `SPLITP`;;
let PREFIX_DEF = definition `list` `PREFIX_DEF`;;
let SUFFIX_DEF = definition `list` `SUFFIX_DEF`;;
let ZIP        = definition `list` `ZIP`;;
let UNZIP      = definition `list` `UNZIP`;;
let UNZIP_FST_DEF  = definition `list` `UNZIP_FST_DEF`;;
let UNZIP_SND_DEF  = definition `list` `UNZIP_SND_DEF`;;
let SUM        = definition `list` `SUM`;;
let GENLIST    = definition `list` `GENLIST`;;
let REPLICATE  = definition `list` `REPLICATE`;;

% --------------------------------------------------------------------- %
% Fetch a few theorems from num.th					%
% --------------------------------------------------------------------- %
let NOT_SUC = theorem `num` `NOT_SUC`;;
let INV_SUC = theorem `num` `INV_SUC`;;
let INDUCTION = theorem `num` `INDUCTION`;;

% --------------------------------------------------------------------- %
% Fetch a few theorems from prim_rec.th					%
% --------------------------------------------------------------------- %
%<
let num_Axiom = theorem `prim_rec` `num_Axiom`;;
let NOT_LESS_0 = theorem `prim_rec` `NOT_LESS_0`;;
let LESS_0 = theorem `prim_rec` `LESS_0`;;
let LESS_MONO = theorem `prim_rec` `LESS_MONO`;;
let INV_SUC_EQ = theorem `prim_rec` `INV_SUC_EQ`;;
>%
map
 autoload_theory
 [`theorem`, `prim_rec`, `INV_SUC_EQ`;
  `theorem`, `prim_rec`, `LESS_REFL`;
  `theorem`, `prim_rec`, `SUC_LESS`;
  `theorem`, `prim_rec`, `NOT_LESS_0`;
  `theorem`, `prim_rec`, `LESS_MONO`;
  `theorem`, `prim_rec`, `LESS_SUC_REFL`;
  `theorem`, `prim_rec`, `LESS_SUC`;
  `theorem`, `prim_rec`, `LESS_THM`;
  `theorem`, `prim_rec`, `LESS_SUC_IMP`;
  `theorem`, `prim_rec`, `LESS_0`;
  `theorem`, `prim_rec`, `EQ_LESS`;
  `theorem`, `prim_rec`, `SUC_ID`;
  `theorem`, `prim_rec`, `NOT_LESS_EQ`;
  `theorem`, `prim_rec`, `LESS_NOT_EQ`;
  `theorem`, `prim_rec`, `LESS_SUC_SUC`;
  `theorem`, `prim_rec`, `PRE`;
  `theorem`, `prim_rec`, `num_Axiom`];;

% --------------------------------------------------------------------- %
% Fetch a few things from arithmetic.th					%
% --------------------------------------------------------------------- %
%<
let ADD_CLAUSES = theorem `arithmetic` `ADD_CLAUSES`;;
let LESS_MONO_EQ = theorem `arithmetic` `LESS_MONO_EQ`;;
let ADD_EQ_0 = theorem `arithmetic` `ADD_EQ_0`;;
let SUC_NOT = theorem `arithmetic` `SUC_NOT`;; % WW %
let EQ_MONO_ADD_EQ = theorem `arithmetic` `EQ_MONO_ADD_EQ;;
let ADD1 = theorem `arithmetic` `ADD1`;;
>%

map
 autoload_theory
 [`definition`, `arithmetic`, `LESS_OR_EQ`;
  `definition`, `arithmetic`, `ADD`;
  `definition`, `arithmetic`, `SUB`;

  `theorem`, `arithmetic`, `ADD_SUC`;
  `theorem`, `arithmetic`, `ADD_CLAUSES`;
  `theorem`, `arithmetic`, `ADD_SYM`;
  `theorem`, `arithmetic`, `LESS_MONO_EQ`;
  `theorem`, `arithmetic`, `SUC_SUB1`;
  `theorem`, `arithmetic`, `LESS_ADD`;
  `theorem`, `arithmetic`, `SUB_0`;
  `theorem`, `arithmetic`, `LESS_TRANS`;
  `theorem`, `arithmetic`, `ADD1`;
  `theorem`, `arithmetic`, `ADD_0`;
  `theorem`, `arithmetic`, `LESS_ANTISYM`;
  `theorem`, `arithmetic`, `LESS_LESS_SUC`;

  `theorem`, `arithmetic`, `LESS_SUC_EQ_COR`;
  `theorem`, `arithmetic`, `LESS_OR`;
  `theorem`, `arithmetic`, `OR_LESS`;
  `theorem`, `arithmetic`, `LESS_EQ`;
  `theorem`, `arithmetic`, `LESS_NOT_SUC`;

  `theorem`, `arithmetic`, `LESS_EQ_ANTISYM`;
  `theorem`, `arithmetic`, `LESS_EQ_ADD`;
  `theorem`, `arithmetic`, `NOT_LESS`;
  `theorem`, `arithmetic`, `SUB_EQ_0`;
  `theorem`, `arithmetic`, `ADD_ASSOC`;
  `theorem`, `arithmetic`, `SUB_ADD`;
  `theorem`, `arithmetic`, `ADD_EQ_0`;
  `theorem`, `arithmetic`, `ADD_INV_0_EQ`;

  `theorem`, `arithmetic`, `LESS_SUC_NOT`;
  `theorem`, `arithmetic`, `LESS_MONO_ADD`;
  `theorem`, `arithmetic`, `LESS_MONO_ADD_EQ`;
  `theorem`, `arithmetic`, `EQ_MONO_ADD_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_MONO_ADD_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_TRANS`;
  `theorem`, `arithmetic`, `LESS_EQ_LESS_EQ_MONO`;
  `theorem`, `arithmetic`, `LESS_EQ_REFL`;
  `theorem`, `arithmetic`, `LESS_IMP_LESS_OR_EQ`;
  `theorem`, `arithmetic`, `LESS_MONO_MULT`;
  `theorem`, `arithmetic`, `LESS_0_CASES`;

  `theorem`, `arithmetic`, `ZERO_LESS_EQ`;
  `theorem`, `arithmetic`, `LESS_EQ_MONO`;
  `theorem`, `arithmetic`, `LESS_OR_EQ_ADD`;
  `theorem`, `arithmetic`, `SUC_NOT`;

  `theorem`, `arithmetic`, `SUB_MONO_EQ`;
  `theorem`, `arithmetic`, `SUB_LESS_EQ`;
  `theorem`, `arithmetic`, `LESS_EQUAL_ANTISYM`;
  `theorem`, `arithmetic`, `SUB_LESS_0`;
  `theorem`, `arithmetic`, `SUB_LESS_OR`;
  `theorem`, `arithmetic`, `LESS_ADD_SUC`;
  `theorem`, `arithmetic`, `LESS_SUB_ADD_LESS`;
  `theorem`, `arithmetic`, `ADD_SUB`;
  `theorem`, `arithmetic`, `LESS_EQ_ADD_SUB`;
  `theorem`, `arithmetic`, `SUB_EQUAL_0`;
  `theorem`, `arithmetic`, `LESS_EQ_SUB_LESS`;
  `theorem`, `arithmetic`, `NOT_SUC_LESS_EQ`;
  `theorem`, `arithmetic`, `SUB_SUB`;
  `theorem`, `arithmetic`, `LESS_IMP_LESS_ADD`;
  `theorem`, `arithmetic`, `LESS_EQ_IMP_LESS_SUC`;
  `theorem`, `arithmetic`, `SUB_LESS_EQ_ADD`;
  `theorem`, `arithmetic`, `LESS_LESS_CASES`;
  `theorem`, `arithmetic`, `LESS_EQ_0`;


  `theorem`, `arithmetic`, `EQ_LESS_EQ`;
  `theorem`, `arithmetic`, `ADD_MONO_LESS_EQ`;
  `theorem`, `arithmetic`, `NOT_SUC_LESS_EQ_0`;

  `theorem`, `arithmetic`, `PRE_SUC_EQ`;
  `theorem`, `arithmetic`, `NOT_LEQ`;
  `theorem`, `arithmetic`, `NOT_NUM_EQ`;
  `theorem`, `arithmetic`, `NOT_GREATER`;
  `theorem`, `arithmetic`, `NOT_GREATER_EQ`;
  `theorem`, `arithmetic`, `SUC_ONE_ADD`;
  `theorem`, `arithmetic`, `SUC_ADD_SYM`;
  `theorem`, `arithmetic`, `NOT_SUC_ADD_LESS_EQ`;
  `theorem`, `arithmetic`, `MULT_LESS_EQ_SUC`;
  `theorem`, `arithmetic`, `PRE_SUB1`;
  `theorem`, `arithmetic`, `SUB_PLUS`;
  `theorem`, `arithmetic`, `GREATER_EQ`
];;



% --------------------------------------------------------------------- %
% Fetch a few definitions and theorems from fun.th			%
% --------------------------------------------------------------------- %
let ASSOC_DEF =  definition `fun` `ASSOC_DEF`;;
let COMM_DEF =  definition `fun` `COMM_DEF`;;
let FCOMM_DEF =  definition `fun` `FCOMM_DEF`;;
let RIGHT_ID_DEF =  definition `fun` `RIGHT_ID_DEF`;;
let LEFT_ID_DEF =  definition `fun` `LEFT_ID_DEF`;;
let MONOID_DEF =  definition `fun` `MONOID_DEF`;;

let ASSOC_CONJ =  theorem `fun` `ASSOC_CONJ`;;
let ASSOC_DISJ =  theorem `fun` `ASSOC_DISJ`;;
let FCOMM_ASSOC =  theorem `fun` `FCOMM_ASSOC`;;
let MONOID_CONJ_T =  theorem `fun` `MONOID_CONJ_T`;;
let MONOID_DISJ_F =  theorem `fun` `MONOID_CONJ_T`;;
% --------------------------------------------------------------------- %
% Fetch a few definitions and theorems from combin.th			%
% --------------------------------------------------------------------- %
let o_DEF = definition `combin` `o_DEF`;;
let o_THM = theorem `combin` `o_THM`;;
let I_THM = theorem `combin` `I_THM`;;

let UNCURRY_DEF = definition `bool` `UNCURRY_DEF`;;

% --------------------------------------------------------------------- %
% We need to load in the induction tactic.  It's in ml/ind.ml, but it	%
% is part of hol rather than basic hol. So it's loaded in uncompiled 	%
% (because it may not have been recompiled since basic-hol was last	%
% rebuilt. 						 [TFM 88.04.02] %
% --------------------------------------------------------------------- %

loadt (concat ml_dir_pathname `ind.ml`);;

% --------------------------------------------------------------------- %
% Create an induction tactic for :num					%
% --------------------------------------------------------------------- %
let INDUCT_TAC = INDUCT_THEN (theorem `num` `INDUCTION`) ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Load the code for primitive recursive definitions on arbitrary types.	%
% 									%
% Note that prim_rec_ml.o must be recompiled if basic-hol has been	%
% rebuilt. The uncompiled version is therefore loaded here.        	%
%									%
% TFM 88.04.02								%
% --------------------------------------------------------------------- %
loadt (concat ml_dir_pathname `prim_rec.ml`);;

% --------------------------------------------------------------------- %
% Load the auxiliary code for recursive types.				%
% NOTE: uses things defined in prim_rec.ml (load uncompiled)		%
% --------------------------------------------------------------------- %
loadt (concat ml_dir_pathname `tyfns.ml`);;

loadt (concat ml_dir_pathname `numconv.ml`);;
% ---------------------------------------------------------------------	%
% Proofs of some theorems about lists.					%
% --------------------------------------------------------------------- %

let NULL = 
    prove_thm
     (`NULL`,
      "(NULL (NIL:(*)list)) /\ !h t. ~NULL(CONS (h:*) t)",
      REWRITE_TAC [NULL_DEF]);;

% List induction							%
% |- P NIL /\ (!t. P t ==> !h. P(CONS h t)) ==> (!x.P x) 		%

let list_INDUCT = 
     save_thm (`list_INDUCT`, prove_induction_thm list_Axiom);;

% Create a tactic.							%
let LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;;

% Cases theorem: |- !l. (l = []) \/ (?t h. l = CONS h t)		%
let list_CASES = 
    save_thm(`list_CASES`, prove_cases_thm list_INDUCT);;

% CONS11:  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t') %
let CONS_11 = 
    save_thm(`CONS_11`, prove_constructors_one_one list_Axiom);;

let NOT_NIL_CONS = 
    save_thm(`NOT_NIL_CONS`, prove_constructors_distinct list_Axiom);;

let NOT_CONS_NIL = 
    save_thm
     (`NOT_CONS_NIL`, CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);;

let LIST_NOT_EQ =
    prove_thm
    (`LIST_NOT_EQ`,
     "!l1 l2. ~(l1 = l2) ==> !h1:*. !h2. ~(CONS h1 l1 = CONS h2 l2)",
     REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [CONS_11]);;

let NOT_EQ_LIST =
    prove_thm
    (`NOT_EQ_LIST`,
     "!h1:*. !h2. ~(h1 = h2) ==> !l1 l2. ~(CONS h1 l1 = CONS h2 l2)",
     REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [CONS_11]);;

let EQ_LIST =
    prove_thm
    (`EQ_LIST`,
     "!h1:*.!h2.(h1=h2) ==> !l1 l2. (l1 = l2) ==> (CONS h1 l1 = CONS h2 l2)",
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [CONS_11]);;

let CONS = 
    prove_thm 
      (`CONS`,
       "!l:(*)list. ~NULL l ==> (CONS (HD l) (TL l) = l)",
       STRIP_TAC THEN
       STRIP_ASSUME_TAC (SPEC "l:(*)list" list_CASES) THEN
       POP_ASSUM SUBST1_TAC THEN
       ASM_REWRITE_TAC [HD;TL;NULL]);;


let APPEND_ASSOC = 
    prove_thm
     (`APPEND_ASSOC`,
      "!l1:(*)list. !l2 l3. 
	APPEND l1 (APPEND l2 l3) = (APPEND (APPEND l1 l2) l3)",
      LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);;

let LENGTH_APPEND = 
    prove_thm
     (`LENGTH_APPEND`,
      "!l1:(*)list.!l2:(*)list. 
         LENGTH (APPEND l1 l2) = (LENGTH l1) + (LENGTH l2)",
      LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;APPEND;ADD_CLAUSES]);;

let MAP_APPEND = 
    prove_thm
     (`MAP_APPEND`,
      "!f:*->**.!l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)",
      STRIP_TAC THEN
      LIST_INDUCT_TAC THEN 
      ASM_REWRITE_TAC [MAP;APPEND]);;

let LENGTH_MAP = 
    prove_thm
     (`LENGTH_MAP`,
      "!l. !f:*->**. LENGTH (MAP f l) = LENGTH l",
      LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;LENGTH]);;

%< DELETED by WW 2 Jan 94 EVERY --> ALL_EL
let EVERY_EL = 
    prove_thm
     (`EVERY_EL`,
      "!l P. EVERY P l = !n. n < LENGTH l ==> P(EL n l:*)",
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [EVERY_DEF;LENGTH;NOT_LESS_0] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN INDUCT_TAC THENL
       [ASM_REWRITE_TAC [EL;HD];
        ASM_REWRITE_TAC [LESS_MONO_EQ;EL;TL]];
       REPEAT STRIP_TAC THENL
       [POP_ASSUM (MP_TAC o SPEC "0") THEN
        REWRITE_TAC [LESS_0;EL;HD];
	POP_ASSUM ((ANTE_RES_THEN ASSUME_TAC) o (MATCH_MP LESS_MONO)) THEN
	POP_ASSUM MP_TAC THEN REWRITE_TAC [EL;TL]]]);;

let EVERY_CONJ = 
    prove_thm
    (`EVERY_CONJ`,
     "!l. EVERY (\x:*. P x /\ Q x) l = (EVERY P l /\ EVERY Q l)",
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);;

let ALL_EL_CONJ = prove_thm(`ALL_EL_CONJ`,
     "!P Q l. ALL_EL (\x:*. P x /\ Q x) l = (ALL_EL P l /\ ALL_EL Q l)",
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [ALL_EL] THEN CONV_TAC (DEPTH_CONV BETA_CONV)
     THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN FIRST_ASSUM ACCEPT_TAC);;
>%

let LENGTH_NIL = 
    prove_thm
    (`LENGTH_NIL`,
     "!l. (LENGTH l = 0) = (l:(*)list = NIL)",
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH;NOT_SUC;NOT_CONS_NIL]);;

let LENGTH_CONS = 
    prove_thm
    (`LENGTH_CONS`,
     "!l n. (LENGTH l = (SUC n)) = 
	    (?h:*. ?l'. (LENGTH l' = n) /\ (l = CONS h l'))", 
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC
       [LENGTH;NOT_EQ_SYM(SPEC_ALL NOT_SUC);NOT_NIL_CONS];
     REWRITE_TAC [LENGTH;INV_SUC_EQ;CONS_11] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [EXISTS_TAC "h:*" THEN EXISTS_TAC "l:(*)list" THEN
      ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []]]);;

let LENGTH_EQ_SUC =
    prove_thm
    (`LENGTH_EQ_CONS`,
     "!P:(*)list->bool. !n:num. 
      (!l. (LENGTH l = SUC n) ==> P l) 
         =  
       !l. (LENGTH l = n) ==> (\l. !x:*. P (CONS x l)) l",
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [LENGTH];
      DISCH_TAC THEN
      INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
      [REWRITE_TAC [LENGTH;NOT_NIL_CONS;NOT_EQ_SYM(SPEC_ALL NOT_SUC)];
       ASM_REWRITE_TAC [LENGTH;INV_SUC_EQ;CONS_11] THEN
       REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);;

let LENGTH_EQ_NIL =
    prove_thm
    (`LENGTH_EQ_NIL`,
     "!P:(*)list->bool. (!l. (LENGTH l = 0) ==> P l) = P []",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [LENGTH];
      DISCH_TAC THEN
      INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
      [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [LENGTH;NOT_SUC]]]);;


% Added by WW 07-05-93 %
let LENGTH_MAP2 = prove_thm(`LENGTH_MAP2`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     (!f:*->**->***. (LENGTH(MAP2 f l1 l2) = LENGTH l1) /\
      (LENGTH(MAP2 f l1 l2) = LENGTH l2))",
    LIST_INDUCT_TAC THENL[
      LIST_INDUCT_TAC THENL[
    	DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
    	THEN REWRITE_TAC[LENGTH];
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN REWRITE_TAC[SUC_NOT]];
      GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[NOT_SUC];
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
    	THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ]
    	THEN DISCH_TAC THEN RES_THEN ASSUME_TAC THEN GEN_TAC
    	THEN CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

loadt`mk_list_thm2`;;

quit();;
