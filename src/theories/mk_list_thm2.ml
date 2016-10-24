%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_list_thm2.ml                                       %
%                                                                             %
%     DESCRIPTION:      Extends the theory list.th with more theorems         %
%                       loaded by mk_list_thms.ml			      %
%                                                                             %
%     AUTHORS:          W. Wong (2 Jan 94)                                    %
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
%     COPYRIGHT:        W. Wong 1994                                          %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% --------------------------------------------------------------------- %
% Define some useful functions	    					%
% --------------------------------------------------------------------- %

begin_section `Q_PERM`;;

let chk_var vl v = (is_var v & (mem v vl)) ;;

let FORALL_PERM_RULE = 
  \tms thm.
    let vs = (fst o strip_forall) (concl thm) in
    if (forall (chk_var vs) tms) then
        let vs' = subtract vs tms in (GENL (tms @ vs')(SPEC_ALL thm))
    else failwith `not all variables are quantified`
 ?\s failwith (`FORALL_PERM_RULE: `^s);;

let FORALL_PERM_CONV = 
    let forall_perm_rule = \tms thm. GENL tms (SPEC_ALL thm) in
  \tms tm.
    let (vs,body) =  strip_forall tm in
    if (forall (chk_var vs) tms) then
        let vs' = tms @ (subtract vs tms) in 
    	let th1 = DISCH_ALL (forall_perm_rule vs' (ASSUME tm)) in
    	let th2 = DISCH_ALL (forall_perm_rule vs
    	     (ASSUME(list_mk_forall(vs',body)))) in
    	(IMP_ANTISYM_RULE th1 th2)
    else failwith `not all variables are quantified`
     ?\s failwith (`FORALL_PERM_CONV: `^s);;

let FORALL_PERM_TAC = 
  \tms (asm,gl).
    CONV_TAC (FORALL_PERM_CONV tms) (asm,gl);;

(FORALL_PERM_RULE,FORALL_PERM_CONV,FORALL_PERM_TAC);;

end_section `Q_PERM`;;

let (FORALL_PERM_RULE,FORALL_PERM_CONV,FORALL_PERM_TAC) = it;;


%-==============================================================-%
%- Theorems about lists	    	    				-%
%-==============================================================-%

let NULL_EQ_NIL = prove_thm (`NULL_EQ_NIL`,
    "!l:(*)list .  NULL l = (l = [])",
    GEN_TAC THEN STRUCT_CASES_TAC (SPEC_ALL list_CASES)
    THEN REWRITE_TAC [NULL;NOT_CONS_NIL]);;

let LENGTH_EQ = prove_thm (`LENGTH_EQ`,
    "! (x:* list) y. (x = y) ==> (LENGTH x = LENGTH y)",
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []);;

let LENGTH_NOT_NULL = prove_thm(`LENGTH_NOT_NULL`,
    "!(l:(*)list). (0 < LENGTH l) = (~(NULL l))",
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC [LENGTH;NULL;NOT_LESS_0];
      REWRITE_TAC [LENGTH;NULL;LESS_0]]);;

let REVERSE_SNOC = prove_thm(`REVERSE_SNOC`,
    "!(x:*) l. REVERSE (SNOC x l) = CONS x (REVERSE l)",
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC;REVERSE]);;

let REVERSE_REVERSE = prove_thm (`REVERSE_REVERSE`,
    "!l:(*)list. REVERSE (REVERSE l) = l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE;REVERSE_SNOC]);;

let forall_REVERSE = TAC_PROOF(([],
    "!P. (!l:(*)list. P(REVERSE l)) = (!l. P l)"),
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[REVERSE_REVERSE]
     o (SPEC "REVERSE l:(*)list"))));;

let f_REVERSE_lemma = TAC_PROOF (([],
    "!f1 f2.
    ((\x. (f1:(*)list->**) (REVERSE x)) = (\x. f2 (REVERSE x))) = (f1 = f2)"),
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL[
      POP_ASSUM (\x.ACCEPT_TAC (EXT (REWRITE_RULE[REVERSE_REVERSE]
      (GEN "x:(*)list" (BETA_RULE (AP_THM x "REVERSE (x:(*)list)"))))));
      ASM_REWRITE_TAC[]]);;

let SNOC_Axiom = prove_thm(`SNOC_Axiom`,
    "!(e:**) (f:** -> (* -> ((*)list -> **))).
     ?! fn. (fn[] = e) /\ (!x l. fn(SNOC x l) = f(fn l)x l)",
    let lemma =  CONV_RULE (EXISTS_UNIQUE_CONV)
       (REWRITE_RULE[REVERSE_REVERSE] (BETA_RULE (SPECL
    	 ["e:**";"(\ft h t. f ft h (REVERSE t)):** -> (* -> ((*)list -> **))"]
        (PURE_ONCE_REWRITE_RULE
    	 [SYM (CONJUNCT1 REVERSE);
    	  PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL REVERSE_SNOC)]
    	   (BETA_RULE (SPEC "\l:(*)list.fn(CONS x l) =
    	    	       (f:** -> (* -> ((*)list -> **)))(fn l)x l"
    	     (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) forall_REVERSE)))]
    	    list_Axiom)))) in
    REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
    THEN STRIP_ASSUME_TAC lemma THEN CONJ_TAC THENL[
      EXISTS_TAC "(fn:(*)list->**) o REVERSE"
      THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN POP_ASSUM (ACCEPT_TAC o SPEC_ALL o
    	REWRITE_RULE[REVERSE_REVERSE;f_REVERSE_lemma] o
        BETA_RULE o REWRITE_RULE[o_DEF] o
        SPECL ["(fn' o REVERSE):(*)list->**";"(fn'' o REVERSE):(*)list->**"])
     ]);;

let SNOC_INDUCT = save_thm(`SNOC_INDUCT`, prove_induction_thm SNOC_Axiom);;
let SNOC_CASES =  save_thm(`SNOC_CASES`,prove_cases_thm SNOC_INDUCT);;

let LENGTH_SNOC = prove_thm(`LENGTH_SNOC`,
    "!(x:*) l. LENGTH (SNOC x l) = SUC (LENGTH l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;SNOC]);;

let NOT_NULL_SNOC = PROVE(
    "!(x:*) l. ~NULL(SNOC x l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC;NULL]);;

% NOT_NIL_SNOC = |- !x l. ~([] = SNOC x l) %
let NOT_NIL_SNOC = save_thm(`NOT_NIL_SNOC`,
    prove_constructors_distinct SNOC_Axiom);;

% NOT_SNOC_NIL = |- !x l. ~(SNOC x l = []) %
let NOT_SNOC_NIL = save_thm(`NOT_SNOC_NIL`,
    GSYM NOT_NIL_SNOC);;

let SNOC_11 =  save_thm(`SNOC_11`,prove_constructors_one_one SNOC_Axiom);;

let SNOC_EQ_LENGTH_EQ = prove_thm (`SNOC_EQ_LENGTH_EQ`,
    "!x1 (l1:(*)list) x2 l2.
         ((SNOC x1 l1) = (SNOC x2 l2)) ==> (LENGTH l1 = LENGTH l2)",
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (AP_TERM "LENGTH:(*)list -> num")
    THEN RULE_ASSUM_TAC(REWRITE_RULE [LENGTH_SNOC;LENGTH;EQ_MONO_ADD_EQ;ADD1])
    THEN FIRST_ASSUM ACCEPT_TAC);;

let SNOC_REVERSE_CONS = save_thm (`SNOC_REVERSE_CONS`,
   % "!(x:*) l. (SNOC x l) = REVERSE (CONS x (REVERSE l))", %
    GEN_ALL (REWRITE_RULE [REVERSE_REVERSE]
      (AP_TERM "REVERSE:(*)list -> (*)list" (SPEC_ALL REVERSE_SNOC))));;

let SNOC_APPEND = prove_thm(`SNOC_APPEND`,
   "!x (l:(*) list). SNOC x l = APPEND l [x]",
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [SNOC;APPEND]);;

let MAP_SNOC  = prove_thm(`MAP_SNOC`,
    "!(f:*->**) x (l:* list). MAP f(SNOC x l) = SNOC(f x)(MAP f l)",
     (REWRITE_TAC [SNOC_APPEND;MAP_APPEND;MAP]));;

let FOLDR_SNOC = prove_thm(`FOLDR_SNOC`,
    "!(f:*->**->**) e x l. FOLDR f e (SNOC x l) = FOLDR f (f x e) l",
    REPEAT (FILTER_GEN_TAC "l:* list")
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC;FOLDR]
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);;

let FOLDL_SNOC = prove_thm(`FOLDL_SNOC`,
    "!(f:**->*->**) e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x",
    let lem = PROVE(
        "!l (f:**->*->**) e x. FOLDL f e (SNOC x l) = f (FOLDL f e l) x",
    	LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC;FOLDL]
        THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]) in
    MATCH_ACCEPT_TAC lem);;

let SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;;

let FOLDR_FOLDL = prove_thm(`FOLDR_FOLDL`,
    "!(f:*->*->*) e. MONOID f e ==> !l. FOLDR f e l = FOLDL f e l",
    REPEAT GEN_TAC
    THEN REWRITE_TAC[MONOID_DEF;ASSOC_DEF;LEFT_ID_DEF;RIGHT_ID_DEF]
    THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; FOLDR]
    THEN FIRST_ASSUM SUBST1_TAC THEN GEN_TAC
    THEN SPEC_TAC ("l:* list","l:* list") THEN SNOC_INDUCT_TAC THENL[
      ASM_REWRITE_TAC[FOLDL];
      PURE_ONCE_REWRITE_TAC[FOLDL_SNOC] THEN GEN_TAC
      THEN ASM_REWRITE_TAC[]]);;

let LENGTH_FOLDR = prove_thm(`LENGTH_FOLDR`,
    "!l:* list. LENGTH l = FOLDR (\x l'. SUC l') 0 l",
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;FOLDR]
    THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]);;

let LENGTH_FOLDL = prove_thm(`LENGTH_FOLDL`,
    "!l:* list. LENGTH l = FOLDL (\l' x. SUC l') 0 l",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC;FOLDL_SNOC] THENL[
      REWRITE_TAC[LENGTH;FOLDL];
      CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
      THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
      THEN ASM_REWRITE_TAC[]]);;

let MAP_FOLDR = prove_thm(`MAP_FOLDR`,
    "!(f:*->**) l. MAP f l = FOLDR (\x l'. CONS (f x) l') [] l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP;FOLDR]
    THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]);;

let MAP_FOLDL = prove_thm(`MAP_FOLDL`,
    "!(f:*->**) l. MAP f l = FOLDL (\l' x. SNOC (f x) l') [] l",
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[MAP_SNOC;FOLDL_SNOC] THENL[
      REWRITE_TAC[FOLDL;MAP];
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC (DEPTH_CONV BETA_CONV)
      THEN GEN_TAC THEN REFL_TAC]);;

let MAP_o = prove_thm(`MAP_o`,
    "!f:**->***. !g:*->**.  MAP (f o g) = (MAP f) o (MAP g)",
    REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP;o_THM]);;

let MAP_MAP_o = prove_thm(`MAP_MAP_o`,
    "!(f:**->***) (g:*->**) l. MAP f (MAP g l) = MAP (f o g) l",
    REPEAT GEN_TAC THEN REWRITE_TAC [MAP_o;o_DEF]
    THEN BETA_TAC THEN REFL_TAC);;

let FILTER_FOLDR = prove_thm(`FILTER_FOLDR`,
    "!P (l:* list). FILTER P l = FOLDR (\x l'. P x => CONS x l' | l') [] l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER;FOLDR]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]);;

let FILTER_SNOC = prove_thm(`FILTER_SNOC`,
    "!P (x:*) l. FILTER P (SNOC x l) = 
    	P x => SNOC x (FILTER P l) | FILTER P l",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER;SNOC]
    THEN GEN_TAC THEN REPEAT COND_CASES_TAC
    THEN ASM_REWRITE_TAC[SNOC]);;

let FILTER_FOLDL = prove_thm(`FILTER_FOLDL`,
    "!P (l:* list). FILTER P l = FOLDL (\l' x. P x => SNOC x l' | l') [] l",
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[FILTER;FOLDL];
      REWRITE_TAC[FILTER_SNOC;FOLDL_SNOC]
      THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);;

let FILTER_COMM = prove_thm(`FILTER_COMM`,
    "!f1 f2 (l:* list). FILTER f1 (FILTER f2 l) = FILTER f2 (FILTER f1 l)",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);;

let FILTER_IDEM = prove_thm(`FILTER_IDEM`,
    "!f (l:* list). FILTER f (FILTER f l) = FILTER f l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);;

let FILTER_MAP = prove_thm(`FILTER_MAP`,
    "!f1 (f2:*->**) (l:* list).
     FILTER f1 (MAP f2 l) = MAP f2 (FILTER (f1 o f2) l)",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER;MAP]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[o_THM]
    THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER;MAP]);;

%- 18 Nov. 93 -%
let LENGTH_SEG = prove_thm(`LENGTH_SEG`,
    "!n k (l:* list). ((n + k) <= (LENGTH l)) ==> (LENGTH (SEG n k l) = n)",
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[SEG;LENGTH];
      REWRITE_TAC[SEG;LENGTH];
      LIST_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH;ADD_0;LESS_OR_EQ;NOT_SUC;NOT_LESS_0];
        REWRITE_TAC[SEG;LENGTH;ADD;LESS_EQ_MONO;INV_SUC_EQ] 
    	THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o (SPEC "0"))];
      LIST_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH;ADD;LESS_OR_EQ;NOT_SUC;NOT_LESS_0];
        REWRITE_TAC[LENGTH;SEG;(GSYM ADD_SUC);LESS_EQ_MONO]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

let APPEND_NIL = prove_thm(`APPEND_NIL`,
    "(!l:(*)list . APPEND l [] = l) /\ (!l:(*)list . APPEND [] l = l)",
    CONJ_TAC THENL
       [LIST_INDUCT_TAC;ALL_TAC] THEN ASM_REWRITE_TAC [APPEND]);;

let APPEND_SNOC = prove_thm(`APPEND_SNOC`,
    "!l1 (x:*) l2. APPEND l1 (SNOC x l2) = SNOC x (APPEND l1 l2)",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND;SNOC]);;

let REVERSE_APPEND = prove_thm (`REVERSE_APPEND`,
    "!(l1:(*)list) l2.
     REVERSE (APPEND l1 l2) = (APPEND (REVERSE l2) (REVERSE l1))",
    LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[APPEND;APPEND_NIL;REVERSE;APPEND_SNOC]);;

let APPEND_FOLDR = prove_thm(`APPEND_FOLDR`,
    "!(l1:* list) l2. APPEND l1 l2  = FOLDR CONS l2 l1",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND;FOLDR]);;

let APPEND_FOLDL = prove_thm(`APPEND_FOLDL`,
    "!(l1:* list) l2. APPEND l1 l2  = FOLDL (\l' x. SNOC x l') l1 l2",
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
     REWRITE_TAC[APPEND_NIL;FOLDL];
     ASM_REWRITE_TAC[APPEND_SNOC;FOLDL_SNOC] THEN GEN_TAC
     THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN REFL_TAC]);;

let FOLDR_APPEND = prove_thm(`FOLDR_APPEND`,
    "!(f:*->**->**) e l1 l2.
     FOLDR f e (APPEND l1 l2) = FOLDR f (FOLDR f e l2) l1",
    FORALL_PERM_TAC["l2:* list"] THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[APPEND_NIL;FOLDR];
      REWRITE_TAC[APPEND_SNOC;FOLDR_SNOC] THEN REPEAT GEN_TAC
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let FOLDL_APPEND = prove_thm(`FOLDL_APPEND`,
    "!(f:*->**->*) e l1 l2.
     FOLDL f e (APPEND l1 l2) = FOLDL f (FOLDL f e l1) l2",
    FORALL_PERM_TAC["l1:** list"] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[APPEND;FOLDL] THEN REPEAT GEN_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let CONS_APPEND = prove_thm(`CONS_APPEND`,
    "!(x:*) l. CONS x l = APPEND [x] l",
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[APPEND_NIL];
      ASM_REWRITE_TAC[APPEND_SNOC;(GSYM(CONJUNCT2 SNOC))]]);;

let ASSOC_APPEND = prove_thm (`ASSOC_APPEND`,
    "ASSOC (APPEND:* list -> * list -> * list)",
    REWRITE_TAC[ASSOC_DEF;APPEND_ASSOC]);;

let RIGHT_ID_APPEND_NIL = prove(
    "RIGHT_ID APPEND ([]:* list)",
    REWRITE_TAC[RIGHT_ID_DEF;APPEND;APPEND_NIL]);;

let LEFT_ID_APPEND_NIL = PROVE(
    "LEFT_ID APPEND ([]:* list)",
    REWRITE_TAC[LEFT_ID_DEF;APPEND;APPEND_NIL]);;

let MONOID_APPEND_NIL = prove_thm (`MONOID_APPEND_NIL`,
    "MONOID APPEND ([]:* list)",
    REWRITE_TAC[MONOID_DEF;APPEND;APPEND_NIL;APPEND_ASSOC;
            LEFT_ID_DEF;ASSOC_DEF;RIGHT_ID_DEF]);;

let APPEND_LENGTH_EQ = prove_thm(`APPEND_LENGTH_EQ`,
    "!l1 l1'. (LENGTH l1 = LENGTH l1') ==>
     !l2 l2':* list. (LENGTH l2 = LENGTH l2') ==>
     ((APPEND l1 l2 = APPEND l1' l2') = ((l1 = l1') /\ (l2 = l2')))",
    let APPEND_11 = PROVE(
    	"!(x:* list) (y:* list) (z:* list).
    	 ((APPEND x y) = (APPEND x z)) = (y = z)",
    	LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND;CONS_11]) in
    let EQ_LENGTH_INDUCT_TAC =
    	LIST_INDUCT_TAC THENL[
         LIST_INDUCT_TAC THENL[ 
    	  REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (\t.ALL_TAC);
          REWRITE_TAC[LENGTH;SUC_NOT]];
    	 GEN_TAC THEN LIST_INDUCT_TAC
    	 THEN REWRITE_TAC[LENGTH;NOT_SUC;INV_SUC_EQ]
     	 THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC]
    in
    EQ_LENGTH_INDUCT_TAC THEN REWRITE_TAC[APPEND]
    THEN EQ_LENGTH_INDUCT_TAC THEN REWRITE_TAC[APPEND_11;CONS_11;APPEND_NIL]
    THEN FIRST_ASSUM (\t. ASSUME_TAC
      (MATCH_MP t (ASSUME"LENGTH (l1:* list) = LENGTH (l1':* list)")))
    THEN POP_ASSUM (ASSUME_TAC o (REWRITE_RULE[LENGTH;INV_SUC_EQ]) o
     (SPECL["CONS h'' l2:* list";"CONS h''' l2':* list"]))
    THEN POP_ASSUM (\t1. FIRST_ASSUM (\t2. SUBST1_TAC (MP t1 t2)))
    THEN REWRITE_TAC[CONS_11;CONJ_ASSOC]);;

let FILTER_APPEND = prove_thm(`FILTER_APPEND`,
    "!f l1 (l2:* list).
     FILTER f (APPEND l1 l2) = APPEND (FILTER f l1) (FILTER f l2)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER;APPEND]
    THEN REPEAT GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[APPEND]);;

let FLAT_SNOC = prove_thm(`FLAT_SNOC`,
    "!(x:* list) l. FLAT (SNOC x l) = APPEND (FLAT l) x",
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT;SNOC;APPEND;APPEND_NIL;APPEND_ASSOC]);;

let FLAT_FOLDR = prove_thm(`FLAT_FOLDR`,
    "!l:* list list. FLAT l = FOLDR APPEND [] l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT;FOLDR]);;

let FLAT_FOLDL = prove_thm(`FLAT_FOLDL`,
    "!l:* list list. FLAT l = FOLDL APPEND [] l",
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[FLAT;FOLDL];
      ASM_REWRITE_TAC[FLAT_SNOC;FOLDL_SNOC]]);;

let LENGTH_FLAT = prove_thm(`LENGTH_FLAT`,
    "!l:* list list. LENGTH(FLAT l) = SUM (MAP LENGTH l)",
    LIST_INDUCT_TAC THEN REWRITE_TAC[FLAT] THENL[
      REWRITE_TAC[LENGTH;MAP;SUM];
      ASM_REWRITE_TAC[LENGTH_APPEND;MAP;SUM]]);;

let REVERSE_FOLDR = prove_thm(`REVERSE_FOLDR`,
    "!l:* list. REVERSE l = FOLDR SNOC [] l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE;FOLDR]);;

let REVERSE_FOLDL = prove_thm(`REVERSE_FOLDL`,
    "!l:* list. REVERSE l = FOLDL (\l' x. CONS x l') [] l",
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[REVERSE;FOLDL];
      REWRITE_TAC[REVERSE_SNOC;FOLDL_SNOC]
      THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);;

let LENGTH_REVERSE = prove_thm(`LENGTH_REVERSE`,
    "!l:(*)list. LENGTH (REVERSE l) = LENGTH l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH;REVERSE;LENGTH_SNOC]);;

let REVERSE_EQ_NIL = prove_thm(`REVERSE_EQ_NIL`,
    "!l:* list. (REVERSE l = []) = (l = [])",
    LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE;NOT_CONS_NIL;NOT_SNOC_NIL]);;

let ALL_EL_SNOC = prove_thm(`ALL_EL_SNOC`,
    "!P (x:*) l. ALL_EL P (SNOC x l) = ALL_EL P l /\ P x",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC;ALL_EL;CONJ_ASSOC]);;

let ALL_EL_CONJ = prove_thm(`ALL_EL_CONJ`,
     "!P Q l. ALL_EL (\x:*. P x /\ Q x) l = (ALL_EL P l /\ ALL_EL Q l)",
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [ALL_EL] THEN BETA_TAC
     THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN FIRST_ASSUM ACCEPT_TAC);;

let ALL_EL_MAP = prove_thm(`ALL_EL_MAP`,
    "!P (f:*->**) l. ALL_EL P (MAP f l) = ALL_EL (P o f) l",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC [ALL_EL;MAP] THEN ASM_REWRITE_TAC [o_DEF]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let ALL_EL_APPEND = prove_thm(`ALL_EL_APPEND`,
    "!P (l1:(*)list) l2.
     (ALL_EL P (APPEND l1 l2)) = ((ALL_EL P l1) /\ (ALL_EL P l2))",
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;ALL_EL]
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [CONJ_ASSOC]);;

let SOME_EL_SNOC = prove_thm(`SOME_EL_SNOC`,
    "!P (x:*) l. SOME_EL P (SNOC x l) = P x \/ (SOME_EL P l)",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC;SOME_EL] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC);;

let NOT_ALL_EL_SOME_EL = prove_thm(`NOT_ALL_EL_SOME_EL`,
    "!P (l:* list). ~(ALL_EL P l) = SOME_EL ($~ o P) l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL;SOME_EL]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM;o_THM]
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);;

let NOT_SOME_EL_ALL_EL = prove_thm(`NOT_SOME_EL_ALL_EL`,
    "!P (l:* list). ~(SOME_EL P l) = ALL_EL ($~ o P) l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL;SOME_EL]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM;o_THM]
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);;

let IS_EL = prove_thm(`IS_EL`,
    "(!x:*. IS_EL x[] = F) /\
     (!(y:*) x l. IS_EL y(CONS x l) = (y = x) \/ IS_EL y l)",
    REWRITE_TAC[IS_EL_DEF;SOME_EL] THEN REPEAT GEN_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN REFL_TAC);;

let IS_EL_SNOC = prove_thm(`IS_EL_SNOC`,
    "!(y:*) x l. IS_EL y (SNOC x l) = (y = x) \/ IS_EL y l",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC;IS_EL] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC);;

let SUM_SNOC = prove_thm(`SUM_SNOC`,
    "!x l. SUM (SNOC x l) = (SUM l) + x",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUM;SNOC;ADD;ADD_0]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[ADD_ASSOC]);;

let SUM_FOLDR = prove_thm(`SUM_FOLDR`,
    "!l:num list. SUM l = FOLDR $+ 0 l",
    LIST_INDUCT_TAC THEN REWRITE_TAC[SUM;FOLDR;ADD]
    THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);;

let SUM_FOLDL = prove_thm(`SUM_FOLDL`,
    "!l:num list. SUM l = FOLDL $+ 0 l",
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[SUM;FOLDL];
      REWRITE_TAC[SUM_SNOC;FOLDL_SNOC]
      THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
      THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC]);;


let IS_PREFIX_APPEND = prove_thm(`IS_PREFIX_APPEND`,
    "!l1 l2:* list. (IS_PREFIX l1 l2 = (?l. l1 = APPEND l2 l))",
    LIST_INDUCT_TAC THENL[
     LIST_INDUCT_TAC THENL[
      REWRITE_TAC[IS_PREFIX;APPEND]
      THEN EXISTS_TAC "[]:* list" THEN REFL_TAC; 
      REWRITE_TAC[IS_PREFIX;APPEND;GSYM NOT_CONS_NIL]];
     GEN_TAC THEN LIST_INDUCT_TAC THENL[
      REWRITE_TAC[IS_PREFIX;APPEND]
      THEN EXISTS_TAC "CONS (h:*) l1" THEN REFL_TAC;
      ASM_REWRITE_TAC[IS_PREFIX;APPEND;CONS_11] THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);;

let IS_SUFFIX_APPEND = prove_thm(`IS_SUFFIX_APPEND`,
    "!l1 l2:* list. (IS_SUFFIX l1 l2 = (?l. l1 = APPEND l l2))",
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[IS_SUFFIX;APPEND_NIL]
      THEN EXISTS_TAC "[]:* list" THEN REFL_TAC;
      REWRITE_TAC[IS_SUFFIX;APPEND_SNOC]
      THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
      THEN REWRITE_TAC[GSYM NULL_EQ_NIL;NOT_NULL_SNOC]];
     GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[IS_SUFFIX;APPEND_NIL]
      THEN EXISTS_TAC "SNOC (x:*) l1" THEN REFL_TAC;
      ASM_REWRITE_TAC[IS_SUFFIX;APPEND_SNOC;SNOC_11] THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);;

let IS_SUBLIST_APPEND = prove_thm(`IS_SUBLIST_APPEND`,
    "!l1 l2:* list. IS_SUBLIST l1 l2 = (?l l'. l1 = APPEND l(APPEND l2 l'))",
    let NOT_NIL_APPEND_CONS2 = PROVE(
    	"!l1 (l2:* list) x. ~([] = (APPEND l1 (CONS x l2)))",
    	LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN REPEAT GEN_TAC
        THEN MATCH_ACCEPT_TAC (GSYM NOT_CONS_NIL)) in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "l2:* list")
    THEN LIST_INDUCT_TAC THENL[
    	REWRITE_TAC[IS_SUBLIST;APPEND]
        THEN MAP_EVERY EXISTS_TAC ["[]:* list"; "[]:* list"]
    	THEN REWRITE_TAC[APPEND];
        GEN_TAC THEN REWRITE_TAC[IS_SUBLIST;APPEND;NOT_NIL_APPEND_CONS2];
        REWRITE_TAC[IS_SUBLIST;APPEND]
    	THEN MAP_EVERY EXISTS_TAC ["[h]:* list"; "l1:* list"]
        THEN MATCH_ACCEPT_TAC CONS_APPEND;
    	GEN_TAC THEN REWRITE_TAC[IS_SUBLIST] THEN EQ_TAC 
        THEN ONCE_ASM_REWRITE_TAC[IS_PREFIX_APPEND] THENL[
    	  STRIP_TAC THENL[
    	    MAP_EVERY EXISTS_TAC ["[]:* list"; "l:* list"]
    	    THEN ASM_REWRITE_TAC[APPEND];
    	    MAP_EVERY EXISTS_TAC ["(CONS h l):* list"; "l':* list"]
    	    THEN ONCE_ASM_REWRITE_TAC[APPEND] THEN REFL_TAC];
          CONV_TAC LEFT_IMP_EXISTS_CONV THEN LIST_INDUCT_TAC THENL[
    	    REWRITE_TAC[APPEND;CONS_11] THEN STRIP_TAC THEN DISJ1_TAC
    	    THEN ASM_REWRITE_TAC[IS_PREFIX_APPEND]
    	    THEN EXISTS_TAC "l':* list" THEN REFL_TAC;
    	    GEN_TAC THEN REWRITE_TAC[APPEND;CONS_11]
    	    THEN STRIP_TAC THEN DISJ2_TAC
    	    THEN MAP_EVERY EXISTS_TAC ["l:* list"; "l':* list"]
    	    THEN FIRST_ASSUM ACCEPT_TAC]]]);;

let IS_PREFIX_IS_SUBLIST = prove_thm(`IS_PREFIX_IS_SUBLIST`,
    "!l1 l2:* list. IS_PREFIX l1 l2 ==> IS_SUBLIST l1 l2",
    LIST_INDUCT_TAC THEN TRY (FILTER_GEN_TAC "l2:* list")
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[IS_PREFIX;IS_SUBLIST]
    THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let IS_SUFFIX_IS_SUBLIST = prove_thm(`IS_SUFFIX_IS_SUBLIST`,
    "!l1 l2:* list. IS_SUFFIX l1 l2 ==> IS_SUBLIST l1 l2",
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND;IS_SUBLIST_APPEND]
    THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN MAP_EVERY EXISTS_TAC ["l:* list"; "[]:* list"]
    THEN REWRITE_TAC[APPEND_NIL]);;

let IS_PREFIX_REVERSE = prove_thm(`IS_PREFIX_REVERSE`,
    "!l1 l2:* list. IS_PREFIX (REVERSE l1) (REVERSE l2) = IS_SUFFIX l1 l2",
    let NOT_NIL_APPEND_SNOC2 = PROVE(
        "!l1 (l2:* list) x. ~([] = (APPEND l1 (SNOC x l2)))",
    	LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND_SNOC] THEN REPEAT GEN_TAC
    	THEN MATCH_ACCEPT_TAC NOT_NIL_SNOC) in
    SNOC_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "l2:* list")
    THEN SNOC_INDUCT_TAC THENL[
        REWRITE_TAC[IS_SUFFIX_APPEND;REVERSE;IS_PREFIX]
    	THEN EXISTS_TAC "[]:* list" THEN REWRITE_TAC[APPEND];
        GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND;REVERSE;REVERSE_SNOC;IS_PREFIX]
    	THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC
        THEN REWRITE_TAC[APPEND;NOT_NIL_APPEND_SNOC2];
    	REWRITE_TAC[IS_SUFFIX_APPEND;REVERSE;APPEND_NIL;IS_PREFIX]
        THEN EXISTS_TAC "SNOC (x:*) l1" THEN REFL_TAC;
    	GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND;REVERSE_SNOC;IS_PREFIX]
        THEN PURE_ONCE_ASM_REWRITE_TAC[]
    	THEN REWRITE_TAC[IS_SUFFIX_APPEND;APPEND_SNOC;SNOC_11]
        THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN REFL_TAC]);;

let IS_SUFFIX_REVERSE = save_thm(`IS_SUFFIX_REVERSE`,
   % "!l1 l2:* list. IS_SUFFIX (REVERSE l1) (REVERSE l2) = IS_PREFIX l1 l2"%
    GEN_ALL(SYM (REWRITE_RULE[REVERSE_REVERSE]
    (SPECL["REVERSE(l1:* list)"; "REVERSE(l2:* list)"] IS_PREFIX_REVERSE))));;

let IS_SUBLIST_REVERSE = prove_thm(`IS_SUBLIST_REVERSE`,
    "!l1 l2:* list. IS_SUBLIST (REVERSE l1) (REVERSE l2) = IS_SUBLIST l1 l2",
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUBLIST_APPEND]
    THEN EQ_TAC THEN STRIP_TAC THENL[
      MAP_EVERY EXISTS_TAC ["REVERSE(l':* list)"; "REVERSE(l:* list)"]
      THEN FIRST_ASSUM (SUBST1_TAC o
    	 (REWRITE_RULE[REVERSE_REVERSE;REVERSE_APPEND]) o
    	 (AP_TERM "REVERSE:* list -> * list"))
      THEN REWRITE_TAC[APPEND_ASSOC];
      FIRST_ASSUM SUBST1_TAC
      THEN REWRITE_TAC[REVERSE_APPEND;APPEND_ASSOC]
      THEN MAP_EVERY EXISTS_TAC ["REVERSE(l':* list)"; "REVERSE(l:* list)"]
      THEN REFL_TAC]);;

let PREFIX_FOLDR = prove_thm(`PREFIX_FOLDR`,
    "!P (l:* list). PREFIX P l = FOLDR (\x l'. P x => CONS x l' | []) [] l",
    GEN_TAC THEN  REWRITE_TAC[PREFIX_DEF]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDR;SPLITP]
    THEN GEN_TAC THEN REWRITE_TAC[o_THM] THEN BETA_TAC
    THEN ASM_CASES_TAC "(P:*->bool) h" THEN ASM_REWRITE_TAC[]);;

let PREFIX = prove_thm(`PREFIX`,
    "(!P:*->bool. PREFIX P [] = []) /\
     (!P (x:*) l. PREFIX P (CONS x l) = P x => CONS x (PREFIX P l) |[])",
    REWRITE_TAC[PREFIX_FOLDR;FOLDR]
    THEN REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);;

let IS_PREFIX_PREFIX = prove_thm(`IS_PREFIX_PREFIX`,
    "!P (l:* list). IS_PREFIX l (PREFIX P l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[IS_PREFIX;PREFIX]
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_PREFIX]);;

let LENGTH_SCANL = prove_thm(`LENGTH_SCANL`,
    "!(f:**->*->**) e l. LENGTH(SCANL f e l) = SUC (LENGTH l)",
    FORALL_PERM_TAC ["l:* list"] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SCANL;LENGTH]
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);;

let LENGTH_SCANR = prove_thm(`LENGTH_SCANR`,
    "!(f:*->**->**) e l. LENGTH(SCANR f e l) = SUC (LENGTH l)",
    FORALL_PERM_TAC ["l:* list"] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SCANR] THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[LENGTH]);;


let COMM_MONOID_FOLDL = prove_thm(`COMM_MONOID_FOLDL`,
    "!f:*->*->*. COMM f ==>
      !e'. MONOID f e' ==>
       (!e l. FOLDL f e l = f e (FOLDL f e' l))",
    REWRITE_TAC[MONOID_DEF;ASSOC_DEF;LEFT_ID_DEF;COMM_DEF]
    THEN REPEAT STRIP_TAC THEN SPEC_TAC ("e:*","e:*")
    THEN SPEC_TAC ("l:* list","l:* list")
    THEN LIST_INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[FOLDL] THENL[
      GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM);
      REPEAT GEN_TAC THEN POP_ASSUM (\t.PURE_ONCE_REWRITE_TAC[t])
      THEN POP_ASSUM (\t.PURE_ONCE_REWRITE_TAC[t])
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM)] );;

let COMM_MONOID_FOLDR = prove_thm(`COMM_MONOID_FOLDR`,
    "!f:*->*->*. COMM f ==>
      !e'. (MONOID f e') ==>
       (!e l. FOLDR f e l = f e (FOLDR f e' l))",
    REWRITE_TAC[MONOID_DEF;ASSOC_DEF;LEFT_ID_DEF;COMM_DEF]
    THEN GEN_TAC THEN DISCH_THEN
      (\th_sym. GEN_TAC THEN DISCH_THEN
        (\th_assoc_etc. let th_assoc = CONJUNCT1 th_assoc_etc in
    	    	let th_ident = CONJUNCT2(CONJUNCT2 th_assoc_etc) in
            	GEN_TAC THEN LIST_INDUCT_TAC 
    	        THEN PURE_ONCE_REWRITE_TAC[FOLDR] THENL[
                 PURE_ONCE_REWRITE_TAC[th_sym]
    	         THEN MATCH_ACCEPT_TAC (GSYM th_ident);
    	    	 REPEAT GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
    	         THEN PURE_ONCE_REWRITE_TAC[th_ident]
    	         THEN PURE_ONCE_REWRITE_TAC[th_assoc]
                 THEN AP_THM_TAC THEN AP_TERM_TAC
    	    	 THEN MATCH_ACCEPT_TAC (GSYM th_sym)])) );;


let FCOMM_FOLDR_APPEND = prove_thm(`FCOMM_FOLDR_APPEND`,
    "!(g:*->*->*) (f:**->*->*). FCOMM g f ==>
     (!e. LEFT_ID g e ==>
       (!l1 l2. FOLDR f e (APPEND l1 l2) = g (FOLDR f e l1) (FOLDR f e l2)))",
    REWRITE_TAC[FCOMM_DEF;LEFT_ID_DEF] THEN REPEAT GEN_TAC
    THEN REPEAT DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND;FOLDR]);;

let FCOMM_FOLDL_APPEND = prove_thm(`FCOMM_FOLDL_APPEND`,
    "!(f:*->**->*) (g:*->*->*). FCOMM f g ==>
     (!e. RIGHT_ID g e ==>
       (!l1 l2. FOLDL f e (APPEND l1 l2) = g (FOLDL f e l1) (FOLDL f e l2)))",
    REWRITE_TAC[FCOMM_DEF;RIGHT_ID_DEF] THEN REPEAT GEN_TAC
    THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN GEN_TAC
    THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[APPEND_NIL;APPEND_SNOC;FOLDL_SNOC;FOLDL]);;


let MONOID_FOLDR_APPEND_FOLDR = PROVE(
    "!(f:*->*->*) e. MONOID f e ==>
     (!l1 l2. FOLDR f e (APPEND l1 l2) = f (FOLDR f e l1) (FOLDR f e l2))",
    REWRITE_TAC[MONOID_DEF;GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);;

let MONOID_FOLDL_APPEND_FOLDL = PROVE(
    "!(f:*->*->*) e. MONOID f e ==>
      (!l1 l2. FOLDL f e (APPEND l1 l2) = f (FOLDL f e l1) (FOLDL f e l2))",
    REWRITE_TAC[MONOID_DEF;GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);;


let FOLDL_SINGLE = prove_thm(`FOLDL_SINGLE`,
    "!(f:*->**->*) e x. FOLDL f e [x] = f e x",
    REWRITE_TAC[FOLDL]);;

let FOLDR_SINGLE = prove_thm(`FOLDR_SINGLE`,
    "!(f:*->**->**) e x. FOLDR f e [x] = f x e",
    REWRITE_TAC[FOLDR]);;


let FOLDR_CONS_NIL = prove_thm(`FOLDR_CONS_NIL`,
    "!(l:* list). FOLDR CONS [] l = l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDR]);;

let FOLDL_SNOC_NIL = prove_thm(`FOLDL_SNOC_NIL`,
    "!(l:* list). FOLDL (\xs x. SNOC x xs) [] l = l",
    SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL;FOLDL_SNOC]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let FOLDR_FOLDL_REVERSE = prove_thm(`FOLDR_FOLDL_REVERSE`,
    "!(f:*->**->**) e l. 
       FOLDR f e l = FOLDL (\x y. f y x) e (REVERSE l)",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDR;FOLDL;REVERSE;FOLDL_SNOC]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let FOLDL_FOLDR_REVERSE = prove_thm(`FOLDL_FOLDR_REVERSE`,
    "!(f:*->**->*) e l. 
       FOLDL f e l = FOLDR (\x y. f y x) e (REVERSE l)",
    GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE;FOLDR;FOLDL;REVERSE_SNOC;FOLDR_SNOC]
    THEN BETA_TAC THEN ASM_REWRITE_TAC[FOLDL_SNOC]);;

let FOLDR_REVERSE = prove_thm(`FOLDR_REVERSE`,
    "!(f:*->**->**) e l. 
       FOLDR f e (REVERSE l) = FOLDL (\x y. f y x) e l",
    REWRITE_TAC[FOLDR_FOLDL_REVERSE;REVERSE_REVERSE]);;

let FOLDL_REVERSE = prove_thm(`FOLDL_REVERSE`,
    "!(f:*->**->*) e l. 
       FOLDL f e (REVERSE l) = FOLDR (\x y. f y x) e l",
    REWRITE_TAC[FOLDL_FOLDR_REVERSE;REVERSE_REVERSE]);;


let FOLDR_MAP = prove_thm(`FOLDR_MAP`,
    "!(f:*->*->*) e (g:** ->*) l. 
       FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l",
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDL;MAP;FOLDR] THEN BETA_TAC
    THEN REWRITE_TAC[]);;

let FOLDL_MAP = prove_thm(`FOLDL_MAP`,
    "!(f:*->*->*) e (g:** ->*) l. 
       FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l",
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[MAP;FOLDL;FOLDL_SNOC;MAP_SNOC;FOLDR]
    THEN BETA_TAC THEN REWRITE_TAC[]);;


let ALL_EL_FOLDR = prove_thm(`ALL_EL_FOLDR`,
    "!(P:*->bool) l. ALL_EL P l = FOLDR (\x l'. P x /\ l') T l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL_EL;FOLDR;MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let ALL_EL_FOLDL = prove_thm(`ALL_EL_FOLDL`,
    "!(P:*->bool) l. ALL_EL P l = FOLDL (\l' x. l' /\ P x) T l",
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[ALL_EL;FOLDL;MAP];
      ASM_REWRITE_TAC[ALL_EL_SNOC;FOLDL_SNOC;MAP_SNOC]]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let SOME_EL_FOLDR = prove_thm(`SOME_EL_FOLDR`,
    "!P (l:* list). SOME_EL P l = FOLDR (\x l'. P x \/ l') F l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SOME_EL;MAP;FOLDR] THEN
    BETA_TAC THEN REWRITE_TAC[]);;

let SOME_EL_FOLDL = prove_thm(`SOME_EL_FOLDL`,
    "!P (l:* list). SOME_EL P l = FOLDL (\l' x. l' \/ P x) F l",
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[SOME_EL;MAP;FOLDL];
      REWRITE_TAC[SOME_EL_SNOC;MAP_SNOC;FOLDL_SNOC]
      THEN BETA_TAC THEN GEN_TAC
      THEN FIRST_ASSUM SUBST1_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM] );;

let ALL_EL_FOLDR_MAP = prove_thm(`ALL_EL_FOLDR_MAP`,
    "!(P:*->bool) l. ALL_EL P l = FOLDR $/\  T (MAP P l)",
    REWRITE_TAC[ALL_EL_FOLDR;FOLDR_MAP]);;

let ALL_EL_FOLDL_MAP = prove_thm(`ALL_EL_FOLDL_MAP`,
    "!(P:*->bool) l. ALL_EL P l = FOLDL $/\  T (MAP P l)",
    REWRITE_TAC[ALL_EL_FOLDL;FOLDL_MAP]);;

let SOME_EL_FOLDR_MAP = prove_thm(`SOME_EL_FOLDR_MAP`,
    "!(P:*->bool) l. SOME_EL P l = FOLDR $\/ F (MAP P l)",
    REWRITE_TAC[SOME_EL_FOLDR;FOLDR_MAP]);;

let SOME_EL_FOLDL_MAP = prove_thm(`SOME_EL_FOLDL_MAP`,
    "!(P:*->bool) l. SOME_EL P l = FOLDL $\/ F (MAP P l)",
    REWRITE_TAC[SOME_EL_FOLDL;FOLDL_MAP]);;


let FOLDR_FILTER = prove_thm(`FOLDR_FILTER`,
    "!(f:*->*->*) e (P:* -> bool) l. 
       FOLDR f e (FILTER P l) = FOLDR (\x y. P x => f x y  | y) e l",
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDL; FILTER; FOLDR] THEN BETA_TAC
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FOLDR]);;

let FOLDL_FILTER = prove_thm(`FOLDL_FILTER`,
    "!(f:*->*->*) e (P:* -> bool) l. 
       FOLDL f e (FILTER P l) = FOLDL (\x y. P y => f x y | x) e l",
     GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
     THEN ASM_REWRITE_TAC[FOLDL;FOLDR_SNOC;FOLDL_SNOC;FILTER;FOLDR;FILTER_SNOC]
     THEN BETA_TAC THEN GEN_TAC THEN COND_CASES_TAC
     THEN ASM_REWRITE_TAC[FOLDL_SNOC]);;

let ASSOC_FOLDR_FLAT = prove_thm(`ASSOC_FOLDR_FLAT`,
    "!(f:*->*->*). ASSOC f ==>
     (! e. LEFT_ID f e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR f e (MAP (FOLDR f e) l)))",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT;MAP;FOLDR]
    THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);;

let ASSOC_FOLDL_FLAT = prove_thm(`ASSOC_FOLDL_FLAT`,
    "!(f:*->*->*). ASSOC f ==>
     (! e. RIGHT_ID f e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL f e (MAP (FOLDL f e) l)))",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT_SNOC;MAP_SNOC;MAP;FLAT;FOLDL_SNOC]
    THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);;

let MAP_FLAT = prove_thm(`MAP_FLAT`,
    "!(f:*->**) l. MAP f (FLAT l) = FLAT (MAP  (MAP f) l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT;MAP;MAP_APPEND]);;

let FILTER_FLAT = prove_thm(`FILTER_FLAT`,
    "!(P:*->bool) l. FILTER P (FLAT l) = FLAT (MAP (FILTER P) l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[FLAT;MAP;FILTER;FILTER_APPEND]);;


let SOME_EL_MAP = prove_thm(`SOME_EL_MAP`,
    "!P (f:*->**) l. SOME_EL P (MAP f l) = SOME_EL (P o f) l",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL[
      REWRITE_TAC [SOME_EL;MAP];
      REWRITE_TAC [SOME_EL;MAP] THEN ASM_REWRITE_TAC [o_DEF]
      THEN BETA_TAC THEN REWRITE_TAC[]]);;


let SOME_EL_APPEND = prove_thm(`SOME_EL_APPEND`,
    "!P (l1:(*)list) l2.
     (SOME_EL P (APPEND l1 l2)) = ((SOME_EL P l1) \/ (SOME_EL P l2))",
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;SOME_EL]
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [DISJ_ASSOC]);;

let SOME_EL_DISJ = prove_thm(`SOME_EL_DISJ`,
    "!P Q (l:* list).
     SOME_EL (\x. P x \/ Q x) l = SOME_EL P l \/ SOME_EL Q l",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SOME_EL] THEN GEN_TAC THEN BETA_TAC
    THEN POP_ASSUM SUBST1_TAC THEN CONV_TAC (AC_CONV (DISJ_ASSOC,DISJ_SYM)));;

let IS_EL_APPEND = prove_thm(`IS_EL_APPEND`,
    "!(l1:(*)list) l2 x.
     (IS_EL x (APPEND l1 l2)) = ((IS_EL x l1) \/ (IS_EL x l2))",
    REWRITE_TAC[IS_EL_DEF;SOME_EL_APPEND]);;

let IS_EL_FOLDR = prove_thm(`IS_EL_FOLDR`,
    "!(y:*) l. IS_EL y l = FOLDR (\x l'. (y = x) \/ l') F l",
    REWRITE_TAC[IS_EL_DEF; SOME_EL_FOLDR;FOLDR_MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let IS_EL_FOLDL = prove_thm(`IS_EL_FOLDL`,
    "!(y:*) l. IS_EL y l = FOLDL (\l' x. l' \/ (y = x)) F l",
    REWRITE_TAC[IS_EL_DEF;SOME_EL_FOLDL;FOLDL_MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);;

let NULL_FOLDR = prove_thm(`NULL_FOLDR`,
    "!(l:* list). NULL l = FOLDR (\x l'. F) T l",
    LIST_INDUCT_TAC THEN REWRITE_TAC[NULL_DEF;FOLDR]);;


let NULL_FOLDL = prove_thm(`NULL_FOLDL`,
    "!(l:* list). NULL l = FOLDL (\x l'. F) T l",
    SNOC_INDUCT_TAC THEN
    REWRITE_TAC[NULL_DEF;FOLDL_SNOC;NULL_EQ_NIL;FOLDL;
                GSYM (prove_constructors_distinct SNOC_Axiom)]);;


let MAP_REVERSE = prove_thm(`MAP_REVERSE`,
    "!(f:* -> **) l. MAP f (REVERSE l) = REVERSE (MAP f l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE;MAP;MAP_SNOC]);;

let FILTER_REVERSE = prove_thm(`FILTER_REVERSE`,
    "!(P:* -> bool) l. FILTER P (REVERSE l) = REVERSE (FILTER P l)",
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE;FILTER;FILTER_SNOC]
    THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REVERSE]);;

let LAST = save_thm(`LAST`,
    % "!(x:*) l. LAST (SNOC x l) = x", %
    let lem = PROVE(
    "!x (l:* list).  (SEG 1 (PRE(LENGTH (SNOC x l))) (SNOC x l)) = [x]",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[SNOC;SEG]
    THEN FIRST_ASSUM ACCEPT_TAC) in
    GEN_ALL(REWRITE_RULE[lem;HD](SPEC "SNOC (x:*) l" LAST_DEF)));;

let BUTLAST = save_thm(`BUTLAST`,
    % "!x l. BUTLAST (SNOC x l) = l", %
    let lem = PROVE(
    "!x:*. !l. SEG (PRE(LENGTH (SNOC x l))) 0 (SNOC x l) = l",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN ASM_REWRITE_TAC[SNOC;SEG]) in
    GEN_ALL(REWRITE_RULE[lem](SPEC "SNOC (x:*) l" BUTLAST_DEF)));;


let SEG_LENGTH_ID = prove_thm(`SEG_LENGTH_ID`,
    "!l:* list. SEG (LENGTH l) 0 l = l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH;SEG]);;

let SEG_SUC_CONS = prove_thm(`SEG_SUC_CONS`,
    "!m n l (x:*). (SEG m (SUC n) (CONS x l) = SEG m n l)",
    INDUCT_TAC THEN REWRITE_TAC[SEG]);;

let SEG_0_SNOC = prove_thm(`SEG_0_SNOC`,
    "!m l (x:*). (m <= (LENGTH l)) ==> (SEG m 0 (SNOC x l) = SEG m 0 l)",
    INDUCT_TAC THENL[
    	REWRITE_TAC[SEG];
    	LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH] THENL[
    	    REWRITE_TAC[LESS_OR_EQ;NOT_SUC;NOT_LESS_0];
    	    REWRITE_TAC[SNOC;SEG;LESS_EQ_MONO]
            THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);;

let BUTLASTN_SEG = prove_thm(`BUTLASTN_SEG`,
    "!n (l:* list). (n <= (LENGTH l)) ==>
     (BUTLASTN n l = SEG (LENGTH l - n) 0 l)",
    INDUCT_TAC THEN REWRITE_TAC[BUTLASTN;SUB_0;SEG_LENGTH_ID]
    THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;BUTLASTN] THENL[
    	REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LESS_EQ_MONO;SUB_MONO_EQ]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    	THEN MATCH_MP_TAC (GSYM SEG_0_SNOC)
    	THEN MATCH_ACCEPT_TAC SUB_LESS_EQ]);;

let LASTN_CONS = prove_thm(`LASTN_CONS`,
    "!n (l:* list). (n <= (LENGTH l)) ==>
     (!x. LASTN n (CONS x l) = LASTN n l)",
    INDUCT_TAC THEN REWRITE_TAC[LASTN] THEN SNOC_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH;LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LENGTH_SNOC;(GSYM(CONJUNCT2 SNOC));LESS_EQ_MONO]
    	THEN REPEAT STRIP_TAC THEN RES_TAC
    	THEN ASM_REWRITE_TAC[LASTN]]);;

let LENGTH_LASTN = prove_thm(`LENGTH_LASTN`,
    "!n (l:(*)list). (n <= LENGTH l) ==> (LENGTH (LASTN n l) = n)",
    INDUCT_TAC THEN REWRITE_TAC[LASTN;LENGTH] THEN SNOC_INDUCT_TAC
    THENL[
    	REWRITE_TAC[LENGTH;LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LENGTH_SNOC;LASTN;LESS_EQ_MONO]
    	THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC]);;

let LASTN_LENGTH_ID = prove_thm(`LASTN_LENGTH_ID`,
    "!l:* list. LASTN (LENGTH l) l = l",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;LASTN]
    THEN GEN_TAC THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);;

let LASTN_LASTN = prove_thm(`LASTN_LASTN`,
    "!l:* list.!n m. (m <= LENGTH l) ==>
    (n <= m) ==> (LASTN n (LASTN m l) = LASTN n l)",
    SNOC_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH;LESS_OR_EQ;NOT_LESS_0]
    	THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN REWRITE_TAC[NOT_LESS_0;LASTN];
    	GEN_TAC THEN REPEAT INDUCT_TAC
    	THEN REWRITE_TAC[LENGTH_SNOC;LASTN;LESS_EQ_MONO;ZERO_LESS_EQ] THENL[
    	    REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	    REPEAT DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);;

let NOT_SUC_LESS_EQ_0 = PROVE("!n. ~(SUC n <= 0)",
    REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC]);;

let FIRSTN_LENGTH_ID = prove_thm(`FIRSTN_LENGTH_ID`,
    "!l:* list. FIRSTN (LENGTH l) l = l",
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;FIRSTN]
    THEN GEN_TAC THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);;

let FIRSTN_SNOC = prove_thm(`FIRSTN_SNOC`,
    "!n (l:* list). (n <= (LENGTH l)) ==>
     (!x. FIRSTN n (SNOC x l) = FIRSTN n l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FIRSTN;LENGTH] THENL[
    	REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LESS_EQ_MONO;SNOC;FIRSTN]
    	THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]);;

let BUTLASTN_LENGTH_NIL = prove_thm(`BUTLASTN_LENGTH_NIL`,
    "!l:* list. BUTLASTN (LENGTH l) l = []",
    SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC;BUTLASTN]);;

let BUTLASTN_SUC_BUTLAST = prove_thm(`BUTLASTN_SUC_BUTLAST`,
    "!n (l:(*)list). (n < (LENGTH l)) ==>
     (BUTLASTN (SUC n) l =  BUTLASTN n (BUTLAST l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_LESS_0;BUTLASTN;BUTLAST]);;

let BUTLASTN_BUTLAST = prove_thm(`BUTLASTN_BUTLAST`,
    "!n (l:(*)list). (n < (LENGTH l)) ==>
     (BUTLASTN n (BUTLAST l) = BUTLAST (BUTLASTN n l))",
    INDUCT_TAC THEN REWRITE_TAC[BUTLASTN] THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;NOT_LESS_0;
    	LESS_MONO_EQ;BUTLASTN;BUTLAST]
    THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SUC_BUTLAST
    THEN RES_TAC);;

let LENGTH_BUTLASTN = prove_thm(`LENGTH_BUTLASTN`,
    "!n (l:(*)list). (n <= LENGTH l) ==> 
     (LENGTH (BUTLASTN n l) = LENGTH l - n)",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[BUTLASTN;SUB_0] THENL[
    	REWRITE_TAC[LENGTH;LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO;SUB_MONO_EQ]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let ADD_SUC_lem = let l = CONJUNCTS ADD_CLAUSES in
    	GEN_ALL (TRANS (el 4 l) (SYM (el 3 l))) ;;

let BUTLASTN_BUTLASTN = prove_thm(`BUTLASTN_BUTLASTN`,
    "!m n (l:* list).  ((n + m) <= LENGTH l) ==>
     (BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l)",
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;ADD;ADD_0;BUTLASTN] THENL[
    	REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO;ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let APPEND_BUTLASTN_LASTN = prove_thm (`APPEND_BUTLASTN_LASTN`,
    "!n (l:(*)list) . (n <= LENGTH l) ==>
     (APPEND (BUTLASTN n l) (LASTN n l) = l)",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[BUTLASTN;LASTN;APPEND;APPEND_NIL] THENL[
    	REWRITE_TAC[LENGTH;LESS_OR_EQ;NOT_LESS_0;NOT_SUC];
    	REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO;APPEND_SNOC]
    	THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC]);;


let APPEND_FIRSTN_LASTN = prove_thm(`APPEND_FIRSTN_LASTN`,
  "!m n (l:* list). ((m + n) = (LENGTH l)) ==> 
         (APPEND (FIRSTN n l) (LASTN m l) = l)",
    let ADD_EQ_LESS_EQ = PROVE("!m n p. ((n + m) = p) ==> (m <= p)",
      REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM)
      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
      THEN MATCH_ACCEPT_TAC LESS_EQ_ADD) in
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;ADD;ADD_0;FIRSTN;LASTN;
    	APPEND;APPEND_NIL;SUC_NOT;NOT_SUC] THENL[
    	GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN SUBST1_TAC (SYM(SPEC_ALL LENGTH_SNOC))
    	THEN MATCH_ACCEPT_TAC FIRSTN_LENGTH_ID;
    	PURE_ONCE_REWRITE_TAC[INV_SUC_EQ] THEN GEN_TAC
    	THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LASTN_LENGTH_ID];
    	PURE_ONCE_REWRITE_TAC[INV_SUC_EQ;ADD_SUC_lem;APPEND_SNOC]
    	THEN REPEAT STRIP_TAC THEN IMP_RES_TAC ADD_EQ_LESS_EQ
    	THEN IMP_RES_TAC FIRSTN_SNOC THEN RES_TAC
    	THEN ASM_REWRITE_TAC[]]);;

let BUTLASTN_APPEND2 = prove_thm (`BUTLASTN_APPEND2`,
    "!n l1 (l2:* list). (n <= LENGTH l2) ==>
     (BUTLASTN n (APPEND l1 l2) = APPEND l1 (BUTLASTN n l2))",
    INDUCT_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTLASTN;NOT_SUC_LESS_EQ_0;APPEND_SNOC]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO]);;

%----------------------------------------------------------------------------%
% "!(l1:* list) (l2:* list). BUTLASTN(LENGTH l2)(APPEND l1 l2) = l1"         %
%----------------------------------------------------------------------------%
let BUTLASTN_LENGTH_APPEND = save_thm(`BUTLASTN_LENGTH_APPEND`,
    GEN_ALL (REWRITE_RULE[LESS_EQ_REFL;BUTLASTN_LENGTH_NIL;APPEND_NIL]
     (SPECL["LENGTH (l2:* list)";"l1:* list";"l2:* list"] BUTLASTN_APPEND2)));;

let LASTN_LENGTH_APPEND = prove_thm(`LASTN_LENGTH_APPEND`,
    "!l1 (l2:* list). LASTN (LENGTH l2) (APPEND l1 l2) = l2",
    GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;APPEND;APPEND_SNOC;LASTN]
    THEN ASM_REWRITE_TAC[BUTLAST;LAST;SNOC_APPEND]);;

let BUTLASTN_CONS = prove_thm(`BUTLASTN_CONS`,
    "!n l. (n <= (LENGTH l)) ==> 
     (!x:*. BUTLASTN n(CONS x l) = CONS x(BUTLASTN n l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_SUC_LESS_EQ_0;BUTLASTN;GSYM(CONJUNCT2 SNOC)]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO]);;

%  |- !l x. BUTLASTN(LENGTH l)(CONS x l) = [x] %
let BUTLASTN_LENGTH_CONS = save_thm(`BUTLASTN_LENGTH_CONS`,
    let thm1 = SPECL ["LENGTH (l:* list)";"l:* list"] BUTLASTN_CONS in
    GEN_ALL(REWRITE_RULE[LESS_EQ_REFL;BUTLASTN_LENGTH_NIL] thm1));;

let LAST_LASTN_LAST = prove_thm(`LAST_LASTN_LAST`,
    "!n (l:(*)list). (n <= LENGTH l) ==> (0 < n) ==>
     (LAST(LASTN n l) = LAST l)",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_LESS_0;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LASTN;LAST]);;

let BUTLASTN_LASTN_NIL = prove_thm(`BUTLASTN_LASTN_NIL`,
    "!n. !l:* list. n <= (LENGTH l) ==> (BUTLASTN n (LASTN n l) = [])",
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN (\t. SUBST_OCCS_TAC [[1],(SYM t)]) LENGTH_LASTN
    THEN MATCH_ACCEPT_TAC BUTLASTN_LENGTH_NIL);;

let LASTN_BUTLASTN = prove_thm(`LASTN_BUTLASTN`,
    "!n m. !l:* list. ((n + m) <= LENGTH l) ==>
     (LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l))",
    let ADD_SUC_SYM = GEN_ALL (SYM (TRANS 
    	(SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))) in
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_SUC_LESS_EQ_0;ADD;ADD_0;LASTN;BUTLASTN]
    THEN REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO] THENL[
    	DISCH_TAC THEN CONV_TAC SYM_CONV THEN IMP_RES_TAC BUTLASTN_LASTN_NIL;
    	 PURE_ONCE_REWRITE_TAC[ADD_SUC_SYM] THEN DISCH_TAC THEN RES_TAC]);;

let BUTLASTN_LASTN = prove_thm(`BUTLASTN_LASTN`,
    "!m n. !l:* list. ((m <= n) /\ (n <= LENGTH l)) ==>
     (BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l))",
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_LESS_0;NOT_SUC_LESS_EQ_0;SUB_0;BUTLASTN;LASTN]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC;LESS_EQ_MONO;SUB_MONO_EQ]);;

let LASTN_1 = prove_thm(`LASTN_1`,
    "!l:* list. ~(l = []) ==> (LASTN 1 l = [LAST l])",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LASTN;APPEND_NIL;SNOC;LAST]);;

let BUTLASTN_1 = prove_thm(`BUTLASTN_1`,
    "!l:* list. ~(l = []) ==> (BUTLASTN 1 l = BUTLAST l)",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[BUTLAST;BUTLASTN]);;

let BUTLASTN_APPEND1 = prove_thm(`BUTLASTN_APPEND1`,
    "!l2 n. (LENGTH l2 <= n) ==>
     (!l1:* list. BUTLASTN n (APPEND l1 l2) = BUTLASTN (n - (LENGTH l2)) l1)",
    SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;APPEND;APPEND_SNOC;APPEND_NIL;SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;LESS_EQ_MONO;BUTLASTN;SUB_MONO_EQ]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let LASTN_APPEND2 = prove_thm(`LASTN_APPEND2`,
    "!n (l2:* list). n <= (LENGTH l2) ==>
     (!l1. LASTN n (APPEND l1 l2) = LASTN n l2)",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;LASTN;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO;LASTN;APPEND_SNOC]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let LASTN_APPEND1 = prove_thm(`LASTN_APPEND1`,
    "!(l2:* list) n. (LENGTH l2) <= n ==>
     (!l1. LASTN n (APPEND l1 l2) = APPEND (LASTN (n - (LENGTH l2)) l1) l2)",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;
    	APPEND;APPEND_SNOC;APPEND_NIL;LASTN;SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;LASTN;LESS_EQ_MONO;SUB_MONO_EQ]
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let LASTN_MAP = prove_thm(`LASTN_MAP`,
    "!n l. (n <= LENGTH l) ==>
     (!(f:*->**). LASTN n (MAP f l) = MAP f (LASTN n l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LASTN;MAP;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LENGTH_SNOC;LASTN;MAP_SNOC;LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let BUTLASTN_MAP = prove_thm(`BUTLASTN_MAP`,
    "!n l. (n <= LENGTH l) ==>
     (!(f:*->**). BUTLASTN n (MAP f l) = MAP f (BUTLASTN n l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTLASTN;MAP;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LENGTH_SNOC;BUTLASTN;MAP_SNOC;LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let ALL_EL_LASTN = prove_thm(`ALL_EL_LASTN`,
    "!P (l:* list). ALL_EL P l ==>
     (!m. m <= (LENGTH l) ==> ALL_EL P (LASTN m l))",
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[ALL_EL;LENGTH]
    THEN GEN_TAC THENL[
    	REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0]
    	THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_EL;LASTN];
    	REWRITE_TAC[ALL_EL_SNOC;LENGTH_SNOC] THEN STRIP_TAC
    	THEN INDUCT_TAC THENL[
    	    REWRITE_TAC[ALL_EL;LASTN];
    	    REWRITE_TAC[ALL_EL_SNOC;LASTN;LESS_EQ_MONO]
    	    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);;

let ALL_EL_BUTLASTN = prove_thm(`ALL_EL_BUTLASTN`,
    "!P (l:* list). ALL_EL P l ==>
     (!m. m <= (LENGTH l) ==> ALL_EL P (BUTLASTN m l))",
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[ALL_EL;LENGTH]
    THEN GEN_TAC THENL[
    	REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0]
    	THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_EL;BUTLASTN];
    	REWRITE_TAC[ALL_EL_SNOC;LENGTH_SNOC] THEN STRIP_TAC
    	THEN INDUCT_TAC THENL[
    	    DISCH_TAC THEN ASM_REWRITE_TAC[ALL_EL_SNOC;BUTLASTN];
    	    REWRITE_TAC[ALL_EL_SNOC;BUTLASTN;LESS_EQ_MONO]
    	    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);;

let LENGTH_FIRSTN = prove_thm (`LENGTH_FIRSTN`,
    "!n (l:(*)list). (n <= LENGTH l) ==> (LENGTH (FIRSTN n l) = n)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;FIRSTN;NOT_SUC_LESS_EQ_0;LESS_EQ_MONO]
    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC);;

let FIRSTN_FIRSTN = prove_thm(`FIRSTN_FIRSTN`,
    "!m (l:* list). (m <= LENGTH l) ==>
    !n. (n <= m) ==> (FIRSTN n (FIRSTN m l) = FIRSTN n l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;FIRSTN] THENL[
    	GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
    	THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;FIRSTN];
    	REWRITE_TAC[NOT_SUC_LESS_EQ_0];
    	GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC
    	THEN INDUCT_TAC THEN REWRITE_TAC[FIRSTN]
    	THEN REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC THEN RES_TAC
    	THEN ASM_REWRITE_TAC[]]);;

let LENGTH_BUTFIRSTN = prove_thm(`LENGTH_BUTFIRSTN`,
    "!n (l:* list). (n <= (LENGTH l)) ==>
     (LENGTH (BUTFIRSTN n l) = LENGTH l - n)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTFIRSTN;SUB_0;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO;SUB_MONO_EQ]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let BUTFIRSTN_LENGTH_NIL = prove_thm(`BUTFIRSTN_LENGTH_NIL`,
    "!l:* list. BUTFIRSTN (LENGTH l) l = []",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH;BUTFIRSTN]);;

let BUTFIRSTN_APPEND1 = prove_thm(`BUTFIRSTN_APPEND1`,
    "!n (l1:* list). (n <= LENGTH l1) ==>
     !l2. BUTFIRSTN n (APPEND l1 l2) = APPEND (BUTFIRSTN n l1) l2",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTFIRSTN;NOT_SUC_LESS_EQ_0;LESS_EQ_MONO]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[APPEND;BUTFIRSTN]);;

let BUTFIRSTN_APPEND2 = prove_thm(`BUTFIRSTN_APPEND2`,
    "!(l1:* list) n. ((LENGTH l1) <= n) ==>
     !l2. BUTFIRSTN n (APPEND l1 l2) = BUTFIRSTN (n - (LENGTH l1)) l2",
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;BUTFIRSTN;APPEND;SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC
    	[NOT_SUC_LESS_EQ_0;LESS_EQ_MONO;BUTFIRSTN;SUB_MONO_EQ]);;

let BUTFIRSTN_BUTFIRSTN = prove_thm(`BUTFIRSTN_BUTFIRSTN`,
    "!n m (l:* list). ((n + m) <= LENGTH l) ==>
     (BUTFIRSTN n(BUTFIRSTN m l) = BUTFIRSTN (n + m) l)",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTFIRSTN;NOT_SUC_LESS_EQ_0;NOT_LESS_0;ADD;ADD_0]
    THEN REWRITE_TAC[ADD_SUC_lem;LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let APPEND_FIRSTN_BUTFIRSTN = prove_thm(`APPEND_FIRSTN_BUTFIRSTN`,
    "!n (l:* list). (n <= LENGTH l) ==>
     (APPEND (FIRSTN n l) (BUTFIRSTN n l) = l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;FIRSTN;BUTFIRSTN;APPEND;NOT_SUC_LESS_EQ_0]
    THEN PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN GEN_TAC
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let LASTN_SEG = prove_thm(`LASTN_SEG`,
    "!n (l:* list). (n <= (LENGTH l)) ==>
     (LASTN n l = SEG n (LENGTH l - n) l)",
    let SUB_SUC = PROVE("!k m. (m < k) ==> (k - m = SUC (k - SUC m))",
      REPEAT GEN_TAC THEN SUBST_TAC[SYM(SPECL["k:num";"m:num"]SUB_MONO_EQ)]
      THEN DISCH_THEN \thm .  
               let thm' = MATCH_MP  LESS_SUC_NOT thm in
               ACCEPT_TAC (REWRITE_RULE [thm'] 
                      (SPECL ["k:num";"SUC m"] (CONJUNCT2 SUB)))) in
    INDUCT_TAC THEN REWRITE_TAC[LASTN;SUB_0;SEG] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LASTN;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO;SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN IMP_RES_TAC LESS_OR_EQ THENL[
    	IMP_RES_THEN SUBST1_TAC SUB_SUC
    	THEN PURE_ONCE_REWRITE_TAC[SEG] THEN IMP_RES_TAC LESS_EQ
    	THEN RES_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC LASTN_CONS
    	THEN FIRST_ASSUM ACCEPT_TAC;
    	FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC[SUB_EQUAL_0]
    	THEN SUBST1_TAC(SYM(SPECL["h:*";"l:* list"](CONJUNCT2 LENGTH)))
    	THEN REWRITE_TAC[SEG_LENGTH_ID;LASTN_LENGTH_ID]]);;
    	
let FIRSTN_SEG = prove_thm(`FIRSTN_SEG`,
    "!n (l:* list). (n <= (LENGTH l)) ==> (FIRSTN n l = SEG n 0 l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;FIRSTN;SEG;NOT_SUC_LESS_EQ_0;LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let BUTFIRSTN_SEG = prove_thm(`BUTFIRSTN_SEG`,
    "!n (l:* list). (n <= (LENGTH l)) ==>
     (BUTFIRSTN n l = SEG (LENGTH l - n) n l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTFIRSTN;SEG;NOT_SUC_LESS_EQ_0;
    	LESS_EQ_MONO;SUB_0;SEG_LENGTH_ID]
    THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN ASM_REWRITE_TAC[SUB_MONO_EQ;SEG_SUC_CONS]);;

let APPEND_BUTLAST_LAST  = prove_thm(`APPEND_BUTLAST_LAST`,
    "!l:* list. ~(l = []) ==> (APPEND (BUTLAST l) [(LAST l)] = l)",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SNOC_NIL;BUTLAST;LAST;SNOC_APPEND]);;

let BUTFIRSTN_SNOC = prove_thm(`BUTFIRSTN_SNOC`,
    "!n (l:* list). (n <= LENGTH l) ==>
     (!x. BUTFIRSTN n (SNOC x l) = SNOC x (BUTFIRSTN n l))",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;BUTFIRSTN;SNOC;NOT_SUC_LESS_EQ_0;LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let APPEND_BUTLASTN_BUTFIRSTN = prove_thm(`APPEND_BUTLASTN_BUTFIRSTN`,
    "!m n (l:* list). ((m + n) = (LENGTH l)) ==>
     (APPEND (BUTLASTN m l) (BUTFIRSTN n l) = l)",
    let ADD_EQ_LESS_EQ = PROVE("!m n p. ((m+n)=p) ==> (m<=p)",
      REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
      ASM_REWRITE_TAC[LESS_EQ_ADD]) in
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;APPEND;ADD;ADD_0;NOT_SUC;SUC_NOT;SNOC;
    	NOT_SUC_LESS_EQ_0;LESS_EQ_MONO;INV_SUC_EQ] THENL[
    	REWRITE_TAC[BUTLASTN;BUTFIRSTN;APPEND];
    	GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN SUBST1_TAC (SYM(SPECL["h:*";"l:* list"](CONJUNCT2 LENGTH)))
    	THEN REWRITE_TAC[BUTFIRSTN_LENGTH_NIL;BUTLASTN;APPEND_NIL];
    	GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN SUBST1_TAC (SYM(SPECL["h:*";"l:* list"](CONJUNCT2 LENGTH)))
    	THEN REWRITE_TAC[BUTLASTN_LENGTH_NIL;BUTFIRSTN;APPEND];
    	GEN_TAC THEN DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[BUTFIRSTN]
    	THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_SUC_lem])
    	THEN IMP_RES_TAC ADD_EQ_LESS_EQ THEN IMP_RES_TAC BUTLASTN_CONS
    	THEN ASM_REWRITE_TAC[APPEND;CONS_11] THEN RES_TAC]);;

let SEG_SEG = prove_thm(`SEG_SEG`,
    "!n1 m1 n2 m2 (l:* list).
     (((n1 + m1) <= (LENGTH l)) /\ ((n2 + m2) <= n1)) ==>
     (SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l)",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC 
    THEN REWRITE_TAC[LENGTH;SEG;NOT_LESS_0;NOT_SUC_LESS_EQ_0;ADD;ADD_0]
    THENL[
    	GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO;CONS_11]
    	THEN STRIP_TAC THEN SUBST_OCCS_TAC[[3],(SYM(SPEC"0"ADD_0))]
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0];
    	REWRITE_TAC[LESS_EQ_MONO;ADD_SUC_lem] THEN STRIP_TAC
    	THEN SUBST_OCCS_TAC[[2],SYM(SPEC"m2:num"(CONJUNCT1 ADD))]
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0];
    	REWRITE_TAC[LESS_EQ_MONO;ADD_SUC_lem] THEN STRIP_TAC
    	THEN SUBST_OCCS_TAC[[2],SYM(SPEC"m1:num"ADD_0)]
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LESS_EQ_MONO;ADD_0];
    	PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN STRIP_TAC
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL[
    	    PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC_lem]
    	    THEN FIRST_ASSUM ACCEPT_TAC;
    	    ASM_REWRITE_TAC[ADD;LESS_EQ_MONO]]]);;

let SEG_APPEND1 = prove_thm(`SEG_APPEND1`,
    "!n m (l1:* list). ((n + m) <= LENGTH l1) ==>
     (!l2. SEG n m (APPEND l1 l2) = SEG n m l1)",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC 
    THEN REWRITE_TAC[LENGTH;SEG;NOT_LESS_0;NOT_SUC_LESS_EQ_0;ADD;ADD_0]
    THEN GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO;APPEND;SEG;CONS_11] THENL[
    	DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC
    	THEN ASM_REWRITE_TAC[ADD_0];
    	PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let SEG_APPEND2 = prove_thm(`SEG_APPEND2`,
    "!l1:* list. !m n l2.
     (LENGTH l1 <= m) /\ (n <= LENGTH l2) ==>
     (SEG n m (APPEND l1 l2) = SEG n (m - (LENGTH l1)) l2)",
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "m:num")
    THEN REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;SEG;NOT_LESS_0;NOT_SUC_LESS_EQ_0;ADD;ADD_0]
    THEN REPEAT GEN_TAC THEN REWRITE_TAC[SUB_0;APPEND;SEG]
    THEN REWRITE_TAC[LESS_EQ_MONO;SUB_MONO_EQ] THEN STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH;LESS_EQ_MONO]);;

let SEG_FIRSTN_BUTFIRSTN = prove_thm(`SEG_FIRSTN_BUTFISTN`,
    "!n m (l:* list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m l = FIRSTN n (BUTFIRSTN m l))",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_SUC_LESS_EQ_0;ADD;ADD_0;
    	SEG;FIRSTN;BUTFIRSTN;LESS_EQ_MONO;CONS_11] THENL[
    	MATCH_ACCEPT_TAC (GSYM FIRSTN_SEG);
    	PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let SEG_APPEND = prove_thm(`SEG_APPEND`,
    "!m (l1:* list) n l2. (m < LENGTH l1) /\ ((LENGTH l1) <= (n + m)) /\
      ((n + m) <= ((LENGTH l1) + (LENGTH l2))) ==>
      (SEG n m (APPEND l1 l2) =
    	APPEND (SEG ((LENGTH l1) - m) m l1) (SEG ((n + m)-(LENGTH l1)) 0 l2))",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "n:num")
    THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH;SEG;NOT_LESS_0;NOT_SUC_LESS_EQ_0;ADD;ADD_0;SUB_0]
    THEN REWRITE_TAC
    	[LESS_EQ_MONO;SUB_0;SUB_MONO_EQ;APPEND;SEG;NOT_SUC_LESS_EQ_0;CONS_11]
    THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_0;SUB_0])
    THENL[
    	DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
    	THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
    	THEN REWRITE_TAC[SEG;APPEND_NIL;SUB_EQUAL_0];
    	STRIP_TAC THEN DISJ_CASES_TAC (SPEC "LENGTH (l1:* list)"LESS_0_CASES)
    	THENL[
    	    POP_ASSUM (ASSUME_TAC o SYM) THEN IMP_RES_TAC LENGTH_NIL
    	    THEN ASM_REWRITE_TAC[APPEND;SEG;SUB_0];
    	    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]];
    	DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
    	THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
    	THEN REWRITE_TAC[SEG;APPEND_NIL;SUB_EQUAL_0];
    	REWRITE_TAC[LESS_MONO_EQ;GSYM NOT_LESS] THEN STRIP_TAC THEN RES_TAC;
    	DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
    	THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
    	THEN REWRITE_TAC[SEG;APPEND_NIL;SUB_EQUAL_0]
    	THEN REWRITE_TAC[ADD_SUC_lem;ADD_SUB;SEG];
    	REWRITE_TAC[LESS_MONO_EQ;SEG_SUC_CONS] THEN STRIP_TAC
    	THEN PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_MP_TAC
    	THEN ASM_REWRITE_TAC[GSYM ADD_SUC_lem;LENGTH]]);;


let SEG_LENGTH_SNOC = prove_thm(`SEG_LENGTH_SNOC`,
    "!(l:* list) x. SEG 1 (LENGTH l) (SNOC x l) = [x]",
    CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;SNOC;SEG]);;

let SEG_SNOC = prove_thm(`SEG_SNOC`,
    "!n m (l:* list). ((n + m) <= LENGTH l) ==>
     !x. SEG n m (SNOC x l) = SEG n m l",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;NOT_SUC_LESS_EQ_0;ADD;ADD_0;SNOC;SEG] THENL[
    	REWRITE_TAC[CONS_11;LESS_EQ_MONO] THEN REPEAT STRIP_TAC
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0];
    	REWRITE_TAC[LESS_EQ_MONO;ADD_SUC_lem] THEN DISCH_TAC
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let ELL_SEG = prove_thm(`ELL_SEG`,
    "!n (l:* list). (n < LENGTH l) ==>
     (ELL n l = HD(SEG 1 (PRE(LENGTH l - n)) l))",
    let SUC_PRE = PROVE("!n . (0 < n) ==> ((SUC (PRE n)) = n)",
      REPEAT STRIP_TAC THEN  (ACCEPT_TAC (REWRITE_RULE[]
          (MATCH_MP (SPECL["PRE n";"n:num"] PRE_SUC_EQ)
                 (ASSUME "0 < n") )))) in
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;NOT_LESS_0] THENL[
    	REWRITE_TAC[PRE;SUB_0;ELL;LAST;SEG_LENGTH_SNOC;HD];
    	REWRITE_TAC[LESS_MONO_EQ;ELL;BUTLAST;SUB_MONO_EQ]
    	THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    	THEN CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN MATCH_MP_TAC SEG_SNOC
    	THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
        THEN PURE_ONCE_REWRITE_TAC[GSYM ADD1]
    	THEN IMP_RES_TAC SUB_LESS_0 THEN IMP_RES_THEN SUBST1_TAC SUC_PRE
    	THEN MATCH_ACCEPT_TAC SUB_LESS_EQ]);;

%---------------------------------------------------------------------- %
% 31 Jan 94 	    	    	    					%
%---------------------------------------------------------------------- %

let REWRITE1_TAC = \t.REWRITE_TAC[t];;

let SNOC_FOLDR = prove_thm (`SNOC_FOLDR`,
    "!(x:*) l. SNOC x l = FOLDR CONS [x] l ",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDR;SNOC]);;

let IS_EL_FOLDR_MAP = prove_thm(`IS_EL_FOLDR_MAP`,
    "!(x:*) l. IS_EL x l = FOLDR $\/ F (MAP ($= x) l)",
    REWRITE_TAC[IS_EL_FOLDR;FOLDR_MAP]);;

let IS_EL_FOLDL_MAP = prove_thm(`IS_EL_FOLDL_MAP`,
    "!(x:*) l. IS_EL x l = FOLDL $\/ F (MAP ($= x) l)",
    REWRITE_TAC[IS_EL_FOLDL;FOLDL_MAP]);;

let FILTER_FILTER = prove_thm(`FILTER_FILTER`,
    "!P Q (l:* list). FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l",
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN BETA_TAC THEN GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[FILTER]);;

let FCOMM_FOLDR_FLAT = prove_thm(`FCOMM_FOLDR_FLAT`,
    "!(g:*->*->*) (f:**->*->*). FCOMM g f ==>
     (! e. LEFT_ID g e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR g e (MAP (FOLDR f e) l)))",
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT;MAP;FOLDR]
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);;

let FCOMM_FOLDL_FLAT = prove_thm(`FCOMM_FOLDL_FLAT`,
    "!(f:*->**->*) (g:*->*->*). FCOMM f g ==>
     (! e. RIGHT_ID g e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL g e (MAP (FOLDL f e) l)))",
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN DISCH_TAC THEN SNOC_INDUCT_TAC 
    THEN ASM_REWRITE_TAC[FLAT_SNOC;MAP_SNOC;MAP;FLAT;FOLDL_SNOC;FOLDL]
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);;

let FOLDR1 = PROVE(
    "!(f:*->*->*).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. (FOLDR f (f h e) l = f h (FOLDR f e l)))",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[REVERSE; FOLDR] THEN ONCE_REWRITE_TAC
    [ASSUME "!a b c. (f:*->*->*) a (f b c) = f b (f a c)"]
    THEN REWRITE_TAC[ASSUME"FOLDR (f:*->*->*)(f h e) l = f h (FOLDR f e l)"]);;

let FOLDL1 = PROVE(
    "!(f:*->*->*).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. (FOLDL f (f e h) l = f (FOLDL f e l) h))",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[REVERSE; FOLDL; FOLDL_SNOC]
    THEN ONCE_REWRITE_TAC
    [ASSUME "!a b c. (f:*->*->*) (f a b) c = f (f a c) b"]
    THEN REWRITE_TAC[ASSUME"FOLDL(f:*->*->*)(f e h) l = f (FOLDL f e l) h"]);;

let FOLDR_REVERSE2 = PROVE(
    "!(f:*->*->*).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. FOLDR f e (REVERSE l) = FOLDR f e l)",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE; FOLDR; FOLDR_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN ASM_REWRITE_TAC[]);;

let FOLDR_MAP_REVERSE = prove_thm(`FOLDR_MAP_REVERSE`,
    "!(f:*->*->*).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e (g:**->*) l. FOLDR f e (MAP g (REVERSE l)) = FOLDR f e (MAP g l))",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE; FOLDR; FOLDR_SNOC;MAP;MAP_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN ASM_REWRITE_TAC[]);;

let FOLDR_FILTER_REVERSE = prove_thm(`FOLDR_FILTER_REVERSE`,
    "!(f:*->*->*).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e (P:*->bool) l. 
           FOLDR f e (FILTER P (REVERSE l)) = FOLDR f e (FILTER P l))",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE; FOLDR; FOLDR_SNOC;FILTER;FILTER_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN GEN_TAC THEN COND_CASES_TAC THENL[
    	ASM_REWRITE_TAC[ FOLDR; FOLDR_SNOC;FILTER;FILTER_SNOC]
    	THEN ASM_REWRITE_TAC[GSYM FILTER_REVERSE];
    	ASM_REWRITE_TAC[ FOLDR; FOLDR_SNOC;FILTER;FILTER_SNOC]]);;

let FOLDL_REVERSE2 = PROVE(
    "!(f:*->*->*).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l)",
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE;REVERSE_SNOC; FOLDL; FOLDL_SNOC]
    THEN IMP_RES_TAC FOLDL1 THEN ASM_REWRITE_TAC[]);;

let COMM_ASSOC_LEM1 = PROVE(
    "!(f:*->*->*). COMM f ==> (ASSOC f ==>
      (!a b c. f a (f b c) = f b (f a c)))",
    REWRITE_TAC[ASSOC_DEF] THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[] THEN SUBST1_TAC(SPECL ["a:*";"b:*"]
      (REWRITE_RULE [COMM_DEF] (ASSUME "COMM (f:*->*->*)")))
    THEN REWRITE_TAC[]);;

let COMM_ASSOC_LEM2 = PROVE(
    "!(f:*->*->*). COMM f ==> (ASSOC f ==>
      (!a b c. f (f a b) c = f (f a c) b))",
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC
      [GSYM (REWRITE_RULE[ASSOC_DEF] (ASSUME "ASSOC (f:*->*->*)"))]
    THEN SUBST1_TAC(SPECL ["b:*";"c:*"]
      (REWRITE_RULE [COMM_DEF] (ASSUME "COMM (f:*->*->*)")))
    THEN REWRITE_TAC[]);;

let COMM_ASSOC_FOLDR_REVERSE = prove_thm(`COMM_ASSOC_FOLDR_REVERSE`,
    "!f:*->*->*. COMM f ==> (ASSOC f ==>
       (!e l. FOLDR f e (REVERSE l) = FOLDR f e l))",
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDR_REVERSE2
    THEN IMP_RES_TAC COMM_ASSOC_LEM1);;

let COMM_ASSOC_FOLDL_REVERSE = prove_thm(`COMM_ASSOC_FOLDL_REVERSE`,
    "!f:*->*->*. COMM f ==> (ASSOC f ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l))",
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDL_REVERSE2
    THEN IMP_RES_TAC COMM_ASSOC_LEM2);;



%<------------------------------------------------------------>%
let ELL_LAST = prove_thm(`ELL_LAST`,
    "!l:* list. ~(NULL l) ==> (ELL 0 l = LAST l)",
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[NULL];
      REPEAT STRIP_TAC THEN REWRITE_TAC[ELL]]);;

let ELL_0_SNOC = prove_thm(`ELL_0_SNOC`,
    "!l:* list. !x. (ELL 0 (SNOC x l) = x)",
     REPEAT GEN_TAC THEN REWRITE_TAC[ELL;LAST]);;

let ELL_SNOC = prove_thm(`ELL_SNOC`,
    "!n. (0 < n) ==> !x (l:* list).ELL n (SNOC x l) = ELL (PRE n) l",
    INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0];
      REWRITE_TAC[ELL;BUTLAST;PRE;LESS_0]]);;

% |- !n x (l:* list). (ELL (SUC n) (SNOC x l) = ELL n l) %
let ELL_SUC_SNOC = save_thm(`ELL_SUC_SNOC`,
    GEN_ALL(PURE_ONCE_REWRITE_RULE[PRE]
    (MP (SPEC "SUC n" ELL_SNOC) (SPEC_ALL LESS_0))));;

let ELL_CONS = prove_thm(`ELL_CONS`,
    "!n (l:* list). n < (LENGTH l) ==> (!x. ELL n (CONS x l) = ELL n l)",
    let SNOC_lem = GSYM(CONJUNCT2 SNOC) in
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0;LENGTH]
    THENL[
    	REPEAT STRIP_TAC THEN REWRITE_TAC[SNOC_lem;ELL_0_SNOC];
    	GEN_TAC THEN REWRITE_TAC[LENGTH_SNOC;LESS_MONO_EQ;
    	    ELL_SUC_SNOC;SNOC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let ELL_LENGTH_CONS = prove_thm(`ELL_LENGTH_CONS`, 
    "!l:* list. !x. (ELL (LENGTH l) (CONS x l) = x)",
    let LAST_EL = % "!x:*. LAST [x] = x" %
    	GEN_ALL(REWRITE_RULE[SNOC](SPECL["x:*";"[]:* list"]LAST)) in
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[ELL;LENGTH;LAST_EL];
      REWRITE_TAC[ELL;LENGTH_SNOC;BUTLAST;(GSYM(CONJUNCT2 SNOC))]
      THEN POP_ASSUM ACCEPT_TAC]);;

let ELL_LENGTH_SNOC = prove_thm(`ELL_LENGTH_SNOC`, 
    "!l:* list. !x. (ELL (LENGTH l) (SNOC x l) = (NULL l => x | HD l))",
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC[ELL_0_SNOC;LENGTH;NULL];
      REWRITE_TAC[ELL_SUC_SNOC;LENGTH;HD;NULL;ELL_LENGTH_CONS]]);;

let ELL_APPEND2 = prove_thm(`ELL_APPEND2`,
    "!n l2. n < LENGTH l2 ==> !l1:* list. ELL n (APPEND l1 l2) = ELL n l2",
    INDUCT_TAC THEN SNOC_INDUCT_TAC 
    THEN REWRITE_TAC[LENGTH;NOT_LESS_0]
    THEN REWRITE_TAC[APPEND_SNOC;ELL_0_SNOC;ELL_SUC_SNOC;
    	LENGTH_SNOC;LESS_MONO_EQ] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let ELL_APPEND1 = prove_thm(`ELL_APPEND1`,
    "!l2 n. LENGTH l2 <= n ==>
     !l1:* list. ELL n (APPEND l1 l2) = ELL (n - LENGTH l2) l1",
    SNOC_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "n:num")
    THEN INDUCT_TAC THEN REWRITE_TAC
    	[LENGTH;LENGTH_SNOC;SUB_0;APPEND_NIL;NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO;ELL_SUC_SNOC;SUB_MONO_EQ;APPEND_SNOC]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let ELL_PRE_LENGTH = prove_thm(`ELL_PRE_LENGTH`,
    "!l:* list. ~(l = []) ==> (ELL (PRE(LENGTH l)) l  = HD l)",
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;PRE]
    THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ELL_LENGTH_CONS;HD]);;

let EL_LENGTH_SNOC = prove_thm(`EL_LENGTH_SNOC`, 
    "!l:* list. !x. EL (LENGTH l) (SNOC x l) = x",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EL;SNOC;HD;TL;LENGTH]);;

let EL_PRE_LENGTH = prove_thm(`EL_PRE_LENGTH`,
    "!l:* list. ~(l = []) ==> (EL (PRE(LENGTH l)) l  = LAST l)",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC;PRE;LAST;EL_LENGTH_SNOC]);;

let EL_SNOC = prove_thm(`EL_SNOC`,
    "!n (l:* list). n < (LENGTH l) ==> (!x. EL n (SNOC x l) = EL n l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;NOT_LESS_0]
    THENL[
    	REWRITE_TAC[SNOC;EL;HD];
    	REWRITE_TAC[SNOC;EL;TL;LESS_MONO_EQ]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let LESS_PRE_SUB_LESS = PROVE("!n m. (m < n) ==> (PRE(n - m) < n)",
    let PRE_K_K = PROVE("!k . (0<k) ==> (PRE k < k)",
      INDUCT_THEN INDUCTION MP_TAC THEN
      REWRITE_TAC [LESS_REFL;LESS_0;PRE;LESS_SUC_REFL]) in
    REPEAT INDUCT_TAC THENL[
    	REWRITE_TAC[NOT_LESS_0];
    	REWRITE_TAC[NOT_LESS_0];
    	REWRITE_TAC[SUB_0;PRE_K_K];
    	REWRITE_TAC[LESS_MONO_EQ;SUB_MONO_EQ;LESS_THM]
    	THEN DISCH_TAC THEN DISJ2_TAC THEN RES_TAC]);;

let EL_ELL = prove_thm(`EL_ELL`,
    "!n (l:* list). n < LENGTH l ==> (EL n l = ELL (PRE((LENGTH l) - n)) l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;NOT_LESS_0]
    THENL[
    	REWRITE_TAC[PRE;EL;ELL_LENGTH_CONS;HD;SUB_0];
        REWRITE_TAC[EL;TL;LESS_MONO_EQ;SUB_MONO_EQ]
    	THEN GEN_TAC THEN DISCH_TAC
    	THEN MAP_EVERY IMP_RES_TAC [LESS_PRE_SUB_LESS;ELL_CONS]
    	THEN RES_TAC THEN ASM_REWRITE_TAC[]]);;

let EL_LENGTH_APPEND = prove_thm(`EL_LENGTH_APPEND`,
  "!(l2:(*)list) (l1:(*)list) .
      ~(NULL l2)==> ( EL (LENGTH l1) (APPEND l1 l2) = HD l2)",
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;APPEND;EL;TL;NULL]
  THEN REPEAT STRIP_TAC THEN RES_TAC);;

let ELL_EL = prove_thm(`ELL_EL`,
    "!n (l:* list). n < LENGTH l ==> (ELL n l = EL (PRE((LENGTH l) - n)) l)",
    let lem = PROVE("!n m. n < m ==> ?k. (m - n = SUC k) /\ k < m",
    	REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THENL[
    	    REWRITE_TAC[SUB_0] THEN DISCH_TAC
    	    THEN EXISTS_TAC "m:num" THEN REWRITE_TAC[LESS_SUC_REFL];
    	    ASM_REWRITE_TAC[LESS_MONO_EQ;SUB_MONO_EQ]
    	    THEN DISCH_TAC THEN RES_TAC THEN EXISTS_TAC "k:num"
    	    THEN IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC[]]) in
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH;NOT_LESS_0]
    THENL[
        REWRITE_TAC[SUB_0;ELL_0_SNOC;LENGTH_SNOC;PRE;EL_LENGTH_SNOC];
    	REWRITE_TAC[LENGTH_SNOC;ELL_SUC_SNOC;SUB_MONO_EQ;LESS_MONO_EQ]
    	THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC 
    	THEN MATCH_MP_TAC (GSYM EL_SNOC)
    	THEN IMP_RES_TAC lem THEN ASM_REWRITE_TAC[PRE]]);;

let ELL_MAP = prove_thm(`ELL_MAP`,
    "!n l (f:*->**). n < (LENGTH l) ==> (ELL n (MAP f l) = f (ELL n l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH;NOT_LESS_0]
    THENL[
        REWRITE_TAC[ELL_0_SNOC;MAP_SNOC];
        REWRITE_TAC[LENGTH_SNOC;ELL_SUC_SNOC;MAP_SNOC;LESS_MONO_EQ] 
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let LENGTH_BUTLAST = prove_thm(`LENGTH_BUTLAST`,
    "!l:* list. ~(l = []) ==> (LENGTH(BUTLAST l) = PRE(LENGTH l))",
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC;BUTLAST;PRE]);;

let BUTFIRSTN_LENGTH_APPEND = prove_thm(`BUTFIRSTN_LENGTH_APPEND`,
    "!l1 l2:* list. BUTFIRSTN(LENGTH l1)(APPEND l1 l2) = l2",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH;BUTFIRSTN;APPEND]);;

let FIRSTN_APPEND1 = prove_thm(`FIRSTN_APPEND1`,
    "!n (l1:* list). n <= (LENGTH l1) ==>
     !l2. FIRSTN n (APPEND l1 l2) = FIRSTN n l1",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC
    	[LENGTH;NOT_SUC_LESS_EQ_0;FIRSTN;APPEND;CONS_11;LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let FIRSTN_APPEND2 = prove_thm(`FIRSTN_APPEND2`,
    "!(l1:* list) n. (LENGTH l1) <= n ==>
     !l2. FIRSTN n (APPEND l1 l2) = APPEND l1 (FIRSTN (n - (LENGTH l1)) l2)",
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;APPEND;SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;
    	LESS_EQ_MONO;SUB_MONO_EQ;FIRSTN;CONS_11]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let FIRSTN_LENGTH_APPEND = prove_thm(`FIRSTN_LENGTH_APPEND`,
    "!(l1:* list) l2. FIRSTN (LENGTH l1) (APPEND l1 l2) = l1",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH;FIRSTN;APPEND]);;

%<---------------------------------------------------------------------->%

let REVERSE_FLAT = prove_thm(`REVERSE_FLAT`,
   "!l:* list list. REVERSE (FLAT l) = FLAT(REVERSE(MAP REVERSE l))",
   LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE;FLAT;MAP]
   THEN ASM_REWRITE_TAC[REVERSE_APPEND;FLAT_SNOC]);;

let MAP_COND = prove(
   "!(f:*-> **) c l1 l2.
        (MAP f (c => l1 | l2)) = (c => (MAP f l1) | (MAP f l2))",
   REPEAT GEN_TAC THEN BOOL_CASES_TAC "c:bool" THEN ASM_REWRITE_TAC[]);;

let MAP_FILTER = prove_thm(`MAP_FILTER`,
   "!(f:* -> *) P l. 
        (!x. P (f x) = P x) ==>
             (MAP f (FILTER P l) = FILTER P (MAP f l))",
   GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP;FILTER]
   THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MAP_COND;MAP]
   THEN RES_THEN SUBST1_TAC THEN REFL_TAC);;

let FLAT_APPEND = prove_thm(`FLAT_APPEND`,
    "!l1 l2:* list list.
         FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)",
    LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND;FLAT]
    THEN ASM_REWRITE_TAC[APPEND_ASSOC]);;

let FLAT_REVERSE = prove_thm(`FLAT_REVERSE`,
    "!l:* list list. FLAT (REVERSE l) = REVERSE (FLAT (MAP REVERSE l))",
    LIST_INDUCT_TAC THEN  REWRITE_TAC[FLAT;REVERSE;MAP]
    THEN ASM_REWRITE_TAC[FLAT_SNOC;REVERSE_APPEND;REVERSE_REVERSE]);;

let FLAT_FLAT = prove_thm(`FLAT_FLAT`,
    "!l:* list list list. FLAT (FLAT l) = FLAT(MAP FLAT l)",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT;FLAT_APPEND;MAP]);;

let ALL_EL_REVERSE = prove_thm(`ALL_EL_REVERSE`,
    "!P (l:* list). ALL_EL P (REVERSE l) = ALL_EL P l",
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[ALL_EL;REVERSE;ALL_EL_SNOC]
    THEN GEN_TAC THEN MATCH_ACCEPT_TAC CONJ_SYM);;

let SOME_EL_REVERSE = prove_thm(`SOME_EL_REVERSE`,
    "!P (l:* list). SOME_EL P (REVERSE l) = SOME_EL P l",
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SOME_EL;REVERSE;SOME_EL_SNOC]
    THEN GEN_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM);;

let ALL_EL_SEG = prove_thm(`ALL_EL_SEG`,
    "!P (l:* list). ALL_EL P l ==>
     !m k. (m + k) <= (LENGTH l) ==> ALL_EL P (SEG m k l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL;SEG;LENGTH] THENL[
      REPEAT INDUCT_TAC
      THEN REWRITE_TAC[ADD;ADD_0;NOT_SUC_LESS_EQ_0;SEG;ALL_EL];
      GEN_TAC THEN STRIP_TAC THEN REPEAT INDUCT_TAC
      THEN REWRITE_TAC[ADD;ADD_0;NOT_SUC_LESS_EQ_0;LESS_EQ_MONO;SEG;ALL_EL]
      THENL[
        RES_THEN (ASSUME_TAC o (REWRITE_RULE[ADD_0]) o (SPECL ["m:num";"0"]))
    	THEN DISCH_TAC THEN RES_TAC
    	THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    	let lem = SPEC"k:num" (GEN "n:num"
    	    (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC)))) in
    	SUBST1_TAC lem THEN DISCH_TAC THEN RES_TAC]]);;

let ALL_EL_FIRSTN = prove_thm(`ALL_EL_FIRSTN`,
    "!P (l:* list). ALL_EL P l ==>
     !m. m <= (LENGTH l) ==> ALL_EL P (FIRSTN m l)",
    REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC FIRSTN_SEG
    THEN IMP_RES_THEN MATCH_MP_TAC ALL_EL_SEG
    THEN ASM_REWRITE_TAC[ADD_0]);;

let ALL_EL_BUTFIRSTN = prove_thm(`ALL_EL_BUTFIRSTN`,
    "!P (l:* list). ALL_EL P l ==>
     !m. m <= (LENGTH l) ==> ALL_EL P (BUTFIRSTN m l)",
    REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC BUTFIRSTN_SEG
    THEN IMP_RES_THEN MATCH_MP_TAC ALL_EL_SEG
    THEN IMP_RES_THEN SUBST1_TAC SUB_ADD
    THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);;

let SOME_EL_SEG = prove_thm(`SOME_EL_SEG`,
    "!m k (l:* list). (m + k) <= (LENGTH l) ==> 
     !P. SOME_EL P (SEG m k l) ==> SOME_EL P l",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SOME_EL;SEG;LENGTH;ADD;ADD_0;NOT_SUC_LESS_EQ_0]
    THEN GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO] THENL[
      FIRST_ASSUM (ASSUME_TAC o (REWRITE_RULE[ADD_0]) o (SPEC"0"))
      THEN REPEAT STRIP_TAC THENL[
    	DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    	DISJ2_TAC THEN RES_TAC];
    	let lem = SPEC"k:num" (GEN "n:num"
    	    (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC)))) in
    	SUBST1_TAC lem THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC]);;

let SOME_EL_FIRSTN = prove_thm(`SOME_EL_FIRSTN`,
    "!m (l:* list). m <= (LENGTH l) ==>
    	!P.  SOME_EL P (FIRSTN m l) ==> SOME_EL P l",
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC FIRSTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN ASM_REWRITE_TAC[ADD_0]);;

let SOME_EL_BUTFIRSTN = prove_thm(`SOME_EL_BUTFIRSTN`,
    "!m (l:* list). m <= (LENGTH l) ==>
     !P. SOME_EL P (BUTFIRSTN m l) ==> SOME_EL P l",
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTFIRSTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN IMP_RES_THEN SUBST1_TAC SUB_ADD
    THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);;

let SOME_EL_LASTN = prove_thm(`SOME_EL_LASTN`,
    "!m (l:* list). m <= (LENGTH l) ==>
     !P. SOME_EL P (LASTN m l) ==> SOME_EL P l",
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC LASTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN IMP_RES_THEN SUBST1_TAC SUB_ADD THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);;

let SOME_EL_BUTLASTN = prove_thm(`SOME_EL_BUTLASTN`,
    "!m (l:* list). m <= (LENGTH l) ==>
     !P. SOME_EL P (BUTLASTN m l) ==> SOME_EL P l",
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN PURE_ONCE_REWRITE_TAC[ADD_0]
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);;

let IS_EL_REVERSE = prove_thm(`IS_EL_REVERSE`,
    "!(x:*) l. IS_EL x (REVERSE l) = IS_EL x l",
    GEN_TAC THEN LIST_INDUCT_TAC 
    THEN ASM_REWRITE_TAC[REVERSE;IS_EL;IS_EL_SNOC]);;

let IS_EL_FILTER = prove_thm(`IS_EL_FILTER`,
    "!P (x:*). P x ==> !l. IS_EL x (FILTER P l) = IS_EL x l",
    REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER;IS_EL] THEN GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[IS_EL] THEN EQ_TAC THENL[
    	DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    	STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN RES_TAC]);;

let IS_EL_SEG = prove_thm(`IS_EL_SEG`,
    "!n m (l:* list). ((n + m) <= (LENGTH l)) ==>
     !x. IS_EL x (SEG n m l) ==> IS_EL x l",
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[ADD;ADD_0;NOT_SUC_LESS_EQ_0;LENGTH;IS_EL;
    	SEG;LESS_EQ_MONO] THEN GEN_TAC THENL[
    	DISCH_TAC THEN FIRST_ASSUM (IMP_RES_TAC o
    	    (REWRITE_RULE[ADD_0]) o (SPEC"0"))
    	THEN GEN_TAC THEN DISCH_THEN (DISJ_CASES_THEN2 
    	    (\t. DISJ1_TAC THEN ACCEPT_TAC t)
    	    (\t. DISJ2_TAC THEN ASSUME_TAC t THEN RES_TAC));
    	let lem = (GEN_ALL
    	    (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC)))) in
    	PURE_ONCE_REWRITE_TAC[lem] THEN REPEAT STRIP_TAC
    	THEN DISJ2_TAC THEN RES_TAC]);;

let IS_EL_SOME_EL = prove_thm(`IS_EL_SOME_EL`,
    "!(x:*) l. IS_EL x l = SOME_EL ($= x) l",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[IS_EL;SOME_EL]);;

let IS_EL_FIRSTN = prove_thm(`IS_EL_FIRSTN`,
    "!m l. m <= (LENGTH l) ==> !x:*.  IS_EL x (FIRSTN m l) ==> IS_EL x l",
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_FIRSTN);;

let IS_EL_BUTFIRSTN = prove_thm(`IS_EL_BUTFIRSTN`,
    "!m l. m <= (LENGTH l) ==> !x:*.  IS_EL x (BUTFIRSTN m l) ==> IS_EL x l",
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_BUTFIRSTN);;

let IS_EL_BUTLASTN = prove_thm(`IS_EL_BUTLASTN`,
    "!m l. m <= (LENGTH l) ==> !x:*.  IS_EL x (BUTLASTN m l) ==> IS_EL x l",
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_BUTLASTN);;

let IS_EL_LASTN = prove_thm(`IS_EL_LASTN`,
    "!m l. m <= (LENGTH l) ==> !x:*.  IS_EL x (LASTN m l) ==> IS_EL x l",
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_LASTN);;


let ZIP_SNOC = prove_thm(`ZIP_SNOC`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !(x1:*) (x2:**). 
      ZIP((SNOC x1 l1), (SNOC x2 l2)) = SNOC (x1,x2) (ZIP(l1,l2))",
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "l2:** list")
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC;ZIP;LENGTH;NOT_SUC;SUC_NOT]
    THEN REWRITE_TAC[INV_SUC_EQ;CONS_11] THEN REPEAT STRIP_TAC
    THEN RES_THEN MATCH_ACCEPT_TAC);;

let UNZIP_SNOC = prove_thm(`UNZIP_SNOC`,
    "!(x:* # **) l.
     UNZIP(SNOC x l) = SNOC(FST x)(FST(UNZIP l)), SNOC(SND x)(SND(UNZIP l))",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC;UNZIP]);;

let LENGTH_ZIP = prove_thm(`LENGTH_ZIP`,
    "!l1:* list. !l2:** list. (LENGTH l1 = LENGTH l2) ==>
    (LENGTH(ZIP(l1,l2)) = LENGTH l1) /\ (LENGTH(ZIP(l1,l2)) = LENGTH l2)",
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "l2:** list")
    THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[ZIP;LENGTH;NOT_SUC;SUC_NOT;INV_SUC_EQ]
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let LENGTH_UNZIP_FST = prove_thm(`LENGTH_UNZIP_FST`,
    "!l:(* # **)list. LENGTH (UNZIP_FST l) = LENGTH l",
    PURE_ONCE_REWRITE_TAC[UNZIP_FST_DEF]
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP;LENGTH]);;

let LENGTH_UNZIP_SND = prove_thm(`LENGTH_UNZIP_SND`,
    "!l:(* # **)list. LENGTH (UNZIP_SND l) = LENGTH l",
    PURE_ONCE_REWRITE_TAC[UNZIP_SND_DEF]
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP;LENGTH]);;

let ZIP_UNZIP = prove_thm(`ZIP_UNZIP`,
    "!l:(* # **)list. ZIP(UNZIP l) = l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP;ZIP]);;

let UNZIP_ZIP = prove_thm(`UNZIP_ZIP`,
    "!l1:* list. !l2:** list.
     (LENGTH l1 = LENGTH l2) ==> (UNZIP(ZIP(l1,l2)) = (l1,l2))",
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "l2:** list")
    THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[UNZIP;ZIP;LENGTH;NOT_SUC;SUC_NOT;INV_SUC_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let SUM_APPEND = prove_thm(`SUM_APPEND`,
    "!l1 l2. SUM (APPEND l1 l2) = SUM l1 + SUM l2",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM;APPEND;ADD;ADD_0;ADD_ASSOC]);;

let SUM_REVERSE = prove_thm(`SUM_REVERSE`,
    "!l. SUM (REVERSE l) = SUM l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM;REVERSE;SUM_SNOC]
    THEN MATCH_ACCEPT_TAC ADD_SYM);;

let SUM_FLAT = prove_thm(`SUM_FLAT`,
    "!l. SUM (FLAT l) = SUM (MAP SUM l)",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM;FLAT;MAP;SUM_APPEND]);;

let EL_APPEND1 = prove_thm(`EL_APPEND1`,
    "!n l1 (l2:* list). n < (LENGTH l1) ==> (EL n (APPEND l1 l2) = EL n l1)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[EL;APPEND;HD;TL;LENGTH;NOT_LESS_0;LESS_MONO_EQ]);;

let EL_APPEND2 = prove_thm(`EL_APPEND2`,
    "!(l1:* list) n. (LENGTH l1) <= n ==>
     !l2. EL n (APPEND l1 l2) = EL (n - (LENGTH l1)) l2",
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;APPEND;SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[EL;APPEND;HD;TL;
    	LENGTH;NOT_SUC_LESS_EQ_0;SUB_MONO_EQ;LESS_EQ_MONO]);;

let EL_MAP = prove_thm(`EL_MAP`,
    "!n l. n < (LENGTH l) ==> !f:*->**. EL n (MAP f l) = f (EL n l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;EL;MAP;LESS_MONO_EQ;NOT_LESS_0;HD;TL]);;

let EL_CONS = prove_thm(`EL_CONS`,
    "!n. 0 < n ==> !(x:*) l. EL n (CONS x l) = EL (PRE n) l",
    INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0;EL;HD;TL;PRE]);;

let EL_SEG = prove_thm(`EL_SEG`,
    "!n (l:* list). n < (LENGTH l) ==> (EL n l = HD (SEG 1 n l))",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;EL;HD;TL;NOT_LESS_0;LESS_MONO_EQ]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REWRITE_TAC[SEG;HD]
    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REFL_TAC);;

let EL_IS_EL = prove_thm(`EL_IS_EL`,
    "!n (l:* list). n < (LENGTH l) ==> (IS_EL (EL n l) l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;EL;HD;TL;NOT_LESS_0;LESS_MONO_EQ;IS_EL]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC);;

let TL_SNOC = prove_thm(`TL_SNOC`,
    "!(x:*) l. TL(SNOC x l) = ((NULL l) => [] | SNOC x (TL l))",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC;TL;NULL]);;

let SUB_SUC_LESS = PROVE(
    "!m n. (n < m) ==> (m - (SUC n)) < m",
    INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0;SUB_MONO_EQ]
    THEN INDUCT_TAC THENL[
    	REWRITE_TAC[SUB_0;LESS_SUC_REFL];
    	REWRITE_TAC[LESS_MONO_EQ] THEN DISCH_TAC THEN RES_TAC
    	THEN IMP_RES_TAC LESS_SUC]);;

let EL_REVERSE = prove_thm(`EL_REVERSE`,
    "!n (l:* list). n < (LENGTH l) ==>
     (EL n (REVERSE l) = EL (PRE(LENGTH l - n)) l)",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC;
    	EL;HD;TL;NOT_LESS_0;LESS_MONO_EQ;SUB_0] THENL[
    	REWRITE_TAC[REVERSE_SNOC;PRE;EL_LENGTH_SNOC;HD];
    	REWRITE_TAC[REVERSE_SNOC;SUB_MONO_EQ;TL]
    	THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    	THEN MATCH_MP_TAC (GSYM EL_SNOC)
    	THEN REWRITE_TAC(PRE_SUB1 . (map GSYM [SUB_PLUS;ADD1]))
    	THEN IMP_RES_TAC SUB_SUC_LESS]);;

let EL_REVERSE_ELL = prove_thm(`EL_REVERSE_ELL`,
    "!n (l:* list). n < (LENGTH l) ==> (EL n (REVERSE l) = ELL n l)",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC;REVERSE_SNOC;
    	EL;ELL;HD;TL;LAST;BUTLAST;NOT_LESS_0;LESS_MONO_EQ;SUB_0]);;

let ELL_LENGTH_APPEND = prove_thm(`ELL_LENGTH_APPEND`,
    "!(l1:(*)list) (l2:(*)list).
      ~(NULL l1)==> (ELL (LENGTH l2) (APPEND l1 l2) = LAST l1)",
    GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC
    	[LENGTH;LENGTH_SNOC;APPEND_SNOC;APPEND_NIL;ELL;TL;BUTLAST]);;

let ELL_IS_EL = prove_thm(`ELL_IS_EL`,
    "!n (l:* list). n < (LENGTH l) ==> (IS_EL (EL n l) l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;EL;HD;TL;NOT_LESS_0;LESS_MONO_EQ;IS_EL]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC);;

let ELL_REVERSE = prove_thm(`ELL_REVERSE`,
    "!n (l:* list). n < (LENGTH l) ==>
     (ELL n (REVERSE l) = ELL (PRE(LENGTH l - n)) l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC;REVERSE;SUB_0;ELL;LAST;
    	BUTLAST;NOT_LESS_0;LESS_MONO_EQ;PRE;ELL_LENGTH_CONS;SUB_MONO_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    THEN MATCH_MP_TAC (GSYM ELL_CONS)
    THEN REWRITE_TAC(PRE_SUB1 . (map GSYM [SUB_PLUS;ADD1]))
    THEN IMP_RES_TAC SUB_SUC_LESS);;

let ELL_REVERSE_EL = prove_thm(`ELL_REVERSE_EL`,
    "!n (l:* list). n < (LENGTH l) ==> (ELL n (REVERSE l) = EL n l)",
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC;REVERSE;REVERSE_SNOC;
    	EL;ELL;HD;TL;LAST;BUTLAST;NOT_LESS_0;LESS_MONO_EQ;SUB_0]);;

%-------------------------- 30 JAN -------------------------------%
let LESS_EQ_SPLIT = 
    let asm_thm = ASSUME "(m + n) <= p" in
    GEN_ALL(DISCH_ALL
     (CONJ(MP(SPECL ["n:num";"m+n";"p:num"] LESS_EQ_TRANS)
       	      (CONJ (SUBS [SPECL ["n:num";"m:num"] ADD_SYM]
                     (SPECL ["n:num";"m:num"] LESS_EQ_ADD)) asm_thm))
	  (MP (SPECL ["m:num";"m+n";"p:num"] LESS_EQ_TRANS)
               (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))));;

let SUB_GREATER_EQ_ADD = PROVE(
    "!p n m. (p >= n) ==> (((p - n) >= m) = (p >= (m + n)))",
    REWRITE_TAC[
      SYM (SPEC "n:num" (SPEC "p-n" (SPEC "m:num" 
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (\th .ASSUME_TAC
      (MP (SPEC "n:num" (SPEC "p:num" SUB_ADD)) 
          (REWRITE_RULE[SPEC "n:num" (SPEC "p:num" GREATER_EQ)] th)))
    THEN SUBST_TAC[(SPEC_ALL ADD_SYM)] THEN ASM_REWRITE_TAC[]);;

% SUB_LESS_EQ_ADD = |- !p n m. n <= p ==> (m <= (p - n) = (m + n) <= p) %
let SUB_LESS_EQ_ADD = (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);;

let FIRSTN_BUTLASTN = prove_thm(`FIRSTN_BUTLASTN`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (FIRSTN n l = BUTLASTN ((LENGTH l) - n) l)",
    INDUCT_TAC THEN REWRITE_TAC[FIRSTN;BUTLASTN_LENGTH_NIL;SUB_0]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;FIRSTN;LENGTH;
    	SUB_0;BUTLASTN;LESS_EQ_MONO;SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BUTLASTN_CONS
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);;

let BUTLASTN_FIRSTN = prove_thm(`BUTLASTN_FIRSTN`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (BUTLASTN n l = FIRSTN ((LENGTH l) - n) l)",
    INDUCT_TAC THEN REWRITE_TAC[FIRSTN;BUTLASTN_LENGTH_NIL;SUB_0]
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;LENGTH;LENGTH_SNOC;
    	SUB_0;BUTLASTN;FIRSTN;FIRSTN_LENGTH_ID;LESS_EQ_MONO;SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIRSTN_SNOC
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);;

let LASTN_BUTFIRSTN = prove_thm(`LASTN_BUTFIRSTN`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (LASTN n l = BUTFIRSTN ((LENGTH l) - n) l)",
    INDUCT_TAC THEN REWRITE_TAC[LASTN;BUTFIRSTN_LENGTH_NIL;SUB_0]
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;LASTN;LENGTH;
    	LENGTH_SNOC;SUB_0;LESS_EQ_MONO;SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BUTFIRSTN_SNOC
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);;

let BUTFIRSTN_LASTN = prove_thm(`BUTFIRSTN_LASTN`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (BUTFIRSTN n l = LASTN ((LENGTH l) - n) l)",
    INDUCT_TAC THEN REWRITE_TAC[LASTN_LENGTH_ID;BUTFIRSTN;SUB_0]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0;LASTN;LENGTH;
    	BUTFIRSTN;SUB_0;LESS_EQ_MONO;SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LASTN_CONS
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);;

let SUB_ADD_lem = PROVE(
    "!l n m. (n + m) <= l ==> ((l - (n + m)) + n = l - m)",
    REPEAT INDUCT_TAC 
    THEN REWRITE_TAC[ADD;ADD_0;SUB_0;NOT_SUC_LESS_EQ_0] THENL[
        MATCH_ACCEPT_TAC SUB_ADD;
    	PURE_ONCE_REWRITE_TAC [GSYM(CONJUNCT2 ADD)] 
    	THEN SUBST1_TAC (SYM (SPECL["SUC n";"m:num"]ADD_SUC))
    	THEN REWRITE_TAC[SUB_MONO_EQ;LESS_EQ_MONO]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let SEG_LASTN_BUTLASTN = prove_thm(`SEG_LASTN_BUTLASTN`,
    "!n m (l:* list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m l = LASTN n (BUTLASTN ((LENGTH l) - (n + m)) l))",
    let th2 = SUBS [(REWRITE_RULE[SUB_LESS_EQ]
        (SPECL["(LENGTH (l:* list)) - m"; "l:* list"]LENGTH_LASTN))]
    	(SPECL["n:num";"LASTN((LENGTH l) - m)(l:* list)"]FIRSTN_BUTLASTN) in
    let th3 = UNDISCH_ALL (SUBS[UNDISCH_ALL
        (SPECL["LENGTH(l:* list)";"m:num";"n:num"]SUB_LESS_EQ_ADD)] th2) in
    let th4 = PURE_ONCE_REWRITE_RULE[ADD_SYM](REWRITE_RULE[
    	UNDISCH_ALL(SPECL["LENGTH(l:* list)";"n:num";"m:num"]SUB_ADD_lem);
    	SUB_LESS_EQ] 
    	(PURE_ONCE_REWRITE_RULE[ADD_SYM](SPECL
    	["n:num";"(LENGTH (l:* list)) - (n + m)";"l:* list"]LASTN_BUTLASTN)))in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN IMP_RES_THEN SUBST1_TAC SEG_FIRSTN_BUTFIRSTN
    THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN SUBST1_TAC (UNDISCH_ALL(SPECL["m:num";"l:* list"] BUTFIRSTN_LASTN))
    THEN SUBST1_TAC th3 THEN REWRITE_TAC[GSYM SUB_PLUS]
    THEN SUBST_OCCS_TAC[[1],(SPEC_ALL ADD_SYM)]
    THEN CONV_TAC SYM_CONV THEN ACCEPT_TAC th4);;

let BUTFIRSTN_REVERSE = prove_thm(`BUTFIRSTN_REVERSE`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (BUTFIRSTN n (REVERSE l) = REVERSE(BUTLASTN n l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0; 
    	LENGTH;LENGTH_SNOC;BUTFIRSTN;BUTLASTN;LESS_EQ_MONO;REVERSE_SNOC]);;

let BUTLASTN_REVERSE = prove_thm(`BUTLASTN_REVERSE`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (BUTLASTN n (REVERSE l) = REVERSE(BUTFIRSTN n l))",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0; 
    	LENGTH;BUTFIRSTN;BUTLASTN;LESS_EQ_MONO;REVERSE]);;
    
let LASTN_REVERSE = prove_thm(`LASTN_REVERSE`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (LASTN n (REVERSE l) = REVERSE(FIRSTN n l))",
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0; 
    	LENGTH;FIRSTN;LASTN;LESS_EQ_MONO;REVERSE;SNOC_11]);;

let FIRSTN_REVERSE = prove_thm(`FIRSTN_REVERSE`,
    "!n (l:* list). n <= (LENGTH l) ==>
     (FIRSTN n (REVERSE l) = REVERSE(LASTN n l))",
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0;LENGTH;LENGTH_SNOC;
    	FIRSTN;LASTN;LESS_EQ_MONO;REVERSE;REVERSE_SNOC;CONS_11]);;

let SEG_REVERSE = prove_thm(`SEG_REVERSE`,
    "!n m (l:* list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m (REVERSE l) =  REVERSE(SEG n (LENGTH l - (n + m)) l))",
    let LEN_REV = (SPEC"l:* list" LENGTH_REVERSE) in
    let SUB_LE_ADD = 
    	SPECL["LENGTH(l:* list)";"m:num";"n:num"]SUB_LESS_EQ_ADD in
    let SEG_lem = REWRITE_RULE[SUB_LESS_EQ](PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	(SUBS[UNDISCH_ALL(SPEC_ALL(SPEC"LENGTH(l:* list)" SUB_ADD_lem))]
    	 (PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	  (SPECL["n:num";"LENGTH(l:* list) -(n+m)";"l:* list"]
    	    SEG_LASTN_BUTLASTN)))) in
    let lem = PURE_ONCE_REWRITE_RULE[ADD_SUB](PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	(SPEC "LENGTH(l:* list)"
    	 (UNDISCH_ALL(SPECL["LENGTH(l:* list)";"m:num"]SUB_SUB))))    in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP  SEG_FIRSTN_BUTFIRSTN)
    	o (SUBS[SYM LEN_REV]))
    THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN IMP_RES_THEN SUBST1_TAC (SPECL["m:num";"l:* list"]BUTFIRSTN_REVERSE)
    THEN FIRST_ASSUM 
    	(ASSUME_TAC o (MP(SPECL["m:num";"(l:* list)"]LENGTH_BUTLASTN)))
    THEN FIRST_ASSUM (\t. ASSUME_TAC (SUBS[t]
    	(SPECL["n:num";"BUTLASTN m (l:* list)"]FIRSTN_REVERSE)))
    THEN FIRST_ASSUM (SUBST_ALL_TAC o (MP SUB_LE_ADD))
    THEN RES_THEN SUBST1_TAC THEN AP_TERM_TAC
    THEN SUBST1_TAC SEG_lem THEN SUBST1_TAC lem THEN REFL_TAC);;

%<---------------------------------------------------------------->%
let LENGTH_GENLIST = prove_thm(`LENGTH_GENLIST`,
    "!(f:num->*) n. LENGTH(GENLIST f n) = n",
    GEN_TAC THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[GENLIST;LENGTH;LENGTH_SNOC]);;

let LENGTH_REPLICATE = prove_thm(`LENGTH_REPLICATE`,
    "!n (x:*). LENGTH(REPLICATE n x) = n",
    INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE;LENGTH]);;

let IS_EL_REPLICATE = prove_thm(`IS_EL_REPLICATE`,
    "!n. 0 < n ==> !x:*. IS_EL x (REPLICATE n x)",
    INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0;IS_EL;REPLICATE]);;

let ALL_EL_REPLICATE = prove_thm(`ALL_EL_REPLICATE`,
    "!(x:*) n. ALL_EL ($= x) (REPLICATE n x)",
    GEN_TAC THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS_0;ALL_EL;REPLICATE]);;


let AND_EL_FOLDL = save_thm(`AND_EL_FOLDL`,
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[ALL_EL_FOLDL;I_THM](AP_THM AND_EL_DEF "l:bool list"))));;

let AND_EL_FOLDR = save_thm(`AND_EL_FOLDR`,
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[ALL_EL_FOLDR;I_THM](AP_THM AND_EL_DEF "l:bool list"))));;

let OR_EL_FOLDL = save_thm(`OR_EL_FOLDL`,
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[SOME_EL_FOLDL;I_THM](AP_THM OR_EL_DEF "l:bool list"))));;

let OR_EL_FOLDR = save_thm(`OR_EL_FOLDR`,
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[SOME_EL_FOLDR;I_THM](AP_THM OR_EL_DEF "l:bool list"))));;

let MAP2_ZIP = prove_thm(`MAP2_ZIP`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !f:*->**->***. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))",
    let UNCURRY_DEF = definition `bool` `UNCURRY_DEF` in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC "l2:** list")
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP;MAP2;ZIP;LENGTH;NOT_SUC;SUC_NOT]
    THEN ASM_REWRITE_TAC[CONS_11;UNCURRY_DEF;INV_SUC_EQ]);;

    
%---------------------------------------------------------------------- %
% End of mk_list_thm2.ml    	    					%
%---------------------------------------------------------------------- %
