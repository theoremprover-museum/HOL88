% ===================================================================== %
% LIBRARY: finite_sets (prior to version 1.12 called "sets")		%
% FILE:    mk_sets.ml							%
%									%
% DESCRIPTION: Defines a new type for finite sets and proves properties %
% of sets.  The theory is a formalization of the theory of sets 	%
% presented in chapter 10 of Manna and Waldingers "The Logical Basis of %
% Computer Programming, VOL 1."						%
%									% 
% AUTHORS: Phil Windley, Philippe Leveilley				%
% DATE:    12 May, 1989							%
%									%
% REVISED: Tom Melham (extensively revised and extended)		%
% DATE:    February 1992						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory.						%
% --------------------------------------------------------------------- %
new_theory `finite_sets`;;

% ===================================================================== %
% Type definition.							%
%									%
% The representing type is *->bool.  The representation of the empty 	%
% set is the abstraction \x.F. The insertion operation is represented 	%
% by \x s. (\e. e = x \/ s e), which gives the representation of the 	%
% set obtained by adding the element x to the set s.			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% A predicate s:*->bool represents a finite set iff it is in the 	%
% intersection of all classes of such predicates that contain the 	%
% representation of empty and are closed under the representation of 	%
% insert operation.  Hence s:*->bool is finite if it can be obtained 	%
% by applying a finite sequence of insert operations to the empty set.	%
% The following proofs derive the existence of a predicate IS_SET_REP   %
% that expresses this definition.					%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Abbreviation for IS_SET_REP.						%
% --------------------------------------------------------------------- %

let IS_SET_REP =
    "\s:*->bool.
     !P. P (\x.F) /\ (!t. P t ==> !x. P(\y. (y=x) \/ t y)) ==> P s";;

% --------------------------------------------------------------------- %
% The predicate \x.F represents the empty set (IS_SET_REP holds of it). %
% --------------------------------------------------------------------- %

let IS_SET_REP_EMPTY =
    TAC_PROOF
    (([], "^IS_SET_REP (\x:*.F)"),
     CONV_TAC BETA_CONV THEN REPEAT STRIP_TAC);;


% --------------------------------------------------------------------- %
% Set representations are closed under the insertion function.		%
% --------------------------------------------------------------------- %

let INSERTION_PRESERVES_IS_SET_REP =
    TAC_PROOF
    (([], "!s:*->bool. ^IS_SET_REP s ==> !x. ^IS_SET_REP (\y.(y=x) \/ s y)"),
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     RES_THEN MATCH_ACCEPT_TAC);;

% --------------------------------------------------------------------- %    
% IS_SET_REP is true of the smallest such class of sets.		%
% --------------------------------------------------------------------- %

let REP_INDUCT =
    TAC_PROOF
    (([], "!P. (P(\x:*.F) /\ (!t. P t ==> (!x. P(\y. (y = x) \/ t y)))) ==>
               !s:*->bool. ^IS_SET_REP s ==> P s"),
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN RES_TAC);;

% --------------------------------------------------------------------- %
% IS_SET_REP is precisely the predicate with these three properties.    %
% --------------------------------------------------------------------- %

let IS_SET_REP_EXISTS =
    TAC_PROOF
    (([], "?IS_SET_REP:(*->bool)->bool.
            (IS_SET_REP \x.F) /\
            (!s. IS_SET_REP s ==> !x. IS_SET_REP (\y.(y=x) \/ s y)) /\
            (!P. (P(\x:*.F) /\ (!t. P t ==> (!x. P(\y. (y = x) \/ t y)))) ==>
                 !s:*->bool. IS_SET_REP s ==> P s)"),
     EXISTS_TAC IS_SET_REP THEN
     REPEAT CONJ_TAC THENL
     [ACCEPT_TAC IS_SET_REP_EMPTY;
      ACCEPT_TAC INSERTION_PRESERVES_IS_SET_REP;
      ACCEPT_TAC REP_INDUCT]);;

% --------------------------------------------------------------------- %
% Define IS_SET_REP to be this predicate.				%
% --------------------------------------------------------------------- %

let IS_SET_REP =
    new_specification `IS_SET_REP`
       [`constant`,`IS_SET_REP`] IS_SET_REP_EXISTS;;
   
% --------------------------------------------------------------------- %
% A slightly stronger induction theorem.				%
% --------------------------------------------------------------------- %

let STRONG_SET_REP_INDUCT =
    TAC_PROOF
    (([], "!P:(*->bool)->bool.
             (P(\x:*. F) /\
             (!t. IS_SET_REP t ==> P t ==> (!x. P(\y. (y = x) \/ t y)))) ==>
               (!s. IS_SET_REP s ==> P s)"),
     let [th1;th2;th3] = CONJUNCTS IS_SET_REP in
     GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
     let th4 = BETA_RULE (SPEC "\s:*->bool. IS_SET_REP s /\ P s" th3) in
     let th5 = CONJUNCT2 (UNDISCH (SPEC "s:*->bool" (UNDISCH th4))) in
     let th6 = DISCH "IS_SET_REP (s:*->bool)" th5 in
     MATCH_MP_TAC (DISCH_ALL th6) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [th1];
      REPEAT STRIP_TAC THENL
      [IMP_RES_TAC th2; RES_TAC] THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

% --------------------------------------------------------------------- %
% Theorem stating that the representing type is non empty.		%
% --------------------------------------------------------------------- %

let EXISTENCE_THM =
    TAC_PROOF
    (([], "?(s:*->bool) . IS_SET_REP s"),
     EXISTS_TAC "\x:*.F" THEN
     REWRITE_TAC [IS_SET_REP]);;

% --------------------------------------------------------------------- %
% Now, make the type definition.					%
% --------------------------------------------------------------------- %

let set_TY_DEF = 
    new_type_definition
    (`set`,"IS_SET_REP:(*->bool)->bool", EXISTENCE_THM);;

% ========================================================================== %
% Abstract characterization of the type (*)set.  This consists of three      %
% constants EMPTY, IN, and INSERT which satisfy:			     %
%									     %
%  NOT_IN_EMPTY    |- !x. ~(IN x EMPTY))                                     %
%  IN_INSERT       |- !x y s. IN x (INSERT y s) = ((x=y) \/ IN x s)          %
%  INSERT_INSERT   |- !x s. INSERT x (INSERT x s) = INSERT x s		     %
%  INSERT_COMM     |- !x y s. INSERT x (INSERT y s) = INSERT y (INSERT x s)  %
%  SET_INDUCT      |- !P:(*)set->bool.					     %
%                       (P EMPTY /\ !s. P s ==> !e. P(INSERT e s))	     %
%                       ==> !s. P s					     %
% ========================================================================== %

let EXISTENCE_LEMMA =
    TAC_PROOF
    (([], "?EMPTY:(*)set.
           ?INSERT:*->(*)set->(*)set.
           ?IN:*->(*)set->bool.
             (!x. ~(IN x EMPTY)) /\
             (!x y s. IN x (INSERT y s) = ((x=y) \/ IN x s)) /\ 
             (!x s. INSERT x (INSERT x s) = INSERT x s) /\
             (!x y s. INSERT x (INSERT y s) = INSERT y (INSERT x s)) /\
             (!P:(*)set->bool.
              (P EMPTY /\ !s. P s ==> !e. P(INSERT e s)) ==> !s. P s)"),
     let thm = MATCH_MP ABS_REP_THM set_TY_DEF in
     STRIP_ASSUME_TAC thm THEN
     EXISTS_TAC "abs (\x:*.F) :(*)set" THEN
     EXISTS_TAC "\x:*. \s:(*)set. abs (\y. (y=x) \/ (rep s y)):(*)set" THEN
     EXISTS_TAC "\x:*. \s:(*)set. (rep s:*->bool) x" THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     let [th1;th2;th3] = CONJUNCTS IS_SET_REP in
     REPEAT (CONJ_TAC ORELSE GEN_TAC) THENL
     [ASSUME_TAC th1 THEN RES_THEN SUBST1_TAC THEN
      CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC;
      let th4 = SYM(BETA_CONV "(\y':*. (y' = y) \/ rep (s:(*)set) y') x") in
      SUBST1_TAC th4 THEN AP_THM_TAC THEN
      FIRST_ASSUM (\th. REWRITE_TAC [SYM (SPEC "r:*->bool" th)]) THEN
      MATCH_MP_TAC th2 THEN ASM_REWRITE_TAC [];
      FIRST_ASSUM (\th.
       let th4 = SPEC "rep (s:(*)set):*->bool" th in
       let as1 = ASSUME "!a:(*)set.abs(rep a:*->bool) = a" in
       let th5 = SPEC "x:*" (MATCH_MP th2 (REWRITE_RULE [as1] th4)) in
       ASSUME_TAC th5 THEN RES_THEN SUBST1_TAC THEN
       CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC [DISJ_ASSOC]);
      FIRST_ASSUM (\th.
       let th4 = SPEC "rep (s:(*)set):*->bool" th in
       let as1 = ASSUME "!a:(*)set.abs(rep a:*->bool) = a" in
       let th5 = MATCH_MP th2 (REWRITE_RULE [as1] th4) in
       ASSUME_TAC (SPEC "x:*" th5) THEN ASSUME_TAC (SPEC "y:*" th5) THEN
       RES_THEN SUBST1_TAC THEN
       CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
       PURE_ONCE_REWRITE_TAC [DISJ_ASSOC] THEN
       let disj = ISPEC "x:* = y" DISJ_SYM in
       CONV_TAC (RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV disj))) THEN
       REFL_TAC);
      REPEAT STRIP_TAC THEN
      let th4 = STRONG_SET_REP_INDUCT in
      let th5 = BETA_RULE (SPEC "\r:*->bool. P(abs r:(*)set):bool" th4) in
      let th6 = SPEC "rep (s:(*)set):*->bool" (UNDISCH th5) in
      MP_TAC (DISCH_ALL th6) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC []]);;

% --------------------------------------------------------------------- %
% Now, define EMPTY, IN and INSERT.					%
% --------------------------------------------------------------------- %

let FINITE_SET_DEF = 
    new_specification `FINITE_SET_DEF`
    [`constant`,`EMPTY`;`infix`,`INSERT`;`infix`,`IN`]
    EXISTENCE_LEMMA;;    
    
% --------------------------------------------------------------------- %
% Set up the {x1,...,xn} notation.					%
% --------------------------------------------------------------------- %
define_finite_set_syntax(`EMPTY`,`INSERT`);;

% --------------------------------------------------------------------- %
% Save the first four conjuncts of FINITE_SET_DEF under separate names. %
% --------------------------------------------------------------------- %

let [NOT_IN_EMPTY;IN_INSERT;INSERT_INSERT;INSERT_COMM;_] =
    CONJUNCTS FINITE_SET_DEF;;

save_thm(`NOT_IN_EMPTY`,NOT_IN_EMPTY);;
save_thm(`IN_INSERT`,IN_INSERT);;
save_thm(`INSERT_INSERT`,INSERT_INSERT);;
save_thm(`INSERT_COMM`,INSERT_COMM);;

% ===================================================================== %
% Basic theorems needed to prove EXTENSION.				%
% ===================================================================== %

let COMPONENT =
    prove_thm
    (`COMPONENT`,
     "!x:*.!s. x IN (x INSERT s)",
     REWRITE_TAC [IN_INSERT]);;

let NOT_EMPTY_INSERT =
    prove_thm
    (`NOT_EMPTY_INSERT`,
     "!x:*. !s. ~({} = x INSERT s)",
     REPEAT GEN_TAC THEN
     DISCH_THEN (MP_TAC o (AP_TERM "IN (x:*)")) THEN
     REWRITE_TAC [IN_INSERT;NOT_IN_EMPTY]);;

let NOT_INSERT_EMPTY =
    save_thm
    (`NOT_INSERT_EMPTY`,
     CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) NOT_EMPTY_INSERT);;

let lemma =
    TAC_PROOF
    (([], "!x:*. !s. x IN s ==> (x INSERT s = s)"),
     let ind = el 5 (CONJUNCTS FINITE_SET_DEF) in
     GEN_TAC THEN INDUCT_THEN ind ASSUME_TAC THENL
     [REWRITE_TAC [NOT_IN_EMPTY];
      PURE_ONCE_REWRITE_TAC [IN_INSERT] THEN
      REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [INSERT_INSERT];
       PURE_ONCE_REWRITE_TAC [INSERT_COMM] THEN
       RES_THEN SUBST1_TAC THEN REFL_TAC]]);;

let ABSORPTION =
    prove_thm
    (`ABSORPTION`,
     "!x:*. !s. x IN s = (x INSERT s = s)",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [MATCH_ACCEPT_TAC lemma;
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      MATCH_ACCEPT_TAC COMPONENT]);;

% ===================================================================== %
% Finite set induction: strong form.					%
% ===================================================================== %

let SET_INDUCT = 
    prove_thm
    (`SET_INDUCT`,
     "!P:(*)set->bool.
      (P EMPTY /\ !s. P s ==> !e. ~(e IN s) ==> P(INSERT e s)) ==> !s. P s",
     let ind = el 5 (CONJUNCTS FINITE_SET_DEF) in
     REPEAT STRIP_TAC THEN MATCH_MP_TAC ind THEN
     REPEAT STRIP_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_CASES_TAC "(e:*) IN s" THENL
      [IMP_RES_THEN SUBST1_TAC ABSORPTION THEN
       FIRST_ASSUM ACCEPT_TAC;
       RES_TAC]]);;

% --------------------------------------------------------------------- %
% Load the set induction tactic in... uncompiled.			%
% --------------------------------------------------------------------- %

loadt `set_ind.ml`;;

% ===================================================================== %
% Axiom of extension.							%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, prove DECOMPOSITION.						%
% --------------------------------------------------------------------- %

let DECOMPOSITION =
    prove_thm
    (`DECOMPOSITION`,
     "!s:(*)set. !x. x IN s = ?t. (s = x INSERT t) /\ ~x IN t",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [MAP_EVERY (SPEC_TAC o (\x.(x,x))) ["x:*";"s:(*)set"] THEN
      SET_INDUCT_TAC THENL
      [REWRITE_TAC [NOT_IN_EMPTY];
       PURE_ONCE_REWRITE_TAC [IN_INSERT] THEN
       REPEAT STRIP_TAC THENL
       [EXISTS_TAC "s:(*)set" THEN ASM_REWRITE_TAC [];
        RES_TAC THEN EXISTS_TAC "(e:*) INSERT t" THEN
        FIRST_ASSUM SUBST1_TAC THEN CONJ_TAC THENL
        [MATCH_ACCEPT_TAC INSERT_COMM;
         ASM_REWRITE_TAC [IN_INSERT] THEN
         DISCH_THEN SUBST_ALL_TAC THEN RES_TAC]]];
      STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT]]);;


% --------------------------------------------------------------------- %
% And prove MEMBER_NOT_EMPTY						%
% --------------------------------------------------------------------- %

let MEMBER_NOT_EMPTY = 
    prove_thm
    (`MEMBER_NOT_EMPTY`,
     "!s:(*)set. (?x. x IN s) = ~(s = {})",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [NOT_IN_EMPTY];
      REWRITE_TAC [NOT_INSERT_EMPTY;IN_INSERT] THEN
      EXISTS_TAC "e:*" THEN REWRITE_TAC []]);;

% --------------------------------------------------------------------- %
% Now, the axiom of EXTENSION.						%
% --------------------------------------------------------------------- %

let lemma =
    TAC_PROOF
    (([], "!s t. (!x:*. x IN s = x IN t) ==> (s = t)"),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [NOT_IN_EMPTY] THEN
      CONV_TAC (ONCE_DEPTH_CONV FORALL_NOT_CONV) THEN
      REWRITE_TAC [MEMBER_NOT_EMPTY] THEN
      GEN_TAC THEN DISCH_THEN (ACCEPT_TAC o SYM);
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (SPECL ["e:*";"s:(*)set"] COMPONENT) THEN
      RES_TAC THEN IMP_RES_TAC DECOMPOSITION THEN
      SUBST_ALL_TAC (ASSUME "t = (e:*) INSERT t'") THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      GEN_TAC THEN
      FIRST_ASSUM (\th.
       let eqn = REWRITE_RULE [IN_INSERT] (SPEC "x:*" th) in
       ASSUME_TAC (GEN_ALL eqn)) THEN
      EQ_TAC THEN STRIP_TAC THEN RES_TAC THEN
      SUBST_ALL_TAC (ASSUME "x:* = e") THEN RES_TAC]);;

let EXTENSION =
    prove_thm
    (`EXTENSION`,
     "!s t. (s=t) = (!x:*. x IN s = x IN t)",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC;
      MATCH_ACCEPT_TAC lemma]);;

let NOT_EQUAL_SETS = 
    prove_thm
    (`NOT_EQUAL_SETS`,
     "!s:(*)set. !t. ~(s = t) = ?x. x IN t = ~x IN s",
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN
      ASM_CASES_TAC "(x:*) IN s" THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC "x:*" THEN 
      ASM_CASES_TAC "(x:*) IN s" THEN ASM_REWRITE_TAC []]);;


% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %

let NUM_SET_WOP =
    prove_thm
    (`NUM_SET_WOP`,
     "!s. (?n. n IN s) = ?n. n IN s /\ (!m. m IN s ==> n <= m)",
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [let th = BETA_RULE (ISPEC "\n:num. n IN s" WOP) in
      IMP_RES_THEN (X_CHOOSE_THEN "N:num" STRIP_ASSUME_TAC) th THEN
      EXISTS_TAC "N:num" THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
       ASM_REWRITE_TAC [GSYM NOT_LESS]];
      EXISTS_TAC "n:num" THEN FIRST_ASSUM ACCEPT_TAC]);;


% --------------------------------------------------------------------- %
% Cases theorem for EMPTY and INSERT.					%
% --------------------------------------------------------------------- %

let SET_CASES = 
    prove_thm
    (`SET_CASES`,
     "!s:(*)set. (s = {}) \/ ?x:*. ?t. ((s = x INSERT t) /\ ~x IN t)",
     SET_INDUCT_TAC THENL
     [DISJ1_TAC THEN REFL_TAC;
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC ["e:*";"s:(*)set"] THEN
      ASM_REWRITE_TAC []]);;

% ===================================================================== %
% Set inclusion.							%
% ===================================================================== %

let SUBSET_DEF = new_infix_definition
    (`SUBSET_DEF`, "SUBSET s t =  !x:*. x IN s ==> x IN t");;

let SUBSET_TRANS = prove_thm
    (`SUBSET_TRANS`,
     "!(s:(*)set) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u",
     REWRITE_TAC [SUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN
     REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);;

let SUBSET_REFL = prove_thm
    (`SUBSET_REFL`,
     "!(s:(*)set). s SUBSET s",
     REWRITE_TAC[SUBSET_DEF]);;

let SUBSET_ANTISYM = prove_thm
    (`SUBSET_ANTISYM`,
     "!(s:(*)set) t. (s SUBSET t) /\ (t SUBSET s) ==> (s = t)",
     REWRITE_TAC [SUBSET_DEF; EXTENSION] THEN
     REPEAT STRIP_TAC THEN
     EQ_TAC THEN 
     FIRST_ASSUM MATCH_ACCEPT_TAC);;

let EMPTY_SUBSET = 
    prove_thm
    (`EMPTY_SUBSET`,
     "!s:(*)set. EMPTY SUBSET s",
     REWRITE_TAC [SUBSET_DEF;NOT_IN_EMPTY]);;

let SUBSET_EMPTY = 
    prove_thm
    (`SUBSET_EMPTY`,
     "!s:(*)set. s SUBSET EMPTY = (s = EMPTY)",
     PURE_REWRITE_TAC [SUBSET_DEF;NOT_IN_EMPTY] THEN
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY]);;

let INSERT_SUBSET = 
    prove_thm
    (`INSERT_SUBSET`,
     "!x:*. !s t. (x INSERT s) SUBSET t = (x IN t /\ s SUBSET t)",
     REWRITE_TAC [IN_INSERT;SUBSET_DEF] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL 
     [FIRST_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN REFL_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC [];
      RES_TAC]);;

let SUBSET_INSERT = 
    prove_thm
    (`SUBSET_INSERT`,
     "!x:*. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) = s SUBSET t",
     PURE_REWRITE_TAC [SUBSET_DEF;IN_INSERT] THEN
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN
      let tac th g = SUBST_ALL_TAC th g ? STRIP_ASSUME_TAC th g in
      RES_THEN (STRIP_THM_THEN tac) THEN RES_TAC;
      REPEAT STRIP_TAC THEN DISJ2_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC]);;

% ===================================================================== %
% Proper subset.							%
% ===================================================================== %

let PSUBSET_DEF = 
    new_infix_definition
    (`PSUBSET_DEF`, "PSUBSET (s:(*)set) t = (s SUBSET t /\ ~(s = t))");;

let PSUBSET_TRANS =
    prove_thm
    (`PSUBSET_TRANS`,
     "!s:(*)set. !t u. (s PSUBSET t /\ t PSUBSET u) ==> (s PSUBSET u)",
     PURE_ONCE_REWRITE_TAC [PSUBSET_DEF] THEN
     REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [IMP_RES_TAC SUBSET_TRANS;
      DISCH_THEN SUBST_ALL_TAC THEN 
      IMP_RES_TAC SUBSET_ANTISYM THEN
      RES_TAC]);;

let PSUBSET_IRREFL = 
    prove_thm
    (`PSUBSET_IRREFL`,
     "!s:(*)set. ~(s PSUBSET s)",
     REWRITE_TAC [PSUBSET_DEF;SUBSET_REFL]);;

let NOT_PSUBSET_EMPTY = 
    prove_thm
    (`NOT_PSUBSET_EMPTY`,
     "!s:(*)set. ~(s PSUBSET EMPTY)",
     REWRITE_TAC [PSUBSET_DEF;SUBSET_EMPTY;NOT_AND]);;

let PSUBSET_INSERT_SUBSET = 
    prove_thm
    (`PSUBSET_INSERT_SUBSET`,
     "!s t. s PSUBSET t = ?x:*. ~(x IN s) /\ (x INSERT s) SUBSET t",
     PURE_REWRITE_TAC [PSUBSET_DEF;NOT_EQUAL_SETS] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [ASM_CASES_TAC "(x:*) IN s" THENL
      [ASM_CASES_TAC "(x:*) IN t" THENL
       [RES_TAC; IMP_RES_TAC SUBSET_DEF THEN RES_TAC];
       EXISTS_TAC "x:*" THEN RES_TAC THEN
       ASM_REWRITE_TAC [INSERT_SUBSET]];
      IMP_RES_TAC INSERT_SUBSET;
      IMP_RES_TAC INSERT_SUBSET THEN
      EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[]]);;


let lemma = 
    TAC_PROOF(([], "~(a:bool = b) = (b = ~a)"),
    BOOL_CASES_TAC "b:bool" THEN REWRITE_TAC[]);;    

let PSUBSET_MEMBER = 
    prove_thm
    (`PSUBSET_MEMBER`,
     "!s:(*)set. !t. s PSUBSET t = (s SUBSET t /\ ?y. y IN t /\ ~y IN s)",
     REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC [PSUBSET_DEF] THEN
     PURE_ONCE_REWRITE_TAC [EXTENSION;SUBSET_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     PURE_ONCE_REWRITE_TAC [lemma] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [RES_TAC;
      EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC "(x:*) IN s" THENL
       [RES_TAC THEN RES_TAC;FIRST_ASSUM ACCEPT_TAC];
      RES_TAC;
      EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[]]);;

% ===================================================================== %
% Union.								%
% ===================================================================== %

let UNION_EXISTS =
    TAC_PROOF
    (([], "!s t. ?u. !x:*. x IN u = x IN s \/ x IN t"),
     SET_INDUCT_TAC THEN GEN_TAC THENL
     [EXISTS_TAC "t:(*)set" THEN
      REWRITE_TAC [NOT_IN_EMPTY];
      FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC "t:(*)set") THEN
      EXISTS_TAC "(e:*) INSERT u" THEN
      ASM_REWRITE_TAC [IN_INSERT;DISJ_ASSOC]]);;

let IN_UNION =
    let th1 = CONV_RULE SKOLEM_CONV UNION_EXISTS in
    new_specification `IN_UNION` [`infix`,`UNION`] th1;;

let UNION_ASSOC =
    prove_thm
    (`UNION_ASSOC`,
     "!(s:(*)set) t u. (s UNION t) UNION u = s UNION (t UNION u)",
     REWRITE_TAC [EXTENSION; IN_UNION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC[]);;

let UNION_IDEMPOT =
    prove_thm
    (`UNION_IDEMPOT`,
     "!(s:(*)set). s UNION s = s",
     REWRITE_TAC[EXTENSION; IN_UNION]);;

let UNION_COMM =
    prove_thm
    (`UNION_COMM`,
     "!(s:(*)set) t. s UNION t = t UNION s",
     REWRITE_TAC[EXTENSION; IN_UNION] THEN
     REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM);;

let SUBSET_UNION = 
    prove_thm
    (`SUBSET_UNION`,
     "(!s:(*)set. !t. s SUBSET (s UNION t)) /\ 
      (!s:(*)set. !t. s SUBSET (t UNION s))",
     PURE_REWRITE_TAC [SUBSET_DEF;IN_UNION] THEN
     REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBSET_UNION_ABSORPTION = 
    prove_thm
    (`SUBSET_UNION_ABSORPTION`,
     "!s:(*)set. !t. s SUBSET t = (s UNION t = t)",
     REWRITE_TAC [SUBSET_DEF;EXTENSION;IN_UNION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [RES_TAC;ASM_REWRITE_TAC[];RES_TAC]);;

let UNION_EMPTY = 
    prove_thm
    (`UNION_EMPTY`,
     "(!s:(*)set. EMPTY UNION s = s) /\
      (!s:(*)set. s UNION EMPTY = s)",
     REWRITE_TAC [IN_UNION;EXTENSION;NOT_IN_EMPTY]);;

let EMPTY_UNION = 
    prove_thm
    (`EMPTY_UNION`,
     "!s:(*)set. !t. (s UNION t = EMPTY) = ((s = EMPTY) /\ (t = EMPTY))",
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY;IN_UNION;DE_MORGAN_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RES_TAC);;

let INSERT_UNION = 
    prove_thm
    (`INSERT_UNION`,
     "!x:*. !s t. 
      (x INSERT s) UNION t = (x IN t => s UNION t | x INSERT (s UNION t))",
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN
     ASM_REWRITE_TAC [EXTENSION;IN_UNION;IN_INSERT] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC []);;

let INSERT_UNION_EQ = 
    prove_thm
    (`INSERT_UNION_EQ`,
     "!x:*. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)",
     REPEAT GEN_TAC THEN 
     REWRITE_TAC [EXTENSION;IN_UNION;IN_INSERT;DISJ_ASSOC]);;


% ===================================================================== %
% Intersection.								%
% ===================================================================== %

let INTER_EXISTS =
    TAC_PROOF
    (([], "!s t. ?i. !x:*. x IN i = x IN s /\ x IN t"),
     SET_INDUCT_TAC THEN GEN_TAC THENL
     [EXISTS_TAC "{}:(*)set" THEN
      REWRITE_TAC [NOT_IN_EMPTY];
      FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC "t:(*)set") THEN
      ASM_CASES_TAC "(e:*) IN t" THENL
      [EXISTS_TAC "(e:*) INSERT i" THEN GEN_TAC THEN
       ASM_CASES_TAC "x:* = e" THEN
       ASM_REWRITE_TAC [IN_INSERT];
       EXISTS_TAC "i:(*)set" THEN GEN_TAC THEN
       ASM_CASES_TAC "x:* = e" THEN
       ASM_REWRITE_TAC [IN_INSERT]]]);;

let IN_INTER =
    let th1 = CONV_RULE SKOLEM_CONV INTER_EXISTS in
    new_specification `IN_INTER` [`infix`,`INTER`] th1;;

let INTER_ASSOC = prove_thm
    (`INTER_ASSOC`,
     "!(s:(*)set) t u. (s INTER t) INTER u = s INTER (t INTER u)",
     REWRITE_TAC [EXTENSION; IN_INTER; CONJ_ASSOC]);;

let INTER_IDEMPOT = prove_thm
    (`INTER_IDEMPOT`,
     "!(s:(*)set). s INTER s = s",
     REWRITE_TAC[EXTENSION; IN_INTER]);;

let INTER_COMM = prove_thm
    (`INTER_COMM`,
     "!(s:(*)set) t. s INTER t = t INTER s",
     REWRITE_TAC[EXTENSION; IN_INTER] THEN
     REPEAT GEN_TAC THEN
     MATCH_ACCEPT_TAC CONJ_SYM);;

let INTER_SUBSET = 
    prove_thm
    (`INTER_SUBSET`,
     "(!s:(*)set. !t. (s INTER t) SUBSET s) /\ 
      (!s:(*)set. !t. (t INTER s) SUBSET s)",
     PURE_REWRITE_TAC [SUBSET_DEF;IN_INTER] THEN
     REPEAT STRIP_TAC);;

let SUBSET_INTER_ABSORPTION = 
    prove_thm
    (`SUBSET_INTER_ABSORPTION`,
     "!s:(*)set. !t. s SUBSET t = (s INTER t = s)",
     REWRITE_TAC [SUBSET_DEF;EXTENSION;IN_INTER] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM ACCEPT_TAC; RES_TAC; RES_TAC]);;

let INTER_EMPTY = 
    prove_thm
    (`INTER_EMPTY`,
     "(!s:(*)set. EMPTY INTER s = EMPTY) /\
      (!s:(*)set. s INTER EMPTY = EMPTY)",
     REWRITE_TAC [IN_INTER;EXTENSION;NOT_IN_EMPTY]);;

let INSERT_INTER = 
    prove_thm
    (`INSERT_INTER`,
     "!x:*. !s t. 
      (x INSERT s) INTER t = (x IN t => x INSERT (s INTER t) | s INTER t)",
     REPEAT GEN_TAC THEN COND_CASES_TAC THEN 
     ASM_REWRITE_TAC [EXTENSION;IN_INTER;IN_INSERT] THEN
     GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC [];
      STRIP_TAC THEN ASM_REWRITE_TAC [];
      PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN
      DISCH_THEN (CONJUNCTS_THEN MP_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [];
      STRIP_TAC THEN ASM_REWRITE_TAC []]);;


% ===================================================================== %
% Distributivity							%
% ===================================================================== %

let UNION_OVER_INTER = prove_thm
   (`UNION_OVER_INTER`,
    "!s:(*)set. !t u. 
      s INTER (t UNION u) = (s INTER t) UNION (s INTER u)",
    REWRITE_TAC [EXTENSION;IN_INTER;IN_UNION] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN 
    ASM_REWRITE_TAC[]);;

let INTER_OVER_UNION = prove_thm
   (`INTER_OVER_UNION`,
    "!s:(*)set. !t u. 
      s UNION (t INTER u) = (s UNION t) INTER (s UNION u)",
    REWRITE_TAC [EXTENSION;IN_INTER;IN_UNION] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN 
    ASM_REWRITE_TAC[]);;


% ===================================================================== %
% Disjoint sets.							%
% ===================================================================== %

let DISJOINT_DEF = 
    new_definition 
    (`DISJOINT_DEF`, "DISJOINT (s:(*)set) t = ((s INTER t) = EMPTY)");;

let IN_DISJOINT = 
    prove_thm
    (`IN_DISJOINT`,
     "!s:(*)set. !t. DISJOINT s t = ~(?x. x IN s /\ x IN t)",
     REWRITE_TAC [DISJOINT_DEF;EXTENSION;IN_INTER;NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
     REPEAT GEN_TAC THEN REFL_TAC);;

let DISJOINT_SYM = 
    prove_thm
    (`DISJOINT_SYM`,
     "!s:(*)set. !t. DISJOINT s t = DISJOINT t s",
     PURE_ONCE_REWRITE_TAC [DISJOINT_DEF] THEN REPEAT GEN_TAC THEN 
     SUBST1_TAC (SPECL ["s:(*)set";"t:(*)set"] INTER_COMM) THEN REFL_TAC);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let DISJOINT_EMPTY =
    prove_thm
    (`DISJOINT_EMPTY`,
     "!s:(*)set. DISJOINT EMPTY s /\ DISJOINT s EMPTY",
     REWRITE_TAC [DISJOINT_DEF;INTER_EMPTY]);;

let DISJOINT_EMPTY_REFL = 
    prove_thm
    (`DISJOINT_EMPTY_REFL`,
     "!s:(*)set. (s = EMPTY) = (DISJOINT s s)",
     REWRITE_TAC [DISJOINT_DEF;INTER_IDEMPOT]);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let DISJOINT_INSERT =
    prove_thm
    (`DISJOINT_INSERT`,
     "!(x:*) s t. DISJOINT (x INSERT s) t = (DISJOINT s t) /\ ~(x IN t)",
     REWRITE_TAC [IN_DISJOINT;IN_INSERT] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
     REWRITE_TAC [DE_MORGAN_THM] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [(let v = genvar ":*" in let GTAC = X_GEN_TAC v in
       DISCH_THEN (\th. CONJ_TAC THENL [GTAC;ALL_TAC] THEN MP_TAC th) THENL
       [DISCH_THEN (STRIP_ASSUME_TAC o SPEC v) THEN ASM_REWRITE_TAC [];
        DISCH_THEN (MP_TAC o SPEC "x:*") THEN REWRITE_TAC[]]);
      REPEAT STRIP_TAC THEN ASM_CASES_TAC "x':* = x" THENL
      [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;


% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let DISJOINT_UNION =
    prove_thm
    (`DISJOINT_UNION`,
     "!s:(*)set. !t u. DISJOINT (s UNION t) u = DISJOINT s u /\ DISJOINT t u",
     REWRITE_TAC [IN_DISJOINT;IN_UNION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV AND_FORALL_CONV) THEN
     REWRITE_TAC [DE_MORGAN_THM;RIGHT_AND_OVER_OR] THEN
     REPEAT GEN_TAC THEN EQ_TAC THEN
     DISCH_THEN (\th. GEN_TAC THEN STRIP_ASSUME_TAC (SPEC "x:*" th)) THEN
     ASM_REWRITE_TAC []);;

% ===================================================================== %
% Set difference							%
% ===================================================================== %

let DIFF_EXISTS =
    TAC_PROOF
    (([], "!s t. ?d. !x:*. x IN d = x IN s /\ ~x IN t"),
     SET_INDUCT_TAC THEN GEN_TAC THENL
     [EXISTS_TAC "{}:(*)set" THEN
      REWRITE_TAC [NOT_IN_EMPTY];
      FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC "t:(*)set") THEN
      ASM_CASES_TAC "(e:*) IN t" THENL
      [EXISTS_TAC "d:(*)set" THEN GEN_TAC THEN
       ASM_CASES_TAC "x:* = e" THEN
       ASM_REWRITE_TAC [IN_INSERT];
       EXISTS_TAC "e INSERT (d:(*)set)" THEN GEN_TAC THEN
       ASM_CASES_TAC "x:* = e" THEN
       ASM_REWRITE_TAC [IN_INSERT]]]);;

let IN_DIFF =
    let th1 = CONV_RULE SKOLEM_CONV DIFF_EXISTS in
    new_specification `IN_DIFF` [`infix`,`DIFF`] th1;;

let DIFF_EMPTY = 
    prove_thm
    (`DIFF_EMPTY`,
     "!s:(*)set. s DIFF EMPTY = s",
     GEN_TAC THEN
     REWRITE_TAC [NOT_IN_EMPTY;IN_DIFF;EXTENSION]);;

let EMPTY_DIFF = 
    prove_thm
    (`EMPTY_DIFF`,
     "!s:(*)set. EMPTY DIFF s = EMPTY",
     GEN_TAC THEN
     REWRITE_TAC [NOT_IN_EMPTY;IN_DIFF;EXTENSION]);;

let DIFF_DIFF = 
    prove_thm
    (`DIFF_DIFF`,
     "!s:(*)set. !t. (s DIFF t) DIFF t = s DIFF t",
     REWRITE_TAC [EXTENSION;IN_DIFF;SYM(SPEC_ALL CONJ_ASSOC)]);;

let DIFF_EQ_EMPTY = 
    prove_thm
    (`DIFF_EQ_EMPTY`,
     "!s:(*)set. s DIFF s = EMPTY",
     REWRITE_TAC [EXTENSION;IN_DIFF;NOT_IN_EMPTY;DE_MORGAN_THM] THEN
     PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
     REWRITE_TAC [EXCLUDED_MIDDLE]);;


% ===================================================================== %
% Removal of an element							%
% ===================================================================== %

let DELETE_DEF = 
    new_infix_definition
    (`DELETE_DEF`, "DELETE s (x:*) = s DIFF {x}");;

let IN_DELETE = 
    prove_thm
    (`IN_DELETE`,
     "!s. !x:*. !y. x IN (s DELETE y) = (x IN s /\ ~(x = y))",
     PURE_ONCE_REWRITE_TAC [DELETE_DEF] THEN
     REWRITE_TAC [IN_DIFF;IN_INSERT;NOT_IN_EMPTY]);;

let DELETE_NON_ELEMENT = 
    prove_thm
    (`DELETE_NON_ELEMENT`,
     "!x:*. !s. ~x IN s = ((s DELETE x) = s)",
     PURE_REWRITE_TAC [EXTENSION;IN_DELETE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM (\th g. SUBST_ALL_TAC th g ? NO_TAC g) THEN RES_TAC;
      RES_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC]);;

let IN_DELETE_EQ = 
    prove_thm
    (`IN_DELETE_EQ`,
     "!s x. !x':*. 
      (x IN s = x' IN s) = (x IN (s DELETE x') = x' IN (s DELETE x))",
     REPEAT GEN_TAC THEN ASM_CASES_TAC "x:* = x'" THENL
     [ASM_REWRITE_TAC [];
      FIRST_ASSUM (ASSUME_TAC o NOT_EQ_SYM) THEN
      ASM_REWRITE_TAC [IN_DELETE]]);;
     
let EMPTY_DELETE = 
    prove_thm
    (`EMPTY_DELETE`,
     "!x:*. EMPTY DELETE x = EMPTY",
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY;IN_DELETE]);;

let DELETE_DELETE = 
    prove_thm
    (`DELETE_DELETE`,
     "!x:*. !s. (s DELETE x) DELETE x = s DELETE x",
     REWRITE_TAC [EXTENSION;IN_DELETE;SYM(SPEC_ALL CONJ_ASSOC)]);;

let DELETE_COMM = 
    prove_thm
    (`DELETE_COMM`,
     "!x:*. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x",
     PURE_REWRITE_TAC [EXTENSION;IN_DELETE;CONJ_ASSOC] THEN
     REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let DELETE_SUBSET = 
    prove_thm
    (`DELETE_SUBSET`,
     "!x:*. !s. (s DELETE x) SUBSET s",
     PURE_REWRITE_TAC [SUBSET_DEF;IN_DELETE] THEN
     REPEAT STRIP_TAC);;

let SUBSET_DELETE = 
    prove_thm
    (`SUBSET_DELETE`,
     "!x:*. !s t. s SUBSET (t DELETE x) = (~(x IN s) /\ (s SUBSET t))",
     REWRITE_TAC [SUBSET_DEF;IN_DELETE;EXTENSION] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THENL
      [ASSUME_TAC (REFL "x:*") THEN RES_TAC; RES_TAC];
      REPEAT STRIP_TAC THENL
      [RES_TAC; FIRST_ASSUM (\th g. SUBST_ALL_TAC th g) THEN RES_TAC]]);;

let SUBSET_INSERT_DELETE = 
    prove_thm
    (`SUBSET_INSERT_DELETE`,
     "!x:*. !s t. s SUBSET (x INSERT t) = ((s DELETE x) SUBSET t)",
     REPEAT GEN_TAC THEN 
     REWRITE_TAC [SUBSET_DEF;IN_INSERT;IN_DELETE] THEN
     EQ_TAC THEN REPEAT STRIP_TAC THENL
     [RES_TAC THEN RES_TAC;
      ASM_CASES_TAC "x':* = x" THEN
      ASM_REWRITE_TAC[] THEN RES_TAC]);;

let DIFF_INSERT = 
    prove_thm
    (`DIFF_INSERT`,
     "!s t. !x:*. s DIFF (x INSERT t) = (s DELETE x) DIFF t",
     PURE_REWRITE_TAC [EXTENSION;IN_DIFF;IN_INSERT;IN_DELETE] THEN
     REWRITE_TAC [DE_MORGAN_THM;CONJ_ASSOC]);;

let DELETE_INSERT = 
    prove_thm
    (`DELETE_INSERT`,
     "!x:*. !y s. 
      (x INSERT s) DELETE y = ((x=y) => s DELETE y | x INSERT (s DELETE y))",
     REWRITE_TAC [EXTENSION;IN_DELETE;IN_INSERT] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN DISCH_TAC THEN
      let tac th g = SUBST_ALL_TAC th g ? ASSUME_TAC th g in
      DISCH_THEN (STRIP_THM_THEN tac) THENL
      [ASM_REWRITE_TAC [IN_INSERT];
       COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_DELETE;IN_INSERT]];
      COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_DELETE;IN_INSERT] THENL
      [STRIP_TAC THEN ASM_REWRITE_TAC []; 
       STRIP_TAC THEN ASM_REWRITE_TAC []]]);;

let INSERT_DELETE = 
    prove_thm
    (`INSERT_DELETE`,
     "!x:*. !s. x IN s ==> (x INSERT (s DELETE x) = s)",
     PURE_REWRITE_TAC [EXTENSION;IN_INSERT;IN_DELETE] THEN
     REPEAT GEN_TAC THEN DISCH_THEN (\th. GEN_TAC THEN MP_TAC th) THEN
     ASM_CASES_TAC "x':* = x" THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let DELETE_INTER =
    prove_thm
    (`DELETE_INTER`,
     "!s t. !x:*. (s DELETE x) INTER t = (s INTER t) DELETE x",
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN REPEAT GEN_TAC THEN
     REWRITE_TAC [IN_INTER;IN_DELETE] THEN
     EQ_TAC THEN REPEAT STRIP_TAC THEN
     FIRST [FIRST_ASSUM ACCEPT_TAC;RES_TAC]);;


% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let DISJOINT_DELETE_SYM =
    prove_thm
    (`DISJOINT_DELETE_SYM`,
     "!s t. !x:*. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s",
     REWRITE_TAC [DISJOINT_DEF;EXTENSION;NOT_IN_EMPTY] THEN
     REWRITE_TAC [IN_INTER;IN_DELETE;DE_MORGAN_THM] THEN
     REPEAT GEN_TAC THEN EQ_TAC THEN
     let X = "X:*" in
     DISCH_THEN (\th. X_GEN_TAC X THEN STRIP_ASSUME_TAC (SPEC X th)) THEN
     ASM_REWRITE_TAC []);;


% ===================================================================== %
% Choice								%
% ===================================================================== %

let CHOICE_EXISTS = 
    TAC_PROOF
    (([], "?CHOICE. !s:(*)set. ~(s = EMPTY) ==> (CHOICE s) IN s"),
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY] THEN
     EXISTS_TAC "\s. @x:*. x IN s" THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV SELECT_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REWRITE_TAC []);;

let CHOICE_DEF = 
    new_specification `CHOICE_DEF` [`constant`,`CHOICE`] CHOICE_EXISTS;;
     

% ===================================================================== %
% The REST of a set after removing a chosen element.			%
% ===================================================================== %

let REST_DEF = 
    new_definition
    (`REST_DEF`, "REST (s:(*)set) = s DELETE (CHOICE s)");;

let CHOICE_NOT_IN_REST = 
    prove_thm
    (`CHOICE_NOT_IN_REST`,
     "!s:(*)set. ~(CHOICE s) IN (REST s)",
     REWRITE_TAC [IN_DELETE;REST_DEF]);;

let CHOICE_INSERT_REST =
    prove_thm
    (`CHOICE_INSERT_REST`,
     "!s:(*)set. ~(s = EMPTY) ==> (((CHOICE s) INSERT (REST s)) = s)",
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC [EXTENSION;IN_INSERT;REST_DEF;IN_DELETE] THEN
     GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [IMP_RES_TAC CHOICE_DEF THEN ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [EXCLUDED_MIDDLE]]);;

let REST_SUBSET = 
    prove_thm
    (`REST_SUBSET`,
     "!s:(*)set. (REST s) SUBSET s",
     REWRITE_TAC [SUBSET_DEF;REST_DEF;IN_DELETE] THEN REPEAT STRIP_TAC);;

let lemma = 
    TAC_PROOF(([], "(P /\ Q = P) = (P ==> Q)"),
    	      BOOL_CASES_TAC "P:bool" THEN REWRITE_TAC[]);;

let REST_PSUBSET = 
    prove_thm
    (`REST_PSUBSET`,
     "!s:(*)set. ~(s = EMPTY) ==> (REST s) PSUBSET s",
     REWRITE_TAC [PSUBSET_DEF;REST_SUBSET] THEN
     GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC [EXTENSION;REST_DEF;IN_DELETE] THEN
     CONV_TAC NOT_FORALL_CONV THEN
     REWRITE_TAC [DE_MORGAN_THM;lemma;NOT_IMP] THEN
     EXISTS_TAC "CHOICE (s:(*)set)" THEN
     IMP_RES_TAC CHOICE_DEF THEN
     ASM_REWRITE_TAC []);;

% ===================================================================== %
% Singleton set.							%
% ===================================================================== %

let SING_DEF = 
    new_definition
    (`SING_DEF`, "SING s = ?x:*. s = {x}");;

let SING = 
    prove_thm
    (`SING`,
     "!x:*. SING {x}",
     PURE_ONCE_REWRITE_TAC [SING_DEF] THEN
     GEN_TAC THEN EXISTS_TAC "x:*" THEN REFL_TAC);;

let IN_SING = 
    prove_thm
    (`IN_SING`,
     "!x y. x IN {y:*} = (x = y)",
     REWRITE_TAC [IN_INSERT;NOT_IN_EMPTY]);;

let NOT_SING_EMPTY = 
    prove_thm
    (`NOT_SING_EMPTY`,
     "!x:*. ~({x} = EMPTY)",
     REWRITE_TAC [EXTENSION;IN_SING;NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     GEN_TAC THEN EXISTS_TAC "x:*" THEN REWRITE_TAC[]);;

let NOT_EMPTY_SING = 
    prove_thm
    (`NOT_EMPTY_SING`,
     "!x:*. ~(EMPTY = {x})",
     REWRITE_TAC [EXTENSION;IN_SING;NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     GEN_TAC THEN EXISTS_TAC "x:*" THEN REWRITE_TAC[]);;

let EQUAL_SING = 
    prove_thm
    (`EQUAL_SING`,
     "!x:*. !y. ({x} = {y}) = (x = y)",
     REWRITE_TAC [EXTENSION;IN_SING] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (\th. REWRITE_TAC [SYM(SPEC_ALL th)]);
      DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC]);;

let DISJOINT_SING_EMPTY = 
    prove_thm
    (`DISJOINT_SING_EMPTY`,
     "!x:*. DISJOINT {x} EMPTY",
     REWRITE_TAC [DISJOINT_DEF;INTER_EMPTY]);;

let INSERT_SING_UNION = 
    prove_thm
    (`INSERT_SING_UNION`,
     "!s. !x:*. x INSERT s = {x} UNION s",
     REWRITE_TAC [EXTENSION;IN_INSERT;IN_UNION;NOT_IN_EMPTY]);;

let SING_DELETE = 
    prove_thm
    (`SING_DELETE`,
    "!x:*. {x} DELETE x = EMPTY",
    REWRITE_TAC [EXTENSION;NOT_IN_EMPTY;IN_DELETE;IN_INSERT] THEN
    PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [DE_MORGAN_THM;EXCLUDED_MIDDLE]);;

let DELETE_EQ_SING = 
    prove_thm
    (`DELETE_EQ_SING`,
     "!s. !x:*. (x IN s) ==> ((s DELETE x = EMPTY) = (s = {x}))",
     PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
     REWRITE_TAC [NOT_IN_EMPTY;DE_MORGAN_THM;IN_INSERT;IN_DELETE] THEN
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN GEN_TAC THEN
      FIRST_ASSUM (\th g. STRIP_ASSUME_TAC (SPEC "x':*" th) g) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN RES_TAC;
      let th = PURE_ONCE_REWRITE_RULE [DISJ_SYM] EXCLUDED_MIDDLE in
      DISCH_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [th]]);;

let CHOICE_SING = 
    prove_thm
    (`CHOICE_SING`,
     "!x:*. CHOICE {x} = x",
     GEN_TAC THEN 
     MP_TAC (MATCH_MP CHOICE_DEF (SPEC "x:*" NOT_SING_EMPTY)) THEN
     REWRITE_TAC [IN_SING]);;

let REST_SING = 
    prove_thm
    (`REST_SING`,
     "!x:*. REST {x} = EMPTY",
     REWRITE_TAC [CHOICE_SING;REST_DEF;SING_DELETE]);;

let SING_IFF_EMPTY_REST = 
    prove_thm
    (`SING_IFF_EMPTY_REST`,
     "!s:(*)set. SING s = ~(s = EMPTY) /\ (REST s = EMPTY)",
     PURE_ONCE_REWRITE_TAC [SING_DEF] THEN
     GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC [REST_SING] THEN
      REWRITE_TAC [EXTENSION;NOT_IN_EMPTY;IN_INSERT] THEN
      CONV_TAC NOT_FORALL_CONV THEN
      EXISTS_TAC "x:*" THEN REWRITE_TAC [];
      EXISTS_TAC "CHOICE s:*" THEN
      IMP_RES_THEN (SUBST1_TAC o SYM) CHOICE_INSERT_REST THEN
      ASM_REWRITE_TAC [EXTENSION;IN_SING;CHOICE_SING]]);;

% ===================================================================== %
% The image of a function on a set.					%
% ===================================================================== %

let IMAGE_EXISTS =
    TAC_PROOF
    (([], "!f:*->**. !s:(*)set. ?t. !y. y IN t = ?x. (y = f x) /\ x IN s"),
     GEN_TAC THEN SET_INDUCT_TAC THENL
     [EXISTS_TAC "{}:(**)set" THEN REWRITE_TAC [NOT_IN_EMPTY];
      FIRST_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
      EXISTS_TAC "(f (e:*):**) INSERT t" THEN
      ASM_REWRITE_TAC [IN_INSERT] THEN GEN_TAC THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL
      [EXISTS_TAC "e:*" THEN ASM_REWRITE_TAC [];
       EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [];
       DISJ2_TAC THEN EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC []]]);;

let IN_IMAGE =
    let th1 = CONV_RULE SKOLEM_CONV IMAGE_EXISTS in
    new_specification `IN_IMAGE` [`constant`,`IMAGE`] th1;;

let IMAGE_IN = 
    prove_thm
    (`IMAGE_IN`,
     "!x s. (x IN s) ==> !(f:*->**). f x IN (IMAGE f s)",
     PURE_ONCE_REWRITE_TAC [IN_IMAGE] THEN
     REPEAT STRIP_TAC THEN 
     EXISTS_TAC "x:*" THEN
     CONJ_TAC THENL [REFL_TAC; FIRST_ASSUM ACCEPT_TAC]);;

let IMAGE_EMPTY =
     prove_thm
     (`IMAGE_EMPTY`,
      "!f:*->**. IMAGE f EMPTY = EMPTY",
      REWRITE_TAC[EXTENSION;IN_IMAGE;NOT_IN_EMPTY]);;

let IMAGE_ID = 
    prove_thm
    (`IMAGE_ID`,
     "!s:* set. IMAGE (\x:*.x) s = s",
     REWRITE_TAC [EXTENSION;IN_IMAGE] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [ALL_TAC;EXISTS_TAC "x:*"] THEN
     ASM_REWRITE_TAC []);;

let IMAGE_COMPOSE = 
    prove_thm
    (`IMAGE_COMPOSE`,
     "!f:**->***. !g:*->**. !s. IMAGE (f o g) s = IMAGE f (IMAGE g s)",
     PURE_REWRITE_TAC [EXTENSION;IN_IMAGE;o_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [EXISTS_TAC "g (x':*):**" THEN
      CONJ_TAC THENL [ALL_TAC;EXISTS_TAC "x':*"] THEN
      ASM_REWRITE_TAC [];
      EXISTS_TAC "x'':*" THEN ASM_REWRITE_TAC[]]);;

let IMAGE_INSERT =
    prove_thm
    (`IMAGE_INSERT`,
     "!(f:*->**) x s. IMAGE f (x INSERT s) = f x INSERT (IMAGE f s)",
     PURE_REWRITE_TAC [EXTENSION;IN_INSERT;IN_IMAGE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [ALL_TAC;DISJ2_TAC THEN EXISTS_TAC "x'':*";
      EXISTS_TAC "x:*";EXISTS_TAC "x'':*"] THEN
     ASM_REWRITE_TAC[]);;

let IMAGE_EQ_EMPTY =
    prove_thm
    (`IMAGE_EQ_EMPTY`,
     "!s. !f:*->**. ((IMAGE f s) = EMPTY) = (s = EMPTY)",
     GEN_TAC THEN
     STRIP_ASSUME_TAC (SPEC "s:(*)set" SET_CASES) THEN
     ASM_REWRITE_TAC [IMAGE_EMPTY;IMAGE_INSERT;NOT_INSERT_EMPTY]);;

let IMAGE_DELETE =
    prove_thm
    (`IMAGE_DELETE`,
     "!(f:*->**) x s. ~(x IN s) ==> (IMAGE f (s DELETE x) = (IMAGE f s))",
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     PURE_REWRITE_TAC [EXTENSION;IN_DELETE;IN_IMAGE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     EXISTS_TAC "x'':*" THEN ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST_ALL_TAC THEN RES_TAC);;

let IMAGE_UNION =
    prove_thm
    (`IMAGE_UNION`,
     "!(f:*->**) s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)",
     PURE_REWRITE_TAC [EXTENSION;IN_UNION;IN_IMAGE] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [DISJ1_TAC;DISJ2_TAC;ALL_TAC;ALL_TAC] THEN
     EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC []);;

let IMAGE_SUBSET = 
    prove_thm
    (`IMAGE_SUBSET`,
     "!s t. (s SUBSET t) ==> !f:*->**. (IMAGE f s) SUBSET (IMAGE f t)",
     PURE_REWRITE_TAC [SUBSET_DEF;IN_IMAGE] THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC []);;

let IMAGE_INTER =
    prove_thm
    (`IMAGE_INTER`,
     "!(f:*->**) s t. IMAGE f (s INTER t) SUBSET (IMAGE f s INTER IMAGE f t)",
     REPEAT GEN_TAC THEN
     REWRITE_TAC [SUBSET_DEF;IN_IMAGE;IN_INTER] THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC "x':*" THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let lemma =
    TAC_PROOF
    (([], "!s x. x IN s ==>  !f:*->**. (f x) IN (IMAGE f s)"),
     REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC [IN_IMAGE] THEN
     EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[]);;

let SET_MINIMUM = 
    prove_thm
    (`SET_MINIMUM`,
     "!s:(*)set. !M.
      (?x. x IN s) = ?x. x IN s /\ !y. y IN s ==> M x <= M y",
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [IMP_RES_THEN (ASSUME_TAC o ISPEC "M:*->num") lemma THEN
      let rule = REWRITE_RULE [IN_IMAGE] in
      IMP_RES_THEN (STRIP_ASSUME_TAC o rule) NUM_SET_WOP THEN
      EXISTS_TAC "x':*" THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM (SUBST_ALL_TAC o SYM) THEN
       REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC "y:*" THEN CONJ_TAC THENL
       [REFL_TAC; FIRST_ASSUM ACCEPT_TAC]];
      EXISTS_TAC "x:*" THEN FIRST_ASSUM ACCEPT_TAC]);;

% ===================================================================== %
% Injective functions on a set.						%
% ===================================================================== %

let INJ_DEF =
    new_definition
    (`INJ_DEF`,
     "INJ (f:*->**) s t =
          (!x. x IN s ==> (f x) IN t) /\ 
          (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y))");;

let INJ_ID =
    prove_thm
    (`INJ_ID`,
     "!s. INJ (\x:*.x) s s",
     PURE_ONCE_REWRITE_TAC [INJ_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC);;
     
let INJ_COMPOSE = 
    prove_thm
    (`INJ_COMPOSE`,
     "!f:*->**. !g:**->***.
      !s t u. (INJ f s t  /\ INJ g t u) ==> INJ (g o f) s u",
     PURE_REWRITE_TAC [INJ_DEF;o_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC;
      RES_TAC THEN RES_TAC]);;

let INJ_EMPTY =
    prove_thm
    (`INJ_EMPTY`,
     "!f:*->**. (!s. INJ f {} s) /\ (!s. INJ f s {} = (s = {}))",
     REWRITE_TAC [INJ_DEF;NOT_IN_EMPTY;EXTENSION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RES_TAC);;


% ===================================================================== %
% Surjective functions on a set.					%
% ===================================================================== %

let SURJ_DEF =
    new_definition
    (`SURJ_DEF`,
     "SURJ (f:*->**) s t =
           (!x. x IN s ==> (f x) IN t) /\ 
           (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))");;

let SURJ_ID =
    prove_thm
    (`SURJ_ID`,
     "!s. SURJ (\x:*.x) s s",
     PURE_ONCE_REWRITE_TAC [SURJ_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC "x':*" THEN
     ASM_REWRITE_TAC []);;

let SURJ_COMPOSE = 
    prove_thm
    (`SURJ_COMPOSE`,
     "!f:*->**. !g:**->***.
      !s t u. (SURJ f s t  /\ SURJ g t u) ==> SURJ (g o f) s u",
     PURE_REWRITE_TAC [SURJ_DEF;o_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC;
      RES_TAC THEN RES_TAC THEN
      EXISTS_TAC "y'':*" THEN
      ASM_REWRITE_TAC []]);;

let SURJ_EMPTY =
    prove_thm
    (`SURJ_EMPTY`,
     "!f:*->**. (!s. SURJ f {} s = (s = {})) /\ (!s. SURJ f s {} = (s = {}))",
     REWRITE_TAC [SURJ_DEF;NOT_IN_EMPTY;EXTENSION]);;

let IMAGE_SURJ =
    prove_thm
    (`IMAGE_SURJ`,
     "!f:*->**. !s t. SURJ f s t = ((IMAGE f s) = t)",
     PURE_REWRITE_TAC [SURJ_DEF;EXTENSION;IN_IMAGE] THEN
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
      [RES_TAC THEN ASM_REWRITE_TAC [];
       MAP_EVERY PURE_ONCE_REWRITE_TAC [[CONJ_SYM];[EQ_SYM_EQ]] THEN
       FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN (ASSUME_TAC o CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)) THEN
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
      [EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC [];
       EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC []]]);;

% ===================================================================== %
% Bijective functions on a set.						%
% ===================================================================== %

let BIJ_DEF =
    new_definition
    (`BIJ_DEF`,
     "BIJ (f:*->**) s t = INJ f s t /\ SURJ f s t");;

let BIJ_ID =
    prove_thm
    (`BIJ_ID`,
     "!s. BIJ (\x:*.x) s s",
     REWRITE_TAC [BIJ_DEF;INJ_ID;SURJ_ID]);;

let BIJ_EMPTY =
    prove_thm
    (`BIJ_EMPTY`,
     "!f:*->**. (!s. BIJ f {} s = (s = {})) /\ (!s. BIJ f s {} = (s = {}))",
     REWRITE_TAC [BIJ_DEF;INJ_EMPTY;SURJ_EMPTY]);;

let BIJ_COMPOSE = 
    prove_thm
    (`BIJ_COMPOSE`,
     "!f:*->**. !g:**->***.
      !s t u. (BIJ f s t  /\ BIJ g t u) ==> BIJ (g o f) s u",
     PURE_REWRITE_TAC [BIJ_DEF] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC INJ_COMPOSE;IMP_RES_TAC SURJ_COMPOSE]);;

% ===================================================================== %
% Left and right inverses.						%
% ===================================================================== %

let lemma1 =
    TAC_PROOF
    (([], "!f:*->**. !s.
           (!x y. x IN s /\ y IN s ==> (f x = f y) ==> (x = y)) =
           (!y. y IN s ==> !x.((x IN s /\ (f x = f y))=(y IN s /\ (x = y))))"),
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     RES_TAC THEN ASM_REWRITE_TAC []);;

let lemma2 =
    TAC_PROOF
    (([],
      "!f:*->**. !s. ?g. !t. INJ f s t ==> !x:*. x IN s ==> (g(f x) = x)"),
     REPEAT GEN_TAC THEN PURE_REWRITE_TAC [INJ_DEF;lemma1] THEN
     EXISTS_TAC "\y:**. @x:*. x IN s /\ (f x = y)" THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN (RES_THEN \th. REWRITE_TAC [th]) THEN
     ASM_REWRITE_TAC [] THEN CONV_TAC SELECT_CONV THEN
     EXISTS_TAC "x:*" THEN REFL_TAC);;

% --------------------------------------------------------------------- %
% LINV_DEF:								%
%   |- !f s t. INJ f s t ==> (!x. x IN s ==> (LINV f s(f x) = x))	%
% --------------------------------------------------------------------- %

let LINV_DEF =
    let th1 = CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) lemma2 in
    let th2 = CONV_RULE SKOLEM_CONV th1 in
        new_specification `LINV_DEF` [`constant`,`LINV`] th2;;

let lemma3 = 
    TAC_PROOF
    (([],
      "!f:*->**. !s. ?g. !t. SURJ f s t ==> !x:**. x IN t ==> (f(g x) = x)"),
     REPEAT GEN_TAC THEN PURE_REWRITE_TAC [SURJ_DEF] THEN    
     EXISTS_TAC "\y:**. @x:*. x IN s /\ (f x = y)" THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN
     (\(A,g).
       let tm = mk_conj("^(rand(lhs g)) IN s",g) in
       SUBGOAL_THEN tm (\th. ACCEPT_TAC(CONJUNCT2 th))(A,g)) THEN
     CONV_TAC SELECT_CONV THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC);;
     
% --------------------------------------------------------------------- %
% RINV_DEF:								%
%   |- !f s t. SURJ f s t ==> (!x. x IN t ==> (f(RINV f s x) = x))      %
% --------------------------------------------------------------------- %

let RINV_DEF =
    let th1 = CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_EXISTS_CONV) lemma3 in
    let th2 = CONV_RULE SKOLEM_CONV th1 in
        new_specification `RINV_DEF` [`constant`,`RINV`] th2;;

% ===================================================================== %
% Cardinality 								%
% ===================================================================== %

% --------------------------------------------------------------------- %
% card_rel_def: defining equations for a relation "R s n", which means  %
% that the finite s has cardinality n.					%
% --------------------------------------------------------------------- %

let card_rel_def = 
    "(!s. R s 0 = (s = EMPTY)) /\
     (!s n. R s (SUC n) = ?x:*. x IN s /\ R (s DELETE x) n)";;

% --------------------------------------------------------------------- %
% Prove that such a relation exists.					%
% --------------------------------------------------------------------- %

let CARD_REL_EXISTS =  prove_rec_fn_exists num_Axiom card_rel_def;;

% --------------------------------------------------------------------- %
% Now, prove that it doesn't matter which element we delete		%
% Proof modified for Version 12 IMP_RES_THEN		 [TFM 91.01.23]	%
% --------------------------------------------------------------------- %

let CARD_REL_DEL_LEMMA = 
    TAC_PROOF
    ((conjuncts card_rel_def,
      "!n:num.!s.!x:*. 
       x IN s ==> R (s DELETE x) n  ==> !y:*. y IN s ==> R (s DELETE y) n"),
     INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      IMP_RES_TAC DELETE_EQ_SING THEN ASM_REWRITE_TAC [] THEN 
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_SING] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SING_DELETE];
      ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
      let th = (SPEC "y:* = x'" EXCLUDED_MIDDLE) in
      DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th THENL
      [MP_TAC (SPECL ["s:(*)set";"x:*";"x':*"] IN_DELETE_EQ) THEN
       ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
       PURE_ONCE_REWRITE_TAC [DELETE_COMM] THEN
       EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
       let th = (SPEC "x:* = y" EXCLUDED_MIDDLE) in
       DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC th THENL
       [EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC [];
        EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC [IN_DELETE] THEN
        RES_THEN (TRY o IMP_RES_THEN ASSUME_TAC) THEN
        PURE_ONCE_REWRITE_TAC [DELETE_COMM] THEN
	FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN_DELETE] THEN
	CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN FIRST_ASSUM ACCEPT_TAC]]]);;


% --------------------------------------------------------------------- %
% So "R s" specifies a unique number.					%
% --------------------------------------------------------------------- %

let CARD_REL_UNIQUE = 
    TAC_PROOF
    ((conjuncts card_rel_def,
      "!n:num. !s:(*)set. R s n ==> (!m. R s m ==> (n = m))"),
     INDUCT_TAC THEN ASM_REWRITE_TAC [] THENL
     [GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THENL
      [STRIP_TAC THEN REFL_TAC; ASM_REWRITE_TAC[NOT_SUC;NOT_IN_EMPTY]];
      GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
      [ASM_REWRITE_TAC [NOT_SUC;SYM(SPEC_ALL MEMBER_NOT_EMPTY)] THEN
       EXISTS_TAC "x:*" THEN FIRST_ASSUM ACCEPT_TAC;
       ASM_REWRITE_TAC [INV_SUC_EQ] THEN STRIP_TAC THEN 
       IMP_RES_TAC CARD_REL_DEL_LEMMA THEN RES_TAC]]);;

% --------------------------------------------------------------------- %
% Now, ?n. R s n if s is finite.					%
% --------------------------------------------------------------------- %

let CARD_REL_EXISTS_LEMMA = 
    TAC_PROOF
    ((conjuncts card_rel_def, "!s:(*)set. ?n:num. R s n"),
     SET_INDUCT_TAC THENL
     [EXISTS_TAC "0" THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM (\th g. CHOOSE_THEN ASSUME_TAC th g) THEN
      EXISTS_TAC "SUC n" THEN ASM_REWRITE_TAC [] THEN
      EXISTS_TAC "e:*" THEN IMP_RES_TAC DELETE_NON_ELEMENT THEN
      ASM_REWRITE_TAC [DELETE_INSERT;IN_INSERT]]);;     

% --------------------------------------------------------------------- %
% So (@n. R s n) = m iff R s m        (\s.@n.R s n defines a function)	%
% Proof modified for Version 12 IMP_RES_THEN		 [TFM 91.01.23]	%
% --------------------------------------------------------------------- %

let CARD_REL_THM = 
    TAC_PROOF
    ((conjuncts card_rel_def, 
     "!m s.((@n:num. R (s:(*)set) n) = m) = R s m"),
     REPEAT STRIP_TAC THEN 
     STRIP_ASSUME_TAC (SPEC "s:(*)set" CARD_REL_EXISTS_LEMMA) THEN 
     EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
      EXISTS_TAC "n:num" THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      STRIP_TAC THEN
      IMP_RES_THEN ASSUME_TAC CARD_REL_UNIQUE THEN
      CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      CONV_TAC SELECT_CONV THEN
      EXISTS_TAC "n:num" THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

% --------------------------------------------------------------------- %
% Now, prove the existence of the required cardinality function.	%
% --------------------------------------------------------------------- %

let CARD_EXISTS = 
    TAC_PROOF
    (([]," ?CARD.
           (CARD EMPTY = 0) /\ 
           (!s. !x:*. CARD(x INSERT s) = (x IN s => CARD s | SUC(CARD s)))"),
     STRIP_ASSUME_TAC CARD_REL_EXISTS THEN
     EXISTS_TAC "\s:(*)set. @n:num. R s n" THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [CARD_REL_THM];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
      [IMP_RES_THEN SUBST1_TAC ABSORPTION THEN REFL_TAC;
       ASM_REWRITE_TAC [CARD_REL_THM] THEN
       EXISTS_TAC "x:*" THEN
       IMP_RES_TAC DELETE_NON_ELEMENT THEN
       ASM_REWRITE_TAC [IN_INSERT;DELETE_INSERT] THEN
       CONV_TAC SELECT_CONV THEN
       MATCH_ACCEPT_TAC CARD_REL_EXISTS_LEMMA]]);;

% --------------------------------------------------------------------- %
% Finally, introduce the CARD function via a constant specification.	%
% --------------------------------------------------------------------- %

let CARD_DEF = 
    new_specification `CARD_DEF` [`constant`,`CARD`] CARD_EXISTS;;

% --------------------------------------------------------------------- %
% Various cardinality results.						%
% --------------------------------------------------------------------- %

let CARD_EMPTY = save_thm(`CARD_EMPTY`,CONJUNCT1 CARD_DEF);;

let CARD_INSERT = save_thm(`CARD_INSERT`,CONJUNCT2 CARD_DEF);;

let CARD_EQ_0 = 
    prove_thm
    (`CARD_EQ_0`,
     "!s:(*)set. (CARD s = 0) = (s = EMPTY)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [CARD_EMPTY];
      ASM_REWRITE_TAC [CARD_INSERT;NOT_INSERT_EMPTY;NOT_SUC]]);;
      
let CARD_DELETE = 
    prove_thm
    (`CARD_DELETE`,
     "!s. !x:*. CARD(s DELETE x) = (x IN s => (CARD s) - 1 | CARD s)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DELETE;NOT_IN_EMPTY];
      PURE_REWRITE_TAC [DELETE_INSERT;IN_INSERT] THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC "x:* = e" THENL
      [ASM_REWRITE_TAC [SUC_SUB1;CARD_DEF];
       SUBST1_TAC (SPECL ["e:*";"x:*"] EQ_SYM_EQ) THEN
       ASM_REWRITE_TAC [CARD_DEF;IN_DELETE;SUC_SUB1] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
       STRIP_ASSUME_TAC (SPEC "CARD(s:(*)set)" num_CASES) THENL
       [(let tac th g = SUBST_ALL_TAC th g ? ASSUME_TAC th g in
	 REPEAT_GTCL IMP_RES_THEN tac CARD_EQ_0 THEN
	 IMP_RES_TAC NOT_IN_EMPTY);
	 ASM_REWRITE_TAC [SUC_SUB1]]]]);;


let lemma1 = 
    TAC_PROOF
    (([], "!n m. (SUC n <= SUC m) = (n <= m)"),
     REWRITE_TAC [LESS_OR_EQ;INV_SUC_EQ;LESS_MONO_EQ]);;

let lemma2 = 
    TAC_PROOF
    (([], "!n m. (n <= SUC m) = (n <= m \/ (n = SUC m))"),
     REWRITE_TAC [LESS_OR_EQ;LESS_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[]);;

let CARD_INTER_LESS_EQ = 
    prove_thm
    (`CARD_INTER_LESS_EQ`,
     "!s:(*)set. !t. CARD (s INTER t) <= CARD s",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [CARD_DEF;INTER_EMPTY;LESS_EQ_REFL];
      PURE_ONCE_REWRITE_TAC [INSERT_INTER] THEN
      GEN_TAC THEN COND_CASES_TAC THENL
      [ASM_REWRITE_TAC [CARD_DEF;IN_INTER;lemma1];
       ASM_REWRITE_TAC [CARD_DEF;lemma2]]]);;

let CARD_UNION = 
    prove_thm
    (`CARD_UNION`,
     "!s:(*)set. !t. 
       (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [UNION_EMPTY;INTER_EMPTY;CARD_DEF;ADD_CLAUSES];
      REPEAT STRIP_TAC THEN REWRITE_TAC [INSERT_UNION;INSERT_INTER] THEN 
      ASM_CASES_TAC "(e:*) IN t" THENL
      [ASM_REWRITE_TAC [IN_INTER;ADD_CLAUSES;CARD_DEF];
       ASM_REWRITE_TAC [CARD_DEF;ADD_CLAUSES; INV_SUC_EQ; IN_UNION]]]);;

let lemma = 
    TAC_PROOF
    (([], "!n m. (n <= SUC m) = (n <= m \/ (n = SUC m))"),
     REWRITE_TAC [LESS_OR_EQ;LESS_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[]);;

let CARD_SUBSET = 
    prove_thm
    (`CARD_SUBSET`,
     "!s:(*)set. !t. t SUBSET s ==> (CARD t <= CARD s)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [SUBSET_EMPTY;CARD_EMPTY] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [CARD_DEF;LESS_EQ_REFL];
      ASM_REWRITE_TAC [CARD_INSERT;SUBSET_INSERT_DELETE] THEN
      REPEAT STRIP_TAC THEN RES_THEN MP_TAC THEN
      ASM_REWRITE_TAC [CARD_DELETE] THEN COND_CASES_TAC THENL
      [(let th = SPEC "CARD (t:(*)set)" num_CASES in
        REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC th) THENL
	[REWRITE_TAC [LESS_OR_EQ;LESS_0];
         REWRITE_TAC [SUC_SUB1;LESS_OR_EQ;LESS_MONO_EQ;INV_SUC_EQ]];
       STRIP_TAC THEN ASM_REWRITE_TAC [lemma]]]);;

let CARD_PSUBSET = 
    prove_thm
    (`CARD_PSUBSET`,
     "!s:(*)set. !t. t PSUBSET s ==> (CARD t < CARD s)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC PSUBSET_DEF THEN
     IMP_RES_THEN MP_TAC CARD_SUBSET THEN
     PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN 
     DISCH_THEN (STRIP_THM_THEN (\th g. ACCEPT_TAC th g ? MP_TAC th g)) THEN
     IMP_RES_THEN STRIP_ASSUME_TAC PSUBSET_INSERT_SUBSET THEN
     IMP_RES_THEN MP_TAC CARD_SUBSET THEN
     IMP_RES_TAC INSERT_SUBSET THEN 
     ASM_REWRITE_TAC [CARD_INSERT;LESS_EQ] THEN
     REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let CARD_SING = 
    prove_thm
    (`CARD_SING`,
     "!x:*. CARD {x} = 1",
     CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
     REWRITE_TAC [CARD_EMPTY;CARD_INSERT;NOT_IN_EMPTY]);;

let SING_IFF_CARD1 = 
    prove_thm
    (`SING_IFF_CARD1`,
     "!s:(*)set. (SING s) = (CARD s = 1)",
     REWRITE_TAC [SING_DEF;num_CONV "1"] THEN 
     GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
      REWRITE_TAC [CARD_SING;num_CONV "1"];
      STRIP_ASSUME_TAC (SPEC "s:(*)set" SET_CASES) THENL
      [ASM_REWRITE_TAC [CARD_EMPTY;NOT_EQ_SYM(SPEC_ALL NOT_SUC)];
       FIRST_ASSUM SUBST1_TAC THEN
       ASM_REWRITE_TAC [CARD_INSERT;INV_SUC_EQ;CARD_EQ_0] THEN
       DISCH_TAC THEN EXISTS_TAC "x:*" THEN
       ASM_REWRITE_TAC []]]);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let CARD_DIFF =
    prove_thm
    (`CARD_DIFF`,
     "!t:(*)set. !s. CARD (s DIFF t) = (CARD s - CARD (s INTER t))",
     SET_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC [DIFF_EMPTY;INTER_EMPTY;CARD_EMPTY;SUB_0];
      PURE_ONCE_REWRITE_TAC [INTER_COMM] THEN
      PURE_ONCE_REWRITE_TAC [INSERT_INTER] THEN
      COND_CASES_TAC THENL
      [ASM_REWRITE_TAC [CARD_INSERT;IN_INTER;DIFF_INSERT;CARD_DELETE] THEN
       PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL SUB_PLUS)] THEN
       REWRITE_TAC [num_CONV "1";ADD_CLAUSES;DELETE_INTER] THEN
       MP_TAC (SPECL ["s':(*)set";"s:(*)set";"e:*"] IN_INTER) THEN
       ASM_REWRITE_TAC [DELETE_NON_ELEMENT] THEN
       DISCH_THEN SUBST1_TAC THEN
       SUBST1_TAC (SPECL ["s:(*)set";"s':(*)set"] INTER_COMM) THEN REFL_TAC;
       IMP_RES_TAC DELETE_NON_ELEMENT THEN
       PURE_ONCE_REWRITE_TAC [INTER_COMM] THEN
       ASM_REWRITE_TAC [DIFF_INSERT]]]);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let LESS_CARD_DIFF =
    prove_thm
    (`LESS_CARD_DIFF`,
     "!t:(*)set. !s. (CARD t < CARD s) ==> (0 < CARD(s DIFF t))",
     PURE_REWRITE_TAC [CARD_DIFF; GSYM SUB_LESS_0] THEN
     REPEAT STRIP_TAC THEN
     let th1 = SPECL ["s:(*)set";"t:(*)set"] CARD_INTER_LESS_EQ in
     let th2 = PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] th1 in
     DISJ_CASES_THEN2 ACCEPT_TAC (SUBST_ALL_TAC o SYM) th2 THEN
     let th3 = SPECL ["t:(*)set";"s:(*)set"] CARD_INTER_LESS_EQ in
     let th4 = PURE_ONCE_REWRITE_RULE [INTER_COMM] th3 in
     IMP_RES_TAC (PURE_ONCE_REWRITE_RULE [GSYM NOT_LESS] th4));;


quit();; % Needed for Common Lisp %
