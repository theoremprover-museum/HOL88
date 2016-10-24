% ===================================================================== %
% LIBRARY: sets								%
% FILE:    mk_sets.ml							%
% DESCRIPTION: a simple theory of sets					%
%									% 
% AUTHOR:  Philippe Leveilley						%
% DATE:    June 9, 1989							%
%									%
% REVISED: Tom Melham (extensively revised and extended)		%
% DATE:    August 1990							%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory.						%
% --------------------------------------------------------------------- %
new_theory `sets`;;

% ===================================================================== %
% Type definition for (*)set.						%
%									%
% Sets are represented by predicates of type *->bool.  The empty set is %
% is represented by the abstraction \x.F.  A set is represented by its  %
% characteristic function. 						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Theorem stating that the representing type is non empty.		%
% --------------------------------------------------------------------- %
let EXISTENCE_THM = 
     TAC_PROOF(([],"?s:*->bool. (\p.T) s"),
               EXISTS_TAC "p:*->bool" THEN
	       CONV_TAC BETA_CONV THEN 
	       ACCEPT_TAC TRUTH);;

% --------------------------------------------------------------------- %
% Now, make the type definition.					%
% --------------------------------------------------------------------- %
let set_TY_DEF = 
    new_type_definition(`set`,"\p:*->bool.T", EXISTENCE_THM);;

% --------------------------------------------------------------------- %
% Define (*)set <-> (*->bool) bijections  				%
% --------------------------------------------------------------------- %
let set_ISO_DEF = 
    define_new_type_bijections `set_ISO_DEF` `SPEC` `CHF` set_TY_DEF;;

% --------------------------------------------------------------------- %
% Prove that CHF is one-to-one.						%
% --------------------------------------------------------------------- %
let CHF_11 = REWRITE_RULE [] (prove_rep_fn_one_one set_ISO_DEF);;

% --------------------------------------------------------------------- %
% Remove the lambda in set_ISO_DEF					%
% --------------------------------------------------------------------- %
let set_ISO_DEF = REWRITE_RULE [] set_ISO_DEF;;

% ===================================================================== %
% Membership.								%
% ===================================================================== %

let IN_DEF = 
    new_infix_definition (`IN_DEF`, "$IN (x:*) (s:(*)set) = CHF s x");;

% --------------------------------------------------------------------- %
% Axiom of specification: x IN {y | P y} iff P x			%
% --------------------------------------------------------------------- %

let SPECIFICATION =
    prove_thm
    (`SPECIFICATION`,
     "!(P:*->bool) x. x IN (SPEC P) = P x",
     REWRITE_TAC [IN_DEF; set_ISO_DEF]);;

% --------------------------------------------------------------------- %
% Axiom of extension: (s = t) iff !x. x IN s = x in t			%
% --------------------------------------------------------------------- %

let EXTENSION = prove_thm
   (`EXTENSION`,
    "!s t. (s=t) = (!x:*. x IN s = x IN t)",
    REPEAT GEN_TAC THEN
    REWRITE_TAC [IN_DEF;SYM (FUN_EQ_CONV "f:*->** = g");CHF_11]);;

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

% ===================================================================== %
% Generalized set specification.					%
% ===================================================================== %
let GSPEC_DEF = 
    new_definition
    (`GSPEC_DEF`,
     "GSPEC f = SPEC(\y:*. ?x:**. (y,T) = f x)");;

% --------------------------------------------------------------------- %
% generalized axiom of specification.					%
% --------------------------------------------------------------------- %

let GSPECIFICATION = 
    prove_thm
    (`GSPECIFICATION`,
     "!f. !v:*. v IN (GSPEC f) = ?x:**. v,T = f x",
     REPEAT GEN_TAC THEN
     REWRITE_TAC [GSPEC_DEF;SPECIFICATION] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REFL_TAC);;

% --------------------------------------------------------------------- %
% load generalized specification code.					%
% --------------------------------------------------------------------- %
loadt `gspec.ml`;;

% --------------------------------------------------------------------- %
% activate generalized specification parser/pretty-printer.		%
% --------------------------------------------------------------------- %
define_set_abstraction_syntax `GSPEC`;;
set_flag(`print_set`,true);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %

let lemma =
    TAC_PROOF
    (([], "!s x. x IN s ==>  !f:*->**. (f x) IN {f x | x IN s}"),
     REPEAT STRIP_TAC THEN CONV_TAC SET_SPEC_CONV THEN
     EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[]);;

let SET_MINIMUM = 
    prove_thm
    (`SET_MINIMUM`,
     "!s:(*)set. !M.
      (?x. x IN s) = ?x. x IN s /\ !y. y IN s ==> M x <= M y",
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [IMP_RES_THEN (ASSUME_TAC o ISPEC "M:*->num") lemma THEN
      let th = SET_SPEC_CONV "(n:num) IN {M x | (x:*) IN s}" in
      IMP_RES_THEN (STRIP_ASSUME_TAC o REWRITE_RULE [th]) NUM_SET_WOP THEN
      EXISTS_TAC "x':*" THEN CONJ_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM (SUBST_ALL_TAC o SYM) THEN
       REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
       EXISTS_TAC "y:*" THEN CONJ_TAC THENL
       [REFL_TAC; FIRST_ASSUM ACCEPT_TAC]];
      EXISTS_TAC "x:*" THEN FIRST_ASSUM ACCEPT_TAC]);;


% ===================================================================== %
% The empty set								%
% ===================================================================== %

let EMPTY_DEF = new_definition
    (`EMPTY_DEF`, "EMPTY = SPEC(\x:*.F)");;

let NOT_IN_EMPTY = 
    prove_thm
    (`NOT_IN_EMPTY`,
     "!x:*.~(x IN EMPTY)",
     PURE_REWRITE_TAC [EMPTY_DEF;SPECIFICATION] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC);;

let MEMBER_NOT_EMPTY = 
    prove_thm
    (`MEMBER_NOT_EMPTY`,
     "!s:(*)set. (?x. x IN s) = ~(s = EMPTY)",
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REWRITE_TAC [NOT_CLAUSES]);;

% ===================================================================== %
% The set of everything							%
% ===================================================================== %

let UNIV_DEF = new_definition
    (`UNIV_DEF`,"UNIV = SPEC(\x:*.T)");;

let IN_UNIV = 
    prove_thm
    (`IN_UNIV`,
     "!x:*. x IN UNIV",
     GEN_TAC THEN PURE_REWRITE_TAC [UNIV_DEF;SPECIFICATION] THEN
     CONV_TAC BETA_CONV THEN ACCEPT_TAC TRUTH);;

let UNIV_NOT_EMPTY = 
    prove_thm
    (`UNIV_NOT_EMPTY`,
     "~(UNIV:(*)set = EMPTY)",
     REWRITE_TAC [EXTENSION;IN_UNIV;NOT_IN_EMPTY]);;

let EMPTY_NOT_UNIV = 
    prove_thm
    (`EMPTY_NOT_UNIV`,
     "~(EMPTY = (UNIV:(*)set))",
     REWRITE_TAC [EXTENSION;IN_UNIV;NOT_IN_EMPTY]);;

let EQ_UNIV = 
    prove_thm
    (`EQ_UNIV`,
     "(!x:*. x IN s) = (s = UNIV)",
     REWRITE_TAC [EXTENSION;IN_UNIV]);;

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

let SUBSET_UNIV = 
    prove_thm
    (`SUBSET_UNIV`,
     "!s:(*)set. s SUBSET UNIV",
     REWRITE_TAC [SUBSET_DEF;IN_UNIV]);;

let UNIV_SUBSET = 
    prove_thm
    (`UNIV_SUBSET`,
     "!s:(*)set. UNIV SUBSET s = (s = UNIV)",
     REWRITE_TAC [SUBSET_DEF;IN_UNIV;EXTENSION]);;

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

let NOT_UNIV_PSUBSET = 
    prove_thm
    (`NOT_UNIV_PSUBSET`,
     "!s:(*)set. ~(UNIV PSUBSET s)",
     REWRITE_TAC [PSUBSET_DEF;UNIV_SUBSET;DE_MORGAN_THM] THEN
     GEN_TAC THEN CONV_TAC (RAND_CONV SYM_CONV) THEN
     PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
     MATCH_ACCEPT_TAC EXCLUDED_MIDDLE);;

let PSUBSET_UNIV = 
    prove_thm
    (`PSUBSET_UNIV`,
     "!s:(*)set. (s PSUBSET UNIV) = ?x:*. ~(x IN s)",
     REWRITE_TAC [PSUBSET_DEF;SUBSET_UNIV;EXTENSION;IN_UNIV] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN GEN_TAC THEN REFL_TAC);;

% ===================================================================== %
% Union									%
% ===================================================================== %

let UNION_DEF = new_infix_definition
     (`UNION_DEF`, "UNION s t = {x:* | x IN s \/ x IN t}");;

let IN_UNION = prove_thm
     (`IN_UNION`,
      "!s t (x:*). x IN (s UNION t) = x IN s \/ x IN t",
      PURE_ONCE_REWRITE_TAC [UNION_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);;

let UNION_ASSOC = prove_thm
    (`UNION_ASSOC`,
     "!(s:(*)set) t u. (s UNION t) UNION u = s UNION (t UNION u)",
     REWRITE_TAC [EXTENSION; IN_UNION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC[]);;

let UNION_IDEMPOT = prove_thm
    (`UNION_IDEMPOT`,
     "!(s:(*)set). s UNION s = s",
     REWRITE_TAC[EXTENSION; IN_UNION]);;

let UNION_COMM = prove_thm
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

let UNION_UNIV = 
    prove_thm
    (`UNION_UNIV`,
     "(!s:(*)set. UNIV UNION s = UNIV) /\
      (!s:(*)set. s UNION UNIV = UNIV)",
     REWRITE_TAC [IN_UNION;EXTENSION;IN_UNIV]);;

let EMPTY_UNION = 
    prove_thm
    (`EMPTY_UNION`,
     "!s:(*)set. !t. (s UNION t = EMPTY) = ((s = EMPTY) /\ (t = EMPTY))",
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY;IN_UNION;DE_MORGAN_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN RES_TAC);;

% ===================================================================== %
% Intersection								%
% ===================================================================== %

let INTER_DEF = new_infix_definition
     (`INTER_DEF`,
      "INTER s t = {x:* | x IN s /\ x IN t}");;

let IN_INTER = prove_thm
     (`IN_INTER`,
      "!s t (x:*). x IN (s INTER t) = x IN s /\ x IN t",
      PURE_ONCE_REWRITE_TAC [INTER_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);;

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

let INTER_UNIV = 
    prove_thm
    (`INTER_UNIV`,
     "(!s:(*)set. UNIV INTER s = s) /\
      (!s:(*)set. s INTER UNIV = s)",
     REWRITE_TAC [IN_INTER;EXTENSION;IN_UNIV]);;


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
 
let DIFF_DEF = new_infix_definition
    (`DIFF_DEF`,
     "DIFF s t = {x:* | x IN s /\ ~ x IN t}");;

let IN_DIFF = prove_thm
    (`IN_DIFF`,
     "!(s:(*)set) t x. x IN (s DIFF t) = x IN s /\ ~x IN t",
     REPEAT GEN_TAC THEN
     PURE_ONCE_REWRITE_TAC [DIFF_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
     REFL_TAC);;

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

let DIFF_UNIV = 
    prove_thm
    (`DIFF_UNIV`,
     "!s:(*)set. s DIFF UNIV = EMPTY",
     GEN_TAC THEN
     REWRITE_TAC [NOT_IN_EMPTY;IN_DIFF;IN_UNIV;EXTENSION]);;

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
% The insertion function.					        %
% ===================================================================== %

let INSERT_DEF = 
    new_infix_definition
    (`INSERT_DEF`, "INSERT (x:*) s = {y | (y = x) \/ y IN s}");;

% --------------------------------------------------------------------- %
% Set up the {x1,...,xn} notation.					%
% --------------------------------------------------------------------- %
define_finite_set_syntax(`EMPTY`,`INSERT`);;

% --------------------------------------------------------------------- %
% Theorems about INSERT.						%
% --------------------------------------------------------------------- %

let IN_INSERT = 
     prove_thm
     (`IN_INSERT`,
      "!x:*. !y s. x IN (y INSERT s) = ((x=y) \/ x IN s)",
      PURE_ONCE_REWRITE_TAC [INSERT_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);;

let COMPONENT = 
     prove_thm
     (`COMPONENT`,
      "!x:*. !s. x IN (x INSERT s)",
      REWRITE_TAC [IN_INSERT]);;

let SET_CASES = 
    prove_thm
    (`SET_CASES`,
     "!s:(*)set. (s = EMPTY) \/ ?x:*. ?t. ((s = x INSERT t) /\ ~x IN t)",
     REWRITE_TAC [EXTENSION;NOT_IN_EMPTY] THEN GEN_TAC THEN
     DISJ_CASES_THEN MP_TAC (SPEC "?x:*. x IN s" EXCLUDED_MIDDLE) THENL
     [STRIP_TAC THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC ["x:*";"{y:* | y IN s /\ ~(y = x)}"] THEN
      REWRITE_TAC [IN_INSERT] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      ASM_REWRITE_TAC[EXCLUDED_MIDDLE];
      CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      STRIP_TAC THEN DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let DECOMPOSITION = 
    prove_thm
    (`DECOMPOSITION`,
     "!s:(*)set. !x. x IN s = ?t. (s = x INSERT t) /\ ~x IN t",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC "{y:* | y IN s /\ ~(y = x)}" THEN
      ASM_REWRITE_TAC [EXTENSION;IN_INSERT] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REWRITE_TAC [] THEN 
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
      ASM_REWRITE_TAC [EXCLUDED_MIDDLE];
      STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT]]);;

let ABSORPTION =
    prove_thm
    (`ABSORPTION`,
     "!x:*. !s. (x IN s) = (x INSERT s = s)",
     REWRITE_TAC [EXTENSION;IN_INSERT] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     ASM_REWRITE_TAC [] THEN
     FIRST_ASSUM (\th g. PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL th)] g) THEN
     DISJ1_TAC THEN REFL_TAC);;

let INSERT_INSERT = 
    prove_thm
    (`INSERT_INSERT`,
     "!x:*. !s. x INSERT (x INSERT s) = x INSERT s",
     REWRITE_TAC [IN_INSERT;EXTENSION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN 
     ASM_REWRITE_TAC[]);;

let INSERT_COMM = 
    prove_thm
    (`INSERT_COMM`,
     "!x:*. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)",
     REWRITE_TAC [IN_INSERT;EXTENSION] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN 
     ASM_REWRITE_TAC[]);;

let INSERT_UNIV = 
    prove_thm
    (`INSERT_UNIV`,
     "!x:*. x INSERT UNIV = UNIV",
     REWRITE_TAC [EXTENSION;IN_INSERT;IN_UNIV]);;

let NOT_INSERT_EMPTY = 
    prove_thm
    (`NOT_INSERT_EMPTY`,
     "!x:*. !s. ~(x INSERT s = EMPTY)",
     REWRITE_TAC [EXTENSION;IN_INSERT;NOT_IN_EMPTY;IN_UNION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REPEAT GEN_TAC THEN EXISTS_TAC "x:*" THEN 
     REWRITE_TAC []);;

let NOT_EMPTY_INSERT = 
    prove_thm
    (`NOT_EMPTY_INSERT`,
     "!x:*. !s. ~(EMPTY = x INSERT s)",
     REWRITE_TAC [EXTENSION;IN_INSERT;NOT_IN_EMPTY;IN_UNION] THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
     REPEAT GEN_TAC THEN EXISTS_TAC "x:*" THEN 
     REWRITE_TAC []);;

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

let INSERT_DIFF = 
    prove_thm
    (`INSERT_DIFF`,
     "!s t. !x:*. (x INSERT s) DIFF t = 
     		  (x IN t => s DIFF t | (x INSERT (s DIFF t)))",
     REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [EXTENSION;IN_DIFF;IN_INSERT] THEN
      GEN_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN 
       FIRST_ASSUM (\th g. SUBST_ALL_TAC th g) THEN RES_TAC;
       STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC [EXTENSION;IN_DIFF;IN_INSERT] THEN
      REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC [] THENL
      [FIRST_ASSUM (\th g. SUBST_ALL_TAC th g) THEN RES_TAC;RES_TAC]]);;

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

let IMAGE_DEF =
    new_definition
    (`IMAGE_DEF`, "IMAGE (f:*->**) s = {f x | x IN s}");;

let IN_IMAGE = 
    prove_thm
    (`IN_IMAGE`,
     "!y:**. !s f. (y IN (IMAGE f s)) = ?x:*. (y = f x) /\ x IN s",
      PURE_ONCE_REWRITE_TAC [IMAGE_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REPEAT GEN_TAC THEN REFL_TAC);;

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
% Finiteness								%
% ===================================================================== %

let FINITE_DEF = 
    new_definition
    (`FINITE_DEF`,
     "!s:(*)set.
      FINITE s = 
      !P. (P EMPTY /\ (!s. P s ==> !e. P (e INSERT s))) ==> P s");;

let FINITE_EMPTY = 
    prove_thm
    (`FINITE_EMPTY`,
     "FINITE (EMPTY:(*)set)",
     PURE_ONCE_REWRITE_TAC [FINITE_DEF] THEN
     REPEAT STRIP_TAC);;

let FINITE_INSERT = 
    TAC_PROOF
    (([], "!s. FINITE s ==> !x:*. FINITE (x INSERT s)"),
     PURE_ONCE_REWRITE_TAC [FINITE_DEF] THEN
     REPEAT STRIP_TAC THEN SPEC_TAC ("x:*","x:*") THEN
     REPEAT (FIRST_ASSUM MATCH_MP_TAC) THEN
     CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let SIMPLE_FINITE_INDUCT = 
    TAC_PROOF
    (([], "!P. P EMPTY /\ (!s. P s ==> (!e:*. P(e INSERT s)))
                ==>
               !s. FINITE s ==> P s"),
     GEN_TAC THEN STRIP_TAC THEN
     PURE_ONCE_REWRITE_TAC [FINITE_DEF] THEN
     GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []);;

let lemma = 
    let tac = ASM_CASES_TAC "P:bool" THEN ASM_REWRITE_TAC[] in
    let lem = TAC_PROOF(([],"(P ==> P /\ Q) = (P ==> Q)"), tac) in
    let th1 = SPEC "\s:(*)set. FINITE s /\ P s" SIMPLE_FINITE_INDUCT in
        REWRITE_RULE [lem;FINITE_EMPTY] (BETA_RULE th1);;

let FINITE_INDUCT = 
    prove_thm
    (`FINITE_INDUCT`,
     "!P. P EMPTY /\ (!s. FINITE s /\ P s ==> (!e. ~e IN s ==> P(e INSERT s)))
         ==>
        !s:(*)set. FINITE s ==> P s",
     GEN_TAC THEN STRIP_TAC THEN
     MATCH_MP_TAC lemma THEN 
     ASM_REWRITE_TAC [] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT;
      ASM_CASES_TAC "(e:*) IN s" THENL
      [IMP_RES_THEN SUBST1_TAC ABSORPTION; RES_TAC] THEN
      ASM_REWRITE_TAC []]);;

% --------------------------------------------------------------------- %
% Load the set induction tactic in... uncompiled.			%
% --------------------------------------------------------------------- %

loadt `set_ind`;;

let FINITE_DELETE = 
    TAC_PROOF
    (([], "!s. FINITE s ==> (!x:*. FINITE(s DELETE x))"),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DELETE;FINITE_EMPTY];
      PURE_ONCE_REWRITE_TAC [DELETE_INSERT] THEN
      REPEAT STRIP_TAC THEN
      COND_CASES_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC;
       FIRST_ASSUM (\th g. ASSUME_TAC (SPEC "x:*" th) g) THEN
       IMP_RES_TAC FINITE_INSERT THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

let INSERT_FINITE = 
    TAC_PROOF
    (([], "!x:*. !s. FINITE(x INSERT s) ==> FINITE s"),
     REPEAT GEN_TAC THEN ASM_CASES_TAC "(x:*) IN s" THENL
     [IMP_RES_TAC ABSORPTION THEN ASM_REWRITE_TAC [];
      DISCH_THEN (MP_TAC o SPEC "x:*" o  MATCH_MP FINITE_DELETE) THEN
      REWRITE_TAC [DELETE_INSERT] THEN
      IMP_RES_TAC DELETE_NON_ELEMENT THEN ASM_REWRITE_TAC[]]);;

let FINITE_INSERT = 
    prove_thm
    (`FINITE_INSERT`,
     "!x:*. !s. FINITE(x INSERT s) = FINITE s",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [MATCH_ACCEPT_TAC INSERT_FINITE; 
      DISCH_THEN (MATCH_ACCEPT_TAC o MATCH_MP FINITE_INSERT)]);;

let DELETE_FINITE = 
    TAC_PROOF
    (([], "!x:*. !s. FINITE (s DELETE x) ==> FINITE s"),
     REPEAT GEN_TAC THEN ASM_CASES_TAC "(x:*) IN s" THEN
     DISCH_TAC THENL
     [IMP_RES_THEN (SUBST1_TAC o SYM) INSERT_DELETE THEN
      ASM_REWRITE_TAC [FINITE_INSERT];
      IMP_RES_THEN (SUBST1_TAC o SYM) DELETE_NON_ELEMENT THEN
      FIRST_ASSUM ACCEPT_TAC]);;


let FINITE_DELETE = 
    prove_thm
    (`FINITE_DELETE`,
     "!x:*. !s. FINITE(s DELETE x) = FINITE s",
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [MATCH_ACCEPT_TAC DELETE_FINITE; 
      DISCH_THEN (MATCH_ACCEPT_TAC o MATCH_MP FINITE_DELETE)]);;

let UNION_FINITE = 
    TAC_PROOF
    (([], "!s:(*)set. FINITE s ==> !t. FINITE t ==> FINITE (s UNION t)"),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [UNION_EMPTY];
      SET_INDUCT_TAC THENL
      [IMP_RES_TAC FINITE_INSERT THEN ASM_REWRITE_TAC [UNION_EMPTY];
       SUBST1_TAC (SPECL ["s':(*)set";"e':*"] INSERT_SING_UNION) THEN
       PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL UNION_ASSOC)] THEN
       PURE_REWRITE_TAC [SPECL ["s:(*)set";"{x:*}"] UNION_COMM] THEN
       PURE_REWRITE_TAC [UNION_ASSOC; SYM(SPEC_ALL INSERT_SING_UNION)] THEN
       IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT]]);;

let FINITE_UNION_LEMMA = 
    TAC_PROOF
    (([], "!s:(*)set. FINITE s ==> !t. FINITE (s UNION t) ==> FINITE t"),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [UNION_EMPTY];
      GEN_TAC THEN ASM_REWRITE_TAC [INSERT_UNION] THEN
      COND_CASES_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC;
       DISCH_THEN (MP_TAC o MATCH_MP INSERT_FINITE) THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

let FINITE_UNION = 
    TAC_PROOF
    (([], "!s:(*)set. !t. FINITE(s UNION t) ==> (FINITE s /\ FINITE t)"),
     REPEAT STRIP_TAC THEN 
     IMP_RES_THEN MATCH_MP_TAC FINITE_UNION_LEMMA THENL
     [SUBST1_TAC (SPECL ["s:(*)set";"t:(*)set"] UNION_COMM) THEN
      REWRITE_TAC [UNION_ASSOC;UNION_IDEMPOT] THEN
      PURE_ONCE_REWRITE_TAC [UNION_COMM] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC [UNION_ASSOC;UNION_IDEMPOT]]);;

let FINITE_UNION = 
    prove_thm
    (`FINITE_UNION`,
     "!s:(*)set. !t. FINITE(s UNION t) = (FINITE s /\ FINITE t)",
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN IMP_RES_TAC FINITE_UNION;
      REPEAT STRIP_TAC THEN IMP_RES_TAC UNION_FINITE]);;

let INTER_FINITE = 
    prove_thm
    (`INTER_FINITE`,
     "!s:(*)set. FINITE s ==> !t. FINITE (s INTER t)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [INTER_EMPTY;FINITE_EMPTY];
      REWRITE_TAC [INSERT_INTER] THEN GEN_TAC THEN
      COND_CASES_TAC THENL
      [FIRST_ASSUM (\th g. ASSUME_TAC (SPEC "t:(*)set" th) g ? NO_TAC g) THEN
       IMP_RES_TAC FINITE_INSERT THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC;
       FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

let SUBSET_FINITE = 
    prove_thm
    (`SUBSET_FINITE`,
     "!s:(*)set. FINITE s ==> (!t. t SUBSET s ==> FINITE t)",
     SET_INDUCT_TAC THENL
     [PURE_ONCE_REWRITE_TAC [SUBSET_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [FINITE_EMPTY];
      GEN_TAC THEN ASM_CASES_TAC "(e:*) IN t" THENL
      [REWRITE_TAC [SUBSET_INSERT_DELETE] THEN
       STRIP_TAC THEN RES_TAC THEN IMP_RES_TAC DELETE_FINITE;
       IMP_RES_TAC SUBSET_INSERT THEN ASM_REWRITE_TAC []]]);;

let PSUBSET_FINITE = 
    prove_thm
    (`PSUBSET_FINITE`,
     "!s:(*)set. FINITE s ==> (!t. t PSUBSET s ==> FINITE t)",
     PURE_ONCE_REWRITE_TAC [PSUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC SUBSET_FINITE);;

let FINITE_DIFF = 
    prove_thm
    (`FINITE_DIFF`,
     "!s:(*)set. FINITE s ==> !t. FINITE(s DIFF t)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DIFF;FINITE_EMPTY];
      ASM_REWRITE_TAC [INSERT_DIFF] THEN 
      GEN_TAC THEN COND_CASES_TAC THENL
      [FIRST_ASSUM MATCH_ACCEPT_TAC;
       FIRST_ASSUM (\th g. ASSUME_TAC (SPEC "t:(*)set" th) g) THEN
       IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT]]);;

let FINITE_SING = 
    prove_thm
    (`FINITE_SING`,
     "!x:*. FINITE {x}",
     GEN_TAC THEN MP_TAC FINITE_EMPTY THEN
     SUBST1_TAC (SYM (SPEC "x:*" SING_DELETE)) THEN
     DISCH_TAC THEN IMP_RES_THEN MATCH_ACCEPT_TAC FINITE_INSERT);;

let SING_FINITE = 
    prove_thm
    (`SING_FINITE`,
     "!s:(*)set. SING s ==> FINITE s",
     PURE_ONCE_REWRITE_TAC [SING_DEF] THEN
     GEN_TAC THEN DISCH_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
     MATCH_ACCEPT_TAC FINITE_SING);;

let IMAGE_FINITE =
    prove_thm
    (`IMAGE_FINITE`,
     "!s. FINITE s ==> !f:*->**. FINITE(IMAGE f s)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [IMAGE_EMPTY;FINITE_EMPTY];
      ASM_REWRITE_TAC [IMAGE_INSERT;FINITE_INSERT]]);;

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
    ((conjuncts card_rel_def, "!s:(*)set. FINITE s ==> ?n:num. R s n"),
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
     "!m s. FINITE s ==> (((@n:num. R (s:(*)set) n) = m) = R s m)"),
     REPEAT STRIP_TAC THEN 
     IMP_RES_TAC CARD_REL_EXISTS_LEMMA THEN 
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
           (!s. FINITE s ==> 
                !x:*. CARD(x INSERT s) = (x IN s => CARD s | SUC(CARD s)))"),
     STRIP_ASSUME_TAC CARD_REL_EXISTS THEN
     EXISTS_TAC "\s:(*)set. @n:num. R s n" THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [ASSUME_TAC FINITE_EMPTY THEN IMP_RES_TAC CARD_REL_THM THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [];
      REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
      [IMP_RES_THEN SUBST1_TAC ABSORPTION THEN REFL_TAC; 
       IMP_RES_THEN (ASSUME_TAC o SPEC "x:*") FINITE_INSERT THEN
       IMP_RES_THEN (TRY o MATCH_MP_TAC) CARD_REL_THM THEN
       ASM_REWRITE_TAC [] THEN EXISTS_TAC "x:*" THEN
       IMP_RES_TAC DELETE_NON_ELEMENT THEN
       ASM_REWRITE_TAC [IN_INSERT;DELETE_INSERT] THEN
       CONV_TAC SELECT_CONV THEN
       IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) CARD_REL_EXISTS_LEMMA]]);;

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
     "!s:(*)set. FINITE s ==> ((CARD s = 0) = (s = EMPTY))",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [CARD_EMPTY];
      IMP_RES_TAC CARD_INSERT THEN
      ASM_REWRITE_TAC [NOT_INSERT_EMPTY;NOT_SUC]]);;
      
let CARD_DELETE = 
    prove_thm
    (`CARD_DELETE`,
     "!s. FINITE s ==> 
          !x:*. CARD(s DELETE x) = (x IN s => (CARD s) - 1 | CARD s)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [EMPTY_DELETE;NOT_IN_EMPTY];
      PURE_REWRITE_TAC [DELETE_INSERT;IN_INSERT] THEN
      REPEAT GEN_TAC THEN ASM_CASES_TAC "x:* = e" THENL
      [IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [SUC_SUB1];
       SUBST1_TAC (SPECL ["e:*";"x:*"] EQ_SYM_EQ) THEN
       IMP_RES_THEN (ASSUME_TAC o SPEC "x:*") FINITE_DELETE THEN
       IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [IN_DELETE;SUC_SUB1] THEN
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
     "!s:(*)set. FINITE s ==> !t. CARD (s INTER t) <= CARD s",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [CARD_DEF;INTER_EMPTY;LESS_EQ_REFL];
      PURE_ONCE_REWRITE_TAC [INSERT_INTER] THEN
      GEN_TAC THEN COND_CASES_TAC THENL
      [IMP_RES_THEN (ASSUME_TAC o SPEC "t:(*)set") INTER_FINITE THEN
       IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [IN_INTER;lemma1];
       IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [lemma2]]]);;

let CARD_UNION = 
    prove_thm
    (`CARD_UNION`,
     "!s:(*)set.
       FINITE s ==>
       !t. FINITE t ==>
           (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [UNION_EMPTY;INTER_EMPTY;CARD_DEF;ADD_CLAUSES];
      REPEAT STRIP_TAC THEN REWRITE_TAC [INSERT_UNION;INSERT_INTER] THEN 
      ASM_CASES_TAC "(e:*) IN t" THENL
      [IMP_RES_THEN (ASSUME_TAC o SPEC "t:(*)set") INTER_FINITE THEN
       IMP_RES_TAC CARD_DEF THEN RES_TAC THEN
       ASM_REWRITE_TAC [IN_INTER;ADD_CLAUSES];
       IMP_RES_TAC UNION_FINITE THEN
       IMP_RES_TAC CARD_DEF THEN RES_TAC THEN
       ASM_REWRITE_TAC [ADD_CLAUSES; INV_SUC_EQ; IN_UNION]]]);;

let lemma = 
    TAC_PROOF
    (([], "!n m. (n <= SUC m) = (n <= m \/ (n = SUC m))"),
     REWRITE_TAC [LESS_OR_EQ;LESS_THM] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[]);;

let CARD_SUBSET = 
    prove_thm
    (`CARD_SUBSET`,
     "!s:(*)set. FINITE s ==> (!t. t SUBSET s ==> (CARD t <= CARD s))",
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [SUBSET_EMPTY;CARD_EMPTY] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [CARD_DEF;LESS_EQ_REFL];

      IMP_RES_THEN (ASSUME_TAC o SPEC "e:*") FINITE_INSERT THEN
      IMP_RES_TAC CARD_INSERT THEN
      ASM_REWRITE_TAC [SUBSET_INSERT_DELETE] THEN
      REPEAT STRIP_TAC THEN RES_THEN MP_TAC THEN
      IMP_RES_TAC SUBSET_FINITE THEN
      IMP_RES_TAC DELETE_FINITE THEN
      IMP_RES_TAC CARD_DELETE THEN
      ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL
      [(let th = SPEC "CARD (t:(*)set)" num_CASES in
        REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC th) THENL
	[REWRITE_TAC [LESS_OR_EQ;LESS_0];
         REWRITE_TAC [SUC_SUB1;LESS_OR_EQ;LESS_MONO_EQ;INV_SUC_EQ]];
       STRIP_TAC THEN ASM_REWRITE_TAC [lemma]]]);;

let CARD_PSUBSET = 
    prove_thm
    (`CARD_PSUBSET`,
     "!s:(*)set. FINITE s ==> (!t. t PSUBSET s ==> (CARD t < CARD s))",
     REPEAT STRIP_TAC THEN IMP_RES_TAC PSUBSET_DEF THEN
     IMP_RES_THEN (IMP_RES_THEN MP_TAC) CARD_SUBSET THEN
     PURE_ONCE_REWRITE_TAC [LESS_OR_EQ] THEN 
     DISCH_THEN (STRIP_THM_THEN (\th g. ACCEPT_TAC th g ? MP_TAC th g)) THEN
     IMP_RES_THEN STRIP_ASSUME_TAC PSUBSET_INSERT_SUBSET THEN
     IMP_RES_THEN (IMP_RES_THEN MP_TAC) CARD_SUBSET THEN
     IMP_RES_TAC INSERT_SUBSET THEN 
     IMP_RES_TAC SUBSET_FINITE THEN
     IMP_RES_TAC CARD_INSERT THEN
     ASM_REWRITE_TAC [LESS_EQ] THEN
     REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let CARD_SING = 
    prove_thm
    (`CARD_SING`,
     "!x:*. CARD {x} = 1",
     CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
     GEN_TAC THEN ASSUME_TAC FINITE_EMPTY THEN
     IMP_RES_THEN (ASSUME_TAC o SPEC "x:*") FINITE_INSERT THEN
     IMP_RES_TAC CARD_DEF THEN ASM_REWRITE_TAC [NOT_IN_EMPTY;CARD_DEF]);;

let SING_IFF_CARD1 = 
    prove_thm
    (`SING_IFF_CARD1`,
     "!s:(*)set. (SING s) = ((CARD s = 1) /\ (FINITE s))",
     REWRITE_TAC [SING_DEF;num_CONV "1"] THEN 
     GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
      CONJ_TAC THENL
      [ASSUME_TAC FINITE_EMPTY THEN
       IMP_RES_TAC CARD_INSERT THEN 
       ASM_REWRITE_TAC [CARD_EMPTY;NOT_IN_EMPTY];
       REWRITE_TAC [FINITE_INSERT;FINITE_EMPTY]];
      STRIP_ASSUME_TAC (SPEC "s:(*)set" SET_CASES) THENL
      [ASM_REWRITE_TAC [CARD_EMPTY;NOT_EQ_SYM(SPEC_ALL NOT_SUC)];
       ASM_REWRITE_TAC [FINITE_INSERT] THEN
       DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
       IMP_RES_TAC CARD_INSERT THEN
       IMP_RES_TAC CARD_EQ_0 THEN
       ASM_REWRITE_TAC [INV_SUC_EQ] THEN
       DISCH_TAC THEN EXISTS_TAC "x:*" THEN
       ASM_REWRITE_TAC []]]);;

% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let CARD_DIFF =
    prove_thm
    (`CARD_DIFF`,
     "!t:(*)set. FINITE t ==>
      !s:(*)set. FINITE s ==>
                 (CARD (s DIFF t) = (CARD s - CARD (s INTER t)))",
     SET_INDUCT_TAC THEN REPEAT STRIP_TAC THENL
     [REWRITE_TAC [DIFF_EMPTY;INTER_EMPTY;CARD_EMPTY;SUB_0];
      PURE_ONCE_REWRITE_TAC [INTER_COMM] THEN
      PURE_ONCE_REWRITE_TAC [INSERT_INTER] THEN
      COND_CASES_TAC THENL
      [let th = SPEC "s':(*)set" (UNDISCH (SPEC "s:(*)set" INTER_FINITE)) in
       PURE_ONCE_REWRITE_TAC [MATCH_MP CARD_INSERT th] THEN
       IMP_RES_THEN (ASSUME_TAC o SPEC "e:*") FINITE_DELETE THEN
       IMP_RES_TAC CARD_DELETE THEN
       RES_TAC THEN ASM_REWRITE_TAC [IN_INTER;DIFF_INSERT] THEN
       PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL SUB_PLUS)] THEN
       REWRITE_TAC [num_CONV "1";ADD_CLAUSES;DELETE_INTER] THEN
       MP_TAC (SPECL ["s':(*)set";"s:(*)set";"e:*"] IN_INTER) THEN
       ASM_REWRITE_TAC [DELETE_NON_ELEMENT] THEN
       DISCH_THEN SUBST1_TAC THEN
       SUBST1_TAC (SPECL ["s:(*)set";"s':(*)set"] INTER_COMM) THEN REFL_TAC;
       IMP_RES_TAC DELETE_NON_ELEMENT THEN
       PURE_ONCE_REWRITE_TAC [INTER_COMM] THEN
       RES_TAC THEN ASM_REWRITE_TAC [DIFF_INSERT]]]);;


% --------------------------------------------------------------------- %
% A theorem from homeier@org.aero.uniblab (Peter Homeier)		%
% --------------------------------------------------------------------- %
let LESS_CARD_DIFF =
    prove_thm
    (`LESS_CARD_DIFF`,
     "!t:(*)set. FINITE t ==>
      !s. FINITE s ==> (CARD t < CARD s) ==> (0 < CARD(s DIFF t))",
     REPEAT STRIP_TAC THEN
     REPEAT_GTCL IMP_RES_THEN SUBST1_TAC CARD_DIFF THEN
     PURE_REWRITE_TAC [GSYM SUB_LESS_0] THEN
     let th1 = UNDISCH (SPEC "s:(*)set" CARD_INTER_LESS_EQ) in
     let th2 = SPEC "t:(*)set" (PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] th1) in
     DISJ_CASES_THEN2 ACCEPT_TAC (SUBST_ALL_TAC o SYM) th2 THEN
     let th3 = SPEC "s:(*)set" (UNDISCH(SPEC "t:(*)set" CARD_INTER_LESS_EQ)) in
     let th4 = PURE_ONCE_REWRITE_RULE [INTER_COMM] th3 in
     IMP_RES_TAC (PURE_ONCE_REWRITE_RULE [GSYM NOT_LESS] th4));;

% ===================================================================== %
% Infiniteness								%
% ===================================================================== %

let INFINITE_DEF = 
    new_definition (`INFINITE_DEF`, "!s:(*)set. INFINITE s = ~(FINITE s)");;

let NOT_IN_FINITE = 
    prove_thm
    (`NOT_IN_FINITE`,
     "INFINITE (UNIV:(*)set) = !s:(*)set. FINITE s ==> ?x. ~ (x IN s)",
     PURE_ONCE_REWRITE_TAC [INFINITE_DEF] THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN
      CONV_TAC (ONCE_DEPTH_CONV NOT_FORALL_CONV) THEN
      REWRITE_TAC [NOT_IMP] THEN
      CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
      REWRITE_TAC [EQ_UNIV] THEN 
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [];
      REPEAT STRIP_TAC THEN RES_THEN STRIP_ASSUME_TAC THEN
      ASSUME_TAC (SPEC "x:*" IN_UNIV) THEN RES_TAC]);;

let INVERSE_LEMMA = 
    TAC_PROOF
    (([], "!f:*->**. (!x y. (f x = f y) ==> (x = y)) ==>
                     ((\x:**. @y:*. x = f y) o f = \x:*.x)"),
     REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN
     PURE_ONCE_REWRITE_TAC [o_THM] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
     EXISTS_TAC "x:*" THEN REFL_TAC);;

let IMAGE_11_INFINITE = 
    prove_thm
    (`IMAGE_11_INFINITE`,
     "!f:*->**. (!x y. (f x = f y) ==> (x = y)) ==>
      !s:(*)set. INFINITE s ==> INFINITE (IMAGE f s)",
     GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
     CONV_TAC CONTRAPOS_CONV THEN
     REWRITE_TAC [INFINITE_DEF] THEN STRIP_TAC THEN 
     let thm = INST_TYPE [":*",":**";":**",":*"] IMAGE_FINITE in
     IMP_RES_THEN (MP_TAC o ISPEC "\x:**.@y:*.x=f y") thm THEN
     REWRITE_TAC [SYM(SPEC_ALL IMAGE_COMPOSE)] THEN
     IMP_RES_TAC INVERSE_LEMMA THEN
     ASM_REWRITE_TAC [IMAGE_ID]);;

let INFINITE_SUBSET = 
    prove_thm
    (`INFINITE_SUBSET`,
     "!s:(*)set. INFINITE s ==> (!t. s SUBSET t ==> INFINITE t)",
     PURE_ONCE_REWRITE_TAC [INFINITE_DEF] THEN 
     REPEAT STRIP_TAC THEN IMP_RES_TAC SUBSET_FINITE THEN RES_TAC);;

let IN_INFINITE_NOT_FINITE = 
    prove_thm
    (`IN_INFINITE_NOT_FINITE`,
     "!s t. (INFINITE s /\ FINITE t) ==> ?x:*. x IN s /\ ~x IN t",
     CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV) THEN
     CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN 
     PURE_ONCE_REWRITE_TAC [DE_MORGAN_THM] THEN
     REWRITE_TAC [SYM(SPEC_ALL IMP_DISJ_THM)] THEN
     PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL SUBSET_DEF)] THEN
     PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL INFINITE_DEF)] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC INFINITE_SUBSET);;

% --------------------------------------------------------------------- %
% The next series of lemmas are used for proving that if UNIV:(*)set is %
% INFINITE then :* satisfies an axiom of infinity.			%
%									%
% The function g:num->(*)set defines a series of sets:			%
%									%
%    {}, {x1}, {x1,x2}, {x1,x2,x3},...					%
%									%
% and one then defines an f:*->* such that f(xi)=xi+1.			%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Defining equations for g.						%
% --------------------------------------------------------------------- %

let gdef = 
    ["g 0 = ({}:(*)set)"; "!n. g(SUC n) = (@x:*.~ x IN (g n)) INSERT (g n)"];;

% --------------------------------------------------------------------- %
% Lemma: g n is finite for all n.					%
% --------------------------------------------------------------------- %

let g_finite = 
    TAC_PROOF
    ((gdef, "!n:num. FINITE (g n:(*)set)"),
     INDUCT_TAC THEN ASM_REWRITE_TAC[FINITE_EMPTY;FINITE_INSERT]);;

% --------------------------------------------------------------------- %
% Lemma: g n is contained in g (n+i) for all i.				%
% --------------------------------------------------------------------- %

let g_subset = 
    TAC_PROOF
    ((gdef, "!n. !x:*. x IN (g n) ==> !i. x IN (g (n+i))"),
     REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [ADD_CLAUSES;IN_INSERT]);;

% --------------------------------------------------------------------- %
% Lemma: if x is in g(n) then {x} = g(n+1)-g(n) for some n.		%
% --------------------------------------------------------------------- %

let lemma = 
    TAC_PROOF(([], "((A \/ B) /\ ~B) = (A /\ ~B)"),
              BOOL_CASES_TAC "B:bool" THEN REWRITE_TAC[]);;

let g_cases = 
    TAC_PROOF
    ((gdef, "(!s. FINITE s ==> ?x:*. ~(x IN s)) ==>
    	      !x:*. (?n. x IN (g n)) ==> 
	            (?m. (x IN (g (SUC m))) /\ ~(x IN (g m)))"),
     DISCH_TAC THEN GEN_TAC THEN
     DISCH_THEN (STRIP_THM_THEN MP_TAC o CONV_RULE EXISTS_LEAST_CONV) THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN
     ASM_REWRITE_TAC [NOT_IN_EMPTY;IN_INSERT] THEN STRIP_TAC THENL
     [REWRITE_TAC [lemma] THEN EXISTS_TAC "n':num" THEN
      CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST_ASSUM (\th g. SUBST1_TAC th g) THEN
      CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_ACCEPT_TAC g_finite;
      REWRITE_TAC [lemma] THEN
      FIRST_ASSUM (\th g. MP_TAC (SPEC "n':num" th) g) THEN
      REWRITE_TAC [LESS_SUC_REFL] THEN
      DISCH_THEN IMP_RES_TAC]);;

% --------------------------------------------------------------------- %
% Lemma: @x.~(x IN {}) is an element of every g(n+1).			%
% --------------------------------------------------------------------- %

let z_in_g1 = 
    TAC_PROOF
    ((gdef, "(@x:*.~x IN {}) IN (g (SUC 0))"),
     ASM_REWRITE_TAC [NOT_IN_EMPTY;IN_INSERT]);;

let z_in_gn = 
    TAC_PROOF
    ((gdef, "!n:num. (@x:*.~x IN {}) IN (g (SUC n))"),
     PURE_ONCE_REWRITE_TAC [ADD1] THEN
     PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN 
     MATCH_MP_TAC g_subset THEN
     REWRITE_TAC [num_CONV "1";z_in_g1]);;

% --------------------------------------------------------------------- %
% Lemma: @x.~(x IN g n) is an element of g(n+1).			%
% --------------------------------------------------------------------- %

let in_lemma = 
    TAC_PROOF
    ((gdef, "!n:num. (@x:*. ~(x IN (g n))) IN (g(SUC n))"),
     ASM_REWRITE_TAC [IN_INSERT]);;

% --------------------------------------------------------------------- %
% Lemma: the x added to g(n+1) is not in g(n)				%
% --------------------------------------------------------------------- %

let not_in_lemma = 
    TAC_PROOF
    ((gdef, "(!s. FINITE s ==> ?x:*. ~(x IN s)) ==>
	     !i. !n. ~(@x:*. ~(x IN (g (n+i)))) IN g n"),
     DISCH_TAC THEN INDUCT_TAC THENL
     [ASM_REWRITE_TAC [ADD_CLAUSES] THEN
      GEN_TAC THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN 
      MATCH_ACCEPT_TAC g_finite;
      PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN
      GEN_TAC THEN FIRST_ASSUM (\th g. MP_TAC(SPEC "SUC n" th) g) THEN
      REWRITE_TAC (map ASSUME gdef) THEN
      REWRITE_TAC [IN_INSERT;DE_MORGAN_THM] THEN
      REPEAT STRIP_TAC THEN RES_TAC]);;

% --------------------------------------------------------------------- %
% Lemma: each value is added to a unique g(n).				%
% --------------------------------------------------------------------- %

let less_lemma = 
    TAC_PROOF
    (([], "!m n. ~(m = n) = ((m < n) \/ (n < m))"),
      REPEAT GEN_TAC THEN ASM_CASES_TAC "n < m" THEN 
      ASM_REWRITE_TAC [] THENL
      [DISCH_THEN SUBST_ALL_TAC THEN IMP_RES_TAC LESS_REFL;
       IMP_RES_THEN MP_TAC NOT_LESS THEN
       REWRITE_TAC [LESS_OR_EQ] THEN STRIP_TAC THEN
       ASM_REWRITE_TAC[] THENL
       [IMP_RES_TAC LESS_NOT_EQ; MATCH_ACCEPT_TAC LESS_REFL]]);;

let gn_unique = 
    TAC_PROOF
    ((gdef, "(!s. FINITE s ==> ?x:*. ~(x IN s)) ==>
             !n:num. !m. ((@x:*.~ x IN (g n)) = @x:*.~(x IN (g m))) = (n=m)"),
     DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN 
      REWRITE_TAC [less_lemma] THEN 
      DISCH_THEN (STRIP_THM_THEN MP_TAC) THEN
      DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [num_CONV "1";ADD_CLAUSES] THEN
      REWRITE_TAC [SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN
      IMP_RES_TAC not_in_lemma THEN
      DISCH_TAC THENL
      [MP_TAC (SPEC "n:num" in_lemma) THEN
       EVERY_ASSUM (\th g. SUBST1_TAC th g ? ALL_TAC g) THEN
       DISCH_TAC THEN RES_TAC;
       MP_TAC (SPEC "m:num" in_lemma) THEN
       EVERY_ASSUM (\th g. SUBST1_TAC (SYM th) g ? ALL_TAC g) THEN
       DISCH_TAC THEN RES_TAC];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

% --------------------------------------------------------------------- %
% Lemma: the value added to g(n) to get g(n+1) a unique.		%
% --------------------------------------------------------------------- %

let x_unique = 
    TAC_PROOF
    ((gdef, "!n. !x. !y:*. 
	       (~(x IN g n) /\ ~(y IN g n)) ==>
	       (x IN g(SUC n)) ==> (y IN g(SUC n)) ==> (x = y)"),
     REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT] THEN
     REPEAT (DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

% --------------------------------------------------------------------- %
% Now, show the existence of a non-onto one-one fuction.  The required	%
% function is denoted by fdef.  The theorem cases is:			%
%									%
%   |- (?n. x IN (g n)) \/ (!n. ~x IN (g n))				%
%									%
% and is used to do case splits on the condition of the conditional 	%
% present in fdef.							%
% --------------------------------------------------------------------- %

let fdef = 
    "\x:*. (?n. (x IN (g n))) => 
           (@y.~(y IN (g (SUC @n. x IN g(SUC n) /\ ~ x IN (g n))))) | x";;

let cases = 
    let thm = GEN "x:*" (SPEC "?n:num.(x:*) IN (g n)" EXCLUDED_MIDDLE) in
        CONV_RULE (ONCE_DEPTH_CONV NOT_EXISTS_CONV) thm;;


let INF_IMP_INFINITY =
    TAC_PROOF
    (([],"(!s. FINITE s ==> ?x:*. ~(x IN s)) ==>
	  (?f:*->*. (!x y. (f x = f y) ==> (x=y)) /\ ?y. !x. ~(f x = y))"),
     let xcases = SPEC "x:*" cases and ycases = SPEC "y:*" cases in
     let nv x = "SUC(@n. ^x IN (g(SUC n)) /\ ~^x IN (g n))" in
     STRIP_ASSUME_TAC (prove_rec_fn_exists num_Axiom (list_mk_conj gdef)) THEN
     STRIP_TAC THEN EXISTS_TAC fdef THEN 
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      DISJ_CASES_THEN (\th. REWRITE_TAC[th] THEN
			    STRIP_ASSUME_TAC th) xcases THEN
      DISJ_CASES_THEN (\th. REWRITE_TAC[th] THEN
                            STRIP_ASSUME_TAC th) ycases THENL
      [REWRITE_TAC [UNDISCH gn_unique;INV_SUC_EQ] THEN
       IMP_RES_THEN (IMP_RES_THEN(STRIP_ASSUME_TAC o SELECT_RULE)) g_cases THEN
       DISCH_THEN SUBST_ALL_TAC THEN IMP_RES_TAC x_unique;
       ASSUME_TAC (SPEC (nv "x:*") in_lemma) THEN
       DISCH_THEN (SUBST_ALL_TAC o SYM) THEN RES_TAC;
       ASSUME_TAC (SPEC (nv "y:*") in_lemma) THEN
       DISCH_THEN SUBST_ALL_TAC THEN RES_TAC];
      EXISTS_TAC "@x:*.~(x IN g 0)" THEN GEN_TAC THEN
      DISJ_CASES_THEN (\th. REWRITE_TAC[th] THEN ASSUME_TAC th) xcases THENL
      [REWRITE_TAC [UNDISCH gn_unique;NOT_SUC];
       ASSUME_TAC (SPEC "n:num" z_in_gn) THEN 
       FIRST_ASSUM (\th g. SUBST1_TAC th g) THEN
       DISCH_THEN SUBST_ALL_TAC THEN RES_TAC]]);;

% --------------------------------------------------------------------- %
% We now also prove the converse, namely that if :* satisfies an axiom 	%
% of infinity then UNIV:(*)set is INFINITE.				%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% First, a version of the primitive recursion theorem			%
% --------------------------------------------------------------------- %

let prth = 
    prove_rec_fn_exists num_Axiom
    "(fn f x 0 = x) /\ 
     (fn f x (SUC n) = (f:*->*)(fn f x n))";;

let prmth = 
    TAC_PROOF
    (([], "!x:*. !f. ?fn. (fn 0 = x) /\ !n. fn (SUC n) = f(fn n)"),
     REPEAT GEN_TAC THEN STRIP_ASSUME_TAC prth THEN
     EXISTS_TAC "fn (f:*->*) (x:*) : num->*" THEN
     ASM_REWRITE_TAC []);;

% --------------------------------------------------------------------- %
% Lemma: if f is one-to-one and not onto, there is a one-one f:num->*.	%
% --------------------------------------------------------------------- %

let num_fn_thm = 
    TAC_PROOF
    (([],"(?f:*->*. (!x y. (f x = f y) ==> (x=y)) /\ ?y. !x. ~(f x = y))
          ==>
	  (?fn:num->*. (!n m. (fn n = fn m) ==> (n=m)))"),
     STRIP_TAC THEN STRIP_ASSUME_TAC (SPECL ["y:*";"f:*->*"] prmth) THEN
     EXISTS_TAC "fn:num->*" THEN INDUCT_TAC THENL
     [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN 
      INDUCT_TAC THEN ASM_REWRITE_TAC[];
      INDUCT_TAC THEN ASM_REWRITE_TAC [INV_SUC_EQ] THEN
      REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC]);;

% --------------------------------------------------------------------- %
% Lemma: every finite set of numbers has an upper bound.		%
% --------------------------------------------------------------------- %

let finite_N_bounded = 
    TAC_PROOF
    (([], "!s. FINITE s ==> ?m. !n. (n IN s) ==> n < m"),
     SET_INDUCT_TAC THENL
     [REWRITE_TAC [NOT_IN_EMPTY];
      FIRST_ASSUM (\th g. CHOOSE_THEN ASSUME_TAC th g) THEN
      EXISTS_TAC "(SUC m) + e" THEN REWRITE_TAC [IN_INSERT] THEN 
      REPEAT STRIP_TAC THENL
      [PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC [LESS_ADD_SUC];
       RES_TAC THEN IMP_RES_TAC LESS_IMP_LESS_ADD THEN
       let [_;_;c1;c2] = CONJUNCTS ADD_CLAUSES in
       ASM_REWRITE_TAC [c1;SYM c2]]]);;

% --------------------------------------------------------------------- %
% Lemma: UNIV:(num)set is infinite.					%
% --------------------------------------------------------------------- %

let N_lemma = 
    TAC_PROOF
    (([], "INFINITE(UNIV:(num)set)"),
     REWRITE_TAC [INFINITE_DEF] THEN STRIP_TAC THEN
     IMP_RES_THEN MP_TAC finite_N_bounded THEN
     REWRITE_TAC [IN_UNIV] THEN 
     CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN
     CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC "SUC m" THEN
     REWRITE_TAC [NOT_LESS;LESS_OR_EQ;LESS_SUC_REFL]);;

% --------------------------------------------------------------------- %
% Lemma: if s is finite, f:num->* is one-one, then ?n. f(n) not in s	%
% --------------------------------------------------------------------- %

let main_lemma = 
    TAC_PROOF
    (([], "!s:(*)set. FINITE s ==> 
           !f:num->*. (!n m. (f n = f m) ==> (n=m)) ==> ?n. ~(f n IN s)"),
     REPEAT STRIP_TAC THEN
     ASSUME_TAC N_lemma THEN
     IMP_RES_TAC IMAGE_11_INFINITE THEN
     IMP_RES_THEN (TRY o IMP_RES_THEN MP_TAC) IN_INFINITE_NOT_FINITE THEN
     REWRITE_TAC [IN_IMAGE;IN_UNIV] THEN
     REPEAT STRIP_TAC THEN EXISTS_TAC "x':num" THEN
     EVERY_ASSUM (\th g. SUBST1_TAC (SYM th) g ? ALL_TAC g) THEN
     FIRST_ASSUM ACCEPT_TAC);;

% --------------------------------------------------------------------- %
% Now show that we can always choose an element not in a finite set.	%
% --------------------------------------------------------------------- %

let INFINITY_IMP_INF =
    TAC_PROOF
    (([],"(?f:*->*. (!x y. (f x = f y) ==> (x=y)) /\ ?y. !x. ~(f x = y))
          ==> (!s. FINITE s ==> ?x:*. ~(x IN s))"),
     DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP num_fn_thm) THEN
     GEN_TAC THEN STRIP_TAC THEN 
     IMP_RES_TAC main_lemma THEN
     EXISTS_TAC "(fn:num->*) n" THEN 
     FIRST_ASSUM ACCEPT_TAC);;


% --------------------------------------------------------------------- %
% Finally, we can prove the desired theorem.				%
% --------------------------------------------------------------------- %

let INFINITE_UNIV =
    prove_thm
    (`INFINITE_UNIV`,
     "INFINITE (UNIV:(*)set) 
        =
      (?f:*->*. (!x y. (f x = f y) ==> (x = y)) /\ (?y. !x. ~(f x = y)))",
     PURE_ONCE_REWRITE_TAC [NOT_IN_FINITE] THEN
     ACCEPT_TAC (IMP_ANTISYM_RULE INF_IMP_INFINITY INFINITY_IMP_INF));;

let FINITE_PSUBSET_INFINITE = 
    prove_thm
    (`FINITE_PSUBSET_INFINITE`,
     "!s. INFINITE (s:(*)set) 
           = 
          !t. FINITE (t:(*)set) ==> ((t SUBSET s) ==> (t PSUBSET s))",
     PURE_REWRITE_TAC [INFINITE_DEF;PSUBSET_DEF] THEN
     GEN_TAC THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THENL
      [FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM (\th g. SUBST_ALL_TAC th g ? NO_TAC g) THEN RES_TAC];
      REPEAT STRIP_TAC THEN RES_TAC THEN
      ASSUME_TAC (SPEC "s:(*)set" SUBSET_REFL) THEN
      ASSUME_TAC (REFL "s:(*)set") THEN RES_TAC]);;

let FINITE_PSUBSET_UNIV = 
    prove_thm
    (`FINITE_PSUBSET_UNIV`,
     "INFINITE (UNIV:(*)set) = !s:(*)set. FINITE s ==> s PSUBSET UNIV",
     PURE_ONCE_REWRITE_TAC [FINITE_PSUBSET_INFINITE] THEN
     REWRITE_TAC [PSUBSET_DEF;SUBSET_UNIV]);;

let INFINITE_DIFF_FINITE = 
    prove_thm
    (`INFINITE_DIFF_FINITE`,
     "!s t. (INFINITE s /\ FINITE t) ==> ~(s DIFF t = ({}:(*)set))",
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     IMP_RES_TAC IN_INFINITE_NOT_FINITE THEN
     REWRITE_TAC [EXTENSION;IN_DIFF;NOT_IN_EMPTY] THEN
     CONV_TAC NOT_FORALL_CONV THEN
     EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[]);;


let FINITE_ISO_NUM =
    prove_thm
    (`FINITE_ISO_NUM`,
     "!s:(*)set.
       FINITE s ==>
       ?f. (!n m. (n < CARD s /\ m < CARD s) ==> (f n = f m) ==> (n = m)) /\
           (s = {f n | n < CARD s})",
     SET_INDUCT_TAC THENL
     [PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
      CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
      REWRITE_TAC [CARD_EMPTY;NOT_LESS_0;NOT_IN_EMPTY];
      FIRST_ASSUM (\th g. CHOOSE_THEN STRIP_ASSUME_TAC th g) THEN
      PURE_ONCE_REWRITE_TAC [UNDISCH (SPEC "s:(*)set" CARD_INSERT)] THEN
      FILTER_ASM_REWRITE_TAC is_neg [] THEN
      PURE_ONCE_REWRITE_TAC [LESS_THM] THEN
      EXISTS_TAC "\n. n < (CARD (s:(*)set)) => f n | (e:*)" THEN
      CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
      [REPEAT GEN_TAC THEN
       let ttac th g = SUBST_ALL_TAC th g ? ASSUME_TAC th g in
       DISCH_THEN (REPEAT_TCL STRIP_THM_THEN ttac) THENL
       [REPEAT STRIP_TAC THEN REFL_TAC;
        let is_less t = (fst(strip_comb t) = "<") ? false in
        FILTER_ASM_REWRITE_TAC is_less [LESS_REFL] THEN
        FIRST_ASSUM (\th g. MP_TAC (assert (is_eq o concl) th) g) THEN
        PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
        CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
        REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC;
        let is_less t = (fst(strip_comb t) = "<") ? false in
        FILTER_ASM_REWRITE_TAC is_less [LESS_REFL] THEN
        FIRST_ASSUM (\th g. MP_TAC (assert (is_eq o concl) th) g) THEN
        PURE_ONCE_REWRITE_TAC [EXTENSION] THEN
        CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
        CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
        REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC;
        let is_less t = (fst(strip_comb t) = "<") ? false in
        FILTER_ASM_REWRITE_TAC is_less [LESS_REFL] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
       FIRST_ASSUM (\th g. (MP_TAC (assert(is_eq o concl) th)) g) THEN
       PURE_REWRITE_TAC [EXTENSION;IN_INSERT] THEN
       CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
       DISCH_THEN (\th. PURE_ONCE_REWRITE_TAC [th]) THEN
       GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
       [EXISTS_TAC "CARD (s:(*)set)" THEN
        REWRITE_TAC [LESS_REFL] THEN FIRST_ASSUM ACCEPT_TAC;
        EXISTS_TAC "n:num" THEN
        FILTER_ASM_REWRITE_TAC (\t. not(lhs t) = "s:(*)set" ? true) [];
        SUBST1_TAC (ASSUME "x:* = (n < CARD (s:(*)set) => f n | e)") THEN
        SUBST1_TAC (ASSUME "n = CARD (s:(*)set)") THEN
        REWRITE_TAC [LESS_REFL];
        SUBST1_TAC (ASSUME "x:* = (n < CARD (s:(*)set) => f n | e)") THEN
        DISJ2_TAC THEN EXISTS_TAC "n:num" THEN
        REWRITE_TAC [ASSUME "n < CARD (s:(*)set)"]]]]);;


quit();; % Needed for Common Lisp %
