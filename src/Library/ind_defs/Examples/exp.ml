% ===================================================================== %
% FILE		: exp.ml						%
% DESCRIPTION   : The operational semantics of a trivial language of	%
%	          arithmetic expressions.			 	%
% 		  language.						%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 90.11.24						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the theory.							%
% --------------------------------------------------------------------- %
new_theory `exp`;;

% --------------------------------------------------------------------- %
% Need the ind_defs library.						%
% --------------------------------------------------------------------- %
load_library `ind_defs`;;

% ===================================================================== %
% SYNTAX								%
% ===================================================================== %

let exp_axiom = 
    define_type `exp_axiom`
    `exp = N num | plus exp exp`;;

% --------------------------------------------------------------------- %
% Make plus an infix `++'.						%
% --------------------------------------------------------------------- %

let iplus =
    new_infix_definition
    (`iplus`,
     "$++ e1 e2 = plus e1 e2");;

let exp_axiom = REWRITE_RULE [SYM(SPEC_ALL iplus)] exp_axiom;;

% --------------------------------------------------------------------- %
% distinctness and injectivity of constructors N and ++.		%
% --------------------------------------------------------------------- %

let dist =
    let th = prove_constructors_distinct exp_axiom in
        CONJ th (NOT_EQ_SYM(SPEC_ALL th));;
let oneone = prove_constructors_one_one exp_axiom;;

% --------------------------------------------------------------------- %
% induction.								%
% --------------------------------------------------------------------- %

let sind = prove_induction_thm exp_axiom;;

% ===================================================================== %
% OPERATIONAL SEMANTICS							%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Semantics of natural number expressions.				%
% --------------------------------------------------------------------- %

new_special_symbol `--->`;;

let rules,ind = 
    let R = "---> : exp -> num -> bool" in
    new_inductive_definition true `expsem` 

    ("^R e n", []) 
    
     [ [				             
       % -------------------------------------------- % ],
                        "^R (N n) n"                  ;


       [         "^R e1 n";      "^R e2 m"
       % -------------------------------------------- % ],
                   "^R (e1 ++ e2) (n+m)"	      ];;


% --------------------------------------------------------------------- %
% Tactics for the rules.						%
% --------------------------------------------------------------------- %

let EXP_TAC = FIRST (map RULE_TAC rules);;

% --------------------------------------------------------------------- %
% Cases theorem.							%
% --------------------------------------------------------------------- %

let cases = derive_cases_thm (rules,ind);;

% ===================================================================== %
% PROOF: the operational semantics is deterministic.			%
% ===================================================================== %

let DETERMINISTIC =
    prove_thm
    (`DETERMINISTIC`,
     "!e1 n. e1 ---> n ==> !m. e1 ---> m ==> (n = m)",
     RULE_INDUCT_THEN ind ASSUME_TAC ASSUME_TAC THEN
     REPEAT GEN_TAC THEN
     let rule = REWRITE_RULE [dist;oneone] o MATCH_MP cases in
     DISCH_THEN (STRIP_ASSUME_TAC o rule) THEN
     EVERY_ASSUM (\th g. SUBST_ALL_TAC th g ? ALL_TAC g) THEN
     RES_THEN SUBST1_TAC THEN REFL_TAC);;


% ===================================================================== %
% PROOF: each expression evaluates to something.			%
% ===================================================================== %

let EVAL = 
    prove_thm
    (`EVAL`,
     "!e. ?n. e ---> n",
     INDUCT_THEN sind STRIP_ASSUME_TAC THEN
     REPEAT GEN_TAC THENL
     [EXISTS_TAC "n:num" THEN EXP_TAC;
      EXISTS_TAC "n+n'" THEN EXP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;


