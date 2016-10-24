% ===================================================================== %
% FILE		: CL.ml							%
% DESCRIPTION   : Defines a proof system for minimal intuitionistic 	%
%                 logic, and proves the Curry-Howard isomorphism for	%
%                 this and typed combinatory logic.			%
%									%
% AUTHOR	: Tom Melham and Juanito Camilleri			%
% DATE		: 90.12.03						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Open a new theory and load the inductive definitions library.		%
% --------------------------------------------------------------------- %

new_theory `mil`;;

load_library `ind_defs`;;

% --------------------------------------------------------------------- %
% Load the theory of combinatory logic.					%
% --------------------------------------------------------------------- %

new_parent `cl`;;

% ===================================================================== %
% Combinatory logic types and type judgements.				%
% ===================================================================== %

let ty_axiom = define_type `ty` `ty = G * | fun ty ty`;;

% --------------------------------------------------------------------- %
% Define an infix arrow for function types.				%
% --------------------------------------------------------------------- %
new_special_symbol `->`;;

let infix_fun_def = 
    new_infix_definition
      (`infix_fun_def`,
       "$-> = fun:(*)ty->(*)ty->(*)ty");;

let ty_Axiom =
    save_thm(`ty_Axiom`, SUBS [SYM infix_fun_def] ty_axiom);;

% ===================================================================== %
% Standard syntactic theory, derived by the recursive types package.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Structural induction theorem for types.				%
% --------------------------------------------------------------------- %

let ty_induct = save_thm (`ty_induct`,prove_induction_thm ty_Axiom);;

% --------------------------------------------------------------------- %
% Exhaustive case analysis theorem for types.				%
% --------------------------------------------------------------------- %

let ty_cases = save_thm (`ty_cases`, prove_cases_thm ty_induct);;

% --------------------------------------------------------------------- %
% Prove that the arrow and ground type constructors are one-to-one.	%
% --------------------------------------------------------------------- %

let Gfun11 = save_thm(`Gfun11`, prove_constructors_one_one ty_Axiom);;

% --------------------------------------------------------------------- %
% Prove that the constructors yield syntactically distinct values. One	%
% typically needs all symmetric forms of the inequalities.		%
% --------------------------------------------------------------------- %

let ty_distinct =
    let ths = CONJUNCTS (prove_constructors_distinct ty_Axiom) in
    let rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths in
        save_thm(`ty_distinct`, LIST_CONJ (ths @ rths));;

% ===================================================================== %
% Definition of well-typed terms of combinatory logic.			%
% ===================================================================== %

let (TYrules,TYind) =
    let TY = "IN : cl->(*)ty->bool" in
    new_inductive_definition true `CL_TYPE_DEF` 

    ("^TY c t", [])

    [ 
      [				                               
      % ------------------------------------------------------ % ],
                      "^TY k  (A -> (B -> A))"                  ;

      [				                               
      % ------------------------------------------------------ % ],
          "^TY s ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))"  ;



      [	         "^TY U (t1 -> t2)";     "^TY V t1"	       
      %------------------------------------------------------- % ],
                         "^TY (U ' V) t2"	  	       ];;

% ===================================================================== %
% Mimimal intuitionistic logic.  We now reinterpret -> as implication,  %
% types P:(*)ty as terms of the logic (i.e. propositions), and define a %
% provability predicate "THM" on these terms. The definition is done	%
% inductively by the proof rules for the logic.				%
% ===================================================================== %

let (THMrules,THMind) =
    let THM = "THM:(*)ty->bool" in
    new_inductive_definition false `THM_DEF` 

    ("^THM p", [])

    [ 
      [				                               
      % ------------------------------------------------------ % ],
                     "^THM  (A -> (B -> A))"                   ;

      [				                               
      %------------------------------------------------------- % ],
         "^THM  ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))"   ;


      [	           "^THM  (P -> Q)";     "^THM P"	                
      %------------------------------------------------------- % ],
                            "^THM  Q"			       ];;


% ===================================================================== %
% Derivation of the Curry-Howard isomorphism.				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The left-to-right direction is proved by rule induction for the	%
% inductively defined relation THM, followed by use of the typing rules %
% (i.e. the tactics for them) to prove the conclusion. The proof is	%
% completely straightforward.						%
% --------------------------------------------------------------------- %

let ISO_THM1 =
    TAC_PROOF
    (([], "!P:(*)ty. THM P ==> ?M:cl. M IN P"),
     RULE_INDUCT_THEN THMind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
     REPEAT GEN_TAC THENL
     map EXISTS_TAC ["k:cl";"s:cl";"M ' M'"] THEN
     MAP_FIRST RULE_TAC TYrules THEN
     EXISTS_TAC "P':(*)ty" THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

% --------------------------------------------------------------------- %
% The proof for the other direction proceeds by induction over the 	%
% typing relation.  Again, simple.					%
% --------------------------------------------------------------------- %

let ISO_THM2 =
    TAC_PROOF
    (([], "!P:(*)ty. !M:cl. M IN P ==> THM P"),
     RULE_INDUCT_THEN TYind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
     REPEAT GEN_TAC THEN
     MAP_FIRST RULE_TAC THMrules THEN
     EXISTS_TAC "t1:* ty" THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

% --------------------------------------------------------------------- %
% The final result.							%
% --------------------------------------------------------------------- %

let CURRY_HOWARD =
    prove_thm
    (`CURRY_HOWARD`,
    "!P:(*)ty. THM P = ?M:cl. M IN P",
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
    IMP_RES_TAC (CONJ ISO_THM1 ISO_THM2) THEN
    EXISTS_TAC "M:cl" THEN FIRST_ASSUM ACCEPT_TAC);;


% --------------------------------------------------------------------- %
% End of example.							%
% --------------------------------------------------------------------- %

close_theory();;
quit();;


    
