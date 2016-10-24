% ===================================================================== %
% FILE		: rtc.ml						%
% DESCRIPTION   : reflexitive-transitive closure of a relation.		%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 90.04.29						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory.                  				%
% --------------------------------------------------------------------- %
new_theory `rtc`;;

% --------------------------------------------------------------------- %
% Load the inductive definitions package				%
% --------------------------------------------------------------------- %
load_library `ind_defs`;;

% --------------------------------------------------------------------- %
% Inductive definition the reflexive-transitive closure of a relation.	%
% --------------------------------------------------------------------- %

let (rules,ind) =

    let RTC = "RTC:(*->*->bool)->*->*->bool" in

    new_inductive_definition false `RTC_DEF` 

    ("^RTC R x y", ["R:*->*->bool"])

    [ [				       
      % ------------------------------ %  "R (x:*) (y:*):bool"],
                "^RTC R x y"	       ;

      [				       
      %------------------------------- % ],
                "^RTC R x x"	       ;

      [  "^RTC R x z";   "^RTC R z y"  
      %------------------------------- % ],
                "^RTC R x y"	       ];;


% --------------------------------------------------------------------- %
% Tactics for RTC proofs.						%
% --------------------------------------------------------------------- %

let [IN_TAC;REFL_TAC;TRANS_TAC] = map RULE_TAC rules;;

% --------------------------------------------------------------------- %
% Strong form of rule induction.					%
% --------------------------------------------------------------------- %

let sind = derive_strong_induction_thm (rules,ind);;

% --------------------------------------------------------------------- %
% Cases theorem for RTC.						%
% --------------------------------------------------------------------- %

let cases = derive_cases_thm (rules,ind);;

% --------------------------------------------------------------------- %
% Rule induction tactic for RTC.					%
% --------------------------------------------------------------------- %

let RTC_INDUCT_TAC = RULE_INDUCT_THEN ind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Prove that taking the reflexive-transitive closure preserves symmetry %
% --------------------------------------------------------------------- %

let RTC_PRESERVES_SYMMETRY = 
    prove_thm
    (`RTC_PRESERVES_SYMMETRY`,
     "!R. (!a (b:*). R a b ==> R b a) ==> 
          (!a b. RTC R a b ==> RTC R b a)",
     GEN_TAC THEN DISCH_TAC THEN
     RTC_INDUCT_TAC THENL
     [IN_TAC THEN RES_TAC;
      REFL_TAC;
      TRANS_TAC THEN EXISTS_TAC "z:*" THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

