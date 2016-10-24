% ===================================================================== %
% FILE		: mk_ascii.ml						%
% DESCRIPTION   : Creates a theory of 8-bit ascii character codes	%
% WRITES FILES	: ascii.th						%
%									%
% AUTHOR	: (c) T. Melham 1988					%
% DATE		: 87.07.27						%
% REVISED	: 90.10.27						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory							%
% --------------------------------------------------------------------- %
new_theory `ascii`;;

% --------------------------------------------------------------------- %
% define the type :ascii						%
% --------------------------------------------------------------------- %
let ascii_Axiom = 
    define_type `ascii_Axiom`
    		`ascii = ASCII bool bool bool bool bool bool bool bool`;;

% --------------------------------------------------------------------- %
% prove induction theorem for ascii.					%
% --------------------------------------------------------------------- %
let ascii_Induct = 
    save_thm (`ascii_Induct`, prove_induction_thm ascii_Axiom);;

% --------------------------------------------------------------------- %
% prove cases theorem for ascii.					%
% --------------------------------------------------------------------- %
let ascii_CASES = 
    save_thm (`ascii_CASES`, prove_cases_thm ascii_Induct);;

% --------------------------------------------------------------------- %
% prove that the constructor ASCII is one-to-one			%
% --------------------------------------------------------------------- %
let ASCII_11 = 
    save_thm (`ASCII_11`, prove_constructors_one_one ascii_Axiom);;

quit();;  % Needed for Common Lisp %
