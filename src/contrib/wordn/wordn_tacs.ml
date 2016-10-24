% ===================================================================== %
% FILE		: wordn_tacs.ml						%
% DESCRIPTION   : tactics for wordn 					%
%									%
% AUTHOR	: (c) W. Wong						%
% DATE		: 19 March 1992						%
% ===================================================================== %

let wordn_CASES_TAC w th =
    ASSUME_TAC (SPEC w th)
    THEN REPEAT (POP_ASSUM CHOOSE_TAC) THEN POP_ASSUM SUBST1_TAC;;

let wordn_X_CASES_TAC w th tlst =
    ASSUME_TAC (SPEC w th)
    THEN MAP_EVERY (\t. POP_ASSUM (X_CHOOSE_TAC t)) tlst
    THEN POP_ASSUM SUBST1_TAC;;

