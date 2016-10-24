%=============================================================================%
%                               HOL 88 Version 2.02                           %
%                                                                             %
%     FILE NAME:        mk_fun.ml                                             %
%                                                                             %
%     DESCRIPTION:      Creates the theory "fun.th" containing some basic     %
%                       definitions of predicates about functions and         %
%                       theorems about them.                                  %
%                                                                             %
%     AUTHOR:           W. Wong (02 Jan 94)                                   %
%                                                                             %
%     PARENTS:          BASIC-HOL.th                                          %
%     WRITES FILES:     fun.th                                             %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% Create the new theory.						%
new_theory `fun`;;

%----------------------------------------------------------------%
%- Definitions about functions                                  -%
%----------------------------------------------------------------%
let ASSOC_DEF = new_definition(`ASSOC_DEF`,
    "!f:*->*->*. ASSOC f = !x y z. f x (f y z) = f (f x y) z");;

let COMM_DEF = new_definition(`COMM_DEF`,
    "!f:*->*->**. COMM f = ! x y. f x y = f y x");;

let FCOMM_DEF = new_definition(`FCOMM_DEF`,
    "!(f:*->**->*) (g:***->*->*).
     FCOMM f g = !x y z. g x (f y z) = f (g x y) z");;

let RIGHT_ID_DEF = new_definition(`RIGHT_ID_DEF`,
    "RIGHT_ID (f:*->**->*) e = (!x. f x e =  x)");;

let LEFT_ID_DEF = new_definition(`LEFT_ID_DEF`,
    "LEFT_ID (f:**->*->*) e = (!x. f e x =  x)");;

let  MONOID_DEF = new_definition(`MONOID_DEF`,
    "MONOID (f:*->*->*) e = ASSOC f /\ RIGHT_ID f e /\ LEFT_ID f e");;

% Close the theory.							%
close_theory ();;

%----------------------------------------------------------------%
%- Theorems about functions                                     -%
%----------------------------------------------------------------%
let ASSOC_CONJ = prove_thm (`ASSOC_CONJ`,
    "ASSOC $/\",
    REWRITE_TAC[ASSOC_DEF;CONJ_ASSOC]);;

let ASSOC_DISJ = prove_thm (`ASSOC_DISJ`,
    "ASSOC $\/",
    REWRITE_TAC[ASSOC_DEF;DISJ_ASSOC]);;

let FCOMM_ASSOC = prove_thm (`FCOMM_ASSOC`,
    "!f:*->*->*. FCOMM f f = ASSOC f",
    REWRITE_TAC[ASSOC_DEF;FCOMM_DEF]);;

%<let RIGHT_ID_CONJ_T = prove_thm (`RIGHT_ID_CONJ_T`,
    "RIGHT_ID $/\ T",
    REWRITE_TAC[RIGHT_ID_DEF]);;

let RIGHT_ID_DISJ_F = prove_thm (`RIGHT_ID_DISJ_F`,
    "RIGHT_ID $\/ F",
    REWRITE_TAC[RIGHT_ID_DEF]);;

let LEFT_ID_CONJ_T = prove_thm (`LEFT_ID_CONJ_T`,
    "LEFT_ID $/\ T",
    REWRITE_TAC[LEFT_ID_DEF]);;

let LEFT_ID_DISJ_F = prove_thm (`LEFT_ID_DISJ_F`,
    "LEFT_ID $\/ F",
    REWRITE_TAC[LEFT_ID_DEF]);;
>%

let MONOID_CONJ_T = prove_thm (`MONOID_CONJ_T`,
    "MONOID $/\ T",
    REWRITE_TAC[MONOID_DEF;CONJ_ASSOC;LEFT_ID_DEF;ASSOC_DEF;RIGHT_ID_DEF]);;

let MONOID_DISJ_F = prove_thm (`MONOID_DISJ_F`,
    "MONOID $\/ F",
    REWRITE_TAC[MONOID_DEF;DISJ_ASSOC;LEFT_ID_DEF;ASSOC_DEF;RIGHT_ID_DEF]);;

quit();;
