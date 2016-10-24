% mk_BINOMIAL_integer.ml %
% Binomial theorem specialised to the ring of integers %
`[mk_BINOMIAL_integer] Last modified on Thu Jul 25  9:14:55 BST 1991 by adg`;;

% ------------------------------------------------------------------------- %
% Handy ML utilities.                                                       %
% ------------------------------------------------------------------------- %
%
Matching Modus Ponens for equivalences of the form |- !x1 ... xn. P = Q 
Matches x1 ... xn : 	 |-  P'  ---->  |- Q'  
Matches all types in conclusion except those mentioned in hypotheses
Same as the code for MATCH_MP but with EQ_MP substituted for MP.
%
let MATCH_EQ_MP eqth =
     let match = PART_MATCH (fst o dest_eq) eqth ? failwith `MATCH_EQ_MP` 
     in
     \th. EQ_MP (match (concl th)) th;;

% ------------------------------------------------------------------------- %
% Parent theories and the draft theory.                                     %
%                                                                           %
% Need to load theory BINOMIAL before theory integer, because the former    %
% uses `plus` and `times` as variables, whereas the latter uses them as     %
% constants.                                                                %
% ------------------------------------------------------------------------- %

can unlink `BINOMIAL_integer.th`;;
new_theory `BINOMIAL_integer`;;

loadf `BINOMIAL`;;

load_library `integer`;;
autoload_all_defs_and_thms `integer`;;

% ------------------------------------------------------------------------- %
% The integers form a ring.                                                 %
% ------------------------------------------------------------------------- %

let MONOID_plus =
    prove(
    "MONOID $plus",
    PURE_REWRITE_TAC [RAW_MONOID; ASSOCIATIVE] THEN
    CONJ_TAC THENL
       [ACCEPT_TAC ASSOC_PLUS ;
        EXISTS_TAC "INT 0" THEN REWRITE_TAC [PLUS_IDENTITY]]);;

let inst = INST_TYPE [(":integer",":*")];;

let ID_plus =
    prove(
    "Id $plus = INT 0",
    STRIP_ASSUME_TAC (MATCH_EQ_MP MONOID MONOID_plus) THEN
    MATCH_MP_TAC (STRIP_SPEC_IMP "$plus" (inst UNIQUE_RIGHT_ID)) THEN
    REWRITE_TAC [PLUS_IDENTITY]);;

let GROUP_plus =
    prove(
    "Group $plus",
    PURE_ONCE_REWRITE_TAC [RAW_GROUP] THEN
    CONJ_TAC THENL
       [ACCEPT_TAC MONOID_plus ;
        GEN_TAC THEN
        EXISTS_TAC "neg a" THEN
        REWRITE_TAC [PLUS_INVERSE; ID_plus] ]);;

let MONOID_times =
    prove(
    "MONOID $times",
    PURE_REWRITE_TAC [RAW_MONOID; ASSOCIATIVE] THEN
    CONJ_TAC THENL
       [ACCEPT_TAC ASSOC_TIMES ;
        EXISTS_TAC "INT 1" THEN REWRITE_TAC [TIMES_IDENTITY]]);;

let ID_times =
    prove(
    "Id $times = INT 1",
    STRIP_ASSUME_TAC (MATCH_EQ_MP MONOID MONOID_times) THEN
    MATCH_MP_TAC (STRIP_SPEC_IMP "$times" (inst UNIQUE_RIGHT_ID)) THEN
    REWRITE_TAC [TIMES_IDENTITY]);;

let RING_integer =
    prove_thm
    (`RING_integer`,
    "RING ($plus,$times)",
    PURE_REWRITE_TAC [RING; LEFT_DISTRIB; RIGHT_DISTRIB; COMMUTATIVE] THEN
    REWRITE_TAC
        [GROUP_plus; MONOID_times;
         LEFT_PLUS_DISTRIB; RIGHT_PLUS_DISTRIB] THEN
    CONJ_TAC THENL
    map ACCEPT_TAC [COMM_PLUS; COMM_TIMES]);;

% ------------------------------------------------------------------------- %
% The Binomial Theorem for the integers.                                    %
% ------------------------------------------------------------------------- %

let BINOMIAL_integer =
    save_thm
    (`BINOMIAL_integer`,
    MATCH_MP BINOMIAL RING_integer);;

close_theory();;
