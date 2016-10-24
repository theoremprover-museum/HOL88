% BINOMIAL.ml %
% Load and offer access to the theory BINOMIAL %
`[BINOMIAL.ml] Last modified on Thu Jul 25  9:12:35 BST 1991 by adg`;;

% --------------------------------------------------------------------- %
% Load theory BINOMIAL.                                                 %
% --------------------------------------------------------------------- %

smart_load_theory `BINOMIAL`;;
autoload_all_defs_and_thms `BINOMIAL`;;

% --------------------------------------------------------------------- %
% Duplicate ML code used by tactics in mk_BINOMIAL.ml                   %
% --------------------------------------------------------------------- %

let DEEP_SYM t = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) t;;
let SPEC_EQ v th = UNDISCH(fst(EQ_IMP_RULE (SPEC v th)));;
let SPECL_EQ vs th = UNDISCH(fst(EQ_IMP_RULE (SPECL vs th)));;
let SPEC_IMP v th = UNDISCH(SPEC v th);;
let SPECL_IMP vs th = UNDISCH(SPECL vs th);;
let STRIP_SPEC_IMP v th =
    UNDISCH_ALL(SPEC v (CONV_RULE (ONCE_DEPTH_CONV ANTE_CONJ_CONV) th));;

let plus,times = "plus: *->*->*", "times: *->*->*";;

let RING_TAC =
    GEN_TAC THEN GEN_TAC THEN
    DISCH_THEN (\th. STRIP_ASSUME_TAC (MP RING_LEMMA th));;
