% BINOMIAL_integer.ml %
% Load and offer access to the theory BINOMIAL_integer %
`[BINOMIAL_integer.ml] Last modified on Thu Jul 25 11:36:51 BST 1991 by adg`;;

% --------------------------------------------------------------------- %
% Load theory BINOMIAL_integer, with parents BINOMIAL and integer.      %
% --------------------------------------------------------------------- %

loadf `BINOMIAL`;;
load_library `integer`;;
smart_load_theory `BINOMIAL_integer`;;

map autoload_all_defs_and_thms [`integer`;`BINOMIAL_integer`];;
