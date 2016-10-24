% ===================================================================== %
% FILE		: load_int_mod.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "int_mod" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_int_mod.					%
% --------------------------------------------------------------------- %

let load_int_mod (v:void) =
    if (mem `int_mod` (ancestry())) then
       (print_string `Loading contents of int_mod...`; print_newline();
        include_theory `int_sbgp`;
        include_theory `int_mod`;
        loadt `inst_int_mod`; ()) else
    failwith `theory int_mod not an ancestor of the current theory`;;

