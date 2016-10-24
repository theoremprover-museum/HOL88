% ===================================================================== %
% FILE		: load_quotient.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "quotient" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_quotient.					%
% --------------------------------------------------------------------- %

let load_quotient (v:void) =
    if (mem `quotient` (ancestry())) then
       (print_string `Loading contents of quotient...`; print_newline();
        autoload_theory(`definition`,`quotient`,`REFLEX`);
        autoload_theory(`definition`,`quotient`,`SYMMETRY`);
        autoload_theory(`definition`,`quotient`,`TRANSITIVITY`);
        autoload_theory(`definition`,`quotient`,`EQUIVALENCE`);
        let path st = library_pathname() ^ `/quotient/` ^ st in
            load(path `quotientfns`, get_flag_value `print_lib`);()) else
     failwith `theory quotient not an ancestor of the current theory`;;

