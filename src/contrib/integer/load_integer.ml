% ===================================================================== %
% FILE		: load_integer.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "integer" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_integer.					%
% --------------------------------------------------------------------- %

let load_integer (v:void) =
    if (mem `integer` (ancestry())) then
       (print_string `Loading contents of integer...`; print_newline();
        let path st = library_pathname() ^ `/integer/` ^ st in
            load(path `num_tac`, get_flag_value `print_lib`);
            load(path `integer_tac`, get_flag_value `print_lib`);
        let defs = map fst (definitions `integer`) in
            map (\st. autoload_theory(`definition`,`integer`,st)) defs;
        let thms = map fst (theorems `integer`) in
            map (\st. autoload_theory(`theorem`,`integer`,st)) thms; 
        delete_cache `integer`; ()) else
    failwith `theory integer not an ancestor of the current theory`;;

