% ===================================================================== %
% FILE		: load_sets.ml						%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "sets" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_sets.					%
% --------------------------------------------------------------------- %

let load_sets (v:void) =
    if (mem `sets` (ancestry())) then
       (print_string `Loading contents of sets...`; print_newline();
        define_set_abstraction_syntax `GSPEC`;
        define_finite_set_syntax(`EMPTY`,`INSERT`);
        set_flag(`print_set`,true); 
        let path st = library_pathname() ^ `/sets/` ^ st in
            load(path `gspec`, get_flag_value `print_lib`);
            load(path `set_ind`, get_flag_value `print_lib`);
            load(path `fset_conv`, get_flag_value `print_lib`);
        let defs = map fst (definitions `sets`) in
            map (\st. autoload_theory(`definition`,`sets`,st)) defs;
        let thms = map fst (theorems `sets`) in
            map (\st. autoload_theory(`theorem`,`sets`,st)) thms; 
        delete_cache `sets`; ()) else
    failwith `theory sets not an ancestor of the current theory`;;

