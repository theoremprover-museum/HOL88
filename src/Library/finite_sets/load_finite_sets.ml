% ===================================================================== %
% FILE		: load_finite_sets.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "finite_sets" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 92.02.15						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_finite_sets.					%
% --------------------------------------------------------------------- %

let load_finite_sets (v:void) =
    if (mem `finite_sets` (ancestry())) then
       (print_string `Loading contents of finite_sets...`; print_newline();
        define_finite_set_syntax(`EMPTY`,`INSERT`);
        set_flag(`print_set`,true); 
        let path st = library_pathname() ^ `/finite_sets/` ^ st in
            load(path `set_ind`, get_flag_value `print_lib`);
            load(path `fset_conv`, get_flag_value `print_lib`);
        let defs = map fst (definitions `finite_sets`) in
            map (\st. autoload_theory(`definition`,`finite_sets`,st)) defs;
        let thms = map fst (theorems `finite_sets`) in
            map (\st. autoload_theory(`theorem`,`finite_sets`,st)) thms; 
        delete_cache `finite_sets`; ()) else
    failwith `theory finite_sets not an ancestor of the current theory`;;

