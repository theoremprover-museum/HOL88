% ===================================================================== %
% FILE		: load_pred_sets.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "pred_sets" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 92.01.26						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_pred_sets.					%
% --------------------------------------------------------------------- %

let load_pred_sets (v:void) =
    if (mem `pred_sets` (ancestry())) then
       (print_string `Loading contents of pred_sets...`; print_newline();
        define_set_abstraction_syntax `GSPEC`;
        define_finite_set_syntax(`EMPTY`,`INSERT`);
        set_flag(`print_set`,true); 
        let path st = library_pathname() ^ `/pred_sets/` ^ st in
            load(path `gspec`, get_flag_value `print_lib`);
            load(path `set_ind`, get_flag_value `print_lib`);
            load(path `fset_conv`, get_flag_value `print_lib`);
        let defs = map fst (definitions `pred_sets`) in
            map (\st. autoload_theory(`definition`,`pred_sets`,st)) defs;
        let thms = map fst (theorems `pred_sets`) in
            map (\st. autoload_theory(`theorem`,`pred_sets`,st)) thms; 
        delete_cache `pred_sets`; ()) else
    failwith `theory pred_sets not an ancestor of the current theory`;;

