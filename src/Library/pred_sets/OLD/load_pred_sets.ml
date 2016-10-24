% ===================================================================== %
% FILE		: load_pred_sets.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "pred_sets" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_pred_sets.					%
% --------------------------------------------------------------------- %

let load_pred_sets (v:void) =
    if (mem `pred_sets` (ancestry())) then
       (print_string `Loading contents of pred_sets...`; print_newline();
        autoload_theory(`definition`,`fixpoints`,`BOT`);
        let defs = map fst (definitions `pred_sets`) in
            map (\name. autoload_theory(`definition`,`pred_sets`,name)) defs;
        let thms = map fst (theorems `pred_sets`) in
            map (\name. autoload_theory(`theorem`,`pred_sets`,name)) thms; 
        delete_cache `pred_sets`; ()) else
    failwith `theory pred_sets not an ancestor of the current theory`;;

