% ===================================================================== %
% FILE		: load_bags.ml						%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "bags" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.24						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_bags						%
% --------------------------------------------------------------------- %

let load_bags (v:void) =
    if (mem `bags` (ancestry())) then
       (print_string `Loading contents of bags...`; print_newline();
        let defs = map fst (definitions `bags`) in
            map (\st. autoload_theory(`definition`,`bags`,st)) defs;
        let thms = map fst (theorems `bags`) in
            map (\st. autoload_theory(`theorem`,`bags`,st)) thms; 
        let defs = map fst (definitions `more_arithmetic`) in
            map (\st.autoload_theory(`definition`,`more_arithmetic`,st)) defs;
        let thms = map fst (theorems `more_arithmetic`) in
            map (\st. autoload_theory(`theorem`,`more_arithmetic`,st)) thms; 
      delete_cache `bags`; ()) else
    failwith `theory bags not an ancestor of the current theory`;;

