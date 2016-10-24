% ===================================================================== %
% FILE		: load_auxiliary.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "auxiliary" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_auxiliary.					%
% --------------------------------------------------------------------- %

let load_auxiliary =
    let lib_path = library_pathname () in
 \(v:void).
    if (mem `auxiliary` (ancestry())) then
       (print_string `Loading contents of auxiliary ...`; print_newline();
        let path st = lib_path ^ `/auxiliary/` ^ st in
            (load(path `functions`, get_flag_value `print_lib`);
             load(path `tactics`, get_flag_value `print_lib`);
             load(path `rules`, get_flag_value `print_lib`);
             load(path `conversions`, get_flag_value `print_lib`)) ;
        let defs = map fst (definitions `auxiliary`) in
            map (\name. autoload_theory(`definition`,`auxiliary`,name)) defs; 
        let thms = map fst (theorems `auxiliary`) in
            map (\name. autoload_theory(`theorem`,`auxiliary`,name)) thms; ())
        else 
     failwith `theory auxiliary not an ancestor of the current theory`;;


