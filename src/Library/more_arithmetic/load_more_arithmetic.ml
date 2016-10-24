% ===================================================================== %
% FILE		: load_more_arithmetic.ml				%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "more_arithmetic" into hol.			%
%									%
% AUTHOR	: P. Curzon						%
% DATE		: 8.4.91						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_more_arithmetic.				%
% --------------------------------------------------------------------- %

let load_more_arithmetic =
  let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ()
  in
  let lib_path = library_pathname() in
 \(v:void).
    if (mem `more_arithmetic` (ancestry())) then
       (print_string `Loading contents of more_arithmetic...`;
        print_newline();
        let path st = lib_path ^ `/more_arithmetic/` ^ st in
        load(path `num_convs`, get_flag_value `print_lib`);
        load(path `num_tac`, get_flag_value `print_lib`);
        autoload_defs_and_thms `ineq`;
        autoload_defs_and_thms `zero_ineq`;
        autoload_defs_and_thms `suc`;
        autoload_defs_and_thms `add`;
        autoload_defs_and_thms `sub`;
        autoload_defs_and_thms `pre`;
        autoload_defs_and_thms `mult`;
        autoload_defs_and_thms `min_max`;
        autoload_defs_and_thms `odd_even`;
        autoload_defs_and_thms `div_mod`;
        delete_cache `ineq`;
        delete_cache `zero_ineq`;
        delete_cache `suc`;
        delete_cache `add`;
        delete_cache `sub`;
        delete_cache `pre`;
        delete_cache `mult`;
        delete_cache `min_max`;
        delete_cache `odd_even`;
        delete_cache `div_mod`;
        ()) else
     failwith `theory more_arithmetic not an ancestor of the current theory`;;


