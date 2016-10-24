% ===================================================================== %
% FILE: load_res_quan.ml    DATE: 1 Aug 92 	BY: Wai Wong		%
% Creates a function that loads the contents of the library "res_quan"  %
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_res_quan.					%
% --------------------------------------------------------------------- %

% WW when release, chage the line
let this_lib_path = library_pathname() in %

let load_res_quan (v:void) =
    if (mem `res_quan` (ancestry())) then
       (print_string `Loading contents of res_quan...`; print_newline();
        let this_lib_path = `/homes/ww/hol4` in
        let path st = this_lib_path ^ `/res_quan/` ^ st in
            (load( `cond_rewrite`, get_flag_value `print_lib`);
             load( `res_rules`, get_flag_value `print_lib`));
        let thms = map fst (theorems `res_quan`) in
            map (\st. autoload_theory(`theorem`,`res_quan`,st)) thms; 
        delete_cache `res_quan`; ()) else
     failwith `theory res_quan not an ancestor of the current theory`;;

