% ===================================================================== %
% FILE		: load_string.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "string" into hol.				%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_string.					%
% --------------------------------------------------------------------- %

let load_string (v:void) =
    if (mem `string` (ancestry())) then
       (print_string `Loading contents of string...`; print_newline();
        let path st = library_pathname() ^ `/string/` ^ st in
        load(path `stringconv`, get_flag_value `print_lib`);
        load(path `ascii`, get_flag_value `print_lib`);
        load(path `string_rules`, get_flag_value `print_lib`);
        let thms = map fst (theorems `ascii`) in
            map (\name. autoload_theory(`theorem`,`ascii`,name)) thms; 
        let thms = map fst (theorems `string`) in
            map (\name. autoload_theory(`theorem`,`string`,name)) thms;
        delete_cache `ascii`; delete_cache `string`; ()) else
     failwith `theory string not an ancestor of the current theory`;;

