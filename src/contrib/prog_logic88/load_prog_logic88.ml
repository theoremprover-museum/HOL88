% ===================================================================== %
% FILE		: load_prog_logic88.ml					%
% DESCRIPTION   : creates a function that loads the contents of the	%
%		  library "prog_logic88" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 91.01.20						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% define the function load_prog_logic88.				%
% --------------------------------------------------------------------- %

let load_prog_logic88 (v:void) =
    if (mem `prog_logic88` (ancestry())) then
       (print_string `Loading contents of prog_logic88...`; print_newline();
        let path st = library_pathname() ^ `/prog_logic88/` ^ st in
        let loadfn st = load(path st, get_flag_value `print_lib`) in
            map loadfn
             (words `autoload syntax_functions hol_match hoare_logic 
                     vc_gen halts_logic halts_vc_gen`); ()) else
    failwith `theory prog_logic88 not an ancestor of the current theory`;;

