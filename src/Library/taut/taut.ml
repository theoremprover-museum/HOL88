% ===================================================================== %
% FILE		: taut.ml						%
% DESCRIPTION   : loads the library "taut" into hol.			%
%									%
% AUTHOR	: R.J.Boulton						%
% DATE    	: 9th July 1991						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Add the taut help files to online help.                               %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/taut/help/entries/` in
    print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load the compiled code into ml.					%
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/taut/` ^ st in
    load(path `taut_check`, get_flag_value `print_lib`);;
