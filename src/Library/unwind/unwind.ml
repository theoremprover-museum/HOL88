% ===================================================================== %
% FILE		: unwind.ml						%
% DESCRIPTION   : loads the library "unwind" into hol.			%
%									%
% AUTHOR	: R.J.Boulton						%
% DATE    	: 3rd September 1991					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Add the unwind help files to online help.                             %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/unwind/help/entries/` in
    print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load the compiled code into ml.					%
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/unwind/` ^ st in
    load(path `unwinding`, get_flag_value `print_lib`);;
