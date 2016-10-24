% ===================================================================== %
% FILE		: prettyp.ml						%
% DESCRIPTION   : loads the library "prettyp" into hol.			%
%									%
% DATE    	: 90.12.01						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Add the prettyp help files to online help.                            %
% --------------------------------------------------------------------- %

let path1 = library_pathname() ^ `/prettyp/help/entries/`
and path2 = library_pathname() ^ `/prettyp/help/internals/`
in  print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path1;path2] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load the compiled code into ml.					%
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/prettyp/` ^ st
and flag = get_flag_value `print_lib`
in  map (\st. load(path st, flag))
        [`PP_printer/PP_printer`;
         `PP_parser/PP_parser`;
         `PP_hol/PP_hol`];;

