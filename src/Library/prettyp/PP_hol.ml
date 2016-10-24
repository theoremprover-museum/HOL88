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

load (library_pathname() ^ `/prettyp/PP_hol/PP_hol`,
      get_flag_value `print_lib`);;
