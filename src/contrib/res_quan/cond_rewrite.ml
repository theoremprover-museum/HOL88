% ===================================================================== %
% FILE: res_quan.ml 	DATE: 1 Aug 92 	BY: Wai WONG			%
% Loads the res_quan library.	    					%
% ===================================================================== %

let this_lib_path = library_pathname();; 

% --------------------------------------------------------------------- %
% Put the pathname to the library wordn onto the search path.		%
% --------------------------------------------------------------------- %

let path = this_lib_path ^  `/res_quan/` in
    (print_string `Updating search path`;
     print_newline();
     set_search_path (union (search_path()) [`.`; path]));;

% --------------------------------------------------------------------- %
% Add the help files to online help.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/res_quan/help/entries/` in
    (print_string `Updating help search path`; 
     print_newline();
     set_help_search_path (union [path] (help_search_path())));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

load(`cond_rewr`, get_flag_value `print_lib`);;
