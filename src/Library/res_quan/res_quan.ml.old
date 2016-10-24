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
% Load (or attempt to load) the theory res_quan				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory res_quan a new parent`;
         print_newline();
         new_parent `res_quan`)
   else (load_theory `res_quan` ?
         (print_string `Defining ML function load_res_quan`;
          print_newline() ;
          loadf `load_res_quan`));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `res_quan`)) then
    (load(`cond_rewr`, get_flag_value `print_lib`);
     load(`res_rules`, get_flag_value `print_lib`));
    ();;

% --------------------------------------------------------------------- %
% Set up autoloading of  theorems and definitions      		        %
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `res_quan`)) then
  let autoload_thms thy =
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 () 
  in
    (autoload_thms `res_quan`;
     delete_cache `res_quan`;
     ());;
