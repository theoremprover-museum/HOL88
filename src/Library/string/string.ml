% ===================================================================== %
% FILE		: string.ml						%
% DESCRIPTION   : loads the library "string" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 87.10.09						%
% REVISED	: 90.12.01, 91.01.23					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library string onto the search path.		%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/string/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Add the string help files to online help.				%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/string/help/entries/` in
    print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory string				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory string a new parent`;
         print_newline();
         new_parent `string`)
   else (load_theory `string` ?
         (print_string `Defining ML function load_string`;
          print_newline() ;
          loadf `load_string`));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `string`)) then
   let path st = library_pathname() ^ `/string/` ^ st in
       load(path `stringconv`, get_flag_value `print_lib`);
       load(path `ascii`, get_flag_value `print_lib`);
       load(path `string_rules`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of (selected) theorems from string.th		%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `string`)) then
   let thms = map fst (theorems `ascii`) in
       map (\name. autoload_theory(`theorem`,`ascii`,name)) thms; 
   let thms = map fst (theorems `string`) in
       map (\name. autoload_theory(`theorem`,`string`,name)) thms;
   delete_cache `ascii`; delete_cache `string`; ();;



