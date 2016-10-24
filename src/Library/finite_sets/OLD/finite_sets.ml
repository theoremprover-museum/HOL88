% ===================================================================== %
% FILE		: finite_sets.ml					%
% DESCRIPTION   : loads the library "sets" into hol.			%
%									%
% DATE		: 91.01.23						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library finite_sets onto the search path.	%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/finite_sets/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory finite_sets			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory finite_sets a new parent`;
         print_newline();
         new_parent `finite_sets`)
   else (load_theory `finite_sets` ?
         (print_string `Defining ML function load_finite_sets`;
          print_newline() ;
          loadf `load_finite_sets`));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `finite_sets`)) then
   let path st = library_pathname() ^ `/finite_sets/` ^ st in
       load(path `set_ind`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from finite_sets.th	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `finite_sets`)) then
   let defs = map fst (definitions `finite_sets`) in
       map (\name. autoload_theory(`definition`,`finite_sets`,name)) defs;
   let thms = map fst (theorems `finite_sets`) in
       map (\name. autoload_theory(`theorem`,`finite_sets`,name)) thms; 
   delete_cache `finite_sets`; ();;
