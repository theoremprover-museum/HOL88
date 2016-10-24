% ===================================================================== %
% FILE		: sets.ml						%
% DESCRIPTION   : loads the library "sets" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 90.12.01						%
% REVISED	: 91.01.23						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library sets onto the search path.		%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/sets/` in
    tty_write `Updating search path`; 
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Add the help files to online help.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/sets/help/entries/` in
    print_newline();
    tty_write `Updating help search path`; 
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory sets				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_newline();
         print_string `Declaring theory sets a new parent`;
         print_newline();
         new_parent `sets`)
   else (print_newline();
         load_theory `sets` ?
         (tty_write `Defining ML function load_sets`;
          loadf `load_sets`;
          print_newline()));;

% --------------------------------------------------------------------- %
% Activate parser/pretty-printer support for sets (if possible).	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `sets`)) then
   (define_set_abstraction_syntax `GSPEC`;
    define_finite_set_syntax(`EMPTY`,`INSERT`);
    set_flag(`print_set`,true); ());;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `sets`)) then
   let path st = library_pathname() ^ `/sets/` ^ st in
       load(path `gspec`, get_flag_value `print_lib`);
       load(path `set_ind`, get_flag_value `print_lib`);
       load(path `fset_conv`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from sets.th		%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `sets`)) then
   let defs = map fst (definitions `sets`) in
       map (\name. autoload_theory(`definition`,`sets`,name)) defs;
   let thms = map fst (theorems `sets`) in
       map (\name. autoload_theory(`theorem`,`sets`,name)) thms; 
   delete_cache `sets`; ();;


