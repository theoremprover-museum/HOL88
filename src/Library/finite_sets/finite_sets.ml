% ===================================================================== %
% FILE		: finite_sets.ml					%
% DESCRIPTION   : loads the library "finite_sets" into hol.		%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 92.02.15						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library finite_sets onto the search path.	%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/finite_sets/` in
    tty_write `Updating search path`; 
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Add the help files to online help.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/finite_sets/help/entries/` in
    print_newline();
    tty_write `Updating help search path`; 
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory finite_sets			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_newline();
         print_string `Declaring theory finite_sets a new parent`;
         print_newline();
         new_parent `finite_sets`)
   else (print_newline();
         load_theory `finite_sets` ?
         (tty_write `Defining ML function load_finite_sets`;
          loadf `load_finite_sets`;
          print_newline()));;

% --------------------------------------------------------------------- %
% Activate parser/pretty-printer support for finite_sets (if possible).	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `finite_sets`)) then
   (define_finite_set_syntax(`EMPTY`,`INSERT`);
    set_flag(`print_set`,true); ());;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `finite_sets`)) then
   let path st = library_pathname() ^ `/finite_sets/` ^ st in
       load(path `set_ind`, get_flag_value `print_lib`);
       load(path `fset_conv`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from finite_sets.th	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `finite_sets`)) then
   let defs = map fst (definitions `finite_sets`) in
       map (\name. autoload_theory(`definition`,`finite_sets`,name)) defs;
   let thms = map fst (theorems `finite_sets`) in
       map (\name. autoload_theory(`theorem`,`finite_sets`,name)) thms; 
   delete_cache `finite_sets`; ();;


