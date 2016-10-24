% ===================================================================== %
% FILE		: pred_sets.ml						%
% DESCRIPTION   : loads the library "pred_sets" into hol.		%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 92.02.08						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library pred_sets onto the search path.	%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/pred_sets/` in
    tty_write `Updating search path`; 
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Add the help files to online help.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/pred_sets/help/entries/` in
    print_newline();
    tty_write `Updating help search path`; 
    set_help_search_path (union [path] (help_search_path()));;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory pred_sets			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_newline();
         print_string `Declaring theory pred_sets a new parent`;
         print_newline();
         new_parent `pred_sets`)
   else (print_newline();
         load_theory `pred_sets` ?
         (tty_write `Defining ML function load_pred_sets`;
          loadf `load_pred_sets`;
          print_newline()));;

% --------------------------------------------------------------------- %
% Activate parser/pretty-printer support for pred_sets (if possible).	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `pred_sets`)) then
   (define_set_abstraction_syntax `GSPEC`;
    define_finite_set_syntax(`EMPTY`,`INSERT`);
    set_flag(`print_set`,true); ());;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `pred_sets`)) then
   let path st = library_pathname() ^ `/pred_sets/` ^ st in
       load(path `gspec`, get_flag_value `print_lib`);
       load(path `set_ind`, get_flag_value `print_lib`);
       load(path `fset_conv`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from pred_sets.th	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `pred_sets`)) then
   let defs = map fst (definitions `pred_sets`) in
       map (\name. autoload_theory(`definition`,`pred_sets`,name)) defs;
   let thms = map fst (theorems `pred_sets`) in
       map (\name. autoload_theory(`theorem`,`pred_sets`,name)) thms; 
   delete_cache `pred_sets`; ();;


