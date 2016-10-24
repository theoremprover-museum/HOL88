% ===================================================================== %
% FILE		: pred_sets.ml						%
% DESCRIPTION   : loads the library pred_sets into hol.			%
%									%
% AUTHOR        : T. Kalker						%
% DATE		: 18 September 1989					%
% REVISED       : 90.12.02 by T Melham					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, load the fixpoints library					%
% --------------------------------------------------------------------- %

load_library `fixpoints`;;

% --------------------------------------------------------------------- %
% Put the pathname to the library pred_sets onto the search path	%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/pred_sets/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory pred_sets			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory pred_sets a new parent`;
         print_newline();
         new_parent `pred_sets`)
   else (load_theory `pred_sets` ?
         (print_string `Defining ML function load_pred_sets`;
          print_newline() ;
          loadf `load_pred_sets`));;

% --------------------------------------------------------------------- %
% Special symbols.							%
% --------------------------------------------------------------------- %

new_special_symbol `-->>`;;
new_special_symbol `>-->`;;   
new_special_symbol `<-->`;;

% --------------------------------------------------------------------- %
% Need to autoload a definition from fixpoints.				%
% --------------------------------------------------------------------- %

if (mem `fixpoints` (ancestry())) then
   (autoload_theory(`definition`,`fixpoints`,`BOT`) ; ());;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems			%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `pred_sets`)) then
   let defs = map fst (definitions `pred_sets`) in
       map (\name. autoload_theory(`definition`,`pred_sets`,name)) defs;
   let thms = map fst (theorems `pred_sets`) in
       map (\name. autoload_theory(`theorem`,`pred_sets`,name)) thms; 
   delete_cache `pred_sets`; ();;
