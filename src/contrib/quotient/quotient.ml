% ===================================================================== %
% FILE		: quotient.ml						%
% DESCRIPTION   : loads the library quotient into hol.			%
%									%
% AUTHOR        : T. Kalker						%
% DATE		: 7 June 1989						%
% REVISED (TFM) : 29 January 1991					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, load the auxiliary.						%
% --------------------------------------------------------------------- %

load_library `auxiliary`;;


% --------------------------------------------------------------------- %
% Put the pathname to the library onto the search path.			%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/quotient/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory quotient				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory quotient a new parent`;
         print_newline();
         new_parent `quotient`)
   else (load_theory `quotient` ?
         (print_string `Defining ML function load_quotient`;
          print_newline() ;
          loadf `load_quotient`));;

% --------------------------------------------------------------------- %
% Set up autoloading if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `quotient`)) then
   (autoload_theory(`definition`,`quotient`,`REFLEX`);
    autoload_theory(`definition`,`quotient`,`SYMMETRY`);
    autoload_theory(`definition`,`quotient`,`TRANSITIVITY`);
    autoload_theory(`definition`,`quotient`,`EQUIVALENCE`); ());;


% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `quotient`)) then
   let path st = library_pathname() ^ `/quotient/` ^ st in
       load(path `quotientfns`, get_flag_value `print_lib`);;



