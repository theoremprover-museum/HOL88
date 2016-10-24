% ===================================================================== %
% FILE		: bags.ml						%
% DESCRIPTION   : loads the library "bags" into hol.			%
%									%
% DATE		: 90.12.01						%
% UPDATED (sk)  : 91.01.25                                              %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library `bags` onto the search path.		%
% --------------------------------------------------------------------- %



let path = library_pathname() ^ `/bags/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory `bags`				%
% --------------------------------------------------------------------- %

if draft_mode() 
 then (print_string `Declaring theory bags a new parent`;
       print_newline();
       new_parent `bags`)
   else (load_theory `bags` ?
         (print_string `Defining ML function load_bags`;
          print_newline() ;
          loadf `load_bags`));;


% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems			%
% --------------------------------------------------------------------- %


if (draft_mode() or (current_theory() = `bags`)) then
   let defs = map fst (definitions `bags`) in
       map (\name. autoload_theory(`definition`,`bags`,name)) defs;
   let thms = map fst (theorems `bags`) in
       map (\name. autoload_theory(`theorem`,`bags`,name)) thms; 
   let defs = map fst (definitions `more_arithmetic`) in
       map (\name. autoload_theory(`definition`,`more_arithmetic`,name)) defs;
   let thms = map fst (theorems `more_arithmetic`) in
       map (\name. autoload_theory(`theorem`,`more_arithmetic`,name)) thms; 
   delete_cache `bags`; ();;




