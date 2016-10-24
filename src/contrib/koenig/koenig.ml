% ===================================================================== %
% FILE		: koenig.ml						%
% DESCRIPTION   : load theory koenig					%
% AUTHOR        : Paul Loewenstein                      		%
% DATE		: 							%
% MODIFIED	: 11 April 1990 (for HOL88-1-12)                        %
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, load the libraries						%
% --------------------------------------------------------------------- %

load_library `num_thms`;;
load_library `quantifier`;;
load_library `pair_fun`;;
load_library `unwind_prune`;;
load_library `taut`;;

% --------------------------------------------------------------------- %
% Put the pathname to the library koenig onto the search path.		%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/koenig/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory koenig				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory koenig a new parent`;
         print_newline();
         new_parent `koenig`)
   else (load_theory `koenig` ?
         (print_string `Defining ML function load_koenig`;
          print_newline() ;
          loadf `load_koenig`));;

% --------------------------------------------------------------------- %
% Set up autoloading of theorems from koenig.th		        	%
% --------------------------------------------------------------------- %

 map (\name. autoload_theory(`definition`,`koenig`,name))
     (map fst (definitions `koenig`));;
 map (\name. autoload_theory(`theorem`,`koenig`,name))
     (map fst (theorems `koenig`));;
