% ===================================================================== %
% FILE		: fixpoints.ml						%
% DESCRIPTION   : loads the library fixpoints into hol.			%
%									%
% AUTHOR        : M. Gordon						%
% DATE		: 3 April 1989						%
% MODIFIED	: 11 July 1989 ("UNION" renamed "LUB") 			%
% ===================================================================== %


% --------------------------------------------------------------------- %
% Put the pathname to the library fixpoints onto the search path.	%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/fixpoints/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory fixpoints			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory fixpoints a new parent`;
         print_newline();
         new_parent `fixpoints`)
   else (load_theory `fixpoints` ?
         (print_string `Defining ML function load_fixpoints`;
          print_newline() ;
          loadf `load_fixpoints`));;

% --------------------------------------------------------------------- %
% Set up autoloading of (selected) theorems from fixpoints.th		%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `fixpoints`)) then
   (map autoload_theory
        [`definition`, `fixpoints`, `LESS_DEF`;
         `definition`, `fixpoints`, `FIX`;
         `definition`, `fixpoints`, `ITER`;
         `definition`, `fixpoints`, `LUB`;
         `definition`, `fixpoints`, `BOT`;
         `definition`, `fixpoints`, `LIM_ITER`;
         `definition`, `fixpoints`, `CHAIN`;
         `definition`, `fixpoints`, `TRIV_CHAIN`;
         `definition`, `fixpoints`, `MONO`;
         `definition`, `fixpoints`, `CONTINUOUS`;
         `definition`, `fixpoints`, `ADMITS_INDUCTION`;
       
         `theorem`, `fixpoints`, `TRIV_CHAIN_LEMMA`;
         `theorem`, `fixpoints`, `CHAIN_ITER`;
         `theorem`, `fixpoints`, `LUB_CHAIN_LEMMA`;
         `theorem`, `fixpoints`, `LAMB_TRIV_CHAIN`;
         `theorem`, `fixpoints`, `CONT_MONO`;
         `theorem`, `fixpoints`, `FIX_LEMMA`;
         `theorem`, `fixpoints`, `LEAST_FIX_LEMMA`;
         `theorem`, `fixpoints`, `LEAST_FIX_THM`;
         `theorem`, `fixpoints`, `LIM_ITER_THM`;
         `theorem`, `fixpoints`, `FIX_EXISTS`;
         `theorem`, `fixpoints`, `FIX_THM`;
         `theorem`, `fixpoints`, `ANTISYM_LEMMA`;
         `theorem`, `fixpoints`, `FIX_LIM_ITER_THM`;
         `theorem`, `fixpoints`, `HOARE_ADMITS_LEMMA`;
         `theorem`, `fixpoints`, `SCOTT_INDUCTION_LEMMA`;
         `theorem`, `fixpoints`, `SCOTT_INDUCTION_THM`]; ());;


