% ===================================================================== %
% FILE		: WF.ml	        					%
% DESCRIPTION   : loads the library "WF" into hol.			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library WF onto the search path.		%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/WF/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory WF 				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory WF a new parent`;
         print_newline();
         new_parent `WF`)
   else (load_theory `WF` ?
         (print_string `Loading library WF`;
          print_newline() ;
          loadf `mk_WF`));;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from WF.th		%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `WF`)) then
   let defs = map fst (definitions `WF`) in
       map (\name. autoload_theory(`definition`,`WF`,name)) defs;
   let thms = map fst (theorems `WF`) in
       map (\name. autoload_theory(`theorem`,`WF`,name)) thms; 
   delete_cache `WF`; ();;



