% ===================================================================== %
% FILE		: more_arithmetic.ml					%
% DESCRIPTION   : loads the library "more_arithmetic" into hol.		%
%									%
% AUTHOR	: P. Curzon						%
% DATE		: 8.4.91						%
% ===================================================================== %

% PC 13/8/92 auxiliary library no longer needed%
%load_library `auxiliary`;;%

% --------------------------------------------------------------------- %
% Put the pathname to the library more_arithmetic onto the search path. %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/more_arithmetic/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;



% --------------------------------------------------------------------- %
% Add the string help files to online help.%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/more_arithmetic/help/entries/` in
    print_string `Updating help search path`; print_newline();
    set_help_search_path (union [path] (help_search_path()));;



% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory more_arithmetic			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory more_arithmetic a new parent`;
         print_newline();
         new_parent `more_arithmetic`)
   else (load_theory `more_arithmetic` ?
         (print_string `Defining ML function load_more_arithmetic`;
          print_newline() ;
          loadf `load_more_arithmetic`));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `more_arithmetic`)) then
   let path st = library_pathname() ^ `/more_arithmetic/` ^ st in
       load(path `num_convs`, get_flag_value `print_lib`);
       load(path `num_tac`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of  theorems and definitions      		        %
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `more_arithmetic`)) then
  let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ()
  in
        autoload_defs_and_thms `ineq`;
        autoload_defs_and_thms `zero_ineq`;
        autoload_defs_and_thms `suc`;
        autoload_defs_and_thms `add`;
        autoload_defs_and_thms `sub`;
        autoload_defs_and_thms `pre`;
        autoload_defs_and_thms `mult`;
        autoload_defs_and_thms `min_max`;
        autoload_defs_and_thms `odd_even`;
        autoload_defs_and_thms `div_mod`;
        delete_cache `ineq`;
        delete_cache `zero_ineq`;
        delete_cache `suc`;
        delete_cache `add`;
        delete_cache `sub`;
        delete_cache `pre`;
        delete_cache `mult`;
        delete_cache `min_max`;
        delete_cache `odd_even`;
        delete_cache `div_mod`; ();;

