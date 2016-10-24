% ===================================================================== %
% FILE		: integer.ml						%
% DESCRIPTION   : Loads selected definitions, theorems, rules and	%
%		  tactics developed for the  theory of the integers.	%
%		  All representation dependent facts are excluded.	%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.27						%
%									%
% Modified 23 July 1989 to include more theorems to be autoloaded. ELG	%
%									%
% REVISED	: T Melham 90.12.02 91.01.29				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, load the group library						%
% --------------------------------------------------------------------- %

load_library `group`;;

% --------------------------------------------------------------------- %
% Put the pathname to the library onto the search path.			%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/integer/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory integer				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory integer a new parent`;
         print_newline();
         new_parent `integer`)
   else (load_theory `integer` ?
         (print_string `Defining ML function load_integer`;
          print_newline() ;
          loadf `load_integer`));;

% --------------------------------------------------------------------- %
% Load start_groups from group library.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/group/start_groups` in
    load(path, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Load compiled code, if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `integer`)) then
   let path st = library_pathname() ^ `/integer/` ^ st in
       load(path `num_tac`, get_flag_value `print_lib`);
       load(path `integer_tac`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from integer.th	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `integer`)) then
   let defs = map fst (definitions `integer`) in
       map (\name. autoload_theory(`definition`,`integer`,name)) defs;
   let thms = map fst (theorems `integer`) in
       map (\name. autoload_theory(`theorem`,`integer`,name)) thms; 
   delete_cache `integer`; ();;
