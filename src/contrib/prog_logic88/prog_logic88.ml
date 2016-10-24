% ===================================================================== %
% FILE		: prog_logic88.ml					%
% DESCRIPTION   : loads the library prog_logic88 into hol.		%
%									%
% AUTHOR        : M. Gordon						%
% DATE		: 6 April 1989						%
% REVISED	: 26 January 1991					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, load the string library					%
% --------------------------------------------------------------------- %

load_library `string`;;

% --------------------------------------------------------------------- %
% Put the pathname to the library onto the search path.			%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/prog_logic88/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory prog_logic88			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory prog_logic88 a new parent`;
         print_newline();
         new_parent `prog_logic88`)
   else (load_theory `prog_logic88` ?
         (print_string `Defining ML function load_prog_logic88`;
          print_newline() ;
          loadf `load_prog_logic88`));;

% --------------------------------------------------------------------- %
% Load compiled code and set up autoloading if possible			%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `prog_logic88`)) then
   let path st = library_pathname() ^ `/prog_logic88/` ^ st in
   let loadfn st = load(path st, get_flag_value `print_lib`) in
      map 
       loadfn
         (words `autoload syntax_functions hol_match hoare_logic 
                 vc_gen halts_logic halts_vc_gen`); ();;



