% --------------------------------------------------------------------- %
% FILE		: int_mod.ml						%
% DESCRIPTION   : Loads definitions and theorems from the theories	%
%		  int_sbgp.th and int_mod.th contained in this library,	%
%		  along with the functions for intstantiating the 	%
%		  modular arithmetic with a particular integer value.	%
%		  It also adds this directory to the library search	%
%		  path.							%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.4.22						%
% REVISED [TFM] : 91.01.29						%
%-----------------------------------------------------------------------%

% --------------------------------------------------------------------- %
% First, load the integer library					%
% --------------------------------------------------------------------- %

load_library `integer`;;

% --------------------------------------------------------------------- %
% Put the pathname to the library onto the search path.			%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/int_mod/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory int_mod				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory int_mod a new parent`;
         print_newline();
         new_parent `int_mod`)
   else (load_theory `int_mod` ?
         (print_string `Defining ML function load_int_mod`;
          print_newline() ;
          loadf `load_int_mod`));;

% --------------------------------------------------------------------- %
% Load start_groups from group library.					%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/group/start_groups` in
    load(path, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading of definitions and theorems from int_mod.th	%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `int_mod`)) then
   include_theory `int_sbgp`; include_theory `int_mod`; ();;

% --------------------------------------------------------------------- %
% Attempt to load code.							%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `int_mod`)) then
   loadt `inst_int_mod`;();;

