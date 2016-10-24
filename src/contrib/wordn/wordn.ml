% ===================================================================== %
% FILE		: wordn.ml						%
% DESCRIPTION   : loads the library "wordn" into hol.			%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 90.08.23						%
% MODIFIED by	: Wai Wong						%
% DATE		: 2 April 1992						%
%   	Modified to load more codes and theories			%
% ===================================================================== %


% --------------------------------------------------------------------- %
% Put the pathname to the library wordn onto the search path.		%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/wordn/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [`.`; path]);;

load_library `more_lists`;;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory wordn				%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory wordn a new parent`;
         print_newline();
         new_parent `wordn`)
   else (load_theory `wordn` ?
         (print_string `Defining ML function load_wordn`;
          print_newline() ;
          loadf `load_wordn`));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `wordn`)) then
   let path st = % `./wordn/` ^ % st in
    (map (\name. load(path name, get_flag_value `print_lib`))
    	[`genfuns`; `wordn_rules`; `wordn_conv`; `oconv`;
         `wordn_bit_op`; `wordn_tacs`; `wordn_bits`;
    	 `wordn_num`]);
    ();;


% --------------------------------------------------------------------- %
% Set up autoloading of  theorems and definitions      		        %
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `wordn`)) then
  let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 () 
  in
    (autoload_defs_and_thms `wordn_base`;
     autoload_defs_and_thms `wordn_bitops`;
     autoload_defs_and_thms `wordn_num`;
     delete_cache `wordn_base`;
     delete_cache `wordn_bitops`;
     delete_cache `wordn_num`;
     ());;
