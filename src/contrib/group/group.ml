% ===================================================================== %
% FILE          : group.ml                                              %
% DESCRIPTION   : Loads definitions, theorems, rules and tactics        %
%                 developed for the first-order and higher-order        %
%                 group theory contained in this library.               %
%                                                                       %
%                                                                       %
% AUTHOR        : E. L. Gunter                                          %
% DATE          : 89.3.23                                               %
% REVISED       : T Melham 90.12.02                                     %
% REVISED       : J Harrison 91.07.22                                   %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library group onto the search path.           %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/group/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load compiled code start_groups (can always be loaded)                %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/group/start_groups` in
    load(path, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory more_gp                          %
% --------------------------------------------------------------------- %

if draft_mode()
   then (print_string `Declaring theory more_gp a new parent`;
         print_newline();
         new_parent `more_gp`)
   else (load_theory `more_gp` ?
         (print_string `Defining ML function load_group`;
          print_newline() ;
          loadf `load_group`));;

% --------------------------------------------------------------------- %
% Sets up autoloading (if possible).                                    %
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `more_gp`)) then
   (include_theory `elt_gp`; include_theory `more_gp`); ();;


% --------------------------------------------------------------------- %
% Load group-specific code if possible                                  %
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `more_gp`)) then
   let path st = library_pathname() ^ `/group/` ^ st in
       load(path `group_tac`, get_flag_value `print_lib`);
       load(path `inst_gp`, get_flag_value `print_lib`);;
