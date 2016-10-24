% ===================================================================== %
% FILE          : numeral.ml                                            %
% DESCRIPTION   : loads the library "numeral" into hol.                 %
%                                                                       %
% AUTHOR        : T. Melham                                             %
% DATE          : 92.02.08                                              %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Fail with an error message if HOL isn't in draft mode.                %
% --------------------------------------------------------------------- %

if not (draft_mode()) then
  failwith `HOL must be in draft mode to load the numeral library.`;;

% --------------------------------------------------------------------- %
% Put the pathname to the library numeral onto the search path, and     %
% add the help files to online help.                                    %
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/numeral/` in
        (print_string `Updating search paths to include the numeral library`;
         print_newline();
         set_search_path (union (search_path()) [path]);
         set_help_search_path (union [path] (help_search_path())));;

% --------------------------------------------------------------------- %
% Load the theory numeral.                                              %
% --------------------------------------------------------------------- %

print_string `Declaring theory numeral a new parent`;;
print_newline();;
new_parent `numeral`;;
let t = `numeral` in
map (\s. autoload_theory(`definition`,t,fst s)) (definitions t);
map (\s. autoload_theory(`theorem`,t,fst s)) (theorems t);;

% --------------------------------------------------------------------- %
% The reduce library is needed in a few places.                         %
% --------------------------------------------------------------------- %

load_library `reduce`;;

% --------------------------------------------------------------------- %
% Load the numeral proof rules.                                         %
% --------------------------------------------------------------------- %

let path st = library_pathname() ^ `/numeral/` ^ st in
        (print_string `Loading numeral proof rules`;
         print_newline();
         load(path `numeral_rules`, get_flag_value `print_lib`));;
