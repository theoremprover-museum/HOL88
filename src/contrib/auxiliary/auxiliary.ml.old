% ===================================================================== %
% FILE		: auxiliary.ml						%
% DESCRIPTION   : loads the library "auxiliary" into hol.		%
%									%
% AUTHOR	: T. Kalker						%
% DATE		: 28 August 1989					%
% REVISED	: 90.12.01 (TFM)					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Put the pathname to the library auxiliary onto the search path.	%
% --------------------------------------------------------------------- %

let path = library_pathname() ^ `/auxiliary/` in
    print_string `Updating search path`; print_newline();
    set_search_path (union (search_path()) [path]);;

% --------------------------------------------------------------------- %
% Load (or attempt to load) the theory auxiliary			%
% --------------------------------------------------------------------- %

if draft_mode() 
   then (print_string `Declaring theory auxiliary a new parent`;
         print_newline();
         new_parent `auxiliary`)
   else (load_theory `auxiliary` ?
         (print_string `Defining ML function load_auxiliary`;
          print_newline() ;
          loadf `load_auxiliary`));;

% --------------------------------------------------------------------- %
% Load compiled code if possible					%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `auxiliary`)) then
   let path st = library_pathname() ^ `/auxiliary/` ^ st in
       load(path `functions`, get_flag_value `print_lib`);
       load(path `tactics`, get_flag_value `print_lib`);
       load(path `rules`, get_flag_value `print_lib`);
       load(path `conversions`, get_flag_value `print_lib`);;

% --------------------------------------------------------------------- %
% Set up autoloading.							%
% --------------------------------------------------------------------- %

if (draft_mode() or (current_theory() = `auxiliary`)) then
    (let defs = map fst (definitions `auxiliary`) in
         map (\name. autoload_theory(`definition`,`auxiliary`,name)) defs; 
     let thms = map fst (theorems `auxiliary`) in
         map (\name. autoload_theory(`theorem`,`auxiliary`,name)) thms; ());;

% --------------------------------------------------------------------- %
% Make a couple of abbreviations.		(why? [TFM])		%
% --------------------------------------------------------------------- %

let goal = g
and apply  = expandf;;
