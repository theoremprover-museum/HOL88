%============================================================================%
% Load the "reals" library                                                   %
%============================================================================%

%----------------------------------------------------------------------------%
% Extend the search path                                                     %
%----------------------------------------------------------------------------%

let path = library_pathname() ^ `/reals/theories/` in
    tty_write `Updating search path`;
    set_search_path (union (search_path()) [path]);;

%----------------------------------------------------------------------------%
% And the help search path                                                   %
%----------------------------------------------------------------------------%

let path = library_pathname() ^ `/reals/entries/` in
    print_newline();
    tty_write `Updating help search path`;
    set_help_search_path (union [path] (help_search_path()));;

%----------------------------------------------------------------------------%
% Load (or attempt to load) the theory "TRANSC"                              %
%----------------------------------------------------------------------------%

if draft_mode()
   then (print_newline();
         print_string `Declaring theory TRANSC a new parent`;
         print_newline();
         new_parent `TRANSC`)
   else (print_newline();
         load_theory `TRANSC` ?
         (tty_write `Defining ML function load_reals`;
          loadf `load_reals`;
          print_newline()));;

%----------------------------------------------------------------------------%
% Set up autoloading of definitions and theorems from REAL.th and TRANSC.th  %
%----------------------------------------------------------------------------%

tty_write `Setting up autoloading of main theorems...\L`;;

loadt `autoload_reals`;;

%----------------------------------------------------------------------------%
% Set up interface map                                                       %
%----------------------------------------------------------------------------%

let real_interface_map =
[               `--`,`real_neg`;
 `num_add`,`+`;  `+`,`real_add`;
 `num_mul`,`*`;  `*`,`real_mul`;
 `num_sub`,`-`;  `-`,`real_sub`;
 `num_lt`,`<` ;  `<`,`real_lt`;
 `num_le`,`<=`; `<=`,`real_le`;
 `num_gt`,`>` ;  `>`,`real_gt`;
 `num_ge`,`>=`; `>=`,`real_ge`;
               `inv`,`real_inv`;
                 `&`,`real_of_num`];;
