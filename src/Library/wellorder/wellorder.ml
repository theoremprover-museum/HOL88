%============================================================================%
% Load the wellorder library [JRH 92.05.30]                                  %
%============================================================================%

%----------------------------------------------------------------------------%
% Extend the search path                                                     %
%----------------------------------------------------------------------------%

let path = library_pathname() ^ `/wellorder/` in
    tty_write `Updating search path`;
    set_search_path (union (search_path()) [path]);;

%----------------------------------------------------------------------------%
% And the help search path                                                   %
%----------------------------------------------------------------------------%

let path = library_pathname() ^ `/wellorder/entries/` in
    print_newline();
    tty_write `Updating help search path`;
    set_help_search_path (union [path] (help_search_path()));;

%----------------------------------------------------------------------------%
% Load (or attempt to load) the theory "WELLORDER"                           %
%----------------------------------------------------------------------------%

if draft_mode()
   then (print_newline();
         print_string `Declaring theory WELLORDER a new parent`;
         print_newline();
         new_parent `WELLORDER`)
   else (print_newline();
         load_theory `WELLORDER` ?
         (tty_write `Defining ML function load_wellorder`;
          loadf `load_wellorder`;
          print_newline()));;

%----------------------------------------------------------------------------%
% Set up autoloading of definitions and theorems from WELLORDER.th           %
%----------------------------------------------------------------------------%

if (draft_mode() or (current_theory() = `WELLORDER`)) then
        let defs = map fst (definitions `WELLORDER`) in
            map (\st. autoload_theory(`definition`,`WELLORDER`,st)) defs;
        let thms = [`KL`; `HP`; `ZL`; `WO`] in
            map (\st. autoload_theory(`theorem`,`WELLORDER`,st)) thms;
        delete_cache `WELLORDER`; ();;

%----------------------------------------------------------------------------%
% Provide functions to set and unset the interface map                       %
%----------------------------------------------------------------------------%

let set_wo_map,unset_wo_map =
  let extras =
   [`subset`,`wo_subset`;
    `Union`,`wo_Union`;
    `fl`,`wo_fl`;
    `poset`,`wo_poset`;
    `chain`,`wo_chain`;
    `woset`,`wo_woset`;
    `inseg`,`wo_inseg`;
    `linseg`,`wo_linseg`;
    `ordinal`,`wo_ordinal`;
    `less`,`wo_less`] in
  (\():void. do set_interface_map(union (interface_map()) extras)),
  (\():void. do set_interface_map(subtract (interface_map()) extras));;
