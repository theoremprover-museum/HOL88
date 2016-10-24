% hol-init.ml %
% Pervasive ML definitions %

% --------------------------------------------------------------------- %
% Utilities for loading theories.                                       %
% --------------------------------------------------------------------- %

let smart_load_theory thy =
    if draft_mode() 
     then (if not(mem thy (parents (current_theory()))) 
             then
                (print_newline();
                 print_string (thy^` declared a new parent`);
                 print_newline();
                 new_parent thy)
             else 
                (print_newline();
                 print_string (thy^` is already a parent`);
                 print_newline())
           )
     else (load_theory thy ? print_newline());;  

let autoload_all_defs_and_thms thy =
   let defs = map fst (definitions thy) in
       map (\name. autoload_theory(`definition`,thy,name)) defs;
   let thms = map fst (theorems thy) in
       map (\name. autoload_theory(`theorem`,thy,name)) thms; 
   delete_cache thy;
   print_string(`Definitions and theorems from theory `^thy^` set to autoload`);
   print_newline();;
