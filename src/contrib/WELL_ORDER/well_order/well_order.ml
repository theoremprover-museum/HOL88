% FILE		: well_order.ml						%
% DESCRIPTION   : loads the library WELL-ORDER into hol.	        %
%									%
% AUTHOR        : T. Kalker						%
% DATE		: 10 July 1989						%


if draft_mode() 
 then (if not(mem `transfinite` (parents (current_theory()))) 
         then
            (print_newline();
             print_string `transfinite declared a new parent`;
             print_newline();
             new_parent `transfinite`)
         else 
            (print_newline();
             print_string `transfinite is parent`;
             print_newline())
       )
 else (load_theory`transfinite` ? print_newline());;   

load_library `set`;;

autoload_defs_and_thms `well_order`;;

autoload_defs_and_thms `transfinite`;;
              
loadx `wo_fns`;;

let goal = g
and apply  = expandf;;

