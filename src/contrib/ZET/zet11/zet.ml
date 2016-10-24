% FILE		: zet.ml						%
% DESCRIPTION   : loads the library zet into hol.       	        %
%									%
% AUTHOR        : T. Kalker						%
% DATE		: 10 July 1989						%


if draft_mode() 
 then (if not(mem `zet` (parents (current_theory()))) 
         then
            (print_newline();
             print_string `zet declared a new parent`;
             print_newline();
             new_parent `zet`)
         else 
            (print_newline();
             print_string `zet is parent`;
             print_newline())
       )
 else (load_theory`zet` ? print_newline());;  

load_from_lib false `auxiliary` `functions`;;

autoload_defs_and_thms `zet`;; 

map 
  loadx (words `zet_tactics zet_ind`);;

let goal = g
and apply  = expandf;;

