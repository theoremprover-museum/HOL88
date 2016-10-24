% FILE		: card.ml						%
% DESCRIPTION   : loads the library card into hol.       	        %
%									%
% AUTHOR        : T. Kalker						%
% DATE		: 10 July 1989						%


if draft_mode() 
 then (if not(mem `card` (parents (current_theory()))) 
         then
            (print_newline();
             print_string `card declared a new parent`;
             print_newline();
             new_parent `card`)
         else 
            (print_newline();
             print_string `card is parent`;
             print_newline())
       )
 else (load_theory`card` ? print_newline());; 

new_special_symbol `<<<` ? print_newline();;

load_from_lib false `auxiliary` `functions`;;         

autoload_defs_and_thms `card`;;

let goal = g
and apply  = expandf;;

