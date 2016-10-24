new_special_symbol `!*`;;
new_special_symbol `?*`;;
new_special_symbol `~*`;;
new_special_symbol `/\\*`;;
new_special_symbol `\\/*`;;
new_special_symbol `!<=*`;;
new_special_symbol `?<=*`;;
new_special_symbol `/<=\\*`;;
new_special_symbol `\\<=/*`;;
new_special_symbol `/<\\*`;;
new_special_symbol `\\</*`;;
new_special_symbol `?<*`;;
new_special_symbol `<*`;;
new_special_symbol `>*`;;
new_special_symbol `>=*`;;
new_special_symbol `<=*`;;
new_special_symbol `=*`;;
new_special_symbol `=>*`;;
new_special_symbol `==>*`;;
new_special_symbol `+*`;;
new_special_symbol `-*`;;
new_special_symbol `**`;;

let UNDISCH_ALL_EXCEPT_TAC term_list =
  let th_tac = \(th:thm) (tac:tactic).
        (if mem (concl th) term_list
           then ALL_TAC
           else (UNDISCH_TAC (concl th))) THEN tac in
  let u_asml = (\thml:thm list. itlist  th_tac thml ALL_TAC)
in
   ASSUM_LIST u_asml;;

%
let UNDISCH_ALL_TAC =
  let th_tac = (\(th:thm) (tac:tactic). (UNDISCH_TAC (concl th)) THEN tac) in
  let u_asml = (\thml:thm list. itlist  th_tac thml ALL_TAC)
in
   ASSUM_LIST u_asml;;
%
let UNDISCH_ALL_TAC =
  let th_tac = (\(th:thm) (tac:tactic). (MP_TAC th) THEN tac) in
  let u_asml = (\thml:thm list. itlist  th_tac thml ALL_TAC)
in
   POP_ASSUM_LIST u_asml;;

let UNDISCH_ONE_TAC =
  let th_tac = (\(th:thm) (tac:tactic). (UNDISCH_TAC (concl th)) THEN tac) in
  let u_asm  = (\th:thm. itlist  th_tac [th] ALL_TAC)
in
   FIRST_ASSUM u_asm;;

let autoload_defs_and_thms thy =
 load_theory thy;
 map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ();;
