%
| Makes lnum parent and sets up autoloading
%

load_library `more_arithmetic`;;

new_special_symbol `<-+`;;
new_special_symbol `<+`;;
new_special_symbol `++`;;
new_special_symbol `--`;;

set_search_path (search_path() @ [`/usr/local/hol/contrib/prog_logic92/`]);;

new_parent `lnum`;;
autoload_defs_and_thms `lnum`;;

letrec lnum_cases_TAC l = 
	if null l then ALL_TAC else 
	REPEAT GEN_TAC
	THEN STRUCT_CASES_TAC (SPEC (hd l) lnum_cases)  
	THEN lnum_cases_TAC (tl l);;

let LNUM_LIFT = REWRITE_RULE[WHOLE_rewrite_thm];;
