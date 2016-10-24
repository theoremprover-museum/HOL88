%
| Makes sem parent and sets up autoloading
%

new_special_symbol `:=`;;
new_special_symbol `||`;;
new_special_symbol `|X|`;;
new_special_symbol `;;`;;
new_special_symbol `-->`;;
new_special_symbol `^^`;;
new_special_symbol `<--`;;
new_special_symbol `<o>`;;

load_library `more_arithmetic`;;
load_library `string`;;

set_search_path (search_path() @ [`/usr/local/hol/contrib/prog_logic92/`]);;

new_parent `sem`;;
autoload_defs_and_thms `sem`;;
