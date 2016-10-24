%
| Makes cpo parent and sets up autoloading
%

load_library `more_arithmetic`;;

set_search_path (search_path() @ [`/usr/local/hol/contrib/prog_logic92/`]);;

new_parent `cpo`;;
autoload_defs_and_thms `cpo`;;
