%
| Makes temporal parent and sets up autoloading
%

load_library `more_arithmetic`;;
load_library `string`;;

set_search_path (search_path() @ [`/usr/local/hol/contrib/prog_logic92/`]);;

new_parent `temporal`;;

autoload_defs_and_thms `temporal`;;
