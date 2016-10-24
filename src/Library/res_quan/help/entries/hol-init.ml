
% set_prompt (`HOL88-`^(string_of_int(version()))^`> `);; %

let autoload_all theory =
 (\l.()) (map autoload_theory
  (map (\x.(`axiom`, theory, fst x)) (axioms theory) @
   map (\x.(`definition`, theory, fst x)) (definitions theory) @
   map (\x.(`theorem`, theory, fst x)) (theorems theory)));;

let add_to_search_path p = set_search_path(p.search_path());;
let append_to_search_path p = set_search_path(search_path()@[p]);;

system `echo 'let arch = \`'\`arch\`'\`;;' > arch.ml`;;

loadf`arch`;;

system `rm arch.ml`;;

let my_lib_path = (`/homes/ww/hol-`^arch^`/`);;
set_search_path (my_lib_path . (search_path()));;
set_library_search_path (my_lib_path .(library_search_path()));;

loadf`fast_load_thy`;;

