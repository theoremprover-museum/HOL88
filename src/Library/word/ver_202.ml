%set_library_search_path (`/homes/ww/hol4/`.(library_search_path()));; %

let autoload_all theory =
 (\l.()) (map autoload_theory
  (map (\x.(`axiom`, theory, fst x)) (axioms theory) @
   map (\x.(`definition`, theory, fst x)) (definitions theory) @
   map (\x.(`theorem`, theory, fst x)) (theorems theory)));;

load_library`arith`;;

load_library`res_quan`;;

%let LENGTH_MAP2 = theorem `list` `LENGTH_MAP2`;;%

loadf`genfuns`;;
