% Set up autoloading from ancestor theories of prog_logic88 %


let autoload_defs_and_thms thy =
 map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ();;

map 
 autoload_defs_and_thms
 (words `semantics hoare_thms halts halts_thms 
         halts_logic dijkstra dynamic_logic`);
();;

print_newline();;
message `All definitions and theorems will autoload.`;;
print_newline();;
