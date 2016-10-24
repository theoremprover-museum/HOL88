let autoload_defs_and_thms thy =
    map (\name. autoload_theory (`definitions`,thy,name))
        (map fst (definitions thy));
    map (\name. autoload_theory (`theorem`,thy,name))
        (map fst (theorems thy));
    ();;

let autoload_thms thy =
    map (\name. autoload_theory (`theorem`,thy,name))
        (map fst (theorems thy));
    ();;
