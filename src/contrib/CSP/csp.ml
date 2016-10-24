% Only autoloads the theory process.th and its child theories,	%
% i.e. the trace semantic model for the subset of CSP described %
% in README.							%
% The theories of, for example operator laws and syntactic type %
% for processes and denotational semantics, can be loaded	%
% explicitly if required, since these are still incomplete.	%

if draft_mode() 
 then (print_newline();
       print_string`process declared a new parent`;
       print_newline();
       new_parent`process`)
 else load_theory`process`;;


let autoload_defs_and_thms thy =
 map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ();;

map autoload_defs_and_thms
    [`stop`; `prefix`; `run`; `choice`; `parallel`; `after`; `mu`];;
