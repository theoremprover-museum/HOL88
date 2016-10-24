% --------------------------------------------------------------------- %
% FILE: make_use.ml                                                     %
% By D Syme                                             %
% --------------------------------------------------------------------- %


let make_use thy  =
   let out = openw (thy ^ `.use.ml`) in
   let print_thmname n = write(out, `\`` ^ n ^ `\`;\L`) in
   write(out, `map (\\s.autoload_theory (\`theorem\`,\`` ^ thy ^ `\` ,s))\L`);
   write(out, `[`);
   let thms = map fst (theorems `-`) in
   map print_thmname thms;
   write(out, `\`dummy_THM\`];;\L`);

   write(out, `map (\\s.autoload_theory (\`definition\`,\`` ^ thy ^ `\` ,s))\L`);
   write(out, `[`);
   let thms = map fst (definitions `-`) in
   map print_thmname thms;
   write(out, `\`dummy_THM\`];;\L`);


   write(out, `map (\\s.autoload_theory (\`axiom\`,\`` ^ thy ^ `\` ,s))\L`);
   write(out, `[`);
   let thms = map fst (axioms `-`) in
   map print_thmname thms;
   write(out, `\`dummy_THM\`];;\L`)


;;
