let pred_path = library_pathname() ^ `/predicate/` in
let sets_path = library_pathname() ^ `/sets/` in
    set_search_path (union (search_path()) [pred_path; sets_path]);
    print_string `(1) search path updated`; print_newline();;

if draft_mode() 
   then new_parent `predicate` else load_theory `predicate`;;

if draft_mode()
   then (print_string `(2) predicate declared as new parent` ;
         print_newline())
   else (if ((current_theory() = `predicate`))
         then (print_string `(2) theory predicate loaded` ;
               print_newline())
         else (print_string `Fail to load theory predicate!!` ;
               print_newline())) ;;

associate_restriction (`!!`,`RES_qAND`) ;;
associate_restriction (`??`,`RES_qOR`) ;;

new_special_symbol `|==` ;;

load_library `taut` ;;
loadf `my_misc` ;;
if (draft_mode() or (current_theory() = `predicate`)) 
   then load(`predicate_SUP`, get_flag_value `print_lib`) ;;

if (draft_mode() or (current_theory() = `predicate`)) then
   let defs = map fst (definitions `predicate`) in
       map (\name. autoload_theory(`definition`,`predicate`,name)) defs;
   let thms = map fst (theorems `predicate`) in
       map (\name. autoload_theory(`theorem`,`predicate`,name)) thms; 
   delete_cache `predicate`; ();;


