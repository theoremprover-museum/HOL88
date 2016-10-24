
if version() < 202 then loadf `patch`;;

   lisp `
   #-kcl nil
   #+kcl
	#+sun (progn ()
		  (allocate 'cons 900)
		  (allocate 'string 100)
		  (system:allocate-relocatable-pages 100)
		  (system:set-hole-size 2048))
	#+mips (progn ()
		  (allocate 'cons 2048)
		  (allocate 'string 100)
		  (system:allocate-relocatable-pages 100)
		  (system:set-hole-size 2048))
   `;;

set_flag(`print_load`, false);;

let force_new_theory name = 
    new_theory name ? (unlink(name^`.th`); new_theory name);;

let autoload_defs_and_thms thy =
 map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ();;

loadf `define`;;

%----------------------------------------------------------------------------%
% Hack to set left precedence of tokens for the quotation parser.            %
%----------------------------------------------------------------------------%

let set_left_precedence(tok,n) =
 lisp (`(putprop '|` ^ tok ^`| ` ^ (string_of_int n) ^` 'ollp)`);;

let int_to_term n = mk_const(string_of_int n, ":num")
and term_to_int n = int_of_string(fst(dest_const n));;

new_special_symbol `===>`;;

if not(mem `new_parent` (flags())) then new_flag(`new_parent`,true);;

%<
let new_parent =
 if (version() < 201) & get_flag_value `new_parent`
  then (\thy. new_parent thy; activate_all_binders thy; ())
  else new_parent;;
>%

set_flag(`new_parent`,false);;

%<
loadf `/usr/groups/centaur/contrib/subgoal/centaur.ml`;;
>%

let load_contrib s = loadf (hol_pathname() ^ `/contrib/` ^ s);;

%----------------------------------------------------------------------------%
% Patch for Version 2.01 to handle parsing problem with "::"                 %
%----------------------------------------------------------------------------%

lisp `(load "/Nfs/toton/usr2/mjcg/changes/hol-pars.o")`;;

%----------------------------------------------------------------------------%
% Hack to load Version 2.02 ind_defs in Version 2.01.                        %
%----------------------------------------------------------------------------%

let load_library lib =
 if ((lib = `ind_defs`) & (version() < 202))
  then loadf `/usr/groups/hol/HOL22/Library/ind_defs/ind-defs.ml`
  else load_library lib;;

set_flag(`print_load`, true);;

