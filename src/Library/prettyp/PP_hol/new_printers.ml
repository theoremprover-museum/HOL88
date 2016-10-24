% new_printers.ml                                                             %
%-----------------------------------------------------------------------------%


%  Combined HOL pretty-printing rules  %

let hol_rules_fun = hol_thm_rules_fun then_try
                    hol_term_rules_fun then_try
                    hol_type_rules_fun;;


%  Functions to convert types, terms and theorems into parse-trees.  %

%  The amount of type information included is that required by the rules  %
%  in `hol_rules_fun'.                                                    %

let pp_convert_type t =

   % : (type -> print_tree) %

   type_to_print_tree t;;


let pp_convert_term t =

   % : (term -> print_tree) %

   term_to_print_tree true (if (get_flag_value `show_types`)
                            then Useful_types
                            else Hidden_types) t;;


%  Hypotheses abbreviated  %

let pp_convert_thm t =

   % : (thm -> print_tree) %

   thm_to_print_tree false true (if (get_flag_value `show_types`)
                                 then Useful_types
                                 else Hidden_types) t;;


%  Hypotheses in full  %

let pp_convert_all_thm t =

   % : (thm -> print_tree) %

   thm_to_print_tree true true (if (get_flag_value `show_types`)
                                then Useful_types
                                else Hidden_types) t;;


%  Print functions for HOL types, terms and theorems which simulate the  %
%  standard HOL pretty-printer.                                          %

let pp_print_type t =

   % : (type -> void) %

   pp hol_type_rules_fun `type` [] (pp_convert_type t);;


let pp_print_term t =

   % : (term -> void) %

   pp (hol_term_rules_fun then_try
       hol_type_rules_fun) `term` [] (pp_convert_term t);;


let pp_print_thm t =

   % : (thm -> void) %

   pp (hol_thm_rules_fun then_try
       hol_term_rules_fun then_try
       hol_type_rules_fun) `thm` [] (pp_convert_thm t);;


let pp_print_all_thm t =

   % : (thm -> void) %

   pp (hol_thm_rules_fun then_try
       hol_term_rules_fun then_try
       hol_type_rules_fun) `thm` [] (pp_convert_all_thm t);;


%  Function which simulates the standard HOL function `print_theory'  %

let pp_print_theory s =

   % : (string -> void) %

   let make_type ispair =

      % : ((int # string) -> type) %

      let make_vartypes n =

         % : (int -> type list) %

         letrec make_vartypes' n s l =

            % : (int -> string -> type list -> type list) %

            if (n < 1)
            then (rev l)
            else let s' = `*` ^ s
                 in  make_vartypes' (n - 1) s' ((mk_vartype s').l)

         in make_vartypes' n `` []

      in  mk_type (snd ispair, make_vartypes (fst ispair))

   and print_constant t =

      % : (term -> void) %

      let (name,typ) = ((dest_const t) ? failwith `print_constant`)
      in  do (print_begin 0;
              print_string name;
              print_break (1,0);
              pp_print_type typ;
              print_end ())

   and print_theorem (s,t) =

      % : (string # thm -> void) %

      do (print_begin 0;
          print_string s;
          print_break (2,2);
          pp_print_thm t;
          print_end ())

   in  do (print_newline ();
           print_string (`The Theory ` ^ s);
           print_newline ();
           print_list true `Parents` print_string (parents s);
           print_list true `Types` (pp_print_type o make_type) (types s);
           print_list true `Constants` print_constant (constants s);
           print_list true `Infixes` print_constant (infixes s);
           print_list true `Binders` print_constant (binders s);
           print_list false `Axioms` print_theorem (axioms s);
           print_list false `Definitions` print_theorem (definitions s);
           print_list false `Theorems` print_theorem (theorems s);
           print_string (`******************** `^s^` ********************`);
           print_newline ();
           print_newline ());;


%-----------------------------------------------------------------------------%
