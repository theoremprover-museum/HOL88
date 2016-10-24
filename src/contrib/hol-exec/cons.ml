%------ FILE cons.ml ------%
% Bug fixed in an earlier version %
% sree@cs.ubc.ca %

letrec get_final_ret_type1 cons_type =
        if ((can dest_type) cons_type) then
           let t1 = dest_type cons_type in
           if (null (snd t1)) then cons_type
           else
             if ((fst t1) = `fun`) then
              get_final_ret_type1 (hd (rev (snd t1)))
             else cons_type
        else
           failwith `not a type`;;

let get_final_ret_type cons_term =
       get_final_ret_type1 (type_of cons_term);;

let get_type_axiom_from thy const_term =
       if (is_const const_term) then
          let typ = fst (dest_type (get_final_ret_type const_term)) in
          (let thm_name = concat typ `_Axiom` in
            (get_second thm_name (theorems thy)))
       else
           failwith `get_type_axiom_from: not a constant`;;

let mk_cons_tuple_str_list1 functor arg_list =
     if (null arg_list) then
        concat `CONS__`
         (concat (const_var_to_string functor) `;; \L`)
     else
      concat `CONS__`
       (concat (const_var_to_string functor)
         (concat ` (`
           (concat (inv_words `,` (map const_var_to_string arg_list))
                   `);; \L`)));;
                    
let mk_cons_tuple_str_list thy const_term =
      let t1 = concl (get_type_axiom_from thy const_term) in
       (let list_list = get_args (skolemize t1) in
         (let functor_list = functors_of_args list_list and
              args_list = args_of_args list_list in
            (map2 (uncurry mk_cons_tuple_str_list1) (functor_list,args_list))));;

let is_constructor_from thy const_term = 
      if ((can (get_type_axiom_from thy) ) const_term) then
       let t1 = concl (get_type_axiom_from thy const_term) in
        (let list_list = get_args (skolemize t1) in
         (let functor_list = functors_of_args list_list in
           (let const_name = fst (dest_const const_term) and
                functor_name_list = map fst (map dest_const functor_list) in
           mem const_name functor_name_list)))
      else
        false;;

letrec mk_quick_cons_def_from thy const_term =
      let t1 = concl (get_type_axiom_from thy const_term) in
          (let list_list = get_args (skolemize t1) in
           (let functor_list = functors_of_args list_list in
            (let const_name = fst (dest_const const_term) and
                 functor_name_list = map fst (map dest_const functor_list) in
            (let el_index = index const_name functor_name_list in
              (let args = el el_index (args_of_args list_list) in 
               (let cons_args_term_list = const_term.args in
                (let str_list = map const_var_to_ml_string cons_args_term_list in
                (let let_str =
                  concat `let `
                  (concat (inv_words ` ` str_list)
                   (concat ` = `
                           (mk_cons_tuple_str_list1 const_term args)
                           )) in
                 let_str))))))));;

let type_map = [(`num`,`int`)];;

% Does not capture type constructors like `fun` : retain for safety
letrec mk_type_list hol_type =
      let type_pair = ((dest_type hol_type) ? ((dest_vartype hol_type),[])) in
       (let type1_str = lookup_map type_map (fst type_pair) and
            type2 = snd type_pair in
       if (null type2) then [type1_str]
       else
         append (mk_type_list (hd type2)) [type1_str]);;
%

% Fix the above %
letrec mk_type_list hol_type_list =
      if (null hol_type_list) then []
      else
      let head = hd hol_type_list in
      let type_pair = ((dest_type head) ? ((dest_vartype head),[])) in
      let first = fst type_pair and
          secnd = snd type_pair in
      if (first = `prod`) then
         [inv_words `#` (mk_type_list secnd)]
      else
      if (first = `fun`) then 
         [inv_words `->` (mk_type_list secnd)]
      else
      let type1_str = lookup_map type_map first in
        if (null secnd) then
         type1_str.(mk_type_list (tl hol_type_list))
        else
         (`(`^(inv_words `,` (mk_type_list secnd))^`)`^type1_str).
         (mk_type_list (tl hol_type_list));;
                      
let hol_to_ml_type hol_type = 
      inv_words ` ` (mk_type_list [hol_type]);;

let mk_constructor_defs_strs functor arg_type_list =
      if (null arg_type_list) then 
       concat `CONS__`
               (const_var_to_string functor)
      else
       concat `CONS__`
        (concat (const_var_to_string functor)
	  (concat ` of `
	          (inv_words ` # ` (map hol_to_ml_type arg_type_list))));;

let mk_cons_type_defs1 thy const_term =
      let t1 = concl (get_type_axiom_from thy const_term) in
          (let list_list = get_args (skolemize t1) in
           (let functor_list = functors_of_args list_list in
            (let const_name = fst (dest_const const_term) and
                 functor_name_list = map fst (map dest_const functor_list) in
            (let el_index = index const_name functor_name_list in
              (let args = el el_index (args_of_args list_list) in 
               (let arg_type_list = map type_of args in
           mk_constructor_defs_strs const_term arg_type_list))))));;

let mk_cons_type_defs_str thy cons_list_pair =
% create a unique name for the rectype%
       let rectype_name = hol_to_ml_type (fst cons_list_pair) and
           cons_list = snd cons_list_pair in
       (concat `rectype `
	 (concat rectype_name
	   (concat ` = `
% We could also sort the cons_list according to type minimality,
  though its not required by ML - but we will just use reverse %
	     (concat (inv_words `| ` (map (mk_cons_type_defs1 thy) (rev cons_list)))
                     `;;\L\L`))));;

let map_map f l = map (map f) l;;
letrec mapl l1 l2 =
    if (null l1) then []
    else
       ((hd l1) (hd l2)). (mapl (tl l1) (tl l2));;

let mk_pair_list l1 l2 =
     mapl (map pair l1) l2;;

letrec mk_groups_of_same_type cons_list_pair =
      if (null cons_list_pair) then []
      else
         let type_eq term1 term2 =
                 (snd term1) = 
                 (snd term2) in
         (let type1_list_pair = (sublist (type_eq (hd cons_list_pair)) 
                                                   cons_list_pair) in
           (let cons_list_pair1 = subtract cons_list_pair type1_list_pair in
            (let type1_list = map fst type1_list_pair and
                 type1 = (snd (hd type1_list_pair)) in
             ((type1,type1_list).(mk_groups_of_same_type cons_list_pair1)))));;

let mk_cons_type_defs thy cons_list =
       (let type_list = map get_final_ret_type cons_list in
% We should actually sort the type groups according to containment,
  but we will for the moment assume a reverse order creation: %
        (let cons_list_list = rev 
                               (mk_groups_of_same_type 
                                  (mk_pair_list cons_list type_list)) in
             map (mk_cons_type_defs_str thy) cons_list_list));;


% The following is too complicated and unnecessary
letrec mk_groups_of_same_type cons_list =
      if (null cons_list) then []
      else
         let type_eq term1 term2 =
                 type_of term1 = type_of term2 in
         (let type1_list = sublist (type_eq (hd cons_list)) cons_list in
           (let cons_list1 = subtract cons_list type1_list in
             (type1_list.(mk_groups_of_same_type cons_list1))));;

let map_map f l = map (map f) l;;
letrec mapl l1 l2 =
    if (null l1) then []
    else
       ((hd l1) (hd l2)). (mapl (tl l1) (tl l2));;

let mk_cons_type_defs1 cons_list =
          (let list_list = map get_args (map skolemize cons_list) in
           (let functor_list_list = map functors_of_args list_list in
            (let const_name_list = map fst (map dest_const cons_list) and
                 functor_name_list_list = map_map fst 
                                     (map_map dest_const functor_list_list) in
            (let el_index_list = mapl (map index const_name_list) 
                                        functor_name_list_list in
              (let args_list_list = map_map type_of
                                        (mapl (map el el_index_list)
                                          (map args_of_args list_list)) in 
               mk_cons_defs cons_list args_list_list)))));;
    
let mk_cons_type_defs thy cons_list =
       let t1_list = map concl (map (get_type_axiom_from thy) cons_list) in
        (let cons_list_list = mk_groups_of_same_type cons_list in
         (let def_str_list = map mk_cons_type_defs1 cons_list_list in
           def_str_list));;



%
