% sree@cs.ubc.ca %

letrec pat_to_tree1 term_list subst_list_list arg_list_list
                                              cons_var rec_index =
       if (null (tl term_list)) then mk_let_term (hd subst_list_list) (hd term_list)
       else
          let rec_arg1 = (el rec_index (hd arg_list_list)) and
              term1 = hd term_list in
          (let let_term1 = mk_let_term (hd subst_list_list) term1 and
               rec_arg = mk_let_term (hd subst_list_list) rec_arg1 in
           mk_cond(mk_eq(cons_var,rec_arg), let_term1,
                  (pat_to_tree1 (tl term_list) (tl subst_list_list) (tl arg_list_list) 
                                 cons_var rec_index)));;

let pat_to_tree hol_term =
       let term_list1 = mk_skolem_list hol_term and
           arg_list_list = get_args hol_term and
           rec_index = get_rec_el_num hol_term and
           subst_list_list = mk_all_subst_list hol_term and
           cons_term = get_cons_term hol_term in
           (let cons_var = mk_var(`Cons_Var__`,type_of(cons_term)) in
            (let term_list1' = map (subst [(cons_var,cons_term)]) term_list1 in
             (let term_list = map snd (map dest_eq term_list1') in
              (let lhs = fst (dest_eq (hd (rev term_list1'))) and
                   rhs = (pat_to_tree1 term_list subst_list_list
                                         arg_list_list 
                                           cons_var rec_index) in
             
                mk_eq(lhs,rhs)))));;

