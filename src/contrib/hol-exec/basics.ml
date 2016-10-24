% File "basics.ml" : basic functions for hol-eval %
% sree@cs.ubc.ca %

%load_library `string`;;%

let const_map = 
[(`HD`,`hd`);
(`TL`,`tl`);
(`NULL`,`null`);
(`CONS`,`ml_cons`);
(`SUC`,`ml_suc`);
(`FST`,`fst`);
(`SND`,`snd`);
(`LET`,`ml_let`);
(`UNCURRY`,`ml_uncurry`);
(`DIV`,`ml_div`);
(`MOD`,`ml_mod`);
(`EXP`,`ml_exp`);
(`MAP`,`ml_map`);
(`not`,`hol_not`);
(`and`,`hol_and`);
(`or`,`hol_or`);
(`ARB`,`failwith \`failure due to partial specification\\L\``);
(`APPEND`,`ml_append`);
(`LENGTH`,`ml_length`);
(`+`,`FIX_PLUS`);
(`>`,`FIX_GT`);
(`<`,`FIX_LT`);
(`&`,`FIX_AMPERSAND`);
(`-`,`FIX_MINUS`);
(`/\\`,`FIX_AND`);
(`\\/`,`FIX_OR`);
(`=`,`FIX_EQ`);
(`,`,`FIX_PAIR`);
(`~`,`FIX_NOT`);
(`!`,`FIX_FORALL`);
(`?`,`FIX_EXISTS`);
(`?!`,`FIX_UNIQ`);
(`*`,`FIX_MULT`);
(`==>`,`FIX_IMP`);
(`o`,`FIX_COMPOSE`)];;

% Note the order of arguments for convenience of using map %
letrec inv_words separator str_list =
      if (null str_list) then ``
      else
       if (null (tl str_list)) then (hd str_list)
       else
         concat (hd str_list)
          (concat separator
            (inv_words separator (tl str_list)));;

% A generic function to pull out the second el corr. to a given first %
let get_second first pair_list = 
         let equal_to_first x = ((fst x) = first) in
          snd (find equal_to_first pair_list) ?
          failwith `get_second: first not found in list`;;

% Removing an element el from a list el_list %
letrec rem el el_list =
	if (null el_list) then []
	else
	   if (el = (hd el_list)) then
		(rem el (tl el_list))
	   else
	      (hd el_list).(rem el (tl el_list));;

% Truncate a list to a given number of elements%
letrec trunc_list num_of_el list =
    if ((null list) or (num_of_el = 0)) then []
    else
      (hd list).(trunc_list (num_of_el - 1) (tl list));;

% Combine two lists (may be diff length) governed by the smaller of the two%
letrec combine_min list1 list2 =
    if ((null list1) or (null list2)) then []
    else
       ((hd list1),(hd list2)).(combine_min (tl list1) (tl list2));;

% Get minimal index of element in list %
letrec index el list =
      if (null list) then failwith `element not found in list`
      else
         if (el = (hd list)) then 1
         else
            1+ index el (tl list);;

% Make sublists from a list of elements that (NOT) satisfy a predicate p %
letrec sublist p list =
      if (null list) then []
      else
         if (p (hd list)) then
            (hd list).(sublist p (tl list))
         else
            sublist p (tl list);;

letrec anti_sublist p list =
      if (null list) then []
      else
         if (p (hd list)) then
            anti_sublist p (tl list)
         else
            (hd list).(anti_sublist p (tl list));;

% Remove duplicates from a list: in the right order %
letrec rem_dup list =
     if (null list) then []
     else
      let head = hd list and
          tail = tl list in
       union [head] (rem_dup (tl list));;

% One of true of a predicate %
letrec one_of_true p list =
       if (null list) then false
       else
        if (p (hd list)) then true
        else
          one_of_true p (tl list);;

% Define curried eq %
let eq x y = (x=y);;

% Convert primed strings to indexed strings %
letrec prime_to_index1 char_list pcount =
         if (null char_list) then 
            if (pcount = 0) then ``
            else (string_of_int pcount)
         else
            if ((hd char_list) = `'`) then
               let prime_count = 1+ pcount in
               prime_to_index1 (tl char_list) prime_count
            else
               if (pcount = 0) then 
                  concat (hd char_list) 
                         (prime_to_index1 (tl char_list) 0)
               else
                  concat (string_of_int pcount)
                   (concat (hd char_list)
                           (prime_to_index1 (tl char_list) 0));;

let prime_to_index str =
         prime_to_index1 (explode str) 0;;

let is_var_const hol_term =
         (is_var hol_term) or (is_const hol_term);;

% We need to dest constant or a var with a single function %
let dest_var_const hol_term =
        if (is_var hol_term) then
           dest_var hol_term
        else
           if (is_const hol_term) then
              dest_const hol_term
           else
             failwith `term neither a constant nor a variable`;;

% Create an indexed variant of a var %
letrec ivariant1 var_list var index =
       if (is_const var) then % Var can also be a const %
          let var_term = dest_const var in
          (let var_str1 = fst var_term and
               var_type = snd var_term in
            (let var_str2 = concat var_str1 (string_of_int index) in
               (let var_var = mk_var(var_str2,var_type) in
                 ivariant1 var_list var_var (index+1))))
       else % var is a Var %
          if (mem (fst (dest_var var)) (map fst (map dest_var_const var_list))) then
             let var_term = dest_var var in
             (let var_str1 = fst var_term and
               var_type = snd var_term in
              (let var_str2 = concat var_str1 (string_of_int index) in
               (let var_var = mk_var(var_str2,var_type) in
                 ivariant1 var_list var_var (index+1))))
          else var;;

let ivariant var_list var =
      if (is_const var) then
       let var_term = dest_const var in
       (let var_str = fst var_term and
            var_type = snd var_term in
        (let var_str1 = prime_to_index var_str in
          (let var_var = mk_var(var_str1,var_type) in
            ivariant1 var_list var_var 1)))
      else
      if (is_var var) then
       let var_term = dest_var var in
       (let var_str = fst var_term and
            var_type = snd var_term in
        (let var_str1 = prime_to_index var_str in
          (let var_var = mk_var(var_str1,var_type) in
            ivariant1 var_list var_var 1)))
      else failwith `term neither a constant not a variable`;;

% Destructor for "?!" %
let dest_uniq =
    let check = assert (\c. fst(dest_const c) = `?!`) in
    \tm. (let (_,b) = (check # I) (dest_comb tm) in dest_abs b) ?
         failwith `dest_uniq`;;

let is_uniq = can dest_uniq;;

letrec skolemize1 hol_term var_list =
       if ((is_var hol_term) or (is_const hol_term)) then
          hol_term
       else
       if (is_forall hol_term) then
          let t1 = snd (dest_forall hol_term) and
          old_var = fst (dest_forall hol_term) in
          (let new_var = ivariant var_list old_var in
            subst [(new_var,old_var)]
                  (skolemize1 t1 (new_var.var_list)))
       else
       if (is_exists hol_term) then
          let t1 = snd (dest_exists hol_term) and
          old_var = fst (dest_exists hol_term) in
          (let new_var = ivariant var_list old_var in
            subst [(new_var,old_var)]
                  (skolemize1 t1 (new_var.var_list)))
       else
       if (is_uniq hol_term) then
          let t1 = snd (dest_uniq hol_term) and
          old_var = fst (dest_uniq hol_term) in
          (let new_var = ivariant var_list old_var in
            subst [(new_var,old_var)]
                  (skolemize1 t1 (new_var.var_list)))
       else
       if (is_abs hol_term) then
          let t1 = dest_abs hol_term in
          (let t11 = fst t1 and
               t12 = snd t1 in          
           mk_abs(t11,(skolemize1 t12 var_list)))
       else
       if (is_comb hol_term) then
          let t1 = dest_comb hol_term in
          (let t11 = fst t1 and
               t12 = snd t1 in
          (if (is_const t11) then
           (if (is_binder (fst (dest_const t11))) then
             skolemize1 t12 var_list
            else
            let comb1 = skolemize1 t11 var_list and
                comb2 = skolemize1 t12 var_list in
             mk_comb(comb1,comb2))
           else
            let comb1 = skolemize1 t11 var_list and
                comb2 = skolemize1 t12 var_list in
             mk_comb(comb1,comb2)))
       else
       hol_term;;

let skolemize hol_term =
       let var_list  = vars hol_term in
       skolemize1 hol_term var_list;;

letrec lookup_map table lhs = 
         if (null table) then lhs
         else
           if ((fst (hd table)) = lhs) then
              snd (hd table)
           else
              lookup_map (tl table) lhs;;

let hol_to_fl_string const =
       let str = fst (dest_const const) in
        if ((type_of const) = ":string") then
         let pre = [` `;`"`] in
         implode (append (append pre (rem `\`` (explode str))) [`"`;` `])
        else str;;

let hol_str_to_fl_str str =
         let pre = [` `;`"`] in
         implode (append (append pre (rem `\`` (explode str))) [`"`;` `]);;

let const_var_to_string const_var_term =
        if (is_const const_var_term) then
           fst (dest_const const_var_term)
        else
          if (is_var const_var_term) then
             fst (dest_var const_var_term)
          else
             failwith `term not a constant or variable`;;

let const_var_to_ml_string const_var_term =
	lookup_map const_map (const_var_to_string const_var_term);;
let const_var_to_fl_string const_term = 
         if ((type_of const_term) = ":string") then
          hol_str_to_fl_str (lookup_map const_map
                              (const_var_to_string const_term))
         else
            (lookup_map const_map
                (const_var_to_string const_term));;

letrec strip_forall hol_term =
       if (is_forall hol_term) then 
          (strip_forall (snd (dest_forall hol_term)))
       else
          hol_term;;

letrec strip_exists hol_term =
       if (is_exists hol_term) then 
          (strip_exists (snd (dest_exists hol_term)))
       else
          hol_term;;

letrec strip_outer_quantifiers hol_term = 
      if (is_forall hol_term) then 
         strip_outer_quantifiers (snd (dest_forall hol_term))
      else
         if (is_exists hol_term) then
            strip_outer_quantifiers (snd (dest_exists hol_term))         
         else
            hol_term;;

letrec get_args2 hol_term =
       if (is_comb hol_term) then
          let t1 = dest_comb hol_term in
          if (is_pair (snd t1)) then
             append (get_args2 (fst t1))
                    ((fst (dest_pair (snd t1))).(get_args2(snd (dest_pair (snd t1)))))
          else % is a comb with constructor %
             if (is_comb (snd t1)) then
                append (get_args2 (fst t1))
                       [(snd t1)]
              else
                 append (get_args2 (fst t1)) [(snd t1)]
        else
             [hol_term];;

letrec get_args1 hol_term_list =
      if (null hol_term_list) then []
      else
       let t1 = (strip_outer_quantifiers (hd hol_term_list)) in
         if (is_eq t1) then
          (get_args2 (fst (dest_eq t1))).
          (get_args1 (tl hol_term_list))
         else
            (get_args2 t1).
            (get_args1 (tl hol_term_list));;

letrec form_tl_list list =
      if (null list) then []
      else
         (tl (hd list)).(form_tl_list (tl list));;

let get_args hol_term =
      form_tl_list (get_args1 (conjuncts (strip_outer_quantifiers hol_term)));;

let get_args_rev hol_term =
      rev (get_args hol_term);;

let get_functor hol_term =
      hd (hd (get_args1 (conjuncts (strip_outer_quantifiers hol_term))));;

let get_functors hol_term =
       map get_functor (conjuncts (skolemize hol_term));;

let functors_of_args arg_list_list =
       map get_functor (map hd arg_list_list);;

let args_of_args arg_list_list =
       map hd (map get_args (map hd arg_list_list));;

% Had to modify the following two 'cause we can't recurse on pairs later
letrec form_subst_list1 cons cons_type cons_term_type cons_var index arg_list =
     if (null arg_list) then []
     else
       if (cons_term_type = ":num") then
          ((cons_var - 1),(hd arg_list)).
	  (form_subst_list1 cons cons_type cons_term_type 
				cons_var (index+1) (tl arg_list))
       else
        let dest_str = `dest` and
            arg      = (hd arg_list) in
          (let arg_type = type_of arg in
             (let dest_type = mk_type(`fun`,
                                [":num";mk_type(`fun`,[cons_term_type;arg_type])]) in
               (let dest_var = mk_var(dest_str,dest_type) and
                  index_term = mk_const((string_of_int index),":num") in
                 (let dest_app = mk_comb(dest_var,index_term) in
                  ((mk_comb(dest_app,cons_var)),arg).
                   (form_subst_list1 cons cons_type cons_term_type cons_var 
                                     (index+1) (tl arg_list))))));;

let form_subst_list cons_term =
      let arg_list = hd (get_args cons_term) and
          cons_term_type = type_of cons_term and
          cons = (get_functor cons_term) in
        (let cons_type = type_of cons and
             cons_var = mk_var(`Cons_Var__`,cons_term_type) in
       (form_subst_list1 cons cons_type cons_term_type cons_var 1 arg_list));;
%

letrec form_subst_list1 cons cons_type cons_term_type cons_var index arg_list dest_str =
     if (null arg_list) then []
     else
% Special cases: SUC and CONS and STRING %
       if (cons_term_type = ":num") then
         let term_minus = mk_var(`deSUC`,":num -> num") in
          [((mk_comb(term_minus,cons_var)),(hd arg_list))]
	%  .(form_subst_list1 cons cons_type cons_term_type 
			cons_var (index+1) (tl arg_list) dest_str)
	%
       else
       if (fst (dest_type cons_term_type) = `list`) then
	 let head_type = type_of (hd arg_list) in
         (let get_head = mk_var(`deHEAD`,mk_type(`fun`,
				[cons_term_type;head_type])) and
             get_tail = mk_var(`deTAIL`,mk_type(`fun`,
				[cons_term_type;cons_term_type])) in
	     [((mk_comb(get_head,cons_var)),(hd arg_list));
              ((mk_comb(get_tail,cons_var)),(hd (tl arg_list)))])
       else
       if (fst (dest_type cons_term_type) = `string`) then
	 let char_type = type_of (hd arg_list) in
         (let get_ascii = mk_var(`deASCII`,mk_type(`fun`,
				[cons_term_type;char_type])) and
             get_string = mk_var(`deSTRING`,mk_type(`fun`,
				[cons_term_type;cons_term_type])) in
	     [((mk_comb(get_ascii,cons_var)),(hd arg_list));
              ((mk_comb(get_string,cons_var)),(hd (tl arg_list)))])        
       else % Other cases %

        let dest_str1 = concat dest_str (string_of_int index) and
            arg = (hd arg_list) in
          (let arg_type = type_of arg in
             (let dest_type = mk_type(`fun`,[cons_term_type;arg_type]) in
               (let dest_var = mk_var(dest_str1,dest_type) in
                   ((mk_comb(dest_var,cons_var)),arg).
                   (form_subst_list1 cons cons_type cons_term_type cons_var 
                                     (index+1) (tl arg_list) dest_str))));;

let form_subst_list cons_term =
      let arg_list = hd (get_args cons_term) and
          cons_term_type = type_of cons_term and
          cons = (get_functor cons_term) in
        (let cons_type = type_of cons and
             cons_var = mk_var(`Cons_Var__`,cons_term_type) in
        (let dest_str = concat `dest_CONS__` (fst (dest_const cons)) in
       (form_subst_list1 cons cons_type cons_term_type cons_var 1 arg_list dest_str)));;


% Put the next two defs in t2s.ml later %
letrec mk_destructor_defs1 cons_str arg_list_str arg_list n dest_str =
       if (null arg_list) then ``
       else
          let dest_str1 = concat dest_str (string_of_int n) in
           (concat `let `
            (concat dest_str1
             (concat ` (CONS__`
              (concat cons_str
               (concat ` `
                (concat arg_list_str
                   (concat `) = `
                     (concat (const_var_to_string (hd arg_list))
                       (concat ` ;;\L\L`
                         (mk_destructor_defs1 cons_str arg_list_str 
                                              (tl arg_list) (n+1) 
                                                  dest_str))))))))));;

let mk_destructor_defs cons_term =
      let arg_list = hd (get_args cons_term) and
          cons = (get_functor cons_term) in
      (let cons_str = fst (dest_const cons) in
        (let dest_str = concat `dest_CONS__` cons_str and
             arg_list_str = 
              (concat `(`
               (concat (inv_words `, ` (map const_var_to_string arg_list))
                       `)`)) in
           mk_destructor_defs1 cons_str arg_list_str arg_list 1 dest_str));;


letrec mk_skolem_list1 conj_list =
      if (null conj_list) then []
      else
         (strip_outer_quantifiers (hd conj_list)).
         (mk_skolem_list1 (tl conj_list));;

let mk_skolem_list hol_term =
       mk_skolem_list1 (conjuncts (strip_outer_quantifiers hol_term));;

letrec get_rec_el_num1 arg_list=
       if (is_comb (hd arg_list)) then 1
       else
          1+ (get_rec_el_num1 (tl arg_list));;

let get_rec_el_num hol_term =
       get_rec_el_num1 (hd (get_args_rev hol_term));;

letrec mk_subst_list1 arg_list =
       if (is_comb (hd arg_list)) then (form_subst_list (hd arg_list))
       else
          mk_subst_list1 (tl arg_list);;
let mk_subst_list hol_term =
       (mk_subst_list1 (hd (get_args_rev hol_term))?[]);;

% Keep safe
let mk_all_subst_list hol_term =
       let hol_term' = strip_outer_quantifiers hol_term in
       rem_dup (flat (map mk_subst_list (conjuncts hol_term')));;
%

let mk_all_subst_list hol_term =
       let hol_term' = strip_outer_quantifiers hol_term in
        map mk_subst_list (conjuncts hol_term');;

% Put the next two defs into t2s later %
let block_type_list = [`num`;`list`;`string`];;

let mk_dest_defs hol_term =
      let arg_list = hd (get_args_rev hol_term) in
       (let arg_list_comb = sublist is_comb arg_list and
            type_eq term type_name = (fst (dest_type (type_of term)) = type_name) in
         (let type_eql type_name_list term =
               one_of_true (type_eq term) type_name_list in
         (let arg_list_comb1 = anti_sublist (type_eql block_type_list) 
                                             arg_list_comb in
             inv_words `` (map mk_destructor_defs arg_list_comb1))));;

let mk_all_dest_defs hol_term =
      let hol_term' = strip_outer_quantifiers hol_term in
        inv_words `` (map mk_dest_defs (conjuncts hol_term'));;

letrec get_cons_term1 arg_list =
       if (is_comb (hd arg_list)) then (hd arg_list)
       else
          get_cons_term1 (tl arg_list);;
let get_cons_term hol_term =
       get_cons_term1 (hd (get_args_rev hol_term));;

letrec mk_uncurried_abs term_pair hol_term =
       if (is_pair term_pair) then
	  "UNCURRY^(mk_abs(fst(dest_pair term_pair),
		     (mk_uncurried_abs (snd (dest_pair term_pair)) hol_term)))"
       else
	  mk_abs(term_pair,hol_term);;

letrec mk_lambda_term term_list hol_term =
      if (null term_list) then hol_term
      else
	 mk_lambda_term (tl term_list) (mk_uncurried_abs (hd term_list) hol_term);;

letrec get_args2 hol_term =
       if (is_comb hol_term) then
          let t1 = dest_comb hol_term in
          if (is_pair (snd t1)) then
             append (get_args2 (fst t1))
                    ((fst (dest_pair (snd t1))).(get_args2(snd (dest_pair (snd t1)))))
          else % is a comb with constructor %
             if (is_comb (snd t1)) then
                append (get_args2 (fst t1))
                       [(snd t1)]
              else
                 append (get_args2 (fst t1)) [(snd t1)]
        else
             [hol_term];;

letrec mk_func_and_arg_list comb_term =
      if (is_comb comb_term) then
         let comb_pair = dest_comb comb_term in
          (let t1 = fst comb_pair and
               t2 = snd comb_pair in
           append (mk_func_and_arg_list t1) [t2])
      else [comb_term];;

let pullconst hol_term = 
	if (is_const hol_term) then [hol_term]
	else [];;

let pullvar hol_term =
	if (is_var hol_term) then [hol_term]
	else [];;

letrec mapterm f hol_term =
         if (is_var hol_term) then
	    f hol_term
         else
         if (is_const hol_term) then
	    f hol_term
         if (is_pair hol_term) then
            let t1 = dest_pair hol_term in
            union (mapterm f (fst t1))
                  (mapterm f (snd t1))
         else
         if (is_forall hol_term) then
            let t1 = dest_forall hol_term in
	    union (mapterm f (fst t1))
	           (mapterm f (snd t1))
         else
         if (is_exists hol_term) then
            let t1 = dest_exists hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_neg hol_term) then
            mapterm f (dest_neg hol_term)
         else
         if (is_disj hol_term) then
            let t1 = dest_disj hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_conj hol_term) then
           let t1 = dest_conj hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_imp hol_term) then
           let t1 = dest_imp hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_eq hol_term) then
           let t1 = dest_eq hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_select hol_term) then
           let t1 = dest_select hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_cond hol_term) then
           let t1 = dest_cond hol_term in
            union (mapterm f (fst t1))
                         (append (mapterm f (fst(snd t1)))
                                 (mapterm f (snd(snd t1))))
         else
         if (is_let hol_term) then
             mapterm f (fst (dest_let hol_term))
         else
         if (is_abs hol_term) then
           let t1 = dest_abs hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         if (is_comb hol_term) then
% Any binder %
           let t1 = dest_comb hol_term in
           (if (is_const (fst t1)) then
            (if (is_binder (fst (dest_const (fst t1)))) then
               mapterm f (snd t1)
            else
             union (mapterm f (fst t1))
                   (mapterm f (snd t1)))
           else
             union (mapterm f (fst t1))
                   (mapterm f (snd t1)))
         else
            [hol_term];;

% This is better, but won't work - why?
letrec mapterm f hol_term =
         if (is_var hol_term) then
	    f hol_term
         else
         if (is_const hol_term) then
	    f hol_term
         else
         if (is_abs hol_term) then
           let t1 = dest_abs hol_term in
            union (mapterm f (fst t1))
                   (mapterm f (snd t1))
         else
         let t1 = dest_comb hol_term in
             union (mapterm f (fst t1))
                   (mapterm f (snd t1));;
%

% Utilities involving constants in a term %
letrec where_const1 hol_term thy_list = 
               if (null thy_list) then ``
               else
                  if (mem hol_term (constants (hd thy_list))) then 
                     (hd thy_list) 
                  else 
                    let return_thy = where_const1 hol_term (parents (hd thy_list)) in
                    if (return_thy = ``) then
                       where_const1 hol_term (tl thy_list)
                    else
                       return_thy;;

let where_const hol_term =
       where_const1 hol_term [current_theory()];;

% This gets definitions with equality: robust and efficient for our purpose %
let get_const def_el = 
     let def_el1 = (strip_outer_quantifiers (concl (snd def_el))) in
     if (is_eq def_el1) then
        (hd (mapterm pullconst def_el1))
     else % It has to be a conjunction used in recursive defs %
        if (is_conj def_el1) then
           (hd (mapterm pullconst 
                      (strip_outer_quantifiers (fst (dest_conj def_el1)))))
        else % don't know what to do: just return the concl 
               of the definition: find fails in get_def %
           (concl (snd (def_el)));;

let get_def const = 
       let thy = (where_const const) and
           el_predicate el = (get_const el = const) in
         (snd (find el_predicate (definitions thy)));;

let get_def_from thy const = 
         let el_predicate el = (get_const el = const) in
         (snd (find el_predicate (definitions thy)));;

% Get a definition using the string key associated with it %
letrec get_def_from_key1 str thy_list =
         let head = hd thy_list and
             tail = tl thy_list in
         if (one_of_true (eq head) [`string`;`HOL`]) then 
            failwith ` def not found in user-defined theories: message from get_def_from_key1\L`
         else
         (let defs = definitions head in
          ((get_second str defs)?
            ((get_def_from_key1 str (parents head))?
             (get_def_from_key1 str (tl thy_list)))));;

let get_def_from_key str = 
        let thy = current_theory() in
        (let par_list = parents thy in     
         (let defs = definitions thy in
         ((get_second str defs)?
          (get_def_from_key1 str par_list))));;
             
let get_def_from_key_from_thy thy str =
       let defs = definitions thy in
       ((get_second str defs)?
         failwith `message from get_def_from_key_from_thy: no such key in this theory\L`);; 

% make let terms from a subst_list and a hol_term
  : used instead of making explicit substitution 
%

letrec mk_let_term subst_list hol_term =
         if (null subst_list) then hol_term
         else
           let head = hd subst_list in
            (let lhs = fst head and
                 rhs = snd head in
% probable failure in mk_abs: in which case just subst! %
             ((let abs = mk_abs(rhs,hol_term) in
                mk_let_term (tl subst_list) (mk_let(abs,lhs))) ?
              (let hol_term' = subst [head] hol_term in
                mk_let_term (tl subst_list) hol_term')));;


let is_rec2 const_term =
       let const_term1 = strip_outer_quantifiers const_term in
        if (is_eq const_term1) then
           (let lhs_head = hd (mapterm pullconst 
				(fst (dest_eq const_term1))) and
           % Note that rec fn name need not appear first in rhs:
			look at def of "$+" %
                rhs_consts = (mapterm pullconst 
					(snd (dest_eq const_term1))) in
                
               mem lhs_head rhs_consts)
        else
           failwith `definition is not an equation: message from is_rec1 (not from system)`;;

letrec is_rec1 const_def =
        if (not (is_conj const_def)) then (is_rec2 const_def)
        else % conjunction in definition %
          let conj_pair = (dest_conj const_def) in
          if (is_rec2 (fst conj_pair)) then true
          else
            (is_rec1 (snd conj_pair));;

% This works only for restricted forms (with conjunctions) - doesn't
work for example on "$<" %
let is_rec const_term =
        let const_def = ((concl (get_def const_term)) ? "F") in
        if (is_conj const_def) then is_rec1 const_def
        else false;;

% The is_rec versions above are restricted and slow, so this: %
let is_prim_rec def =
	let def1 = strip_forall def in
	if (is_conj def1) then true
	else
		let args_list = flat (get_args def1) in
		one_of_true is_comb args_list;;	

