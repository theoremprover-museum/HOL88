% sree@cs.ubc.ca %

let pathname = get_path `hol-eval_setup.ml`;;

loadf (pathname ^ `t2s`);;

% One of true of a predicate %
letrec one_of_true p list =
       if (null list) then false
       else
        if (p (hd list)) then true
        else
          one_of_true p (tl list);;

% Define curried eq %
let eq x y = (x=y);;

% predicate blocking defs %
let eq_const const_str_list term = 
       one_of_true (eq (const_var_to_string term)) const_str_list;;

letrec no_fail_map f list =
       if (null list) then []
       else
        (let head = f (hd list) in
         head.(no_fail_map f (tl list)))?
        no_fail_map f (tl list);;

let mk_fl_thy1 def =
          let def' = strip_outer_quantifiers def in
           (concat (t2s_defs def')
                   `;;\L`);;

letrec read_str() = 
      let char_read = tty_read() in
      if (char_read = `\L`) then ``
      else concat char_read (read_str());;

letrec query file =
      tty_write (concat `File ` 
                (concat file ` exists -- type "s" to skip; "a" to append; "w" to overwrite: `));
      let ans = read_str() in
      if ((ans = `s`) or (ans = `a`) or (ans = `w`)) then ans
      else query file;;

let query_apply f thy list =
        let file = concat thy `_hol.ml` in
         ((find_file file;
           let ans = query file in
           if (ans = `a`) then
              let portw = append_openw file in
              f portw thy list
           else
           let portw = openw file in
               f portw thy list)?
           (f (openw file) thy list));;

% Takes an extra list: we need something which takes an 
   arbitrary number of args 
%

let query_apply_extra f thy list1 list2 =
        let file = concat thy `_hol.ml` in
         ((find_file file;
           let ans = query file in
           if (ans = `s`) then
		()
           else
           if (ans = `a`) then
              let portw = append_openw file in
              f portw thy list1 list2
           else
           let portw = openw file in
               f portw thy list1 list2)?
           (f (openw file) thy list1 list2));;

% Same as above except a file is supplied %
let f_query_apply_extra f thy list1 list2 file =
         ((find_file file;
           let ans = query file in
           if (ans = `s`) then
		()
           else
           if (ans = `a`) then
              let portw = append_openw file in
              f portw thy list1 list2
           else
           let portw = openw file in
               f portw thy list1 list2)?
           (f (openw file) thy list1 list2));;

let const_block_list = [`string_CONCAT`];;
let parents_block_list = [`hol2hcl`;`voss`;`ascii`;`auxiliary`;`bags`;`bool`;`convert`;`eval`;`finite_sets`;
                          `fixpoints`;`group`;`ind_defs`;`int_mod`;`integer`;
                          `more_arithmetic`;`more_lists`;`parser`;
                          `pred_sets`;`prettyp`;`prog_logic88`;`quotient`;
                          `reduce`;`sets`;`string`;`taut`;`trs`;`unwind`;
                          `window`;`HOL`;`BASIC_HOL`;`GEN_TRANS`;
                           `PPLAMB`;`P_UNIQUE`;`arithmetic`;`combin`;
			   `ind`;`list`;`ltree`;`num`;`one`;`prim_rec`;
			   `sum`;`time_abs`;`tree`;`tydefs`];;

% HOL stores definitions in reverse order!: so define rev_def %
let mk_ord_def_list thy = rev (definitions thy);;

let mk_fl_thy thy block_def_list block_cons_list =
        let const_list = constants thy and
            def_list1 = map snd (mk_ord_def_list thy) in
        (let def_list = subtract def_list1 block_def_list in
        (let cons_list1 = sublist (is_constructor_from thy) const_list and
          block_const_list = sublist (eq_const const_block_list)
                                      const_list in
         (let cons_list = subtract cons_list1 block_cons_list in
          (let cons_def_list = no_fail_map (get_def_from thy) cons_list and
              block_defs_list = no_fail_map (get_def_from thy) block_const_list in
           (let def_list' = subtract def_list cons_def_list in
            (let def_list'' = subtract def_list' block_defs_list in
            (let cons_def_str_list = map (mk_quick_cons_def_from thy) 
                                          cons_list and
                 cons_type_def_str_list = mk_cons_type_defs thy cons_list and
                 const_def_str_list =
                     no_fail_map mk_fl_thy1 (map concl def_list'') in
        (append cons_type_def_str_list 
               (append 
                  cons_def_str_list
                  const_def_str_list)))))))));;

letrec mk_parents_incl_str1 thy_list =
      let head = hd thy_list in
      if (one_of_true (eq head) parents_block_list) then ``
      else
        (concat `loadf `
          (concat `\``
           (concat head
            (concat `_hol\`;;\L`
                    (mk_parents_incl_str1 (tl thy_list))))));;
       
let mk_parents_incl_str thy =
      let par_list = parents thy in
      mk_parents_incl_str1 par_list;;

let write_once_fl_thy thy l1 l2 =
        let portw = openw (concat thy `_hol.ml`) in
        (let str_list = mk_fl_thy thy l1 l2 in
        (let fl_prog = inv_words `\L` str_list and
             incl_decl = mk_parents_incl_str thy in
         (write(portw,incl_decl);        
          write(portw,fl_prog))));;

letrec write_fl_thy11 cons_list thy portw =
       if (null cons_list) then write(portw,`\L`)
       else
       ((let cons_def_str = mk_quick_cons_def_from thy (hd cons_list) in
          write(portw,cons_def_str); write(portw,`\L`);
          (write_fl_thy11 (tl cons_list) thy portw))? 
        (write_fl_thy11 (tl cons_list) thy portw));;

letrec write_fl_thy121 cons_list_list thy portw =
       if (null cons_list_list) then write(portw,`\L`)
       else
       let cons_type_def_str = mk_cons_type_defs_str thy 
                                      (hd cons_list_list) in
         write(portw,cons_type_def_str); 
         write(portw,`\L`);
         write_fl_thy121 (tl cons_list_list) thy portw;;

let write_fl_thy12 cons_list thy portw =
       if (null cons_list) then write(portw,`\L`)
       else
        let type_list = map get_final_ret_type cons_list in
% We should actually sort the type groups according to containment,
  but we will for the moment assume a reverse order creation: %
         let cons_list_list = rev 
                               (mk_groups_of_same_type 
                                  (mk_pair_list cons_list type_list)) in
         write_fl_thy121 cons_list_list thy portw;;

let write_fl_thy1 cons_list thy portw =
       write_fl_thy12 cons_list thy portw;
       write_fl_thy11 cons_list thy portw;;


letrec write_fl_thy2 def_list portw =
       if (null def_list) then write(portw,`\L`)
       else
         ((let cons_def_str = mk_fl_thy1 (concl (hd def_list)) in
           write(portw,cons_def_str);write(portw,`\L\L`);
          (write_fl_thy2 (tl def_list) portw))? 
          (write(portw,`\L\L`); write_fl_thy2 (tl def_list) portw));;

let write_fl_thy0 file thy block_def_list block_cons_list =
        let const_list = constants thy and
            def_list1 = map snd (mk_ord_def_list thy) in
        (let def_list = subtract def_list1 block_def_list in
        (let cons_list1 = sublist (is_constructor_from thy) const_list and
          block_const_list = sublist (eq_const const_block_list) const_list in
         (let cons_list = subtract cons_list1 block_cons_list in
          (let cons_def_list = no_fail_map (get_def_from thy) cons_list and
              block_defs_list = no_fail_map (get_def_from thy) block_const_list in
           (let def_list' = subtract def_list cons_def_list in
            (let def_list'' = subtract def_list' block_defs_list in
            (let incl_decl = mk_parents_incl_str thy in
           (write(file,incl_decl);        
            write_fl_thy1 cons_list thy file;
            write_fl_thy2 def_list'' file))))))));;

let write_fl_thy thy block_def_list block_cons_list =
        query_apply_extra write_fl_thy0 thy block_def_list block_cons_list;;

letrec mk_load_decls parents =
      let head = hd parents in
       if (one_of_true (eq head) parents_block_list) then ``
       else
         let load_decl =
             (concat `loadf `
              (concat `\``
               (concat head
                       `_hol\`;;\L`))) in
         concat (mk_load_decls (tl parents)) load_decl;;

let write_load_decls thy portw =
       let load_decls = mk_load_decls (parents thy) in
         write(portw,load_decls);;
        
letrec hcomp1 thy_list l1 l2 =
% thy_list is never null %
       let head = hd thy_list in
       if (one_of_true (eq head) parents_block_list) then `done`
       else
        let file = concat head `_hol.ml` in
          (find_file file?
            (write_once_fl_thy head l1 l2;
             hcomp1 (parents head) l1 l2;
             hcomp1 (tl thy_list) l1 l2));;

let hcomp thy block_const_str_list block_cons_term_list = 
      let l1 = no_fail_map get_def_from_key block_const_str_list and
          l2 = block_cons_term_list in
       (let file = concat thy `_hol.ml` in
         (find_file file))?
         ((write_once_fl_thy thy l1 l2);
          (let par_list = parents thy in
           (hcomp1 par_list l1 l2)));;

letrec ihcomp1 thy_list l1 l2=
     if (null thy_list) then ``
     else
% thy_list is probably never null %
       let head = hd thy_list in
% We assume that HOL is a Greatgrand-parent%
       if (eq head `HOL`) then `done`
       else
       if (one_of_true (eq head) parents_block_list) then
             (ihcomp1 (parents head) l1 l2;
              ihcomp1 (tl thy_list) l1 l2)
       else
%
        let file = concat head `_hol.ml` in
          ((find_file file; 
            ihcomp1 (parents head) l1 l2;
             ihcomp1 (tl thy_list) l1 l2)
             ?
%
            (write_fl_thy head l1 l2;
             ihcomp1 (parents head) l1 l2;
             ihcomp1 (tl thy_list) l1 l2);;

%
let ihcomp thy block_const_list block_cons_list = 
      (let l1 = no_fail_map get_def_from_key block_const_list and
           l2 = block_cons_list in
       ((let file = concat thy `_hol.ml` in
         (find_file file);
          (let par_list = parents thy in
           (ihcomp1 par_list l1 l2)))
        ?
        ((write_fl_thy thy l1 l2);
          (let par_list = parents thy in
           (ihcomp1 par_list l1 l2)))));;
%
let ihcomp thy block_const_list block_cons_list = 
      (let l1 = no_fail_map get_def_from_key block_const_list and
           l2 = block_cons_list in
        ((write_fl_thy thy l1 l2);
          (let par_list = parents thy in
           (ihcomp1 par_list l1 l2))));;


% Compile specified constructors %
let hcc_cons1 file thy cons_list =
      let cons_def_str_list = map (mk_quick_cons_def_from thy) 
                                   cons_list and
         cons_type_def_str = inv_words `` (mk_cons_type_defs thy cons_list) in

      (let fl_prog = inv_words `\L` cons_def_str_list in
        write(file,cons_type_def_str);
        write(file,`\L`); 
        write(file,fl_prog));;
       
let hcc_cons cons_list thy =
      query_apply hcc_cons1 thy cons_list;;

% Compile the specified defs %
let hcc_defs1 file thy def_str_list =
        (let def_term_list = map concl 
                              (no_fail_map (get_def_from_key_from_thy thy) def_str_list) in
         (let fl_def_list = no_fail_map mk_fl_thy1 def_term_list in
          (let fl_prog = inv_words `\L` fl_def_list in
            write(file,fl_prog))));;

let hcc_defs def_str_list thy =
        query_apply hcc_defs1 thy def_str_list;;

let hcc1 file thy def_str_list cons_list =
      write_load_decls thy file;
      (let cons_def_str_list = map (mk_quick_cons_def_from thy) 
                                   cons_list and
         cons_type_def_str = inv_words `` (mk_cons_type_defs thy cons_list) in
       (let fl_prog = inv_words `\L` cons_def_str_list in
          write(file,cons_type_def_str);
          write(file,`\L`);
          write(file,fl_prog)));
      (let def_term_list = map concl 
                          (no_fail_map (get_def_from_key_from_thy thy) def_str_list) in
         (let fl_def_list = no_fail_map mk_fl_thy1 def_term_list in
          (let fl_prog = inv_words `\L` fl_def_list in
            write(file,fl_prog))));;

let hcc0 thy def_str_list cons_list =
      if ((null def_str_list) & (null cons_list)) then ()
      else
        query_apply_extra hcc1 thy def_str_list cons_list;;

letrec hcc pair_list =
      if (null pair_list) then `done`
      else
       let head = hd pair_list and
           tail = tl pair_list in
       (let t1 = fst head and
          t2pair = snd head in
         (let t21 = fst t2pair and
              t22 = snd t2pair in
        (hcc0 t1 t21 t22; 
         hcc tail)));;

let ihcc_cons1 file thy cons_list =
        write_fl_thy1 cons_list thy file;;

let ihcc_cons cons_list thy =
        query_apply ihcc_cons1 thy cons_list;;

let ihcc_defs1 file thy def_str_list =
        let def_list = no_fail_map (get_def_from_key_from_thy thy) def_str_list in
         write_fl_thy2 def_list file;;

let ihcc_defs def_str_list thy =
        query_apply ihcc_defs1 thy def_str_list;;

let ihcc1 file thy def_str_list cons_list =
        write_load_decls thy file;
        write_fl_thy1 cons_list thy file;
        let def_list = no_fail_map (get_def_from_key_from_thy thy) def_str_list in
         write_fl_thy2 def_list file;;

let ihcc0 thy def_str_list cons_list =
      if ((null def_str_list) & (null cons_list)) then ()
      else
        query_apply_extra ihcc1 thy def_str_list cons_list;;

letrec evalts pair_list =
      if (null pair_list) then `done`
      else
       let head = hd pair_list and
           tail = tl pair_list in
       (let t1 = fst head and
          t2pair = snd head in
         (let t21 = fst t2pair and
              t22 = snd t2pair in
        (ihcc0 t1 t21 t22; 
         evalts tail)));;

let evalt thy def_str_list cons_list file =
      if ((null def_str_list) & (null cons_list)) then ()
      else
        f_query_apply_extra ihcc1 thy def_str_list cons_list file;;

let h2v hol_term = (term_to_string hol_term)^`;;\R`;;

