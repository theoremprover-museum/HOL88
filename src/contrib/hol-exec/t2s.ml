% sree@cs.ubc.ca %

let pathname = get_path `hol-eval_setup.ml`;;

loadf (pathname ^ `basics`);;
loadf (pathname ^ `cons`);;
loadf (pathname ^ `rec`);;

letrec term_to_string hol_term =
         if (is_var hol_term) then
            concat ` ` 
             (concat (fst (dest_var hol_term))
                      ` `)
         else
         if (is_const hol_term) then
           let const_str1 = fst (dest_const hol_term) in
            (let const_str2 = lookup_map const_map const_str1 in
             concat ` ` 
              (concat const_str2
                      ` `))
         else
         if (is_abs hol_term) then
           let t1 = dest_abs hol_term in
            concat `(\\`
             (concat (fst (dest_var (fst t1)))
               (concat `. `
                 (concat (term_to_string (snd t1))
                         `) `)))
         else
         if (is_forall hol_term) then
            let t1 = dest_forall hol_term in
             (let quant = fst (dest_var (fst t1)) in
               tty_write (`\LWarning: removing universal quantification on ` 
                          ^ quant ^ `\L`);
		  term_to_string (snd t1))


	 else
         if (is_exists hol_term) then
            let t1 = dest_exists hol_term in
             (let quant = fst (dest_var (fst t1)) in
               tty_write (`\LWarning: removing existential quantification on ` 
                          ^ quant ^ `\L`);
		  term_to_string (snd t1))
	 else
	 % Treat conditional separately: see prim.ml for comments%
         if (is_cond hol_term) then
	    let dt = dest_cond hol_term in
	     (let t1 = fst dt and
	 	  t2 = fst (snd dt) and
                  t3 = snd (snd dt) in
	      concat `(if `
		(concat (term_to_string t1)
		  (concat ` then `
		    (concat (term_to_string t2)
		      (concat ` else `
			(concat (term_to_string t3) `)`))))))
         else
         if (is_comb hol_term) then
           let comb_pair = dest_comb hol_term in
           concat (term_to_string (fst comb_pair))
            (concat ` (`
             (concat (term_to_string (snd comb_pair))
                     `)`))
         else
            ``;;

letrec term_to_string_defs let_or_letrec hol_term =
     let def_term = strip_outer_quantifiers hol_term in
       if (is_eq def_term) then
         let eq_pair = dest_eq def_term in
         (let lhs = fst eq_pair and
              rhs = snd eq_pair in 
         (let func_and_arg_list = mk_func_and_arg_list lhs in
          (let func = hd func_and_arg_list and 
               arg_list = tl func_and_arg_list in
           (let abs_rhs = mk_lambda_term (rev arg_list) rhs in
          (concat let_or_letrec
           (concat (term_to_string func) 
            (concat ` = `
                    (term_to_string abs_rhs))))))))
        else
          term_to_string hol_term;;

% Older restricted form - limited recursion finding 
let t2s_defs hol_term =
      let def = strip_outer_quantifiers hol_term in
       if (is_conj def) then
         let rec_def = pat_to_tree def in
         term_to_string_defs rec_def
      else
         term_to_string_defs def;;
%

% Well, this is good, but does not "partially specified"
  HOL recursive functions: because my is_rec finds only
  pure recursive functions 
let t2s_defs hol_term =
      let def = strip_outer_quantifiers hol_term in
       if (is_rec1 def) then
         let dest_defs_str = mk_all_dest_defs def in
          (let rec_def = pat_to_tree def in
            (concat dest_defs_str (term_to_string_defs rec_def)))
      else
         term_to_string_defs def;;
%

% So, use exception to detect left-out "recursive functions":
   quite inefficient 
let t2s_defs hol_term =
      let def = strip_outer_quantifiers hol_term in
       if (is_rec1 def) then
         let rec_def = pat_to_tree def in
         term_to_string_defs rec_def
       else
         (term_to_string_defs def ?
          (let rec_def = pat_to_tree def in
           term_to_string_defs rec_def));;
%

let t2s_defs hol_term =
      let def = strip_outer_quantifiers hol_term in
       if (is_prim_rec def) then
         let rec_def = pat_to_tree def in
          (let str1 = term_to_string_defs `letrec ` rec_def and
               str2 = mk_all_dest_defs def in
            concat str2 str1)
       else
         term_to_string_defs `let ` def;;





