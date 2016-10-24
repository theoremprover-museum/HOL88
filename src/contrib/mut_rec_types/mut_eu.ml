
%
let OUR_EXISTS_UNIQUE_TAC_2 :tactic (asl,w) = 
  letrec doit f x n =
    if n=0 then ([],x)
    else
     let (v,body) = f x in
     let (vs, remains) = doit f body (n-1) in
     (v.vs, remains) in
  let (vars,body)= doit (dest_abs o snd o dest_comb) w 2 in
  let (term_subst, type_subst) =
     match "t:*->**->bool" (list_mk_abs (vars, body)) in
  let instantiated_thm= SPEC (fst(hd term_subst))
                        (INST_TYPE type_subst our_exists_unique_thm_2) in
  let (antecedent, conclusion) = dest_imp(concl instantiated_thm) in
  [(asl, antecedent)], (\l. CONV_RULE
                           (DEPTH_CONV BETA_CONV)
                           (MP instantiated_thm (hd l)));;
%

letrec OUR_EXISTS_UNIQUE_TAC n =
  if n<2 then failwith `Cannot make TAC for less than 2 types` else
  let our_exists_unique_thm n =
    if n=2
    then theorem `mut_rec_tools` `our_exists_unique_thm_2`
    else (theorem `mut_rec_tools` (`our_exists_unique_thm_`^(tok_of_int n))) ? 
         (let prev_tac = OUR_EXISTS_UNIQUE_TAC (n-1) in
          prove_exists_unique_thm prev_tac n) in
  let eu_thm = our_exists_unique_thm n in
  make_our_exists_unique_tac eu_thm n;;

