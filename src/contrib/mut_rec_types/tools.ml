
letrec pick = (\n l. if n=1 then (hd l) else (pick (n-1) (tl l)));;

letrec genvars = (\n. if n=0 then [] else (`v`^(string_of_int n)).(genvars (n-1))) ;; % SUPERSEEDED BY make_vars %

let string2term = (\s. find (\x. fst(dest_const x)=s) (constants `-`)) ;;

letrec foldl op r l =
  if null l
  then r
  else foldl op (op r (hd l)) (tl l);;

letrec foldr op r l =
  if null l
  then r
  else op (hd l) (foldr op r (tl l));;

letrec foldl1 op l =
  if null l
  then fail "foldl1 applied to []"
  else foldl op (hd l) (tl l);;

letrec foldr1 op l =
  if null l
  then fail "foldr1 applied to []"
  else
    let (a.l) = l in
    if null l
    then a
    else op a (foldr1 op l);;

let make_fun x y = mk_type(`fun`,[x;y]);;

let make_repeated_tactic tac n = foldl1 ($THEN) (replicate tac n);;
        
let chop_last l = let (l,[e]) = chop_list (length l - 1) l in (l,e);;

let counted l =
  letrec count i l =
    if null l
    then []
    else (i,hd l).(count (i+1) (tl l)) in
  count 1 l;;

% (upto 1 (length l)) com l;; %

letrec upto from to =
       if from>to then [] else from . (upto (from+1) to);;

let make_vars prefix postfix type_list =
  map (\(i,t). mk_var(prefix^(string_of_int i)^postfix, t)) (counted type_list);;

let pos x l = fst(find (((curry $=) x) o snd) (counted l));;

letrec numbers n =
  if n=0 then [0] else n.(numbers (n-1));;

letrec strip_fun_type typ =
  let (c,typl) = (dest_type typ)?(`tyvar`,[]) in
  if not (c=`fun`)
  then [typ]
  else let [ta;tb] = typl in ta.(strip_fun_type tb);;

let make_star t = mk_vartype(`*`^(fst(dest_type t)));;

letrec transpose m =
  let conj x y = x & y in
  let all_null l = itlist (conj o null) l true in
  if all_null m
  then []
  else (map hd m).(transpose (map tl m));;

let mk_eu (x,t) = mk_comb(mk_const(`?!`,
               make_fun (make_fun (type_of x) ":bool") ":bool"), mk_abs(x,t));;

let list_mk_eu (vars,body) = itlist (curry mk_eu) vars body;;

letrec pick_CONJ = (\n thm. if n=1 then 
                               (if (is_conj (concl thm)) then (CONJUNCT1 thm)
                                else thm)
                            else (pick_CONJ (n-1) (CONJUNCT2 thm)));;

let make_exists_unique_term n =
  if n<2 then fail "attempt to make exists_unique_term for n<2" else
  let tyvars =
    let make_tyvar n = mk_vartype(implode (replicate `*` n)) in
    map make_tyvar (upto 1 n) in
  let t_term =
    mk_var(`t`, foldr make_fun ":bool" tyvars) in
  let xis = map (\(i,t). mk_var(`x`^(string_of_int i), t)) (counted tyvars) in
  let yis = map (\(i,t). mk_var(`y`^(string_of_int i), t)) (counted tyvars) in
  let exists_term = list_mk_exists(xis, list_mk_comb(t_term, xis)) in
  let forall_term =
    let x_term = list_mk_comb(t_term, xis) in
    let y_term = list_mk_comb(t_term, yis) in
    let eqs = map2 mk_eq (xis, yis) in
    let body = mk_imp(mk_conj(x_term, y_term), list_mk_conj eqs) in
    list_mk_forall(flat(map (\(x,y).[x;y]) (xis com yis)), body) in
  let eu_term =
    list_mk_eu(xis, list_mk_comb(t_term, xis)) in
  mk_forall(t_term,mk_imp(mk_conj(exists_term,forall_term),eu_term));;
  
let OUR_EXISTS_TAC (asl,w) =
  let (v,_) = dest_exists w in
  EXISTS_TAC v (asl,w);;

let prove_exists_unique_thm prev_tac n =
  if n<2 then fail "attempt to prove exists_unique_thm for n<2" else
  let tyvars =
    let make_tyvar n = mk_vartype(implode (replicate `*` n)) in
    map make_tyvar (upto 1 n) in
  let xis = make_vars `x` `` tyvars in
  prove_thm(`our_exists_unique_thm_`^(string_of_int n), make_exists_unique_term n,
      (REPEAT STRIP_TAC) THEN
      prev_tac THEN
      CONJ_TAC THENL [
       (REPEAT OUR_EXISTS_TAC) THEN
       BETA_TAC THEN
       (CONV_TAC EXISTS_UNIQUE_CONV) THEN
       CONJ_TAC THENL [
        OUR_EXISTS_TAC THEN
        (FIRST_ASSUM ACCEPT_TAC)
       ;
        BETA_TAC THEN
        (REPEAT GEN_TAC) THEN
        (FIRST_ASSUM (\th. ACCEPT_TAC (
         (\x. let xxis = itlist (\x.\l. x.x.l) (fst(chop_list (n-1) xis)) [] in
              let typ = hd(rev tyvars) in
              let vars = xxis@[mk_var(`x`,typ);mk_var(`y`,typ)] in
              let t1 = SPECL vars x in
          let (lhs,_) = dest_imp (concl t1) in
              let t2 = UNDISCH t1 in
              let t3 = hd(rev(CONJUNCTS t2)) in
              DISCH lhs t3) th) ? NO_TAC))
       ]
      ;
       (CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV)) THEN
       BETA_TAC THEN
       (REPEAT GEN_TAC) THEN
       (DISCH_THEN STRIP_ASSUME_TAC) THEN
       (\(asl,w).FIRST_ASSUM (\th. ACCEPT_TAC (
        (\x. let xps = make_vars `x` `'` tyvars in
             let (ytyvars,xtyvar) = chop_last tyvars in
             let yis = make_vars `y` `` ytyvars in
             let yyis = yis@[mk_var(`x`^(string_of_int n)^`''`, xtyvar)] in
             let vars = itlist (\(x,y).\l.x.y.l) (xps com yyis) [] in
             let t1 = SPECL vars x in
             let c1 = ASSUME (pick 4 asl) and
                 c2 = ASSUME (pick 2 asl) in
             let conj = CONJ c1 c2 in
             let t2 = MP t1 conj in
             (foldr1 CONJ) (fst(chop_last(CONJUNCTS t2)))) th)
         ? NO_TAC) (asl,w))
       ]);;

let make_our_exists_unique_tac eu_thm n (asl:term list,w) = 
  if n<2 then fail "attempt to make exists_unique_tac for n<2" else
  letrec doit f x n =
    if n=0 then ([],x)
    else
     let (v,body) = f x in
     let (vs, remains) = doit f body (n-1) in
     (v.vs, remains) in
  let (vars,body)= doit (dest_abs o snd o dest_comb) w n in
  let tyvars =
    let make_tyvar n = mk_vartype(implode (replicate `*` n)) in
    map make_tyvar (upto 1 n) in
  let t_term =
    mk_var(`t`, foldr (\x.\y. mk_type(`fun`, [x;y])) ":bool" tyvars) in
  let (term_subst, type_subst) =
     match t_term (list_mk_abs (vars, body)) in
  let instantiated_thm= SPEC (fst(hd term_subst))
                        (INST_TYPE type_subst eu_thm) in
  let (antecedent, conclusion) = dest_imp(concl instantiated_thm) in
  [(asl, antecedent)], (\l. CONV_RULE
                           (DEPTH_CONV BETA_CONV)
                           (MP instantiated_thm (hd l)));;

