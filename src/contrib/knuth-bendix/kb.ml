% kb.ml 

  Implements the Huet 1981 JCSS completion procedure.

  Warning. None of the functions that deal with terms in this file 
  check types, i.e. these functions depend on input terms having
  passed the "first order test" coded below.
%

% First some functions that tell if a term is first order
%
let is_uniform_var ty tm = (is_var tm)&(ty = type_of tm);;
let is_uniform_const ty tm = (is_const tm)&(ty = type_of tm);;

letrec strip_uniform_curried_functype ty ftype =
   let (`fun`,[ty1;ty2]) = dest_type ftype
   in
   if (ty = ty1)
   then if (ty = ty2)
        then [ty1 ; ty2]
        else (ty1 . strip_uniform_curried_functype ty ty2)
   else failwith `not function type`;;


% Actually, terms have to be recursively first order and of a
  uniform curried type.
%
letrec first_order ty tm = 
     (type_of tm = ty) &
     ((is_uniform_var ty tm) or
      (is_uniform_const ty tm) or
      (if (is_comb tm)
       then let (c,args) = strip_comb tm
            in
            (forall (first_order ty) args) &
            (is_const c) &
            ((length args)+1 = length (strip_uniform_curried_functype ty (type_of c)))
       else false)) ? false;;


% First order equations %
let first_order_eqn ty tm =
   let tm1,tm2 = dest_eq tm
   in
   if (ty = type_of tm1)
   then (first_order ty tm1) & (first_order ty tm2)
   else failwith `Equation is not of the right type`;;


% Slightly adapted from the system "find_match" function
  so that it keeps an occurrence list.
%
let kb_match pat =
 letrec find_mt occ ob =
  ((match pat ob, occ)
   ? find_mt (0.occ) (rator ob)
   ? find_mt (1.occ) (rand  ob)
   ? failwith `find_match`)
 in
 (I#rev) o (find_mt []);;

% Example
#kb_match "x+1" "3 + 2 + (4 * (7+1)) + 13 - 12";;
(([("7", "x")], []), [1; 1; 0; 1; 1]): (((term # term) list # (type # type) list) # int list)
%

% The occurs check for first order unification
%
letrec occurs t1 t2 =
   if (is_var t1)
   then if (is_var t2)
        then (t1 = t2)
        else if (is_const t2)
             then false
             else if (is_comb t2)
                  then let (c,args) = strip_comb t2
                       in
                       exists (\arg. occurs t1 arg) args
                  else failwith `occurs`
   else failwith `occurs`;;


letrec term_size tm =
   if (is_var tm)
   then 0
   else if (is_const tm)
        then 1
        else if (is_comb tm)
             then 1 + (itlist (\x. \y. (term_size x) + y)
                              (snd (strip_comb tm))
                              0)
             else failwith `term_size`;;

% Substitutions are lists of term pairs. The second gets replaced
  by the first. Applying a substitution to a binding entails leaving
  the second member of the pair undisturbed, but appluying the subst
  to the first member.
%
let subst_in_subst_binding s (tm1,tm2) = ((subst s tm1), tm2);;
let is_ident_binding (t1,t2) = (t1=t2);;

% Substitution composition. s2 o s1. For HOL-style substitutions, we 
  require t/v bindings, i.e., the variable being substituted for is second.
%
let compose s2 s1 =
   if ((forall is_var (map snd s2)) & (forall is_var (map snd s1)))
   then let c = map (subst_in_subst_binding s2) s1
        in
        let c' = filter ($not o is_ident_binding) c
        in
        let c'' = filter (\ (a,b). not (mem b (map snd s1))) s2
        in
        (c'@c'')
   else failwith `NON_VAR_SUBSTITUTION`;;

let app_sub s binding_list = map ((subst s)#(subst s)) binding_list;;

% First order unification example, from Martelli & Montanari paper.
  new_theory `gaz`;;
  new_constant(`f`,":num -> num -> num -> num -> num");;
  new_constant(`g`,":num->num->num");;
  new_constant(`h`,":num->num->num");;

  #unify "f x (g y z) y 0" "f (g (h 1 w) y) x (h 1 u) u";;
  [("g(h 1 0)(h 1 0)", "x");
   ("h 1 0", "y");
   ("h 1 0", "z");
   ("0", "w");
   ("0", "u")]
   : (term # term) list
%

% There are faster ways of doing this.
%
let unify t1 t2 =
   letrec unif bset s = 
      if (null bset)
      then s
      else let (l,r) = hd bset
           and rst = tl bset
      in
      if (l = r) 
      then unif rst s
      else if (is_var l) 
           then if (occurs l r) 
                then failwith `NO_UNIFIER`
                else let new_addition = [(r,l)]
                     in
                     unif (app_sub new_addition rst) (compose new_addition s)
           else if (is_var r)
                then unif ((r,l) . rst) s
                else if ((is_const l) or (is_const r)) 
                     then failwith `NO_UNIFIER`
                     else unif ((rator l, rator r).(rand l, rand r).rst) s
in
unif [(t1,t2)] [];;


let thm_eq th1 th2 = 
   let (h1,c1) = dest_thm th1
   and (h2,c2) = dest_thm th2
   in
   (c1 = c2) & 
   (is_subset h1 h2) &
   (is_subset h2 h1);;


letref global_rule_count = 0;;
let reset_rule_count() = global_rule_count := 0;;

% An abstract data type for what term rewriting people call rewrite
  rules. It's a bit of overkill, but helped me in the writing of
  the code.
%
abstype rule = (int#thm#bool)
with
number r = fst (rep_rule r)
and rule_thm r = fst(snd(rep_rule r))
and marked r = snd(snd(rep_rule r))
and dest_rule r = rep_rule r
and rule_lhs r = (fst o dest_eq o concl o fst o snd o rep_rule) r
and rule_rhs r = (snd o dest_eq o concl o fst o snd o rep_rule) r
and 
mk_rule n th m = 
  let t1 = (fst o dest_eq o concl) th
  and t2 = (snd o dest_eq o concl) th
  in
  if (not (is_subset (vars t2) (vars t1)))
  then failwith `mk_rule: excess vars in rhs`
  else if (is_var t1) 
       then failwith `mk_rule: lhs cannot be a variable`
        else abs_rule(n,th,m)
and
mk_new_rule th = 
% This is a bit dodgy. I should do the checks of mk_rule,
  but I only call mk_new_rule on oriented critical pairs, 
  which are guaranteed to pass the tests in mk_rule.
%
  ( global_rule_count := global_rule_count+1;
    abs_rule (global_rule_count,th,false))
and
mark r = let (n,th,mrked) = rep_rule r
         in
         if mrked
         then failwith `rule already marked`
         else 
         abs_rule(n,th,true)
and
print_rule r = 
  let (n,th,c) = rep_rule r
  in
  let (l,r) = dest_eq (concl th)
  in
  (print_int n;
   print_string `. `;
   print_string (c => `*` | ``);
   print_term l;
   print_string ` --> `;
   print_term r;
   print_newline())

and 
rule_eq r1 r2 =
   let (n1,th1,m1) = rep_rule r1
   and (n2,th2,m2) = rep_rule r2
   in
   thm_eq th1 th2;;


let print_rules R = (map print_rule R;());;

let rule_sort = 
   merge_sort (\x y. let (lhs1,lhs2) = (rule_lhs#rule_lhs) (x,y)
                     in
                     not (term_size lhs1) > (term_size lhs2));;

% Get the first unmarked rule from R. In general, R will stand for the 
  current set of rules and E will stand for the current set of
  equations.
%
let get_unmarked R = 
   let (m,unm) = kb_split marked R
   in
   if (length unm = 0) 
   then failwith `get_unmarked: all rules are marked` 
   else let sorted_unmarked = rule_sort unm
        in
        ((hd sorted_unmarked),((tl sorted_unmarked)@m));;


let kb_match_rule_with_term r t = kb_match (rule_lhs r) t;;


letrec find_kb_match t rule_list= 
   if (null rule_list)
   then failwith `KB_NO_MATCH`
   else let (r,rst) = ((hd rule_list), tl rule_list)
        in
        ((kb_match_rule_with_term r t),r)
        ?? [`term_match`] find_kb_match t rst;;


let replace in_tm =
   letrec repl tm occ_list =
      if (null occ_list)
      then in_tm
      else let (t1,t2) = dest_comb tm
           and (dir.rst) = occ_list
           in
           mk_comb (if (dir=0)
                    then (repl t1 rst, t2)
                    else (t1, repl t2 rst))
   in repl;;


let apply_subst_to_rule s r = 
   mk_rule (number r) (INST s (rule_thm r)) (marked r);;


let normalize_rule r = 
   let normal_subst trm = 
      let trm_vars = vars trm
      and ty = type_of trm
      in
      let new_var_names = map ((concat `x`) o string_of_int)
                              (iota 1 (length trm_vars))
      in
      let new_vars = map (\n. mk_var(n,ty)) new_var_names
      in
      combine (new_vars,trm_vars)
   in
   apply_subst_to_rule (normal_subst (rule_lhs r)) r;;


% Specialize a closed theorem to all new variables, and remember
  which old variables got replaced by which new new ones, i.e., an
  inverse substitution.
%
letrec gspec_w_mem th blist =
   let c = concl th
   in
   if (is_forall c)
   then let (x,body) = dest_forall c
        in
        let v = genvar (type_of x)
        in 
        gspec_w_mem (SPEC v th) ((x,v) . blist)
   else (th,blist);;

% Close the thm up, then specialize all variables to new ones, keeping
  track of the inverse substitution. Thus the following should be
  true (in SML-ese):

     - let val (th1,s1) = RENAME_APART th
       in
       (concl (INST s1 th1)) = (concl (SPEC_ALL th)
       end;

This is so that unification doesn't stumble on the occurs check if
two rules happen to have variables with the same name.
%
let RENAME_APART rle = 
   let (new_th,s) = gspec_w_mem (GEN_ALL (rule_thm rle)) []
   in
   ((mk_rule (number rle) new_th (marked rle)),s);;


% Computes overlaps. We have to check, right at the start, that subt and supert
  are not the same. If they are, then we don't attempt to unify them. Overlaps
  are computed throughout supert
%
letrec superpose teq subt supert occ =
   if (is_var supert)
   then []  % [] stands for no superposition %
   else if (is_const supert)
        then if (subt = supert)
             then [([],occ)]
             else []
        else let top_overlap = if teq
                               then [] 
                               else ([((unify subt supert),occ)] ? [])
             and (t1,t2) = dest_comb supert
             in
             top_overlap@(superpose false subt t1 (0.occ))@
                         (superpose false subt t2 (1.occ));;


% Does some pre-processing before calling superpose.
%
let overlap r1 r2 inv_sub = 
   let lhs1 = rule_lhs r1
   and lhs2 = rule_lhs r2
   % If rules equal before renaming, then superpose needs to ignore the top_overlap %
   and same_rule = rule_eq r1 (apply_subst_to_rule inv_sub r2)
   in
   map (I#rev) (superpose same_rule lhs2 lhs1 []);;


let mk_template th occ =
   let (left,right) = (dest_eq o concl) th
   in
   let v = genvar (type_of left)
   in
   (v, (curry mk_eq (replace v left occ) right));;


% This is the heart of the Knuth-Bendix procedure. The call to 
  overlap computes the overlaps between r1 and r2. From those,
  we infer the critical pairs with SUBST.
%
let crits r1 r2 = 
   let (r2',inv_sub) = RENAME_APART r2
   in
   if (rule_eq r1 r2')  % Possible if no vars in r2 %
   then []
   else map (\(theta,occ).
                  let inst_r1 = INST theta (rule_thm r1)
                  and inst_r2' = INST theta (rule_thm r2')
                  in
                  let (v,template) = mk_template inst_r1 occ
                  in
                  SUBST [(inst_r2',v)] template inst_r1)
            (overlap r1 r2' inv_sub);;


let critical_pairs rule1 rule2 = (crits rule1 rule2)@(crits rule2 rule1);;


let all_cp r R = op_U thm_eq (map (critical_pairs r) R);;

let print_cp th = (print_thm th; print_newline());;

let rule_union = op_union rule_eq
and eqn_U = op_U thm_eq;;

let reduce_eqn_fully R th =
   let ty = type_of (lhs (concl th))
   in
   PSUB_ALL ((INST_TYPE [(ty,":*")](SPEC_ALL REFL_CLAUSE)) . (map rule_thm R)) th;;

let lhs_reducible reducer prospect = 
   can (kb_match_rule_with_term reducer) (rule_lhs prospect);;

let lhs_reduce reducer reducee = RW_LHS_FULLY [rule_thm reducer] reducee;;

let rhs_reduce reducers reducee =
   let (n,th,m) = dest_rule reducee
   in
   mk_rule n (RW_RHS_FULLY (map rule_thm reducers) th) m;;

let show_list pfun alist = 
   if (null alist)
   then ( print_string `none`; print_newline())
   else ( print_newline(); map pfun alist; print_newline());;

let unorderable th orderp = not ((orderp th) or (orderp (SYM th)));;

let reflexive th = thm_eq TRUTH th;;

% The next two functions define a finite state machine. Assess passes control
to transfer, which moves orderable equations from E to R until E is empty. Then
control returns to assess, whereupon we find all critical pairs in R and move
them into E. Then we go back to the initial state. This terminates when a
prospective rule is not orderable, or when we succeed in completing the system.
The program can also loop forever.
%
letrec transfer E unorderableE R orderp =
  if (null E)
  then if (null unorderableE)
       then R
       else ( print_newline();
              print_string `Unorderable equations:`;
              show_list print_thm (map (reduce_eqn_fully R) unorderableE);
              failwith `EQN_NOT_ORIENTABLE`)
  else let e = hd E
       and rst = tl E
       in
       let e' = reduce_eqn_fully R e
       in
       if (reflexive e')
       then (transfer rst unorderableE R orderp)
       else if (unorderable e' orderp) 
            then transfer rst (e . unorderableE) R orderp
            else 
            let rle = mk_new_rule (if (orderp e') 
                                   then e' 
                                   else if (orderp (SYM e'))
                                        then SYM e'
                                        else failwith `unorderable eqn`)
            in
            let (lr,nlr) = (kb_split o lhs_reducible) rle R
            in
            transfer (eqn_U [ rst; unorderableE; map (lhs_reduce rle)
                                                     (map rule_thm lr)])
                     []
                     (rule_union (map (rhs_reduce (rule_union [rle] R)) nlr) [rle])
                     orderp;;




letrec assess E R orderp =
   let R' = if (length E = 0) 
            then R 
            else transfer E [] R orderp
   in
   if (forall marked R')
   then map (rule_thm o normalize_rule) R'
   else let (r,R'') = get_unmarked R'
        in
        let crit_pairs = all_cp r (filter (\x. not (number x) > (number r)) R')
        in
        assess crit_pairs (R''@[(mark r)]) orderp;;


% Notice the test for "first orderness".
%
let kb order_pred E = 
   let E' = map SPEC_ALL E
   in
   let ty = type_of (lhs (concl (hd E')))
   in
   if (forall ((first_order_eqn ty) o concl) E')
   then assess E' [] (\th. (uncurry order_pred) (dest_eq (concl th)))
   else failwith `Some equations are not first order`;;



% Tracing version
%
let show_transfer_args E =
   (print_string `........................................... Transferring equations: `;
    show_list (\x. (print_thm x; print_newline())) E);;


letrec transfer_trace E unorderableE R orderp =
  if (null E)
  then if (null unorderableE)
       then R
       else ( print_newline();
              print_string `Unorderable equations:`;
              show_list print_thm (map (reduce_eqn_fully R) unorderableE);
              failwith `EQN_NOT_ORIENTABLE`)
  else let e = hd E
       and rst = tl E
       in
       ( print_string `Selected equation: `;
         print_thm e;
       let e' = reduce_eqn_fully R e
       in
       ( print_newline();
         print_string `Reduced equation: `;
         print_thm e';
       if (reflexive e')
       then ( print_newline();
              print_string `Reduced to identity.`;
              print_newline();
              transfer_trace rst unorderableE R orderp)
       else if (unorderable e' orderp) 
            then ( print_newline();
                   print_string `shifting equation:`;
                   print_newline();
                   print_thm e; print_newline();
                   print_string `to unorderableE because reduced form:`;
                   print_newline();
                   print_thm e';
                   print_string ` is unorderable.`;
                   print_newline();
                   transfer_trace rst (e . unorderableE) R orderp)
            else 
            let rle = mk_new_rule (if (orderp e') 
                                   then e' 
                                   else if (orderp (SYM e'))
                                        then SYM e'
                                        else failwith `unorderable eqn`)
            in
            ( print_newline();
              print_string `New rule: `;
              print_rule rle;
            let (lr,nlr) = (kb_split o lhs_reducible) rle R
            in
            transfer_trace (eqn_U [ rst; unorderableE; map (lhs_reduce rle)
                                                     (map rule_thm lr)])
                     []
                     (rule_union (map (rhs_reduce (rule_union [rle] R)) nlr) [rle])
                     orderp)));;



letrec assess_trace E R orderp =
   ( show_transfer_args E;
   let R' = if (length E = 0) 
            then R 
            else transfer_trace E [] R orderp
   in
   ( print_string `...................................... transferred all equations`;
     print_newline();
     print_string `rule set is: `;
     show_list print_rule R';
   if (forall marked R')
   then ( let finalR = map (rule_thm o normalize_rule) R'
          in
          print_string `Completion successful. Final rule set is: `;
          show_list print_thm finalR; 
          print_newline();print_newline();print_newline();
          finalR)
   else let (r,R'') = get_unmarked R'
        in
        ( print_newline(); print_newline();
          print_string `Computing critical pairs between `; 
          print_newline();
          print_rule r;
          print_string `and`;
          show_list print_rule (filter (\x. not (number x) > (number r)) R');
        let crit_pairs = all_cp r (filter (\x. not (number x) > (number r)) R')
        in
      ( print_string `Critical pairs: `;
        show_list print_cp crit_pairs; 
        print_newline();
        assess_trace crit_pairs (R''@[(mark r)]) orderp))));;

let kb_trace order_pred E = 
   let E' = map SPEC_ALL E
   in
   let ty = type_of (lhs (concl (hd E')))
   in
   if (forall ((first_order_eqn ty) o concl) E')
   then assess_trace E' [] (\th. (uncurry order_pred) (dest_eq (concl th)))
   else failwith `Some equations are not first order`;;


