%****************************************************************************%
% FILE          : struct_equal.ml                                            %
% DESCRIPTION   : Proof procedure for simplifying an equation between two    %
%                 data-structures of the same type.                          %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton & T.F.Melham                                   %
% DATE          : 4th June 1992                                              %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 14th October 1992                                          %
%****************************************************************************%

%----------------------------------------------------------------------------%
% VAR_NOT_EQ_STRUCT_OF_VAR_CONV : (thm # thm list # thm list) -> conv        %
%                                                                            %
% Proof method developed through discussion between                          %
% R. Boulton, T. Melham and A. Pitts.                                        %
%                                                                            %
% This conversion can be used to prove that a variable is not equal to a     %
% structure containing that variable as a proper subterm. The structures are %
% restricted to applications of constructors from a single recursive type.   %
% The leaf nodes must be either variables or 0-ary constructors of the type. %
%                                                                            %
% The theorems taken as arguments are the induction, distinctness and        %
% injectivity theorems for the recursive type, as proved by the functions:   %
%                                                                            %
%    prove_induction_thm                                                     %
%    prove_constructors_distinct                                             %
%    prove_constructors_one_one                                              %
%                                                                            %
% Since the latter two functions may fail, the distinctness and injectivity  %
% theorems are passed around as lists of conjuncts, so that a failure        %
% results in an empty list.                                                  %
%                                                                            %
% Examples of input terms:                                                   %
%                                                                            %
%    ~(l = CONS h l)                                                         %
%    ~(CONS h1 (CONS h2 l) = l)                                              %
%    ~(n = SUC(SUC(SUC n)))                                                  %
%    ~(t = TWO (ONE u) (THREE v (ONE t) (TWO u (ONE t))))                    %
%                                                                            %
% where the last example is for the type defined by:                         %
%                                                                            %
%    test = ZERO | ONE test | TWO test test | THREE test test test           %
%                                                                            %
% The procedure works by first generalising the structure to eliminate any   %
% irrelevant substructures. If the variable occurs more than once in the     %
% structure the more deeply nested occurrences are replaced by new variables %
% because multiple occurrences of the variable prevent the induction from    %
% working. The generalised term for the last example is:                     %
%                                                                            %
%    TWO a (THREE v (ONE t) b)                                               %
%                                                                            %
% The procedure then forms a conjunction of the inequalities for this term   %
% and all of its `rotations':                                                %
%                                                                            %
%    !t. (!a v b. ~(t = TWO a (THREE v (ONE t) b))) /\                       %
%        (!a v b. ~(t = THREE v (ONE (TWO a t)) b)) /\                       %
%        (!a v b. ~(t = ONE (TWO a (THREE v t b))))                          %
%                                                                            %
% This can be proved by a straightforward structural induction. The reason   %
% for including the rotations is that the induction hypothesis required for  %
% the proof of the original generalised term is the rotation of it.          %
%                                                                            %
% The procedure could be optimised by detecting duplicated rotations. For    %
% example it is not necessary to prove:                                      %
%                                                                            %
%    !n. ~(n = SUC(SUC(SUC n))) /\                                           %
%        ~(n = SUC(SUC(SUC n))) /\                                           %
%        ~(n = SUC(SUC(SUC n)))                                              %
%                                                                            %
% in order to prove "~(n = SUC(SUC(SUC n)))" because the structure is its    %
% own rotations. It is sufficient to prove:                                  %
%                                                                            %
%    !n. ~(n = SUC(SUC(SUC n)))                                              %
%                                                                            %
% The procedure currently uses backwards proof. It would probably be more    %
% efficient to use forwards proof.                                           %
%----------------------------------------------------------------------------%

let VAR_NOT_EQ_STRUCT_OF_VAR_CONV =
 let number_list l =
    letrec number_list' n l =
       if (null l)
       then []
       else (hd l,n).(number_list' (n + 1) (tl l))
    in number_list' 1 l
 in  let name = fst o dest_const
 in  let occurrences constrs v st =
        letrec occurrences' v st path =
           if not (type_of st = type_of v) then []
           if (st = v) then [rev path]
           if (is_var st) then []
           else let (f,args) =
                  (assert ((can (C assoc constrs)) o name) # I) (strip_comb st)
                in  flat (map (\(arg,n). occurrences' v arg (n.path))
                                 (number_list args))
        in occurrences' v st []
 in  let min_length l =
        letrec min_length' (x,n) l =
           if (null l)
           then x
           else if (length (hd l) < n)
                then min_length' (hd l,length (hd l)) (tl l)
                else min_length' (x,n) (tl l)
        in if (null l)
           then failwith `min_length`
           else min_length' (hd l,length (hd l)) (tl l)
 in  letrec generalise (st,occ) =
        letrec replace_side_structs (n,argn',binding) m args =
           if (null args)
           then ([],[])
           else let m' = m + 1
                and arg = hd args
                in  let (rest,bind) =
                       replace_side_structs (n,argn',binding) m' (tl args)
                in  if (m' = n) then ((argn'.rest),(binding @ bind))
                    if (is_var arg) then ((arg.rest),((arg,arg).bind))
                    else let var = genvar (type_of arg)
                         in  ((var.rest),((var,arg).bind))
        in if (null occ)
           then (st,[])
           else let (f,args) = strip_comb st
                and (n.occ') = occ
                in  let (argn',binding) = generalise (el n args,occ')
                in  let (args',bind) =
                           replace_side_structs (n,argn',binding) 0 args
                in  (list_mk_comb (f,args'),bind)
 in  letrec constr_apps v (st,occ) =
        letrec replace_argn (n,argn') m args =
           if (null args)
           then []
           else let m' = m + 1
                in  if (m' = n)
                    then argn'.(tl args)
                    else (hd args).(replace_argn (n,argn') m' (tl args))
        in if (null occ)
           then []
           else let (f,args) = strip_comb st
                and (n.occ') = occ
                in  let args' = replace_argn (n,v) 0 args
                in  (list_mk_comb (f,args')).(constr_apps v (el n args,occ'))
 in  let rotations l =
        letrec rotations' l n =
           if (n < 1)
           then []
           else l.(rotations' ((tl l) @ [hd l]) (n - 1))
        in rotations' l (length l)
 in  let two_constrs = ((fst o strip_comb) # (fst o strip_comb)) o
                       dest_eq o dest_neg o snd o strip_forall o concl
 in  let flip (x,y) = (y,x)
 in  let DEPTH_SYM = GEN_ALL o NOT_EQ_SYM o SPEC_ALL
 in  letrec arg_types ty =
        (let (`fun`,[argty;rest]) = dest_type ty
         in  argty.(arg_types rest))
        ? []
 in  let name_and_args = (I # arg_types) o dest_const
 in
 \(Induction,Distincts,OneOnes).
 let half_distincts = map (\th. (name # name) (two_constrs th), th) Distincts
 in  let distincts = half_distincts @ (map (flip # DEPTH_SYM) half_distincts)
 in  let ind_goals =
        (conjuncts o fst o dest_imp o snd o dest_forall o concl) Induction
 in  let constrs =
        map (name_and_args o fst o strip_comb o rand o snd o strip_forall o
             snd o strip_imp o snd o strip_forall) ind_goals
 in
 \tm.
 (let (l,r) = dest_eq (dest_neg tm)
  in  let (flipped,v,st) =
         if (is_var l)
         then if (is_var r) then fail else (false,l,r)
         else if (is_var r)
              then (true,r,l)
              else fail
  in  let occ = min_length (occurrences constrs v st)
  in  let (st',bind) = generalise (st,occ)
  in  let (vars,subterms) = split bind
  in  let apps = constr_apps v (st',occ)
  in  let rotats =
         map (end_itlist (\t1 t2. subst [(t2,v)] t1)) (rotations apps)
  in  let uneqs = map (mk_neg o (curry mk_eq v)) rotats
  in  let conj =
         mk_forall (v,list_mk_conj (map (curry list_mk_forall vars) uneqs))
  in  let th1 =
         prove (conj,INDUCT_THEN Induction ASSUME_TAC THEN
                     ASM_REWRITE_TAC (OneOnes @ (map snd distincts)))
  in  let th2 = (hd o CONJUNCTS o (SPEC v)) th1
  in  let th3 = SPECL subterms th2
  in  let th4 = if flipped then (NOT_EQ_SYM th3) else th3
  in  EQT_INTRO (CONV_RULE (C ALPHA tm) th4)
 ) ? failwith `VAR_NOT_EQ_STRUCT_OF_VAR_CONV`;;

%----------------------------------------------------------------------------%
% CONJS_CONV : conv -> conv                                                  %
%                                                                            %
% Written by T.F.Melham.                                                     %
% Modified by R.J.Boulton.                                                   %
%                                                                            %
% Apply a given conversion to a sequence of conjuncts.                       %
%                                                                            %
% * need to check T case                                                     %
% * need to flatten conjuncts on RHS                                         %
%----------------------------------------------------------------------------%

let CONJS_CONV =
   let is st th = fst(dest_const(rand(concl th))) = st ? false
   in  let v1 = genvar ":bool" and v2 = genvar ":bool"
   in  let Fthm1 = 
          let th1 = ASSUME (mk_eq(v1,"F"))
          in  let cnj = mk_conj(v1,v2)
          in  let th1 = DISCH cnj (EQ_MP th1 (CONJUNCT1 (ASSUME cnj)))
          in  let th2 = DISCH "F" (CONTR cnj (ASSUME "F"))
          in  DISCH (mk_eq(v1,"F")) (IMP_ANTISYM_RULE th1 th2)
   in  let Fthm2 = CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV CONJ_SYM)) Fthm1
   in  let Fandr th tm = MP (INST [lhs(concl th),v1;tm,v2] Fthm1) th
   in  let Fandl th tm = MP (INST [lhs(concl th),v1;tm,v2] Fthm2) th
   in  let Tthm1 = 
          let th1 = ASSUME (mk_eq(v1,"T"))
          in  let th2 = SUBS_OCCS [[2],th1] (REFL (mk_conj(v1,v2)))
          in  DISCH (mk_eq(v1,"T")) (ONCE_REWRITE_RULE [] th2)
   in  let Tthm2 = CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV CONJ_SYM)) Tthm1
   in  let Tandr th tm = MP (INST [lhs(concl th),v1;tm,v2] Tthm1) th
   in  let Tandl th tm = MP (INST [lhs(concl th),v1;tm,v2] Tthm2) th
   in  letrec cconv conv tm =
          (let (c,cs) = dest_conj tm
           in  let cth = conv c
           in  if (is `F` cth) then Fandr cth cs else
               let csth = cconv conv cs
               in  if (is `F` csth) then Fandl csth c
                   if (is `T` cth) then TRANS (Tandr cth cs) csth
                   if (is `T` csth) then TRANS (Tandl csth c) cth
                   else MK_COMB((AP_TERM "$/\" cth),csth)) ? conv tm
   in  \conv tm. cconv conv tm ? failwith `CONJS_CONV`;;

%----------------------------------------------------------------------------%
% ONE_STEP_RECTY_EQ_CONV : (thm # thm list # thm list) -> conv -> conv       %
%                                                                            %
% Single step conversion for equality between structures of a single         %
% recursive type.                                                            %
%                                                                            %
% Based on code written by T.F.Melham.                                       %
%                                                                            %
% The theorems taken as arguments are the induction, distinctness and        %
% injectivity theorems for the recursive type, as proved by the functions:   %
%                                                                            %
%    prove_induction_thm                                                     %
%    prove_constructors_distinct                                             %
%    prove_constructors_one_one                                              %
%                                                                            %
% Since the latter two functions may fail, the distinctness and injectivity  %
% theorems are passed around as lists of conjuncts.                          %
%                                                                            %
% If one side of the equation is a variable and that variable appears in the %
% other side (nested in a structure) the equation is proved false.           %
%                                                                            %
% If the top-level constructors on the two sides of the equation are         %
% distinct the equation is proved false.                                     %
%                                                                            %
% If the top-level constructors on the two sides of the equation are the     %
% same a conjunction of equations is generated, one equation for each        %
% argument of the constructor. The conversion given as argument is then      %
% applied to each conjunct. If any of the applications of this conversion    %
% fail, so will the entire call.                                             %
%                                                                            %
% In other conditions the function fails.                                    %
%----------------------------------------------------------------------------%

let ONE_STEP_RECTY_EQ_CONV =
   let GEN_REWRITES_CONV =
    let RW_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm
    in
    \(rewrite_fun:conv->conv) built_in_rewrites.
     let basic_net = mk_conv_net built_in_rewrites
     in
     \thl. rewrite_fun (RW_CONV (merge_term_nets (mk_conv_net thl) basic_net))
   in
   \(Induction,Distincts,OneOnes).
   let NOT_EQ_CONV =
          EQF_INTRO o EQT_ELIM o
          (VAR_NOT_EQ_STRUCT_OF_VAR_CONV (Induction,Distincts,OneOnes)) o
          mk_neg
   in  let INJ_REW = GEN_REWRITES_CONV I [] OneOnes
   in  let ths1 = map SPEC_ALL Distincts
   in  let ths2 = map (GEN_ALL o EQF_INTRO o NOT_EQ_SYM) ths1
   in  let dths = ths2 @ (map (GEN_ALL o EQF_INTRO) ths1)
   in  let DIST_REW = GEN_REWRITES_CONV I [] dths
   in  \conv. NOT_EQ_CONV ORELSEC
              DIST_REW ORELSEC
              (INJ_REW THENC (CONJS_CONV conv)) ORELSEC
              (\tm. failwith `ONE_STEP_RECTY_EQ_CONV`);;

%----------------------------------------------------------------------------%
% RECTY_EQ_CONV : (thm # thm list # thm list) -> conv                        %
%                                                                            %
% Function to simplify as far as possible an equation between two structures %
% of some type, the type being specified by the triple of theorems. The      %
% structures may involve variables. The result may be a conjunction of       %
% equations simpler than the original.                                       %
%----------------------------------------------------------------------------%

let RECTY_EQ_CONV (Induction,Distincts,OneOnes) =
   let one_step_conv = ONE_STEP_RECTY_EQ_CONV (Induction,Distincts,OneOnes)
   and REFL_CONV tm =
      let (l,r) = dest_eq tm
      in  if (l = r)
          then EQT_INTRO (REFL l)
          else failwith `REFL_CONV`
   in  letrec conv tm =
          (one_step_conv conv ORELSEC REFL_CONV ORELSEC ALL_CONV) tm
   in  \tm. conv tm ? failwith `RECTY_EQ_CONV`;;
