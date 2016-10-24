%****************************************************************************%
% FILE          : induction.ml                                               %
% DESCRIPTION   : Induction.                                                 %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 26th June 1991                                             %
%                                                                            %
% LAST MODIFIED :                                                            %
% DATE          :                                                            %
%****************************************************************************%

%----------------------------------------------------------------------------%
% is_rec_const_app : term -> bool                                            %
%                                                                            %
% This function returns true if the term it is given is an application of a  %
% currently known recursive function constant.                               %
%----------------------------------------------------------------------------%

let is_rec_const_app tm =
 (let (f,args) = strip_comb tm
  in  let (n,defs) = (snd o get_def o fst o dest_const) f
  in  (n > 0) &
      ((length o snd o strip_comb o lhs o concl o snd o hd) defs = length args)
 ) ? false;;

%----------------------------------------------------------------------------%
% remove_el : int -> * list -> (* # * list)                                  %
%                                                                            %
% Removes a specified (by numerical position) element from a list.           %
%----------------------------------------------------------------------------%

letrec remove_el n l =
   if ((null l) or (n < 1))
   then failwith `remove_el`
   else if (n = 1)
        then (hd l,tl l)
        else let (x,l') = remove_el (n - 1) (tl l)
             in  (x,(hd l).l');;

%----------------------------------------------------------------------------%
% possible_inductions : term -> (term list # term list)                      %
%                                                                            %
% Function to compute two lists of variables on which induction could be     %
% performed. The first list of variables for which the induction is unflawed %
% and the second is of variables for which the induction is flawed.          %
%                                                                            %
% From a list of applications of recursive functions, the arguments are      %
% split into those that are in a recursive argument position and those that  %
% are not. Possible inductions are on the variables in the recursive         %
% argument positions, but if the variable also appears in a non-recursive    %
% argument position then the induction is flawed.                            %
%----------------------------------------------------------------------------%

let possible_inductions tm =
   let apps = find_bm_terms is_rec_const_app tm
   in  let (rec_args,other_args) =
          split (map (\app. let (f,args) = strip_comb app
                            in  let name = fst (dest_const f)
                            in  let n = (fst o snd o get_def) name
                            in  remove_el n args) apps)
   in  let vars = setify (filter is_var rec_args)
   in  let others = setify (flat other_args)
   in  partition (\v. not (mem v others)) vars;;

%----------------------------------------------------------------------------%
% DEPTH_FORALL_CONV : conv -> conv                                           %
%                                                                            %
% Given a term of the form "!x1 ... xn. t", this function applies the        %
% argument conversion to "t".                                                %
%----------------------------------------------------------------------------%

letrec DEPTH_FORALL_CONV conv tm =
   if (is_forall tm)
   then RAND_CONV (ABS_CONV (DEPTH_FORALL_CONV conv)) tm
   else conv tm;;

%----------------------------------------------------------------------------%
% induction_heuristic : (term # bool) -> ((term # bool) list # proof)        %
%                                                                            %
% Heuristic for induction. It performs one of the possible unflawed          %
% inductions on a clause, or failing that, one of the flawed inductions.     %
% The heuristic fails if no inductions are possible.                         %
%                                                                            %
% Having obtained a variable on which to perform induction, the function     %
% computes the name of the top-level type constructor in the type of the     %
% variable. The appropriate induction theorem is then obtained from the      %
% shell environment. The theorem is specialised for the argument clause and  %
% beta-reduction is performed at the appropriate places.                     %
%                                                                            %
% The resulting theorem will be of the form:                                 %
%                                                                            %
%    |- (case1 /\ ... /\ casen) ==> (!x. f[x])                          (*)  %
%                                                                            %
% So, if we can establish casei for each i, we shall have |- !x. f[x]. When  %
% specialised with the induction variable, this theorem has the original     %
% clause as its conclusion. Each casei is of one of these forms:             %
%                                                                            %
%    !x1 ... xn. s ==> (!y1 ... ym. t)                                       %
%    !x1 ... xn. t                                                           %
%                                                                            %
% where the yi's do not appear in s. We simplify the casei's that have the   %
% first form by proving theorems like:                                       %
%                                                                            %
%    |- (!x1 ... xn. s ==> (!y1 ... ym. t)) =                                %
%       (!x1 ... xn y1 ... ym. s ==> t)                                      %
%                                                                            %
% For consistency, theorems of the form |- (!x1 ... xn. t) = (!x1 ... xn. t) %
% are proved for the casei's that have the second form. The bodies of the    %
% right-hand sides of these equations are returned as the new goal clauses.  %
% A body that is an implication is taken to be an inductive step and so is   %
% returned paired with true. Bodies that are not implications are paired     %
% with false.                                                                %
%                                                                            %
% The proof of the original clause from these new clauses proceeds as        %
% follows. The universal quantifications that were stripped from the         %
% right-hand sides are restored by generalizing the theorems. From the       %
% equations we can then obtain theorems for the left-hand sides. These are   %
% conjoined and used to satisfy the antecedant of the theorem (*). As        %
% described above, specialising the resulting theorem gives a theorem for    %
% the original clause.                                                       %
%----------------------------------------------------------------------------%

let induction_heuristic (tm,(ind:bool)) =
 (let (unflawed,flawed) = possible_inductions tm
  in  let var = (hd unflawed) ? (hd flawed)
  in  let ty_name = fst (dest_type (type_of var))
  in  let induct_thm = shell_induct (sys_shell_info ty_name)
  in  let P = mk_abs (var,tm)
  in  let th1 = ISPEC P induct_thm
  in  let th2 =
         CONV_RULE
            (ONCE_DEPTH_CONV
                (\tm. if (rator tm = P) then BETA_CONV tm else fail)) th1
  in  let new_goals = conj_list (rand (rator (concl th2)))
  in  let ths =
         map (REPEATC (DEPTH_FORALL_CONV RIGHT_IMP_FORALL_CONV)) new_goals
  in  let (varsl,tml) = split (map (strip_forall o rhs o concl) ths)
  in  let proof thl =
         let thl' = map (uncurry GENL) (combine (varsl,thl))
         in  let thl'' = map (\(eq,th). EQ_MP (SYM eq) th) (combine (ths,thl'))
         in  SPEC var (MP th2 (LIST_CONJ thl''))
  in  (map (\tm. (tm,((is_imp tm) & (not (is_neg tm))))) tml,
       apply_proof proof tml)
 ) ? failwith `induction_heuristic`;;
