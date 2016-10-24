%****************************************************************************%
% FILE          : solve_ineqs.ml                                             %
% DESCRIPTION   : Functions for solving inequalities.                        %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 12th October 1992                                          %
%****************************************************************************%

%============================================================================%
% Multiplying normalized arithmetic expressions by a constant                %
%============================================================================%

%----------------------------------------------------------------------------%
% CONST_TIMES_ARITH_QCONV : conv                                             %
%                                                                            %
% Converts the product of a constant and a normalized arithmetic expression  %
% to a new normalized arithmetic expression.                                 %
%                                                                            %
% Example:                                                                   %
%                                                                            %
%    CONST_TIMES_ARITH_QCONV "3 * (1 + (3 * x) + (2 * y))"  --->             %
%    |- 3 * (1 + ((3 * x) + (2 * y))) = 3 + ((9 * x) + (6 * y))              %
%----------------------------------------------------------------------------%

let CONST_TIMES_ARITH_QCONV tm =
 (letrec CONST_TIMES_VARS_QCONV tm =
     if (is_mult (arg2 tm))
     then (MULT_ASSOC_CONV THENQC
           (RATOR_QCONV (RAND_QCONV FAST_MULT_CONV))) tm
     else (LEFT_ADD_DISTRIB_CONV THENQC
           (RATOR_QCONV
             (RAND_QCONV (MULT_ASSOC_CONV THENQC
                          (RATOR_QCONV (RAND_QCONV FAST_MULT_CONV))))) THENQC
           (RAND_QCONV CONST_TIMES_VARS_QCONV)) tm
  in let tm' = arg2 tm
  in if (is_const tm') then FAST_MULT_CONV tm
     if (is_mult tm') then
        (MULT_ASSOC_CONV THENQC
         (RATOR_QCONV (RAND_QCONV FAST_MULT_CONV))) tm
     if (is_const (arg1 tm')) then
        (LEFT_ADD_DISTRIB_CONV THENQC
         (RATOR_QCONV (RAND_QCONV FAST_MULT_CONV)) THENQC
         (RAND_QCONV CONST_TIMES_VARS_QCONV)) tm
     else CONST_TIMES_VARS_QCONV tm
 ) ?\s qfailwith s `CONST_TIMES_ARITH_QCONV`;;

%----------------------------------------------------------------------------%
% MULT_LEQ_BY_CONST_QCONV : term -> conv                                     %
%                                                                            %
% Multiplies both sides of a normalized inequality by a non-zero constant.   %
%                                                                            %
% Example:                                                                   %
%                                                                            %
%    MULT_LEQ_BY_CONST_QCONV "3" "(1 + (3 * x) + (2 * y)) <= (3 * z)"  --->  %
%    |- (1 + ((3 * x) + (2 * y))) <= (3 * z) =                               %
%       (3 + ((9 * x) + (6 * y))) <= (9 * z)                                 %
%----------------------------------------------------------------------------%

let MULT_LEQ_BY_CONST_QCONV constant tm =
 (let (tm1,tm2) = dest_leq tm
  and n = int_of_term constant
  in
  if (n = 0) then fail
  if (n = 1) then ALL_QCONV tm
  else let constant' = term_of_int (n - 1)
       in  let th = SYM (num_CONV constant)
       in  let th1 = SPEC constant' (SPEC tm2 (SPEC tm1 MULT_LEQ_SUC))
       in  let th2 =
              ((RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV (\_. th))))) THENC
               (RAND_CONV (RATOR_CONV (RAND_CONV (\_. th)))))
              (rhs (concl th1))
       in  ((\_. th1 TRANS th2) THENQC
            (ARGS_QCONV CONST_TIMES_ARITH_QCONV)) tm
 ) ?\s qfailwith s `MULT_LEQ_BY_CONST_QCONV`;;

%============================================================================%
% Solving inequalities between constants                                     %
%============================================================================%

%----------------------------------------------------------------------------%
% LEQ_CONV : conv                                                            %
%                                                                            %
% Given a term of the form "a <= b" where a and b are constants, returns the %
% theorem |- (a <= b) = T or the theorem |- (a <= b) = F depending on the    %
% values of a and b.                                                         %
%                                                                            %
% Optimized for when one or both of the arguments is zero.                   %
%----------------------------------------------------------------------------%

let LEQ_CONV tm =
 (let (tm1,tm2) = dest_leq tm
  in  let n1 = int_of_term tm1
      and n2 = int_of_term tm2
  in  if (n1 = 0) then SPEC tm2 ZERO_LESS_EQ_T
      if (n2 = 0) then    % n1 must be non-zero here %
         (let n1th = SYM (num_CONV tm1)
          in  let n1tm = rand (lhs (concl n1th))
              and conv = \dummytm. n1th
          in  CONV_RULE (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV conv))))
                        (SPEC n1tm SUC_LESS_EQ_ZERO_F))
      if (n2 < n1)
      then let diff1tm = term_of_int ((n1 - n2) - 1)
           and th = SYM (num_CONV tm1)
           in  let th1 = SPEC diff1tm (SPEC tm2 SUC_ADD_LESS_EQ_F)
           in  CONV_RULE
                (RATOR_CONV
                  (RAND_CONV
                    (RATOR_CONV
                      (RAND_CONV ((RAND_CONV ADD_CONV) THENC (\_. th)))))) th1
      else let difftm = term_of_int (n2 - n1)
           in  EQT_INTRO (CONV_RULE (RAND_CONV ADD_CONV)
                             (SPEC difftm (SPEC tm1 LESS_EQ_PLUS)))
 ) ? failwith `LEQ_CONV`;;

%============================================================================%
% Eliminating variables from sets of inequalities                            %
%============================================================================%

%----------------------------------------------------------------------------%
% WEIGHTED_SUM :                                                             %
%    string ->                                                               %
%    ((int # (string # int) list) # int # (string # int) list) ->            %
%    ((int # (string # int) list) # (void -> thm))                           %
%                                                                            %
% Function to eliminate a specified variable from two inequalities by        %
% forming their weighted sum. The inequalities must be given as bindings.    %
% The result is a pair. The first component is a binding representing the    %
% combined inequality, and the second component is a function. When applied  %
% to ():void this function returns a theorem which states that under the     %
% assumption that the two original inequalities are true, then the resultant %
% inequality is true.                                                        %
%                                                                            %
% The variable to be eliminated should be on the right-hand side of the      %
% first inequality, and on the left-hand side of the second.                 %
%                                                                            %
% Example:                                                                   %
%                                                                            %
%    WEIGHTED_SUM `y` ((1,[(`x`, -3);(`y`, 1)]), (3,[(`x`, -3);(`y`, -1)]))  %
%    --->                                                                    %
%    ((4, [(`x`, -6)]), -)                                                   %
%                                                                            %
%    snd it ()  --->                                                         %
%    (3 * x) <= (1 + (1 * y)), ((3 * x) + (1 * y)) <= 3 |- (6 * x) <= 4      %
%----------------------------------------------------------------------------%

let WEIGHTED_SUM name (coeffs1,coeffs2) =
 (let coeff1 = snd (assoc name (snd coeffs1))
  and coeff2 = 0 - (snd (assoc name (snd coeffs2)))
  in  let mult = lcm (coeff1,coeff2)
  in  let mult1 = mult / coeff1
      and mult2 = mult / coeff2
  in  let coeffs1' = ((\n. n * mult1) # (map (\(s,n). (s,n * mult1)))) coeffs1
      and coeffs2' = ((\n. n * mult2) # (map (\(s,n). (s,n * mult2)))) coeffs2
  in  let (adds1,adds2) = diff_of_coeffs (coeffs1',coeffs2')
  in  let coeffs1'' = merge_coeffs adds1 (lhs_coeffs coeffs1')
      and coeffs2'' = merge_coeffs adds2 (rhs_coeffs coeffs2')
  in  let new_coeffs = merge_coeffs (negate_coeffs coeffs1'') coeffs2''
  in  let thf (():void) =
         let th1 =
            QCONV
            ((if (mult1 = 1)
              then ALL_QCONV
              else MULT_LEQ_BY_CONST_QCONV (term_of_int mult1)) THENQC
             (if (adds1 = (0,[]))
              then ALL_QCONV
              else (ADD_COEFFS_TO_LEQ_QCONV adds1) THENQC
                   (RAND_QCONV
                     (SORT_AND_GATHER_QCONV THENQC NORM_ZERO_AND_ONE_QCONV))))
            (build_leq coeffs1)
         and th2 =
            QCONV
            ((if (mult2 = 1)
              then ALL_QCONV
              else MULT_LEQ_BY_CONST_QCONV (term_of_int mult2)) THENQC
             (if (adds2 = (0,[]))
              then ALL_QCONV
              else (ADD_COEFFS_TO_LEQ_QCONV adds2) THENQC
                   (RATOR_QCONV
                     (RAND_QCONV (SORT_AND_GATHER_QCONV THENQC
                                  NORM_ZERO_AND_ONE_QCONV)))))
            (build_leq coeffs2)
         in  let th = CONJ (UNDISCH (fst (EQ_IMP_RULE th1)))
                           (UNDISCH (fst (EQ_IMP_RULE th2)))
         in  let th1conv =
                if (adds1 = (0,[]))
                then ALL_QCONV
                else RATOR_QCONV
                      (RAND_QCONV
                        (SORT_AND_GATHER_QCONV THENQC NORM_ZERO_AND_ONE_QCONV))
             and th2conv =
                if (adds2 = (0,[]))
                then ALL_QCONV
                else RAND_QCONV
                      (SORT_AND_GATHER_QCONV THENQC NORM_ZERO_AND_ONE_QCONV)
         in  QCONV_RULE (th1conv THENQC th2conv THENQC LESS_OR_EQ_GATHER_QCONV)
                        (MATCH_MP LESS_EQ_TRANSIT th)
  in  (new_coeffs,thf)
 ) ? failwith `WEIGHTED_SUM`;;

%----------------------------------------------------------------------------%
% var_to_elim : (* # (string # int) list) list -> string                     %
%                                                                            %
% Given a list of inequalities (as bindings), this function determines which %
% variable to eliminate. Such a variable must occur in two inequalites on    %
% different sides. The variable chosen is the one that gives rise to the     %
% least number of pairings.                                                  %
%----------------------------------------------------------------------------%

let var_to_elim coeffsl =
 (letrec var_to_elim' bind =
     if (null bind)
     then ([],[])
     else let (name,coeff) = hd bind
          and (occsl,occsr) = var_to_elim' (tl bind)
          in  if (coeff < 0) then ((name,1).occsl,occsr)
              if (coeff > 0) then (occsl,(name,1).occsr)
              else (occsl,occsr)
  and min_increase bind1 bind2 =
     let (name1,num1) = hd bind1
     and (name2,num2) = hd bind2
     in  if (name1 = name2)
         then (let increase = (num1 * num2) - (num1 + num2)
               in  (let (name,min) = min_increase (tl bind1) (tl bind2)
                    in  if (min < increase)
                        then (name,min)
                        else (name1,increase))
                ?  (name1,increase)
              )
         if (string_less name1 name2)
         then min_increase (tl bind1) bind2
         else min_increase bind1 (tl bind2)
  in  let merge = end_itlist (\b1 b2. snd (merge_coeffs (0,b1) (0,b2)))
  in  let occs = map (var_to_elim' o snd) coeffsl
  in  let (occsl,occsr) = (merge # merge) (split occs)
  in  fst (min_increase occsl occsr)
 ) ? failwith `var_to_elim`;;

%----------------------------------------------------------------------------%
% VAR_ELIM : (int # (string # int) list) list -> (int list # (void -> thm))  %
%                                                                            %
% Given a list of inequalities represented by bindings, this function        %
% returns a `lazy' theorem with false (actually an inequality between        %
% constants that can immediately be shown to be false) as its conclusion,    %
% and some of the inequalities as assumptions. A list of numbers is also     %
% returned. These are the positions in the argument list of the inequalities %
% that are assumptions of the theorem. The function fails if the set of      %
% inequalities is satisfiable.                                               %
%                                                                            %
% The function assumes that none of the inequalities given are false, that   %
% is they either contain variables, or evaluate to true. Those that are true %
% are filtered out. The function then determines which variable to eliminate %
% and splits the remaining inequalities into three sets: ones in which the   %
% variable occurs on the left-hand side, ones in which the variable occurs   %
% on the right, and ones in which the variable does not occur.               %
%                                                                            %
% Pairings of the `right' and `left' inequalities are then made, and the     %
% weighted sum of each is determined, except that as soon as a pairing       %
% yields false, the process is terminated. It may well be the case that no   %
% pairing gives false. In this case, the new inequalities are added to the   %
% inequalities that did not contain the variable, and a recursive call is    %
% made.                                                                      %
%                                                                            %
% The list of numbers from the recursive call (representing assumptions) is  %
% split into two: those that point to inequalities that were produced by     %
% doing weighted sums, and those that were not. The latter can be traced     %
% back so that their positions in the original argument list can be          %
% returned. The other inequalities have to be discharged from the theorem    %
% using the theorems proved by performing weighted sums. Each assumption     %
% thus gives rise to two new assumptions and the conclusion remains false.   %
% The positions of the two new assumptions in the original argument list are %
% added to the list to be returned. Duplicates are removed from this list    %
% before returning it.                                                       %
%----------------------------------------------------------------------------%

letrec VAR_ELIM coeffsl =
 letrec upto from to =
    if (from > to)
    then []
    else from.(upto (from + 1) to)
 and left_ineqs var icoeffsl =
    let left_ineq icoeffs =
       not (null (filter (\(name,coeff). (name = var) & (coeff < 0))
                         (snd (snd icoeffs))))
    in  filter left_ineq icoeffsl
 and right_ineqs var icoeffsl =
    let right_ineq icoeffs =
       not (null (filter (\(name,coeff). (name = var) & (coeff > 0))
                         (snd (snd icoeffs))))
    in  filter right_ineq icoeffsl
 and no_var_ineqs var icoeffsl =
    let no_var_ineq icoeffs =
       null (filter (\(name,coeff). (name = var) & (not (coeff = 0)))
                    (snd (snd icoeffs)))
    in  filter no_var_ineq icoeffsl
 and pair_ineqs (ricoeffs,licoeffs) =
    letrec pair (ricoeffs,licoeffs) =
       if (null ricoeffs)
       then []
       else (map (\l. (hd ricoeffs,l)) licoeffs).(pair (tl ricoeffs,licoeffs))
    in flat (pair (ricoeffs,licoeffs))
 and weighted_sums var pairs =
    if (null pairs)
    then (false,[])
    else let (success,rest) = weighted_sums var (tl pairs)
         in  if success
             then (success,rest)
             else let ((lindex,lcoeffs),(rindex,rcoeffs)) = hd pairs
                  in  let ((const,bind),f) = WEIGHTED_SUM var (lcoeffs,rcoeffs)
                  in  if ((null bind) & (const < 0))
                      then (true,[(lindex,rindex),(const,bind),f])
                      else (false,((lindex,rindex),(const,bind),f).rest)
 and chain_assums ineqs thf indexl =
    if (null indexl)
    then ([],thf)
    else let (prev_indexl,thf') = chain_assums ineqs thf (tl indexl)
         and ((lindex,rindex),coeffs,f) = el (hd indexl) ineqs
         in  (lindex.rindex.prev_indexl,\(). PROVE_HYP (f ()) (thf' ()))
 in
 (let icoeffsl = combine (upto 1 (length coeffsl),coeffsl)
  in  let icoeffsl' = filter (\(i,const,bind). not (null bind)) icoeffsl
  in  let var = var_to_elim (map snd icoeffsl')
  in  let ricoeffs = right_ineqs var icoeffsl'
      and licoeffs = left_ineqs var icoeffsl'
      and nicoeffs = no_var_ineqs var icoeffsl'
  in  let pairs = pair_ineqs (ricoeffs,licoeffs)
  in  let (success,new_ineqs) = weighted_sums var pairs
  in  if success
      then let [((lindex,rindex),coeffs,thf)] = new_ineqs
           in  ([lindex;rindex],thf)
      else let n = length new_ineqs
           and new_coeffs = (map (fst o snd) new_ineqs) @ (map snd nicoeffs)
           in  let (indexl,thf) = VAR_ELIM new_coeffs
           in  let (prev_indexl,these_indexl) = partition (\i. i > n) indexl
           in  let prev_indexl' =
                  map (\i. fst (el (i - n) nicoeffs)) prev_indexl
           in  let (these_indexl',thf') =
                  chain_assums new_ineqs thf these_indexl
           in  (setify (these_indexl' @ prev_indexl'),thf')
 ) ? failwith `VAR_ELIM`;;
