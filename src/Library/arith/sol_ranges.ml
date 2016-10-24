%****************************************************************************%
% FILE          : sol_ranges.ml                                              %
% DESCRIPTION   : Functions for determining the ranges of the solutions to   %
%                 linear programming problems, and whether there are natural %
%                 number solutions.                                          %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 18th April 1991                                            %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 1st July 1992                                              %
%****************************************************************************%

%----------------------------------------------------------------------------%
% less_bound : bound -> bound -> bool                                        %
%----------------------------------------------------------------------------%

let less_bound b1 b2 =
   (case (b1,b2)
    of (Neg_inf,Neg_inf) . fail
     | (Neg_inf,Bound (_,[])) . true
     | (Neg_inf,Pos_inf) . true
     | (Bound (_,[]),Neg_inf) . false
     | (Bound (r1,[]),Bound (r2,[])) . (rat_less r1 r2)
     | (Bound (_,[]),Pos_inf) . true
     | (Pos_inf,Neg_inf) . false
     | (Pos_inf,Bound (_,[])) . false
     | (Pos_inf,Pos_inf) . fail
   ) ? failwith `less_bound`;;

%----------------------------------------------------------------------------%
% is_neg_bound : bound -> bool                                               %
%----------------------------------------------------------------------------%

let is_neg_bound b =
   (case b
    of (Bound (r,[])) . (rat_less r rat_zero)
     | Pos_inf . false
     | Neg_inf . true
   ) ? failwith `is_neg_bound`;;

%----------------------------------------------------------------------------%
% is_finite_bound : bound -> bool                                            %
%----------------------------------------------------------------------------%

let is_finite_bound b =
   (case b
    of (Bound (_,[])) . true
     | Pos_inf . false
     | Neg_inf . false
   ) ? failwith `is_finite_bound`;;

%----------------------------------------------------------------------------%
% rat_of_bound : bound -> rat                                                %
%----------------------------------------------------------------------------%

let rat_of_bound b =
   (case b
    of (Bound (r,[])) . r
   ) ? failwith `rat_of_bound`;;

%----------------------------------------------------------------------------%
% is_int_range : rat -> rat -> bool                                          %
%----------------------------------------------------------------------------%

let is_int_range r1 r2 =
   let i1 = upper_int_of_rat r1
   and i2 = lower_int_of_rat r2
   in  not (i2 < i1);;

%----------------------------------------------------------------------------%
% non_neg_int_between : bound -> bound -> int                                %
%----------------------------------------------------------------------------%

let non_neg_int_between b1 b2 =
   (case (b1,b2)
    of (Neg_inf,Neg_inf) . fail
     | (Neg_inf,Bound (r,[])) . (if (rat_less r rat_zero) then fail else 0)
     | (Neg_inf,Pos_inf) . 0
     | (Bound (_,[]),Neg_inf) . fail
     | (Bound (r1,[]),Bound (r2,[])) .
          (let i1 = upper_int_of_rat r1
           and i2 = lower_int_of_rat r2
           in  let i1' = if (i1 < 0) then 0 else i1
           in  if (i2 < i1') then fail else i1')
     | (Bound (r,[]),Pos_inf) .
          (if (rat_less r rat_zero) then 0 else upper_int_of_rat r)
     | (Pos_inf,Neg_inf) . fail
     | (Pos_inf,Bound (_,[])) . fail
     | (Pos_inf,Pos_inf) . fail
   ) ? failwith `non_neg_int_between`;;

%----------------------------------------------------------------------------%
% inst_var_in_coeffs : (string # int) ->                                     %
%                      (int # (string # int) list) list ->                   %
%                      (int # (string # int) list) list                      %
%                                                                            %
% Substitute a constant for a variable in a set of coefficients.             %
%----------------------------------------------------------------------------%

letrec inst_var_in_coeffs (v:string,c) coeffsl =
   if (null coeffsl)
   then []
   else let (const,bind) = hd coeffsl
        in  let ((_,coeff),bind') =
               (remove (\(name,_). name = v) bind ? ((v,0),bind))
        in  (const + (c * coeff),bind').
               (inst_var_in_coeffs (v,c) (tl coeffsl));;

%----------------------------------------------------------------------------%
% Shostak : (int # (string # int) list) list -> (string # int) list          %
%                                                                            %
% Uses SUP-INF in the way described by Shostak to find satisfying values     %
% (natural numbers) for the variables in a set of inequalities (represented  %
% as bindings). The function fails if it can't find such values.             %
%                                                                            %
% The function tries permutations of the variables, because the ordering can %
% affect whether or not satisfying values are found. Lazy evaluation is used %
% to avoid computing all the permutations before they are required. This     %
% should help to avoid problems due to enormously long lists, but even so,   %
% for a large number of variables, the function could execute for a very     %
% long time.                                                                 %
%----------------------------------------------------------------------------%

let Shostak coeffsl =
   let vars_of_coeffs coeffsl = setify (flat (map ((map fst) o snd) coeffsl))
   in
   letrec Shostak' coeffsl vars =
      let no_vars = filter (null o snd) coeffsl
      in  let falses = filter (\(n,_). n < 0) no_vars
      in  if (null falses)
          then if (null vars)
               then []
               else let coeffsl' = filter (\(n,l). not (null l)) coeffsl
                    in  let var = hd vars
                    in  let b = Bound (rat_zero,[var,rat_one])
                    in  let sup = eval_bound (SIMP (SUP coeffsl' (b,[])))
                        and inf = eval_bound (SIMP (INF coeffsl' (b,[])))
                    in  let val = non_neg_int_between inf sup
                    in  let new_coeffsl = inst_var_in_coeffs (var,val) coeffsl'
                    in  (var,val).(Shostak' new_coeffsl (tl vars))
          else fail
   and try f s = case s () of (Stream (x,s')) . (f x ? try f s')
   in  let vars = vars_of_coeffs coeffsl
   in  (if (null vars)
        then Shostak' coeffsl []
        else try (Shostak' coeffsl) (permutations vars))
    ?  failwith `Shostak`;;
