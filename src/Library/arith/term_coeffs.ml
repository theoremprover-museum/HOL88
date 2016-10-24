%****************************************************************************%
% FILE          : term_coeffs.ml                                             %
% DESCRIPTION   : Functions for converting between arithmetic terms and      %
%                 their representation as bindings of variable names to      %
%                 coefficients.                                              %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 24th June 1992                                             %
%****************************************************************************%

%============================================================================%
% Manipulating coefficient representations of arithmetic expressions         %
%============================================================================%

%----------------------------------------------------------------------------%
% negate_coeffs : (int # (* # int) list) -> (int # (* # int) list)           %
%                                                                            %
% Negates constant value and coefficients of variables in a binding.         %
%----------------------------------------------------------------------------%

let negate_coeffs = ((\n. 0 - n) # (map (I # (\n. 0 - n))));;

%----------------------------------------------------------------------------%
% merge_coeffs : (int # (string # int) list) ->                              %
%                (int # (string # int) list) ->                              %
%                (int # (string # int) list)                                 %
%                                                                            %
% Sums constant values and merges bindings by adding coefficients of any     %
% variable that appears in both bindings. If the sum of the coefficients is  %
% zero, the variable concerned is not entered in the new binding.            %
%----------------------------------------------------------------------------%

let merge_coeffs coeffs1 coeffs2 =
   letrec merge bind1 bind2 =
      if (null bind1) then bind2
      if (null bind2) then bind1
      else (let (name1,coeff1) = hd bind1
            and (name2,coeff2) = hd bind2
            in  if (name1 = name2) then
                   (if ((coeff1 + coeff2) = 0)
                    then merge (tl bind1) (tl bind2)
                    else (name1,(coeff1 + coeff2)).
                            (merge (tl bind1) (tl bind2)))
                if (string_less name1 name2)
                then (name1,coeff1).(merge (tl bind1) bind2)
                else (name2,coeff2).(merge bind1 (tl bind2)))
   in let (const1,bind1) = coeffs1
      and (const2,bind2) = coeffs2
      in  ((const1 + const2),merge bind1 bind2);;

%----------------------------------------------------------------------------%
% lhs_coeffs : (int # (* # int) list) -> (int # (* # int) list)              %
%                                                                            %
% Extract strictly negative coefficients and negate them.                    %
%----------------------------------------------------------------------------%

let lhs_coeffs =
   let f n = if (n < 0) then (0 - n) else 0
   in  let g (s,n) = if (n < 0) then (s,(0 - n)) else fail
   in  (f # (mapfilter g));;

%----------------------------------------------------------------------------%
% rhs_coeffs : (int # (* # int) list) -> (int # (* # int) list)              %
%                                                                            %
% Extract strictly positive coefficients.                                    %
%----------------------------------------------------------------------------%

let rhs_coeffs =
   let f n = if (n > 0) then n else 0
   in  (f # (filter (\(_,n). n > 0)));;

%----------------------------------------------------------------------------%
% diff_of_coeffs :                                                           %
%    ((int # (string # int) list) # int # (string # int) list) ->            %
%    ((int # (string # int) list) # int # (string # int) list)               %
%                                                                            %
% Given the coefficients representing two inequalities, this function        %
% computes the terms (as coefficients) that have to be added to each in      %
% order to make the right-hand side of the first equal to the left-hand side %
% of the second.                                                             %
%----------------------------------------------------------------------------%

let diff_of_coeffs (coeffs1,coeffs2) =
   let coeffs1' = rhs_coeffs coeffs1
   and coeffs2' = lhs_coeffs coeffs2
   in  let coeffs = merge_coeffs (negate_coeffs coeffs1') coeffs2'
   in  (rhs_coeffs coeffs,lhs_coeffs coeffs);;

%----------------------------------------------------------------------------%
% vars_of_coeffs : (* # (** # ***) list) list -> ** list                     %
%                                                                            %
% Obtain a list of variable names from a set of coefficient lists.           %
%----------------------------------------------------------------------------%

let vars_of_coeffs coeffsl = setify (flat (map ((map fst) o snd) coeffsl));;

%============================================================================%
% Extracting coefficients and variable names from normalized terms           %
%============================================================================%

%----------------------------------------------------------------------------%
% var_of_prod : term -> string                                               %
%                                                                            %
% Returns variable name from terms of the form "var" and "const * var".      %
%----------------------------------------------------------------------------%

let var_of_prod tm =
 (fst (dest_var tm)) ?
 (fst (dest_var (rand tm))) ?
 failwith `var_of_prod`;;

%----------------------------------------------------------------------------%
% coeffs_of_arith : term -> (int # (string # int) list)                      %
%                                                                            %
% Takes an arithmetic term that has been sorted and returns the constant     %
% value and a binding of variable names to their coefficients, e.g.          %
%                                                                            %
%    coeffs_of_arith "1 + (4 * x) + (10 * y)"  --->                          %
%    (1, [(`x`, 4); (`y`, 10)])                                              %
%                                                                            %
% Assumes that there are no zero coefficients in the argument term. The      %
% function also assumes that when a variable has a coefficient of one, it    %
% appears in the term as (for example) "1 * x" rather than as "x".           %
%----------------------------------------------------------------------------%

let coeffs_of_arith tm =
   let coeff tm = (int_of_term o rand o rator) tm
   in  letrec coeffs tm =
          (let (prod,rest) = dest_plus tm
           in  (var_of_prod prod,coeff prod).(coeffs rest)) ?
          [var_of_prod tm,coeff tm]
   in  (let (const,rest) = dest_plus tm
        in  (int_of_term const,coeffs rest))
       ? (int_of_term tm,[])
       ? (0,coeffs tm)
       ? failwith `coeffs_of_arith`;;

%----------------------------------------------------------------------------%
% coeffs_of_leq : term -> (int # (string # int) list)                        %
%                                                                            %
% Takes a less-than-or-equal-to inequality between two arithmetic terms that %
% have been sorted and returns the constant value and a binding of variable  %
% names to their coefficients for the equivalent term with zero on the LHS   %
% of the inequality, e.g.                                                    %
%                                                                            %
%    coeffs_of_leq "((1 * x) + (1 * z)) <= (1 + (4 * x) + (10 * y))"  --->   %
%    (1, [(`x`, 3); (`y`, 10); (`z`, -1)])                                   %
%                                                                            %
% Assumes that there are no zero coefficients in the argument term. The      %
% function also assumes that when a variable has a coefficient of one, it    %
% appears in the term as (for example) "1 * x" rather than as "x".           %
%----------------------------------------------------------------------------%

let coeffs_of_leq tm =
   (let (tm1,tm2) = dest_leq tm
    in  let coeffs1 = negate_coeffs (coeffs_of_arith tm1)
        and coeffs2 = coeffs_of_arith tm2
    in  merge_coeffs coeffs1 coeffs2
   ) ? failwith `coeffs_of_leq`;;

%----------------------------------------------------------------------------%
% coeffs_of_leq_set = term -> (int # (string # int) list) list               %
%                                                                            %
% Obtains coefficients from a set of normalised inequalities.                %
% See comments for coeffs_of_leq.                                            %
%----------------------------------------------------------------------------%

let coeffs_of_leq_set tm =
 map coeffs_of_leq (conjuncts tm) ? failwith `coeffs_of_leq_set`;;

%============================================================================%
% Constructing terms from coefficients and variable names                    %
%============================================================================%

%----------------------------------------------------------------------------%
% build_arith : int # (string # int) list -> term                            %
%                                                                            %
% Takes an integer and a binding of variable names and coefficients, and     %
% returns a linear sum (as a term) with the constant at the head. Terms with %
% a coefficient of zero are eliminated, as is a zero constant. Terms with a  %
% coefficient of one are not simplified.                                     %
%                                                                            %
% Examples:                                                                  %
%                                                                            %
%    (3,[(`x`,2);(`y`,1)]) ---> "3 + (2 * x) + (1 * y)"                      %
%    (3,[(`x`,2);(`y`,0)]) ---> "3 + (2 * x)"                                %
%    (0,[(`x`,2);(`y`,1)]) ---> "(2 * x) + (1 * y)"                          %
%    (0,[(`x`,0);(`y`,0)]) ---> "0"                                          %
%----------------------------------------------------------------------------%

let build_arith (const,bind) =
   letrec build bind =
      if (null bind)
      then "0"
      else let (name,coeff) = hd bind
           and rest = build (tl bind)
           in  if (coeff = 0)
               then rest
               else let prod = mk_mult (term_of_int coeff,mk_num_var name)
                    in  if (rest = "0")
                        then prod
                        else mk_plus (prod,rest)
   in (let c = term_of_int const
       and rest = build bind
       in  if (rest = "0") then c
           if (const = 0) then rest
           else mk_plus (c,rest)
      ) ? failwith `build_arith`;;

%----------------------------------------------------------------------------%
% build_leq : (int # (string # int) list) -> term                            %
%                                                                            %
% Constructs a less-than-or-equal-to inequality from a constant and          %
% a binding of variable names to coefficients.                               %
% See comments for build_arith.                                              %
%----------------------------------------------------------------------------%

let build_leq coeffs =
   mk_leq (build_arith (lhs_coeffs coeffs),build_arith (rhs_coeffs coeffs));;
