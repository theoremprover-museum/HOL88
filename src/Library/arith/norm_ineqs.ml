%****************************************************************************%
% FILE          : norm_ineqs.ml                                              %
% DESCRIPTION   : Functions for normalizing inequalities.                    %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 23rd July 1992                                             %
%****************************************************************************%

%============================================================================%
% Adding terms to inequalities                                               %
%============================================================================%

%----------------------------------------------------------------------------%
% ADD_TERM_TO_LEQ_CONV : term -> conv                                        %
%                                                                            %
% ADD_TERM_TO_LEQ_CONV "x" "a <= b" returns the theorem:                     %
%                                                                            %
%    |- (a <= b) = ((x + a) <= (x + b))                                      %
%----------------------------------------------------------------------------%

let ADD_TERM_TO_LEQ_CONV addition tm =
 (let (tm1,tm2) = dest_leq tm
  in  let tm' = mk_leq (mk_plus (addition,tm1),mk_plus (addition,tm2))
  in  SYM (LEQ_PLUS_CONV tm')
 ) ? failwith `ADD_TERM_TO_LEQ_CONV`;;

%----------------------------------------------------------------------------%
% ADD_COEFFS_TO_LEQ_QCONV : (int # (string # int) list) -> conv              %
%                                                                            %
% Adds terms to both sides of a less-than-or-equal-to inequality. The        %
% conversion avoids adding a zero constant but does not concern itself with  %
% eliminating zero terms in any other way.                                   %
%----------------------------------------------------------------------------%

let ADD_COEFFS_TO_LEQ_QCONV (const,bind) =
 letrec add_terms_qconv bind =
    if (null bind)
    then ALL_QCONV
    else let (name,coeff) = hd bind
         in  let addition = mk_mult (term_of_int coeff,mk_num_var name)
         in  ((add_terms_qconv (tl bind)) THENQC
              (ADD_TERM_TO_LEQ_CONV addition))
 in \tm.
 (((add_terms_qconv bind) THENQC
   (if (const = 0)
    then ALL_QCONV
    else ADD_TERM_TO_LEQ_CONV (term_of_int const))) tm)
 ?\s qfailwith s `ADD_COEFFS_TO_LEQ_QCONV`;;

%============================================================================%
% Normalizing inequalities                                                   %
%============================================================================%

%----------------------------------------------------------------------------%
% LESS_OR_EQ_GATHER_QCONV : conv                                             %
%                                                                            %
% Assumes that the argument term is a less-than-or-equal-to of two fully     %
% normalized arithmetic expressions. The conversion transforms such a term   %
% to a less-than-or-equal-to in which each variable occurs on only one side  %
% of the inequality, and a constant term appears on at most one side, unless %
% the whole of one side is zero.                                             %
%                                                                            %
% Here is an example result:                                                 %
%                                                                            %
%    |- (1 + ((3 * x) + (1 * z))) <= (2 + ((1 * x) + (4 * y))) =             %
%       ((2 * x) + (1 * z)) <= (1 + (4 * y))                                 %
%----------------------------------------------------------------------------%

let LESS_OR_EQ_GATHER_QCONV =
 letrec subtract_common_terms bind1 bind2 =
    if (null bind1) then ([],[],bind2)
    if (null bind2) then ([],bind1,[])
    else (let (name1,coeff1) = hd bind1
          and (name2,coeff2) = hd bind2
          in  if (name1 = name2) then
                 (let (c,b1,b2) = subtract_common_terms (tl bind1) (tl bind2)
                  in  if (coeff1 = coeff2) then ((name1,coeff1).c,b1,b2)
                      if (coeff1 < coeff2) then
                         ((name1,coeff1).c,b1,(name1,coeff2 - coeff1).b2)
                      else ((name1,coeff2).c,(name1,coeff1 - coeff2).b1,b2))
              if (string_less name1 name2) then
                 (let (c,b1,b2) = subtract_common_terms (tl bind1) bind2
                  in  (c,(name1,coeff1).b1,b2))
              else (let (c,b1,b2) = subtract_common_terms bind1 (tl bind2)
                    in  (c,b1,(name2,coeff2).b2)))
 in \tm.
 (let (tm1,tm2) = dest_leq tm
  in  let (const1,bind1) = coeffs_of_arith tm1
      and (const2,bind2) = coeffs_of_arith tm2
  in  let (bindc,bindl,bindr) = subtract_common_terms bind1 bind2
      and (constc,constl,constr) =
         if (const1 < const2)
         then (const1,0,const2 - const1)
         else (const2,const1 - const2,0)
  in  let tml = build_arith (constl,bindl)
      and tmr = build_arith (constr,bindr)
  in  SYM
       (((ADD_COEFFS_TO_LEQ_QCONV (constc,bindc)) THENQC
         (ARGS_QCONV (SORT_AND_GATHER_QCONV THENQC NORM_ZERO_AND_ONE_QCONV)))
        (mk_leq (tml,tmr)))
 ) ?\s qfailwith s `LESS_OR_EQ_GATHER_QCONV`;;

%----------------------------------------------------------------------------%
% ARITH_FORM_NORM_QCONV : conv                                               %
%                                                                            %
% Converts an arithmetic formula into a disjunction of conjunctions of       %
% less-than-or-equal-to inequalities. The arithmetic expressions are only    %
% allowed to contain variables, addition, the SUC function, and              %
% multiplication by constants. The formula is not allowed to contain         %
% quantifiers, but may have disjunction, conjunction, negation, implication, %
% equality on Booleans, and the natural number relations =, <, <=, >, >=.    %
%                                                                            %
% The inequalities in the result are normalized so that each variable        %
% appears on only one side of the inequality, and each side is a linear sum  %
% in which any constant appears first, followed by products of a constant    %
% and a variable. The variables are ordered lexicographically, and if the    %
% coefficient of the variable is 1, the product of 1 and the variable        %
% appears in the term, not simply the variable.                              %
%----------------------------------------------------------------------------%

let ARITH_FORM_NORM_QCONV tm =
 ((EQ_IMP_ELIM_QCONV is_num_reln) THENQC
  (MOVE_NOT_DOWN_QCONV is_num_reln
    (NUM_RELN_NORM_QCONV
      (SUM_OF_PRODUCTS_QCONV THENQC
       LINEAR_SUM_QCONV THENQC
       SORT_AND_GATHER_QCONV THENQC
       NORM_ZERO_AND_ONE_QCONV)
      LESS_OR_EQ_GATHER_QCONV)) THENQC
  DISJ_NORM_FORM_QCONV)
 tm ?\s qfailwith s `ARITH_FORM_NORM_QCONV`;;
