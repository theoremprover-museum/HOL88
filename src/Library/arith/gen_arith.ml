%****************************************************************************%
% FILE          : gen_arith.ml                                               %
% DESCRIPTION   : Generalised arithmetic proof procedure.                    %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 30th January 1992                                          %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 2nd July 1992                                              %
%****************************************************************************%

%----------------------------------------------------------------------------%
% contains_var : term -> bool                                                %
%                                                                            %
% Returns true if an expression possibly involving SUC, +, *, numeric        %
% constants and variables does contain a variable. Also returns true if any  %
% subterm does not conform to this specification of expressions.             %
%                                                                            %
% The internal function uses failure to denote that the expression evaluates %
% to zero. This is used because, when normalised, zero multiplied by an      %
% expression is zero and hence any variables in the expression can be        %
% ignored.                                                                   %
%----------------------------------------------------------------------------%

let contains_var tm =
   letrec contains_var' tm =
      if (is_var tm) then true
      if (is_const tm) then
         (if (is_zero tm) then fail else not (is_num_const tm))
      if (is_suc tm) then (contains_var' (rand tm) ? false)
      if (is_plus tm) then
         ((let b = contains_var' (arg1 tm)
           in  b or (contains_var' (arg2 tm) ? false))
         ? contains_var' (arg2 tm)
         )
      if (is_mult tm) then
         ((contains_var' (arg1 tm)) or (contains_var' (arg2 tm)))
      else true
   in contains_var' tm ? false;;

%----------------------------------------------------------------------------%
% is_linear_mult : term -> bool                                              %
%                                                                            %
% Returns true if the term is a linear multiplication, i.e. at least one of  %
% the arguments is a constant expression. Fails if the term is not a         %
% multiplication.                                                            %
%----------------------------------------------------------------------------%

let is_linear_mult tm =
 (let (l,r) = dest_mult tm
  in  if (contains_var l) then (not (contains_var r)) else true
 ) ? failwith `is_linear_mult`;;

%----------------------------------------------------------------------------%
% non_presburger_subterms : term -> term list                                %
%                                                                            %
% Computes the subterms of a term that are not in the Presburger subset of   %
% arithmetic. All variables are included.                                    %
%                                                                            %
% The function detects multiplications in which both of the arguments are    %
% non-constant expressions and returns the multiplication in the list of     %
% non-presburger terms. This allows a formula such as:                       %
%                                                                            %
%    m < (n * p) /\ (n * p) < q ==> m < q                                    %
%                                                                            %
% to be proved by the arithmetic procedure.                                  %
%----------------------------------------------------------------------------%

letrec non_presburger_subterms tm =
   (non_presburger_subterms (snd (dest_forall tm))) ?
   (non_presburger_subterms (snd (dest_exists tm))) ?
   (non_presburger_subterms (dest_neg tm)) ?
   (non_presburger_subterms (dest_suc tm)) ?
   (if (is_conj tm) or (is_disj tm) or (is_imp tm) or
       (is_eq tm) or
       (is_less tm) or (is_leq tm) or (is_great tm) or (is_geq tm) or
       (is_plus tm) or (is_minus tm) or (is_linear_mult tm ? false)
    then union (non_presburger_subterms (arg1 tm))
               (non_presburger_subterms (arg2 tm))
    if (is_num_const tm) then []
    else [tm]);;

%----------------------------------------------------------------------------%
% is_presburger : term -> bool                                               %
%                                                                            %
% Returns true if the term is a fomula in the Presburger subset of natural   %
% number arithmetic.                                                         %
%----------------------------------------------------------------------------%

let is_presburger = (forall is_var) o non_presburger_subterms;;

%----------------------------------------------------------------------------%
% ARITH_CONV : conv                                                          %
%                                                                            %
% Proof procedure for purely universal and purely existential Presburger     %
% natural arithmetic (only one kind of quantifier allowed when in prenex     %
% normal form, i.e., only `forall' or only `exists', not a mixture).         %
%                                                                            %
% The subset consists of +, * by a constant, numeric constants, numeric      %
% variables, <, <=, =, >=, >, ~, /\, \/, ==>, = (iff).                       %
% Subtraction and conditionals are allowed.                                  %
% SUC is allowed.                                                            %
% Boolean variables are not allowed.                                         %
% Existential formulae must have all variables quantified because any free   %
% variables will be taken as universally quantified which violates the       %
% constraint that mixed quantifiers are not allowed.                         %
% Substitution instances of universal formulae are also allowed.             %
%                                                                            %
% The procedure will prove many formulae in the subset of arithmetic         %
% specified above, but there is some incompleteness.                         %
%----------------------------------------------------------------------------%

let ARITH_CONV =
   let REWRITES_CONV thl =
      let net = mk_conv_net thl
      in  \tm. FIRST_CONV (lookup_term net tm) tm
   in
   let BOOL_SIMP_CONV = TOP_DEPTH_CONV (REWRITES_CONV basic_rewrites)
   and GEN_ARITH_CONV tm =
      if (is_exists tm)
      then ((EXISTS_ARITH_CONV tm)
            ?? [`EXISTS_ARITH_CONV -- formula not in the allowed subset`]
               failwith `ARITH_CONV -- formula not in the allowed subset`
            ?? [`EXISTS_ARITH_CONV -- cannot prove formula`]
               failwith `ARITH_CONV -- cannot prove formula`)
      else ((INSTANCE_T_CONV non_presburger_subterms FORALL_ARITH_CONV tm)
            ?? [`FORALL_ARITH_CONV -- formula not in the allowed subset`]
               failwith `ARITH_CONV -- formula not in the allowed subset`
            ?? [`FORALL_ARITH_CONV -- cannot prove formula`]
               failwith `ARITH_CONV -- cannot prove formula`)
   in
   SUB_AND_COND_ELIM_CONV THENC
   BOOL_SIMP_CONV THENC
   (\tm. if (tm = "T") or (tm = "F")
         then ALL_CONV tm
         else (PRENEX_CONV THENC GEN_ARITH_CONV) tm);;
