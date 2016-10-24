%****************************************************************************%
% FILE          : exists_arith.ml                                            %
% DESCRIPTION   : Procedure for proving purely existential prenex Presburger %
%                 arithmetic formulae.                                       %
%                                                                            %
% READS FILES   : ../Library/reduce/reduce.ml                                %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 25th June 1992                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 2nd July 1992                                              %
%****************************************************************************%

%----------------------------------------------------------------------------%
% NUM_REDUCE_QCONV : conv                                                    %
%----------------------------------------------------------------------------%

letrec NUM_REDUCE_QCONV tm =
   if (is_suc tm) then ((RAND_QCONV NUM_REDUCE_QCONV) THENQC SUC_CONV) tm
   if (is_plus tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC ADD_CONV) tm
   if (is_mult tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC MUL_CONV) tm
   else ALL_QCONV tm;;

%----------------------------------------------------------------------------%
% INEQ_REDUCE_QCONV : conv                                                   %
%----------------------------------------------------------------------------%

let INEQ_REDUCE_QCONV tm =
   if (is_eq tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC NEQ_CONV) tm
   if (is_leq tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC LE_CONV) tm
   if (is_less tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC LT_CONV) tm
   if (is_geq tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC GE_CONV) tm
   if (is_great tm) then ((ARGS_QCONV NUM_REDUCE_QCONV) THENQC GT_CONV) tm
   else ALL_QCONV tm;;

%----------------------------------------------------------------------------%
% BOOL_REDUCE_QCONV : conv                                                   %
%----------------------------------------------------------------------------%

letrec BOOL_REDUCE_QCONV tm =
   if (is_num_reln tm) then INEQ_REDUCE_QCONV tm
   if (is_neg tm) then ((RAND_QCONV BOOL_REDUCE_QCONV) THENQC NOT_CONV) tm
   if (is_conj tm) then ((ARGS_QCONV BOOL_REDUCE_QCONV) THENQC AND_CONV) tm
   if (is_disj tm) then ((ARGS_QCONV BOOL_REDUCE_QCONV) THENQC OR_CONV) tm
   if (is_imp tm) then ((ARGS_QCONV BOOL_REDUCE_QCONV) THENQC IMP_CONV) tm
   if (is_eq tm) then ((ARGS_QCONV BOOL_REDUCE_QCONV) THENQC BEQ_CONV) tm
   else INEQ_REDUCE_QCONV tm;;

%----------------------------------------------------------------------------%
% WITNESS : (string # int) list -> conv                                      %
%                                                                            %
% This function proves an existentially quantified arithmetic formula given  %
% a witness for the formula in the form of a variable-name/value binding.    %
%----------------------------------------------------------------------------%

letrec WITNESS binding tm =
 (let (var,bdy) = dest_exists tm
  in  let num = term_of_int (snd (assoc (fst (dest_var var)) binding) ? 0)
  in  EXISTS (tm,num) (WITNESS binding (subst [(num,var)] bdy))
 ) ? EQT_ELIM (QCONV BOOL_REDUCE_QCONV tm);;

%----------------------------------------------------------------------------%
% witness : term list -> (string # int) list                                 %
%                                                                            %
% Function to find a witness for a formula from the disjuncts of a           %
% normalised version.                                                        %
%----------------------------------------------------------------------------%

letrec witness tml =
   if (null tml)
   then failwith `witness`
   else Shostak (coeffs_of_leq_set (hd tml)) ? (witness (tl tml));;

%----------------------------------------------------------------------------%
% EXISTS_ARITH_CONV : conv                                                   %
%                                                                            %
% Proof procedure for non-universal Presburger natural arithmetic            %
% (+, * by a constant, numeric constants, numeric variables, <, <=, =, >=, > %
%  ~, /\, \/, ==>, = (iff), ? (when in prenex normal form).                  %
% Expects formula in prenex normal form.                                     %
% Subtraction and conditionals must have been eliminated.                    %
% SUC is allowed.                                                            %
% Boolean variables and constants are not allowed.                           %
%                                                                            %
% The procedure is not complete.                                             %
%----------------------------------------------------------------------------%

let EXISTS_ARITH_CONV tm =
 reset_multiplication_theorems ();
 let th = QCONV ARITH_FORM_NORM_QCONV
             (snd (strip_exists (assert (null o frees) tm)))
        ? failwith `EXISTS_ARITH_CONV -- formula not in the allowed subset`
 in  (let binding = witness (disjuncts (rhs (concl th)))
      in  EQT_INTRO (WITNESS binding tm)
     ) ? failwith `EXISTS_ARITH_CONV -- cannot prove formula`;;
