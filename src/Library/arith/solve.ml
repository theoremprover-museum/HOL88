%****************************************************************************%
% FILE          : solve.ml                                                   %
% DESCRIPTION   : Functions for solving arithmetic formulae.                 %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 19th April 1991                                            %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 2nd July 1992                                              %
%****************************************************************************%

%----------------------------------------------------------------------------%
% INEQS_FALSE_CONV : conv                                                    %
%                                                                            %
% Proves a conjunction of normalized inequalities is false, provided they    %
% are unsatisfiable. Checks for any inequalities that can immediately be     %
% shown to be false before calling VAR_ELIM.                                 %
%                                                                            %
% Example:                                                                   %
%                                                                            %
%    INEQS_FALSE_CONV                                                        %
%       "((2 + (2 * n)) <= (1 * m)) /\                                       %
%        ((1 * m) <= (1 * n)) /\                                             %
%        (0 <= (1 * n)) /\                                                   %
%        (0 <= (1 * m))"                                                     %
%    --->                                                                    %
%    |- (2 + (2 * n)) <= (1 * m) /\                                          %
%       (1 * m) <= (1 * n) /\                                                %
%       0 <= (1 * n) /\                                                      %
%       0 <= (1 * m) =                                                       %
%       F                                                                    %
%----------------------------------------------------------------------------%

let INEQS_FALSE_CONV tm =
 (let ineqs = conjuncts tm
  in  let coeffsl = map coeffs_of_leq ineqs
  in  let falses = filter (\(const,bind). (null bind) & (const < 0)) coeffsl
  in  let th =
         if (null falses)
         then let var_names = setify (map fst (flat (map snd coeffsl)))
              in  let coeffsl' = (map (\v. (0, [(v,1)])) var_names) @ coeffsl
              in  let (_,f) = VAR_ELIM coeffsl'
              in  let axioms =
                     map (\v. SPEC (mk_num_var v) ZERO_LESS_EQ_ONE_TIMES)
                                                                   var_names
              in  itlist PROVE_HYP axioms (f ())
         else ASSUME (build_leq (hd falses))
  in  let th' = CONV_RULE LEQ_CONV th
  in  let th'' = DISCH (last ineqs) th'
  in  let conj_disch tm th = CONV_RULE IMP_IMP_CONJ_IMP_CONV (DISCH tm th)
  in  let th''' = itlist conj_disch (butlast ineqs) th''
  in  CONV_RULE IMP_F_EQ_F_CONV th'''
 ) ? failwith `INEQS_FALSE_CONV`;;

%----------------------------------------------------------------------------%
% DISJ_INEQS_FALSE_QCONV : conv                                              %
%                                                                            %
% Proves a disjunction of conjunctions of normalized inequalities is false,  %
% provided each conjunction is unsatisfiable.                                %
%----------------------------------------------------------------------------%

letrec DISJ_INEQS_FALSE_QCONV tm =
 (if (is_disj tm)
  then ((RATOR_QCONV (RAND_QCONV INEQS_FALSE_CONV)) THENQC
        OR_F_CONV THENQC
        DISJ_INEQS_FALSE_QCONV) tm
  else INEQS_FALSE_CONV tm
 ) ?\s qfailwith s `DISJ_INEQS_FALSE_QCONV`;;

%----------------------------------------------------------------------------%
% NOT_NOT_INTRO_CONV : conv                                                  %
%                                                                            %
% "b"  --->  |- b = ~~b  provided b is of type ":bool".                      %
%----------------------------------------------------------------------------%

let NOT_NOT_INTRO_CONV tm =
 (SYM ((NOT_NOT_NORM_CONV o mk_neg o mk_neg) tm)
 ) ? failwith `NOT_NOT_INTRO_CONV`;;

%----------------------------------------------------------------------------%
% Discriminator functions for T (true) and F (false)                         %
%----------------------------------------------------------------------------%

let is_T = let T = "T" in \tm. tm = T
and is_F = let F = "F" in \tm. tm = F;;

%----------------------------------------------------------------------------%
% NEGATE_CONV : conv -> conv                                                 %
%                                                                            %
% Function for negating the operation of a conversion that proves a formula  %
% to be either true or false. For example if `conv' proves "0 <= n" to be    %
% equal to "T" then `NEGATE_CONV conv' will prove "~(0 <= n)" to be "F".     %
% The function fails if the application of `conv' to the negation of the     %
% formula does not yield either "T" or "F".                                  %
%                                                                            %
% If use of this function succeeds then the input term will necessarily have %
% been changed. Hence it does not need to be a QCONV. It can however take a  %
% QCONV as its argument.                                                     %
%----------------------------------------------------------------------------%

let NEGATE_CONV qconv tm =
 let neg = is_neg tm
 in  let th = QCONV qconv (if neg then (dest_neg tm) else (mk_neg tm))
 in  let r = rhs (concl th)
 in  let truth_th =
        if (is_T r) then NOT_T_F
        if (is_F r) then NOT_F_T
        else failwith `NEGATE_CONV`
 in  let neg_fn = if neg then I else TRANS (NOT_NOT_INTRO_CONV tm)
 in  neg_fn (TRANS (AP_TERM "$~" th) truth_th);;

%----------------------------------------------------------------------------%
% DEPTH_FORALL_QCONV : conv -> conv                                          %
%                                                                            %
% DEPTH_FORALL_QCONV conv "!x1 ... xn. body" applies conv to "body" and      %
% returns a theorem of the form:                                             %
%                                                                            %
%    |- (!x1 ... xn. body) = (!x1 ... xn. body')                             %
%----------------------------------------------------------------------------%

letrec DEPTH_FORALL_QCONV conv tm =
 if (is_forall tm)
 then RAND_QCONV (ABS_QCONV (DEPTH_FORALL_QCONV conv)) tm
 else conv tm;;

%----------------------------------------------------------------------------%
% FORALL_ARITH_CONV : conv                                                   %
%                                                                            %
% Proof procedure for non-existential Presburger natural arithmetic          %
% (+, * by a constant, numeric constants, numeric variables, <, <=, =, >=, > %
%  ~, /\, \/, ==>, = (iff), ! (when in prenex normal form).                  %
% Expects formula in prenex normal form.                                     %
% Subtraction and conditionals must have been eliminated.                    %
% SUC is allowed.                                                            %
% Boolean variables and constants are not allowed.                           %
%                                                                            %
% The procedure will prove most formulae in the subset of arithmetic         %
% specified above, but there is some incompleteness. However, this rarely    %
% manifests itself in practice. It is therefore likely that if the procedure %
% cannot prove a formula in the subset, the formula is not valid.            %
%----------------------------------------------------------------------------%

let FORALL_ARITH_CONV tm =
 reset_multiplication_theorems ();
 QCONV
 (DEPTH_FORALL_QCONV
   (NEGATE_CONV
     ((\tm. ARITH_FORM_NORM_QCONV tm ?\s qfailwith s
            `FORALL_ARITH_CONV -- formula not in the allowed subset`) THENQC
      (\tm. DISJ_INEQS_FALSE_QCONV tm ?\s qfailwith s
            `FORALL_ARITH_CONV -- cannot prove formula`))) THENQC
  REPEATQC FORALL_SIMP_CONV)
 tm;;
