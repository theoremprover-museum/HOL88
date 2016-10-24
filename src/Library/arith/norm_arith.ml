%****************************************************************************%
% FILE          : norm_arith.ml                                              %
% DESCRIPTION   : Functions for normalizing arithmetic terms.                %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 5th October 1992                                           %
%****************************************************************************%

%============================================================================%
% Conversions for normalizing arithmetic                                     %
%============================================================================%

%----------------------------------------------------------------------------%
% COLLECT_NUM_CONSTS_CONV : conv                                             %
%                                                                            %
% Converts a term of the form "a + (b + (...))" into "c + (...)" where       %
% a and b are constants and c is their (constant) sum.                       %
%                                                                            %
% Also handles "a + b" --> "c".                                              %
%----------------------------------------------------------------------------%

let COLLECT_NUM_CONSTS_CONV tm =
 (if ((is_plus tm) & (is_const (arg1 tm)))
  then if ((is_plus (arg2 tm)) & (is_const (arg1 (arg2 tm)))) then
          (ADD_ASSOC_CONV THENC (RATOR_CONV (RAND_CONV ADD_CONV))) tm
       if (is_const (arg2 tm)) then ADD_CONV tm
       else fail
  else fail
 ) ? failwith `COLLECT_NUM_CONSTS_CONV`;;

%----------------------------------------------------------------------------%
% NUM_RELN_NORM_QCONV : conv -> conv -> conv                                 %
%                                                                            %
% Converts arithmetic relations and negations of arithmetic relations into   %
% conjuncts/disjuncts of less-than-or-equal-to. The arguments of the         %
% relation are processed using `arith_qconv', and attempts are made to       %
% gather together numeric constants. The resulting less-than-or-equal-to     %
% inequalities are processed using `leq_qconv'.                              %
%----------------------------------------------------------------------------%

let NUM_RELN_NORM_QCONV arith_qconv leq_qconv tm =
 (if (is_neg tm)
  then (let tm' = rand tm
        in  ((RAND_QCONV (ARGS_QCONV arith_qconv)) THENQC
             (if (is_eq tm') then
                 (NOT_NUM_EQ_NORM_CONV THENQC
                  (ARGS_QCONV
                    ((RATOR_QCONV
                       (RAND_QCONV
                         (TRY_QCONV COLLECT_NUM_CONSTS_CONV))) THENQC
                     leq_qconv)))
              if (is_leq tm') then
                 (NOT_LEQ_NORM_CONV THENQC
                  (RATOR_QCONV
                    (RAND_QCONV (TRY_QCONV COLLECT_NUM_CONSTS_CONV))) THENQC
                  leq_qconv)
              if (is_less tm') then
                 (NOT_LESS_NORM_CONV THENQC leq_qconv)
              if (is_great tm') then
                 (NOT_GREAT_NORM_CONV THENQC leq_qconv)
              if (is_geq tm') then
                 (NOT_GEQ_NORM_CONV THENQC
                  (RATOR_QCONV
                    (RAND_QCONV (TRY_QCONV COLLECT_NUM_CONSTS_CONV))) THENQC
                  leq_qconv)
              else fail)) tm)
  else ((ARGS_QCONV arith_qconv) THENQC
        (if (is_eq tm) then (NUM_EQ_NORM_CONV THENQC (ARGS_QCONV leq_qconv))
         if (is_leq tm) then leq_qconv
         if (is_less tm) then
            (LESS_NORM_CONV THENQC
             (RATOR_QCONV
               (RAND_QCONV (TRY_QCONV COLLECT_NUM_CONSTS_CONV))) THENQC
             leq_qconv)
         if (is_great tm) then
            (GREAT_NORM_CONV THENQC
             (RATOR_QCONV
               (RAND_QCONV (TRY_QCONV COLLECT_NUM_CONSTS_CONV))) THENQC
             leq_qconv)
         if (is_geq tm) then (GEQ_NORM_CONV THENQC leq_qconv)
         else fail)) tm
 ) ?\s qfailwith s `NUM_RELN_NORM_QCONV`;;

%----------------------------------------------------------------------------%
% MULT_CONV : conv                                                           %
%                                                                            %
% Given a term of the form "a * b" where a and b are constants, returns the  %
% theorem |- a * b = c where c is the product of a and b.                    %
%----------------------------------------------------------------------------%

letrec MULT_CONV tm =
 (let (a,b) = dest_mult tm
  in  let aval = int_of_term a
  in  if (aval = 0) then SPEC b ZERO_MULT
      if (aval = 1) then SPEC b ONE_MULT
      else let th1 = RATOR_CONV (RAND_CONV num_CONV) tm
           in  let th2 = SPEC b (SPEC (term_of_int (aval - 1)) MULT_SUC)
           in  let th3 = ((RATOR_CONV (RAND_CONV MULT_CONV)) THENC ADD_CONV)
                            (rhs (concl th2))
           in th1 TRANS th2 TRANS th3
 ) ? failwith `MULT_CONV`;;

%----------------------------------------------------------------------------%
% mult_lookup : ((int # int) # thm) list -> (int # int) -> thm               %
%                                                                            %
% Takes an association list of pairs of integers, and theorems about the     %
% simplification of the products of the pairs of integers. The second        %
% argument is a pair of integers to be looked up. The integers in the        %
% association list should be greater than 1 and the first of each pair       %
% should not exceed the second. If the pair of integers specified (or the    %
% reverse of them) appear in the list, a theorem about the simplification of %
% their product is returned.                                                 %
%                                                                            %
% Given a list l of the form:                                                %
%                                                                            %
%    [((2, 3), |- 2 * 3 = 6); ((2, 2), |- 2 * 2 = 4)]                        %
%                                                                            %
% here are some examples:                                                    %
%                                                                            %
%    mult_lookup l (2,3)  --->  |- 2 * 3 = 6                                 %
%    mult_lookup l (3,2)  --->  |- 3 * 2 = 6                                 %
%    mult_lookup l (3,3)  fails                                              %
%----------------------------------------------------------------------------%

let mult_lookup ths (n,m) =
 (if (m < n)
  then let th2 = snd (assoc (m,n) ths)
       in  let tm = mk_mult (term_of_int n,term_of_int m)
       in  let th1 = MULT_COMM_CONV tm
       in  th1 TRANS th2
  else snd (assoc (n,m) ths)
 ) ? failwith `mult_lookup`;;

%----------------------------------------------------------------------------%
% FAST_MULT_CONV : conv                                                      %
%                                                                            %
% Given a term of the form "a * b" where a and b are constants, returns the  %
% theorem |- a * b = c where c is the product of a and b. A list of          %
% previously proved theorems is maintained to speed up the process. Any      %
% new theorems that have to be proved are added to the list.                 %
%----------------------------------------------------------------------------%

letref multiplication_theorems = ([]:((int # int) # thm) list);;

letrec FAST_MULT_CONV tm =
 (let (a,b) = dest_mult tm
  in  let aval = int_of_term a
      and bval = int_of_term b
  in  if (aval = 0) then SPEC b ZERO_MULT
      if (aval = 1) then SPEC b ONE_MULT
      if (bval = 0) then SPEC a MULT_ZERO
      if (bval = 1) then SPEC a MULT_ONE
      else mult_lookup multiplication_theorems (aval,bval) ?
           (let th1 = RATOR_CONV (RAND_CONV num_CONV) tm
            in  let th2 = SPEC b (SPEC (term_of_int (aval - 1)) MULT_SUC)
            in  let th3 =
                   ((RATOR_CONV (RAND_CONV FAST_MULT_CONV)) THENC ADD_CONV)
                   (rhs (concl th2))
            in  let th = th1 TRANS th2 TRANS th3
            in  if (bval < aval)
                then let th' = (MULT_COMM_CONV (mk_mult (b,a))) TRANS th
                     in  (multiplication_theorems :=
                             ((bval,aval),th').multiplication_theorems; th)
                else (multiplication_theorems :=
                         ((aval,bval),th).multiplication_theorems; th))
 ) ? failwith `FAST_MULT_CONV`;;

let reset_multiplication_theorems (():void) =
   (multiplication_theorems := ([]:((int # int) # thm) list));;

let multiplication_theorems (():void) = multiplication_theorems;;

%----------------------------------------------------------------------------%
% SUM_OF_PRODUCTS_SUC_CONV : conv                                            %
%                                                                            %
% Given a term of the form "SUC x" where x is in sum-of-products form, this  %
% function converts the whole term to sum-of-products form.                  %
%                                                                            %
%    SUC const         ---> const'                                           %
%    SUC var           ---> 1 + var                                          %
%    SUC (const * var) ---> 1 + (const * var)                                %
%    SUC (const + exp) ---> const' + exp                                     %
%    SUC (exp + const) ---> const' + exp                                     %
%    SUC (exp1 + exp2) ---> 1 + (exp1 + exp2)                                %
%                                                                            %
% where const' is the numeric constant one greater than const.               %
%----------------------------------------------------------------------------%

let SUM_OF_PRODUCTS_SUC_CONV tm =
 let add1 = term_of_int o (curry $+ 1) o int_of_term
 in
 (if (is_suc tm)
  then let tm' = rand tm
       in  if (is_const tm') then (SYM o num_CONV o add1) tm'
           if (is_var tm') then SPEC tm' ONE_PLUS
           if ((is_mult tm') & (is_const (arg1 tm')) & (is_var (arg2 tm')))
              then SPEC tm' ONE_PLUS
           if (is_plus tm') then
              (let (a,b) = dest_plus tm'
               in  if (is_const a) then
                      (let th1 = SPEC b (SPEC a SUC_ADD1)
                       and th2 =
                          AP_THM (AP_TERM "$+" ((SYM o num_CONV o add1) a)) b
                       in  th1 TRANS th2)
                   if (is_const b) then
                      (let th1 = SPEC b (SPEC a SUC_ADD2)
                       and th2 =
                          AP_THM (AP_TERM "$+" ((SYM o num_CONV o add1) b)) a
                       in  th1 TRANS th2)
                   else SPEC tm' ONE_PLUS)
           else fail
  else fail
 ) ? failwith `SUM_OF_PRODUCTS_SUC_CONV`;;

%----------------------------------------------------------------------------%
% SUM_OF_PRODUCTS_MULT_QCONV : conv                                          %
%                                                                            %
% Given a term of the form "x * y" where x and y are in sum-of-products form %
% this function converts the whole term to sum-of-products form.             %
%                                                                            %
%    0 * exp                 ---> 0                                          %
%    exp * 0                 ---> 0                                          %
%    const1 * const2         ---> const3                                     %
%    exp * const             ---> SOPM (const * exp)                         %
%    const * var             ---> const * var               (i.e. no change) %
%    const1 * (const2 * var) ---> const3 * var                               %
%    const * (exp1 + exp2)   ---> SOPM (const * exp1) + SOPM (const * exp2)  %
%                                                                            %
% where const3 is the numeric constant whose value is the product of const1  %
% and const2. SOPM denotes a recursive call of SUM_OF_PRODUCTS_MULT_QCONV.   %
%----------------------------------------------------------------------------%

letrec SUM_OF_PRODUCTS_MULT_QCONV tm =
 (if (is_mult tm)
  then (let (tm1,tm2) = dest_mult tm
        in  if (is_zero tm1) then (SPEC tm2 ZERO_MULT)
            if (is_zero tm2) then (SPEC tm1 MULT_ZERO)
            if ((is_const tm1) & (is_const tm2)) then FAST_MULT_CONV tm
            if (is_const tm2) then
               (let conv _ = SPEC tm2 (SPEC tm1 MULT_COMM)
                in  (conv THENQC SUM_OF_PRODUCTS_MULT_QCONV) tm)
            if (is_const tm1)
            then (if (is_var tm2) then ALL_QCONV tm
                  if ((is_mult tm2) &
                      (is_const (arg1 tm2)) &
                      (is_var (arg2 tm2))) then
                     (MULT_ASSOC_CONV THENQC
                      (RATOR_QCONV (RAND_QCONV FAST_MULT_CONV))) tm
                  if (is_plus tm2) then
                     (LEFT_ADD_DISTRIB_CONV THENQC
                      (ARGS_QCONV SUM_OF_PRODUCTS_MULT_QCONV)) tm
                  else fail)
            else fail)
  else fail
 ) ?\s qfailwith s `SUM_OF_PRODUCTS_MULT_QCONV`;;

%----------------------------------------------------------------------------%
% SUM_OF_PRODUCTS_QCONV : conv                                               %
%                                                                            %
% Puts an arithmetic expression involving constants, variables, SUC, + and * %
% into sum-of-products form. That is, SUCs are eliminated, and the result is %
% an arbitrary tree of sums with products as the leaves. The only `products' %
% allowed are constants, variables and products of a constant and a          %
% variable. The conversion fails if the term cannot be put in this form.     %
%----------------------------------------------------------------------------%

letrec SUM_OF_PRODUCTS_QCONV tm =
 (if ((is_const tm) or (is_var tm)) then ALL_QCONV tm
  if (is_suc tm) then
     ((RAND_QCONV SUM_OF_PRODUCTS_QCONV) THENQC SUM_OF_PRODUCTS_SUC_CONV) tm
  if (is_plus tm) then
     ((ARGS_QCONV SUM_OF_PRODUCTS_QCONV) THENQC
      (\tm'. let (tm1,tm2) = dest_plus tm'
             in  if (is_zero tm1) then (SPEC tm2 ZERO_PLUS)
                 if (is_zero tm2) then (SPEC tm1 PLUS_ZERO)
                 if ((is_const tm1) & (is_const tm2)) then (ADD_CONV tm')
                 else ALL_QCONV tm')) tm
  if (is_mult tm) then
     ((ARGS_QCONV SUM_OF_PRODUCTS_QCONV) THENQC SUM_OF_PRODUCTS_MULT_QCONV) tm
  else fail
 ) ?\s qfailwith s `SUM_OF_PRODUCTS_QCONV`;;

%----------------------------------------------------------------------------%
% LINEAR_SUM_QCONV : conv                                                    %
%                                                                            %
% Makes a tree of sums `linear', e.g.                                        %
%                                                                            %
%    (((a + b) + c) + d) + (e + f) ---> a + (b + (c + (d + (e + f))))        %
%----------------------------------------------------------------------------%

let LINEAR_SUM_QCONV =
 letrec FILTER_IN_QCONV tm =
    (TRY_QCONV (SYM_ADD_ASSOC_CONV THENQC (RAND_QCONV FILTER_IN_QCONV))) tm
 in  letrec LINEAR_SUM_QCONV' tm =
        (if (is_plus tm)
         then ((ARGS_QCONV LINEAR_SUM_QCONV') THENQC FILTER_IN_QCONV) tm
         else ALL_QCONV tm
        ) ?\s qfailwith s `LINEAR_SUM_QCONV`
 in  LINEAR_SUM_QCONV';;

%----------------------------------------------------------------------------%
% GATHER_QCONV : conv                                                        %
%                                                                            %
% Converts "(a * x) + (b * x)" to "(a + b) * x" and simplifies (a + b) if    %
% both a and b are constants. Also handles the cases when either or both of  %
% a and b are missing, e.g. "(a * x) + x".                                   %
%----------------------------------------------------------------------------%

let GATHER_QCONV tm =
 (let conv =
     case (is_mult # is_mult) (dest_plus tm)
     of (true,true)   . GATHER_BOTH_CONV
      | (true,false)  . GATHER_LEFT_CONV
      | (false,true)  . GATHER_RIGHT_CONV
      | (false,false) . GATHER_NEITHER_CONV
  in  (conv THENQC (RATOR_QCONV (RAND_QCONV (TRY_QCONV ADD_CONV)))) tm
 ) ?\s qfailwith s `GATHER_QCONV`;;

%----------------------------------------------------------------------------%
% IN_LINE_SUM_QCONV : conv -> conv                                           %
%                                                                            %
% Applies a conversion to the top two summands of a line of sums.            %
%                                                                            %
%    a + (b + ...)  --->  (a + b) + ...  --->  c + ...                       %
%                                                                            %
% where c is the result of applying `qconv' to (a + b). If c is itself a     %
% sum, i.e. (c1 + c2) then the following conversion also takes place:        %
%                                                                            %
%    (c1 + c2) + ...  --->  c1 + (c2 + ...)                                  %
%----------------------------------------------------------------------------%

let IN_LINE_SUM_QCONV qconv tm =
 (ADD_ASSOC_CONV THENQC
  (RATOR_QCONV (RAND_QCONV qconv)) THENQC
  (TRY_QCONV SYM_ADD_ASSOC_CONV)) tm
 ?\s qfailwith s `IN_LINE_SUM_QCONV`;;

%----------------------------------------------------------------------------%
% ONE_PASS_SORT_QCONV : conv                                                 %
%                                                                            %
% Single pass of sort and gather for a linear sum of products.               %
%                                                                            %
% Operations on adjacent summands:                                           %
%                                                                            %
%    const1 + const2                   ---> const3                           %
%    const + exp                       ---> const + exp     (i.e. no change) %
%    exp + const                       ---> const + exp                      %
%                                                                            %
%    (const1 * var) + (const2 * var)   }                                     %
%    (const1 * var) + var              } GATHER                              %
%    var + (const2 * var)              }                                     %
%    var + var                         }                                     %
%                                                                            %
%    (const1 * var1) + (const2 * var2) }                                     %
%    (const1 * var1) + var2            } ADD_SYM if var2 lexicographically   %
%    var1 + (const2 * var2)            }         less than var1              %
%    var1 + var2                       }                                     %
%                                                                            %
% where const3 is the numeric constant whose value is the sum of const1 and  %
% const2.                                                                    %
%----------------------------------------------------------------------------%

letrec ONE_PASS_SORT_QCONV tm =
 (if (is_plus tm)
  then ((RAND_QCONV ONE_PASS_SORT_QCONV) THENQC
        (\tm'.
          let (tm1,tm2) = dest_plus tm'
          in  if (is_plus tm2) then
                 (let tm2' = arg1 tm2
                  in  if ((is_const tm1) & (is_const tm2')) then
                         IN_LINE_SUM_QCONV ADD_CONV tm'
                      if (is_const tm1) then ALL_QCONV tm'
                      if (is_const tm2') then
                         IN_LINE_SUM_QCONV ADD_SYM_CONV tm'
                      else let name1 = var_of_prod tm1
                           and name2 = var_of_prod tm2'
                           in  if (name1 = name2) then
                                  IN_LINE_SUM_QCONV GATHER_QCONV tm'
                               if (string_less name2 name1) then
                                  IN_LINE_SUM_QCONV ADD_SYM_CONV tm'
                               else ALL_QCONV tm')
              if ((is_const tm1) & (is_const tm2)) then ADD_CONV tm'
              if (is_const tm1) then ALL_QCONV tm'
              if (is_const tm2) then ADD_SYM_CONV tm'
              else let name1 = var_of_prod tm1
                   and name2 = var_of_prod tm2
                   in  if (name1 = name2) then GATHER_QCONV tm'
                       if (string_less name2 name1) then ADD_SYM_CONV tm'
                       else ALL_QCONV tm')) tm
  else ALL_QCONV tm
 ) ?\s qfailwith s `ONE_PASS_SORT_QCONV`;;

%----------------------------------------------------------------------------%
% SORT_AND_GATHER_QCONV : conv                                               %
%                                                                            %
% Sort and gather for a linear sum of products. Constants are moved to the   %
% front of the sum and variable terms are sorted lexicographically, e.g.     %
%                                                                            %
%    x + (y + (1 + ((9 * y) + (3 * x))))  --->  1 + ((4 * x) + (10 * y))     %
%----------------------------------------------------------------------------%

let SORT_AND_GATHER_QCONV tm =
 REPEATQC (CHANGED_QCONV ONE_PASS_SORT_QCONV) tm
 ?\s qfailwith s `SORT_AND_GATHER_QCONV`;;

%----------------------------------------------------------------------------%
% SYM_ONE_MULT_VAR_CONV : conv                                               %
%                                                                            %
% If the argument term is a numeric variable, say "x", then this conversion  %
% returns the theorem |- x = 1 * x.                                          %
%----------------------------------------------------------------------------%

let SYM_ONE_MULT_VAR_CONV tm =
 (if (is_var tm)
  then SYM_ONE_MULT_CONV tm
  else fail
 ) ? failwith `SYM_ONE_MULT_VAR_CONV`;;

%----------------------------------------------------------------------------%
% NORM_ZERO_AND_ONE_QCONV : conv                                             %
%                                                                            %
% Performs the following transformations on a linear sum of products:        %
%                                                                            %
%    ... (0 * x)          --->  ... 0                                        %
%    ... + (0 * x) + ...  --->  ... + ...                                    %
%                                                                            %
%    ... x                --->  ... (1 * x)                                  %
%    ... + x + ...        --->  ... + (1 * x) + ...                          %
%                                                                            %
%    ... + exp + 0        --->  ... + exp                                    %
%                                                                            %
% And at top-level only:                                                     %
%                                                                            %
%    0 + exp              --->  exp                                          %
%----------------------------------------------------------------------------%

let NORM_ZERO_AND_ONE_QCONV =
 letrec NORM_QCONV tm =
  if (is_plus tm) then
     ((RAND_QCONV NORM_QCONV) THENQC
      (RATOR_QCONV (RAND_QCONV (TRY_QCONV SYM_ONE_MULT_VAR_CONV))) THENQC
      (TRY_QCONV ZERO_MULT_PLUS_CONV) THENQC
      (TRY_QCONV PLUS_ZERO_CONV)) tm
  else ((TRY_QCONV ZERO_MULT_CONV) THENQC
        (TRY_QCONV SYM_ONE_MULT_VAR_CONV)) tm
 in \tm.
 ((NORM_QCONV THENQC (TRY_QCONV ZERO_PLUS_CONV)) tm
 ) ?\s qfailwith s `NORM_ZERO_AND_ONE_QCONV`;;
