%
-------------------------------------------------------------------------------
Define proof rules for the numeral library.

Things to change:

  Support numerals in the parser and pretty printer.
    delete BASEN_CONV and BASEN_OF_NUM_CONV
    move num_CONV and such into a compatibility library
  Port to hol90.
  Memoize to cache the step theorems that are specialized by radix.
  Memoize to cache the partial products in basen_mul_conv.
  Add INT_ARITH_CONV, REAL_ARITH_CONV, IEEE_ARITH_CONV, etc.

Revision history (most recent first):

* 1994 (Jan)    John Harrison

  Dependence on libraries |more_arith| and |more_list| eliminated by
  explicitly proving the few theorems used.

  Duplicates or near-duplicates of existing functions |rev|, |forall|
  and |funpow| replaced.

  Normalization forced to work correctly for |BASEN_ADD_CONV| and
  |BASEN_MUL_CONV|.

  New, recursive version of |BASEN_MUL_CONV| added which is faster for very
  large arguments (over 10 digits).

* 1993          Tim Leonard

  Initial released version:
    BASEN_ADD_CONV          BASEN_MOD_CONV        NUM_ARITH_TAC
    BASEN_COMPARE_CONV      BASEN_MUL_CONV        ONCE_BASEN_DENORMALIZE_CONV
    BASEN_CONV              BASEN_NORMALIZE_CONV  ONCE_BASEN_NORMALIZE_CONV
    BASEN_DENORMALIZE_CONV  BASEN_OF_NUM_CONV     basen_of_int
    BASEN_DIV_CONV          BASEN_PRE_CONV        dest_basen
    BASEN_EQ_CONV           BASEN_SUB_CONV        dest_binary_basen_comb
    BASEN_EXP_CONV          BASEN_SUC_CONV        dest_unary_basen_comb
    BASEN_GE_CONV           IS_BASEN_CONV         int_of_basen
    BASEN_GT_CONV           IS_NORMALIZED_CONV    is_basen
    BASEN_LE_CONV           NUM_ARITH_CONV        mk_basen
    BASEN_LT_CONV           NUM_ARITH_RULE
-------------------------------------------------------------------------------
%

%----------------------------------------------------------------------------%
% Theorems required from |more_arithmetic|. [JRH 94.01.16]                   %
%----------------------------------------------------------------------------%

let ADDR_GREATER_EQ = PROVE
 ("!m n p. m <= n ==> m <= (n + p)",
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_TAC o REWRITE_RULE[LESS_EQ_EXISTS]) THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; LESS_EQ_ADD]);;

let NOT_LESS_AND_GREATER = PROVE
 ("!n m. n < m ==> ~(m < n)",
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL ["m:num"; "n:num"] LESS_ANTISYM) THEN ASM_REWRITE_TAC[]);;

let ADD_MONO_LESS = PROVE
 ("!m n p. (m + p) < (m + n) = p < n",
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_ACCEPT_TAC LESS_MONO_ADD_EQ);;

let ADD_EQ_IMP_SUB_EQ = PROVE
 ("!a b c. (a = b + c) ==> (a - b = c)",
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB);;

%
Define the radices for which arithmetic will be accelerated by table lookup.
The full_add_table has (max_radix EXP 3) elements, so a radix much over 16
makes for a very large table.  There are also several tables of size (radix
EXP 2) for each radix accelerated, so each additional radix has a cost.  If
you're doing only decimal arithmetic, then let radices = [10].  If you're
doing computer arithmetic, hexadecimal, binary, and possibly octal may be
useful.  By default, only decimal and hex are accelerated.

The tables should actually be caches rather than precomputed (though it may
still make sense to precompute for decimal), which would make this decision
unnecessary.
%

letref radices = [10;16];;

let max x y =
  if x > y then x else y;;

let max_radix =
  end_itlist max radices;;

if max_radix > 20 then
  failwith `Radices larger than 20 make full_add_table too big.`
else if min_radix < 2 then
  failwith `Radices less than 2 are not supported.`
where min_radix =
  let min x y = if x < y then x else y in
  end_itlist min radices;;


%
-------------------------------------------------------------------------------
Define several small ML functions.
-------------------------------------------------------------------------------
%

%----------------------------------------------------------------------------%
% Function |reverse| replaced by inbuilt function |rev| [JRH 94.01.29]       %
%                                                                            %
% Old code:                                                                  %
%                                                                            %
% letrec reverse l = if l = [] then [] else append (reverse (tl l)) [hd l];; %
%----------------------------------------------------------------------------%

%
Return a list that counts from 1 to n.
%

%----------------------------------------------------------------------------%
% More efficient implementation (tail recursion & no append). [JRH 93.10.29] %
%                                                                            %
% Old code:                                                                  %
%                                                                            %
% letrec upto n = if n < 1 then [] else append (upto (n-1)) [n];;            %
%----------------------------------------------------------------------------%

let upto n =
  letrec down l n = (n = 0) => l | down (n.l) (n - 1) in
  down [] n;;

%
Return a list that counts from 0 to n.
%

let zero_upto n = 0 . upto n;;

%----------------------------------------------------------------------------%
% Function |every| replaced by inbuilt function |forall| [JRH 94.01.29]      %
%                                                                            %
% Old code:                                                                  %
%                                                                            %
% letrec every p l =                                                         %
%   if l = [] then true else                                                 %
%   if p (hd l) then every p (tl l) else false;;                             %
%----------------------------------------------------------------------------%

%
Lengthen a list by prefixing it with a given element, a given number of times.
%

letrec lengthen e n l = if n < 1 then l else lengthen e (n-1) (e.l);;

%
Turn an element into a list containing just that element.
%

let listify x = [x];;

%
Get the first n elements of a list, or all the elements of a list except the
first n.
%

let firstn n = fst o (chop_list n);;

let butfirstn n = snd o (chop_list n);;


%
Return the absolute value (the magnitude) of an int.
%

let absolute_value x = if x < 0 then (0-x) else x;;

%----------------------------------------------------------------------------%
% Function |times| replaced by inbuilt function |funpow| [JRH 94.01.29]      %
%                                                                            %
% Old code:                                                                  %
%                                                                            %
% letrec times n f x =                                                       %
%   if n < 1 then x else times (n-1) f (f x);;                               %
%----------------------------------------------------------------------------%

%
Given a term that is a curried function of two operands, and two terms, return
a term containing an application of that function to the two terms.
%

let mk_binary_comb op rand1 rand2 =
  mk_comb (mk_comb (op, rand1), rand2);;


%
Take apart a term that should consist of a known (given) operator applied to
two operands.  Fail if the subterm doesn't have that form, or if it has the
wrong operator.  Otherwise, return the operands.
%

let dest_unary_comb op =
  snd o ((assert (curry $= op)) # I) o dest_comb;;

let dest_binary_comb op =
  (dest_unary_comb op) # I o dest_comb;;


%
Create a list of terms: ["name0"; "name1"; ... ; "namen"].
%

let mk_term_list (name,ty) n =
  let mk_tm n = mk_var (name ^ (string_of_int n), ty) in
  map mk_tm (upto n);;


%
-------------------------------------------------------------------------------
CONS_OF_SNOC_CONV : term -> thm

Synopsis:

Converts a list from SNOC form to CONS form, where possible.

Description:

If x is a term representing a list constructed with SNOC and CONS, then
CONS_OF_SNOC_CONV x returns a theorem equating that x to a list with the
SNOCs pushed to the bottom (if the bottom is a list other than nil), or
with the SNOCs removed and the order reversed (if the bottom is nil).

Failure:

Fails if the term is not a list.

Examples:

#CONS_OF_SNOC_CONV "SNOC 3(SNOC 2(SNOC 1[]))";;
|- SNOC 3(SNOC 2(SNOC 1[])) = [1;2;3]

#CONS_OF_SNOC_CONV "SNOC [1;2;3] (SNOC [3;4] [])";;
|- SNOC[1;2;3](SNOC[3;4][]) = [[3;4];[1;2;3]]

#CONS_OF_SNOC_CONV "SNOC [1;2;3] (CONS [5] (SNOC [3;4] x))";;
|- SNOC[1;2;3](CONS[5](SNOC[3;4]x)) = CONS[5](SNOC[1;2;3](SNOC[3;4]x))
-------------------------------------------------------------------------------
%

let CONS_OF_SNOC_CONV =
  let mk_snoc_thms n thms =
    let ty = ": *" in
    let xs = mk_term_list (`x`, ty) n in
    let ys = mk_term_list (`y`, ty) n in
    let list_ty = ": ^ty list" in
    let xy = mk_var (`xy`, list_ty) in
    let mk_cons = mk_binary_comb "CONS: ^ty -> ^list_ty -> ^list_ty" in
    let mk_snoc = mk_binary_comb "SNOC: ^ty -> ^list_ty -> ^list_ty" in
    %
    -----------------------------------------------------------------------------
    Prove a theorem of the form
      |- ! x1 x2 ... x<n>:*.
        SNOC x1 (SNOC x2 (... (SNOC x<n> []) ...)) = [x<n>; ...; x2; x1]
    -----------------------------------------------------------------------------
    %
    let snoc_nil =
      let lhs = itlist mk_snoc xs "[]: ^list_ty" in
      let rhs = mk_list (rev xs, ty) in
      let goal = list_mk_forall (xs, mk_eq (lhs, rhs)) in
      PROVE (goal, REWRITE_TAC thms) in
    %
    -----------------------------------------------------------------------------
    Prove a theorem of the form
      |- ! (x1 x2 ... x<n> x1 x2 ... x<n>:*) (xy: * list).
           SNOC x1 (SNOC x2 (... (SNOC x<n>
          (CONS y1 (CONS y2 (... (CONS y<n> xy) ...))) ...))) =
           CONS y1 (CONS y2 (... (CONS y<n>
          (SNOC x1 (SNOC x2 (... (SNOC x<n> xy) ...))) ...)))
    -----------------------------------------------------------------------------
    %
    let snoc_cons =
      let lhs = itlist mk_snoc xs (itlist mk_cons ys xy) in
      let rhs = itlist mk_cons ys (itlist mk_snoc xs xy) in
      let goal = list_mk_forall (xs@ys@[xy], mk_eq (lhs,rhs)) in
      PROVE (goal, REWRITE_TAC (snoc_nil.thms)) in
    %
    -----------------------------------------------------------------------------
    Prepend those theorems to the list of theorems.
    -----------------------------------------------------------------------------
    %
    snoc_cons . ( snoc_nil . thms ) in
  let snoc_thm_table = itlist mk_snoc_thms [16;8;4] (CONJUNCTS SNOC) in
  PURE_REWRITE_CONV snoc_thm_table;;


%
-------------------------------------------------------------------------------
SNOC_OF_CONS_CONV : term -> thm

Synopsis:

Converts a list from CONS form to SNOC form.

Description:

If x is a term representing a list constructed with CONS, then
SNOC_OF_CONS_CONV x returns a theorem equating that x to a list constructed
with SNOC.  Only the top-level CONSes are converted into SNOCs; elements of
the list that are themselves lists are left unchanged.

Failure:

Fails if the term is not a list constructed with CONS.

Examples:

#SNOC_OF_CONS_CONV "[1;2;3]";;
|- [1;2;3] = SNOC 3(SNOC 2(SNOC 1[]))

#SNOC_OF_CONS_CONV "[[3;4];[1;2;3]]";;
|- [[3;4];[1;2;3]] = SNOC[1;2;3](SNOC[3;4][])
-------------------------------------------------------------------------------
%

let SNOC_OF_CONS_CONV tm =
  let elements, ty = dest_list tm in
  let nums = upto (length elements) in
  let names = map (\n. mk_var (`t`^(string_of_int n), ty)) nums in
  let cons_template = mk_list (names,ty) in
  letrec mk_snoc l = if l = [] then "[]: ^ty list" else
    mk_binary_comb "SNOC: ^ty -> ^ty list -> ^ty list" (hd l) (mk_snoc(tl l)) in
  let snoc_template = mk_snoc (rev names) in
  let gl = mk_eq (cons_template, snoc_template) in
  let thm = PROVE (gl, REWRITE_TAC [SNOC]) in
  SPECL elements (GEN_ALL thm);;


%
-------------------------------------------------------------------------------
LENGTH_COMPARE_CONV : term -> conv

Synopsis:

Given a numeric comparison operator, checks that a term is that kind of
comparison between the lengths of two lists, and returns the true relationship
between the lengths of the lists.

Description:

Given a term containing a 2-ary operator on nums (like < or =), and a term
containing a expression in which that operator is applied to the lengths of
two lists, returns a theorem stating that the actual relationship between
the lengths of the lists is true.

Examples:

#LENGTH_COMPARE_CONV "<" "LENGTH [3;4;4] < LENGTH [1;2;3;4;5]";;
|- (LENGTH[3;4;4]) < (LENGTH[1;2;3;4;5]) = T

#LENGTH_COMPARE_CONV "<" "LENGTH [3;4;4] < LENGTH [1;2]";;
|- (LENGTH[3;4;4]) > (LENGTH[1;2]) = T

Failure:

Fails if the second term is not the expected operation on the lengths of two
lists.

See also:

COMPARE_xx_RULE, LENGTH_xx_CONV.
-------------------------------------------------------------------------------
%

let LENGTH_COMPARE_CONV =
  let length_eq_basecase =
    PROVE (
      "(LENGTH ([]: * list) = LENGTH ([]: ** list)) = T",
      REWRITE_TAC [LENGTH]) in
  let length_eq_unfold_1 =
    PROVE (
      "! x_hd y_hd (x_tl: * list) (y_tl: ** list).
      ((LENGTH x_tl = LENGTH y_tl) = T) ==>
      ((LENGTH (CONS x_hd x_tl) = LENGTH (CONS y_hd y_tl)) = T)",
      REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LENGTH]) in
  let length_lt_basecase =
    PROVE (
      "! y_hd (x_tl: * list) (y_tl: ** list).
      ((LENGTH x_tl = LENGTH y_tl) = T) ==>
      ((LENGTH x_tl < LENGTH (CONS y_hd y_tl)) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [LENGTH; LESS_SUC_REFL]) in
  let length_lt_unfold_1 =
    PROVE (
      "! y_hd (x_tl: * list) (y_tl: ** list).
      ((LENGTH x_tl < LENGTH y_tl) = T) ==>
      ((LENGTH x_tl < LENGTH (CONS y_hd y_tl)) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [LENGTH] THEN
      IMP_RES_TAC LESS_SUC) in
  let length_gt_basecase =
    PROVE (
      "! x_hd (x_tl: * list) (y_tl: ** list).
      ((LENGTH x_tl = LENGTH y_tl) = T) ==>
      ((LENGTH (CONS x_hd x_tl) > LENGTH y_tl) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [LENGTH; GREATER; LESS_SUC_REFL]) in
  let length_gt_unfold_1 =
    PROVE (
      "! x_hd (x_tl: * list) (y_tl: ** list).
      ((LENGTH x_tl > LENGTH y_tl) = T) ==>
      ((LENGTH (CONS x_hd x_tl) > LENGTH y_tl) = T)",
      REWRITE_TAC [LENGTH; GREATER] THEN
      REPEAT STRIP_TAC THEN
      IMP_RES_TAC LESS_SUC) in
  \ tm.
  (
  let length_xs_tm, length_ys_tm = (rand # I) (dest_comb tm) in
  let x_length, xs_tm = dest_comb length_xs_tm in
  let y_length, ys_tm = dest_comb length_ys_tm in
  if not (fst (dest_const x_length) = `LENGTH`) then fail else
  if not (fst (dest_const y_length) = `LENGTH`) then fail else
  let x_tms, x_type = dest_list xs_tm in
  let y_tms, y_type = dest_list ys_tm in
  let basecase = INST_TYPE [x_type,":*";y_type,":**"] length_eq_basecase in
  letrec unfold_length_compare x_tms y_tms thm relation =
    if x_tms = [] & y_tms = [] then thm else
    if x_tms = [] then
      if relation = `=` then
        let thm' = SPEC (hd y_tms) (MATCH_MP length_lt_basecase thm) in
        unfold_length_compare [] (tl y_tms) thm' `<`
      else
        let thm' = SPEC (hd y_tms) (MATCH_MP length_lt_unfold_1 thm) in
        unfold_length_compare [] (tl y_tms) thm' `<`
    else if y_tms = [] then
      if relation = `=` then
        let thm' = SPEC (hd x_tms) (MATCH_MP length_gt_basecase thm) in
        unfold_length_compare (tl x_tms) [] thm' `>`
      else
        let thm' = SPEC (hd x_tms) (MATCH_MP length_gt_unfold_1 thm) in
        unfold_length_compare (tl x_tms) [] thm' `>`
    else
      let thm' = SPECL [hd x_tms; hd y_tms] (MATCH_MP length_eq_unfold_1 thm) in
      unfold_length_compare (tl x_tms) (tl y_tms) thm' `=` in
  unfold_length_compare (rev x_tms) (rev y_tms) basecase `=`
  ) ? failwith `LENGTH_COMPARE_CONV`;;


%
-------------------------------------------------------------------------------
COMPARE_EQ_RULE : thm -> thm
COMPARE_LT_RULE : thm -> thm
COMPARE_LE_RULE : thm -> thm
COMPARE_GT_RULE : thm -> thm
COMPARE_GE_RULE : thm -> thm

Description:

Given a theorem of the form |- (n op m) = T, where n and m are numbers and op
is "=", "<", or ">", returns a theorem of the form |- (n op' m) = b, where op'
is the relation in the rule's name, and b is "T" or "F".

Examples:

#GT_CONV "3 > 2";;
|- 3 > 2 = T

#COMPARE_LE_RULE it;;
|- 3 <= 2 = F

See also:

LENGTH_COMPARE_CONV, BASEN_COMPARE_CONV.
-------------------------------------------------------------------------------
%


let COMPARE_EQ_RULE =
  let lt_imp_not_eq =
    PROVE (
      "! n m. ((n < m) = T) ==> ((n = m) = F)",
      REWRITE_TAC [LESS_NOT_EQ]) in
  let gt_imp_not_eq =
    PROVE (
      "! n m. ((n > m) = T) ==> ((n = m) = F)",
      REWRITE_TAC [GREATER] THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      REWRITE_TAC [LESS_NOT_EQ]) in
  \ thm.
  ( let op = (fst o dest_const o rator o rator o fst o dest_eq o concl) thm in
    if op = `=` then
      thm
    else if op = `<` then
      MATCH_MP lt_imp_not_eq thm
    else if op = `>` then
      MATCH_MP gt_imp_not_eq thm
    else fail
  ) ? failwith `COMPARE_EQ_RULE`;;

let COMPARE_LT_RULE =
  let eq_imp_not_lt =
    PROVE (
      "! n m. ((n = m) = T) ==> ((n < m) = F)",
      REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_NOT_EQ) in
  let gt_imp_not_lt =
    PROVE (
      "! n m. ((n > m) = T) ==> ((n < m) = F)",
      REWRITE_TAC [GREATER; NOT_LESS_AND_GREATER]) in
  \ thm.
  ( let op = (fst o dest_const o rator o rator o fst o dest_eq o concl) thm in
    if op = `=` then
      MATCH_MP eq_imp_not_lt thm
    else if op = `<` then
      thm
    else if op = `>` then
      MATCH_MP gt_imp_not_lt thm
    else fail
  ) ? failwith `COMPARE_LT_RULE`;;

let COMPARE_LE_RULE =
  let eq_imp_le =
    PROVE (
      "! n m: num. ((n = m) = T) ==> ((n <= m) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [LESS_OR_EQ]) in
  let lt_imp_le =
    PROVE (
      "! n m. ((n < m) = T) ==> ((n <= m) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [LESS_OR_EQ]) in
  let gt_imp_not_le =
    PROVE (
      "! n m. ((n > m) = T) ==> ((n <= m) = F)",
      REWRITE_TAC [GSYM NOT_LESS; GREATER]) in
  \ thm.
  ( let op = (fst o dest_const o rator o rator o fst o dest_eq o concl) thm in
    if op = `=` then
      MATCH_MP eq_imp_le thm
    else if op = `<` then
      MATCH_MP lt_imp_le thm
    else if op = `>` then
      MATCH_MP gt_imp_not_le thm
    else fail
  ) ? failwith `COMPARE_LE_RULE`;;

let COMPARE_GT_RULE =
  let eq_imp_not_gt =
    PROVE (
      "! n m. ((n = m) = T) ==> ((n > m) = F)",
      REWRITE_TAC [GREATER] THEN
      REPEAT GEN_TAC THEN
      DISCH_TAC THEN
      ASM_REWRITE_TAC [LESS_REFL]) in
  let lt_imp_not_gt =
    PROVE (
      "! n m. ((n < m) = T) ==> ((n > m) = F)",
      REWRITE_TAC [GREATER; NOT_LESS_AND_GREATER]) in
  \ thm.
  ( let op = (fst o dest_const o rator o rator o fst o dest_eq o concl) thm in
    if op = `=` then
      MATCH_MP eq_imp_not_gt thm
    else if op = `<` then
      MATCH_MP lt_imp_not_gt thm
    else if op = `>` then
      thm
    else fail
  ) ? failwith `COMPARE_GT_RULE`;;

let COMPARE_GE_RULE =
  let eq_imp_ge =
    PROVE (
      "! n m: num. ((n = m) = T) ==> ((n >= m) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [GREATER_OR_EQ]) in
  let lt_imp_not_ge =
    PROVE (
      "! n m. ((n < m) = T) ==> ((n >= m) = F)",
      REWRITE_TAC [GREATER_EQ; GSYM NOT_LESS; GREATER]) in
  let gt_imp_ge =
    PROVE (
      "! n m. ((n > m) = T) ==> ((n >= m) = T)",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [GREATER_OR_EQ]) in
  \ thm.
  ( let op = (fst o dest_const o rator o rator o fst o dest_eq o concl) thm in
    if op = `=` then
      MATCH_MP eq_imp_ge thm
    else if op = `<` then
      MATCH_MP lt_imp_not_ge thm
    else if op = `>` then
      MATCH_MP gt_imp_ge thm
    else fail
  ) ? failwith `COMPARE_GE_RULE`;;


%
-------------------------------------------------------------------------------
LENGTH_EQ_CONV : conv
LENGTH_LT_CONV : conv
LENGTH_LE_CONV : conv
LENGTH_GT_CONV : conv
LENGTH_GE_CONV : conv

Synopsis:

Given a term of the form "LENGTH [...] op LENGTH [...]", where op is the
comparison operation in the name of the conversion, returns a theorem of the
form |- (LENGTH [...] op LENGTH [...]) = b, where b is "T" or "F".

Examples:

#LENGTH_EQ_CONV "LENGTH [1;2;3] = LENGTH [2,3;2,3;2,3]";;
|- (LENGTH[1;2;3] = LENGTH[2,3;2,3;2,3]) = T

#LENGTH_GE_CONV "LENGTH [1;2] >= LENGTH [2,3;2,3;2,3]";;
|- (LENGTH[1;2]) >= (LENGTH[2,3;2,3;2,3]) = F

See also:

LENGTH_COMPARE_CONV.
-------------------------------------------------------------------------------
%

let LENGTH_EQ_CONV tm =
  ( COMPARE_EQ_RULE o LENGTH_COMPARE_CONV o (assert is_eq) ) tm
  ? failwith `LENGTH_EQ_CONV`;;


let is_lt tm = (rator o rator) tm = "<";;

let LENGTH_LT_CONV tm =
  ( COMPARE_LT_RULE o LENGTH_COMPARE_CONV o (assert is_lt) ) tm
  ? failwith `LENGTH_LT_CONV`;;


let is_le tm = (rator o rator) tm = "<=";;

let LENGTH_LE_CONV tm =
  ( COMPARE_LE_RULE o LENGTH_COMPARE_CONV o (assert is_le) ) tm
  ? failwith `LENGTH_LE_CONV`;;


let is_gt tm = (rator o rator) tm = ">";;

let LENGTH_GT_CONV tm =
  ( COMPARE_GT_RULE o LENGTH_COMPARE_CONV o (assert is_gt) ) tm
  ? failwith `LENGTH_GT_CONV`;;


let is_ge tm = (rator o rator) tm = ">=";;

let LENGTH_GE_CONV tm =
  ( COMPARE_GE_RULE o LENGTH_COMPARE_CONV o (assert is_ge) ) tm
  ? failwith `LENGTH_GE_CONV`;;


%
-------------------------------------------------------------------------------
fast_num_CONV : conv

Synopsis:

Given a term of the form "n" where n is a numeric constant greater than 0,
return the theorem: |- n = SUC m

Notes:

Once numerals are integrated, this function will be internal to the numeral
library, since it deals with numeric constants.
-------------------------------------------------------------------------------
%

let fast_num_CONV =
  let fast_num_CONV_table =
    map (num_CONV o term_of_int) (upto (max_radix * max_radix)) in
  \x_tm. ( el (int_of_term x_tm) fast_num_CONV_table ) ? num_CONV x_tm;;


%
-------------------------------------------------------------------------------
fast_GT_CONV

Given a term of the form "n > m" where both n and m are numeric constants,
return a theorem saying whether that is true or false.
-------------------------------------------------------------------------------
%

let fast_GT_CONV =
  %
  -----------------------------------------------------------------------------
  Prove two theorems needed in fast_GT_CONV.
  -----------------------------------------------------------------------------
  %
  let gt_not_refl =
    PROVE (
      "! x. x > x = F",
      REWRITE_TAC [GREATER;LESS_REFL]) in
  let gt_antisym =
    PROVE (
      "! x y. (y > x = T) ==> (x > y = F)",
      REWRITE_TAC [GREATER;NOT_LESS_AND_GREATER]) in
  %
  -----------------------------------------------------------------------------
  Create a lookup table for doing GT_CONV quickly.
  -----------------------------------------------------------------------------
  %
  let fast_GT_CONV_table =
    let row_init_lemma =
      PROVE (
        "! x y. (x = SUC y) ==> (x > y = T)",
        ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
        REWRITE_TAC [GREATER; EQ_LESS]) in
    let row_next_lemma =
      PROVE (
        "! y y'. (y = SUC y') ==> ! x. (x > y = T) ==> (x > y' = T)",
        REPEAT GEN_TAC THEN
        REWRITE_TAC [GREATER] THEN
        ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
        DISCH_TAC THEN
        IMP_RES_TAC EQ_LESS THEN
        GEN_TAC THEN
        UNDISCH_TAC "y' < y" THEN
        DISCH_THEN (\t1.
          DISCH_THEN (\t2.
            ASSUME_TAC (CONJ t1 (SPEC_ALL t2)))) THEN
        UNDISCH_TAC "y' < y /\ y < x" THEN REWRITE_TAC [LESS_TRANS]) in
    letrec extend_row y prev_column =
      let this_column =
        let step_lemma =
          MATCH_MP row_next_lemma (fast_num_CONV (term_of_int y)) in
        MATCH_MP step_lemma prev_column in
      if y = 1 then
        [this_column]
      else
        append (extend_row (y-1) this_column) [this_column] in
    let mk_row x =
      let final_column =
        MATCH_MP row_init_lemma (fast_num_CONV (term_of_int x)) in
      if x = 1 then [final_column] else
      append (extend_row (x-1) final_column) [final_column] in
    map mk_row (upto max_radix) in
  %
  -----------------------------------------------------------------------------
  Use the lookup table if possible, and fall back on GT_CONV otherwise.
  -----------------------------------------------------------------------------
  %
  \ tm.
  ( if not (rator (rator tm)) = "$>" then fail else
    let x_tm = rand (rator tm) in
    let y_tm = rand tm in
    let x = int_of_term x_tm in
    let y = int_of_term y_tm in
    if x = y then
      SPEC x_tm gt_not_refl
    else if x > y & x < (max_radix + 1) then
      el (y+1) (el x fast_GT_CONV_table)
    else if x < y & y < (max_radix + 1) then
      MP (SPECL [x_tm; y_tm] gt_antisym) (el (x+1) (el y fast_GT_CONV_table))
    else
      GT_CONV tm
  ) ? failwith `fast_GT_CONV`;;


%
-------------------------------------------------------------------------------
fast_LT_CONV

Given a term of the form "n < m" where both n and m are numeric constants,
return a theorem saying whether that is true or false.
-------------------------------------------------------------------------------
%

let fast_LT_CONV =
  let lt_not_refl =
    PROVE (
      "! x. x < x = F",
      REWRITE_TAC [LESS_REFL]) in
  \ tm.
  ( if not (rator (rator tm)) = "$<" then fail else
    let x_tm = rand (rator tm) in
    let y_tm = rand tm in
    let x = int_of_term x_tm in
    let y = int_of_term y_tm in
    let gt_tm = mk_binary_comb "$>" y_tm x_tm in
    if x = y then
      SPEC x_tm lt_not_refl
    else
      SUBS [SPECL [y_tm; x_tm] GREATER] (fast_GT_CONV gt_tm)
  ) ? failwith `fast_LT_CONV`;;


%
-------------------------------------------------------------------------------
mk_basen : term -> term list -> term
dest_basen : term -> (term # term)
is_basen : term -> bool

Synopsis:

These functions are convenient for building, checking for, and taking apart
terms describing BASEN numerals.

Description:

Given a term containing a numeric constant to be used as a radix, and a list
of terms to be taken as the digits, mk_basen constructs a term containing a
BASEN numeral in that radix with those digits.  Given a term containing such
a BASEN numeral, dest_base returns a term containing the radix and a term
containing the list of digits.  (Note that the two are not exactly symmetric,
in that mk_basen takes a list of digit terms, and dest_basen returns a single
term of the digit list.)  Given a term, is_basen returns true if the term is
a BASEN numeral, and returns false otherwise.

Failure:

dest_basen fails if the term is not a BASEN numeral.  mk_basen fails if the
terms are of the wrong types.
-------------------------------------------------------------------------------
%

let mk_basen r_tm digit_tms =
  mk_comb ( mk_comb ("BASEN", r_tm), mk_list (digit_tms, ": num"));;

let dest_basen basen_r_x =
  (dest_binary_comb "BASEN" basen_r_x) ? failwith `dest_basen`;;

let is_basen basen_r_x =
  (dest_basen basen_r_x; true) ? false;;


%
-------------------------------------------------------------------------------
dest_unary_basen_comb : term ->
   (term # term # term # term # term list)
dest_binary_basen_comb : term ->
   (term # term # term # term # term list # term # term # term list)

Synopsis:

Takes apart a term containing an operation on BASEN numerals, and returns the
parts.

Description:

Given a term containing an operation applied to one (for the `unary` variant)
or two (for the `binary` variant) BASEN numerals, returns the operation, the
radix of the two numerals, the numerals themselves, and the numerals' digits
(in two forms).

Examples:

#dest_binary_basen_comb "$*" "BASEN 10 [2;3;4] * BASEN 10 [6;7;8;9]";;
("10",
 "BASEN 10[2;3;4]",
 "[2;3;4]",
 ["2"; "3"; "4"],
 "BASEN 10[6;7;8;9]",
 "[6;7;8;9]",
 ["6"; "7"; "8"; "9"])
: (term # term # term # term list # term # term # term list)

Failure:

The binary form fails if the numerals have different radices.
-------------------------------------------------------------------------------
%

let dest_unary_basen_comb basen_comb =
  ( let op, basen_r_x = dest_comb basen_comb in
    let r_tm, xs_tm = dest_basen basen_r_x in
    let x_tms = fst (dest_list xs_tm) in
      (op, r_tm, basen_r_x, xs_tm, x_tms)
  ) ? failwith `dest_unary_basen_comb`;;

let dest_binary_basen_comb basen_comb =
  ( let (op, basen_r_x), basen_r_y = (dest_comb # I) (dest_comb basen_comb) in
    let r_tm, xs_tm = dest_basen basen_r_x in
    let r2_tm, ys_tm = dest_basen basen_r_y in
    let x_tms = fst (dest_list xs_tm) in
    let y_tms = fst (dest_list ys_tm) in
    if r_tm = r2_tm then
      (op, r_tm, basen_r_x, xs_tm, x_tms, basen_r_y, ys_tm, y_tms)
    else fail
  ) ? failwith `dest_binary_basen_comb`;;


%
-------------------------------------------------------------------------------
basen_of_int : (int # int) -> term

Synopsis:

Given a radix and a value, returns a term containing a BASEN numeral in that
radix, with that value.

Description:

If r and n are ints, and r is at least 2, and n is positive, then
basen_of_int r n returns the term containing the canonical BASEN numeral in
that radix, of that value.

Failure:

The radix must have a value of at least 2, and n must be positive.

Examples:

#basen_of_int (10, 34567);;
"BASEN 10[3;4;5;6;7]" : term

#basen_of_int (2, 23);;
"BASEN 2[1;0;1;1;1]" : term

#basen_of_int (16, 3072);;
"BASEN 16[12;0;0]" : term

See also:

mk_basen, BASEN_OF_NUM_CONV, int_of_basen.
-------------------------------------------------------------------------------
%

letrec numeral_of_int (r, n) =
  if n < 0 then fail else
  let mod x y = x - (y * (x / y)) in
  if n = 0 then
    []
  else if n < r then
    [n]
  else
    append (numeral_of_int (r, (n / r))) [mod n r];;

let basen_of_numeral (r, xs) =
  ( let r_tm = term_of_int r in
    let x_tms = map term_of_int xs in
    mk_basen r_tm x_tms
  ) ? failwith `basen_of_numeral`;;

let basen_of_int (r, n) =
  ( basen_of_numeral (r, numeral_of_int (r,n)) ) ? failwith `basen_of_int`;;


%
-------------------------------------------------------------------------------
int_of_basen : term -> int

Synopsis:

Given a term containing a BASEN numeral, return the value of that numeral.

Description:

If r is an int and n is an int list, then int_of_basen "BASEN r n" returns
the value of the base-r numeral with digits n.

Failure:

None.

Examples:

#int_of_basen "BASEN 10[3;4;5;6;7]";;
34567 : int

#int_of_basen "BASEN 2[1;0;1;1;1]";;
23 : int

#int_of_basen "BASEN 16[12;0;0]";;
3072 : int

See also:

dest_basen, BASEN_CONV, basen_of_int.
-------------------------------------------------------------------------------
%

let numeral_of_basen basen_r_x =
  ( let r_tm, xs_tm = dest_basen basen_r_x in
    let x_tms = fst (dest_list xs_tm) in
    let r = int_of_term r_tm in
    let xs = map int_of_term x_tms in
    (r, xs)
  ) ? failwith `numeral_of_basen`;;

letrec int_of_numeral (r, digits) =
  if digits = [] then
    0
  else
    r * (int_of_numeral (r, (butlast digits))) + (last digits);;

let int_of_basen =
  ( int_of_numeral o numeral_of_basen ) ? failwith `int_of_basen`;;


%
-------------------------------------------------------------------------------
IS_BASEN_CONV : conv

Synopsis:

Proves that a numeral's digits are or are not all less than its radix.

Description:

If r is a radix and m is a list of radix-r digits (that is, each digit is less
than r), then IS_BASEN_CONV "IS_BASEN r m" returns the theorem:

        |- IS_BASEN r m = T

and if one or more digits of m is not a radix-r digit (that is, if some digit
in m is equal to or greater than r), then IS_BASEN_CONV "IS_BASEN r m"
returns the theorem:

        |- IS_BASEN r m = F

Failure:

The argument to IS_BASEN_CONV must be of the form "IS_BASEN r [...]", and the
radix must be a numeric constant that is at least 2, and all elements of the
digit list must be numeric constants.

Examples:

#IS_BASEN_CONV "IS_BASEN 10 [2;3;5;0]";;
|- IS_BASEN 10 [2;3;5;0] = T

#IS_BASEN_CONV "IS_BASEN 10 [2;3;15;0]";;
|- IS_BASEN 10 [2;3;15;0] = F

#IS_BASEN_CONV "IS_BASEN 16 [2;3;15;0]";;
|- IS_BASEN 16 [2;3;15;0] = F

See also:

IS_NORMALIZED_CONV, BASEN_NORMALIZE_CONV.
-------------------------------------------------------------------------------
%

let IS_BASEN_CONV =
  let is_basen_basecase =
    PROVE (
      "! r. IS_BASEN r [] = T",
      REWRITE_TAC [IS_BASEN_NIL]) in
  let is_basen_unfold_1 =
    PROVE (
      "! r e.
        (e < r = T) ==>
        ! l. (IS_BASEN r l = T) ==>
        (IS_BASEN r (CONS e l) = T)",
      REWRITE_TAC [IS_BASEN; ALL_EL; GREATER] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]) in
  let isnt_basen_basecase =
    PROVE (
      "! r e l.
        (e < r = F) ==>
        (IS_BASEN r (CONS e l) = F)",
      REWRITE_TAC [IS_BASEN; ALL_EL; GREATER] THEN
      REPEAT STRIP_TAC THEN RES_TAC) in
  let isnt_basen_unfold_1 =
    PROVE (
      "! r e l.
        (IS_BASEN r l = F) ==>
        (IS_BASEN r (CONS e l) = F)",
      REWRITE_TAC [IS_BASEN; ALL_EL; GREATER] THEN
      REPEAT STRIP_TAC THEN RES_TAC) in
  %
  Define a function to prove that a numeral IS_BASEN.
  %
  letrec prove_is_basen r_tm digit_tms digit_thms =
    if length digit_tms = 0 then SPEC r_tm is_basen_basecase else
    let step =
      MP (SPECL [r_tm;hd digit_tms] is_basen_unfold_1) (hd digit_thms) in
    MATCH_MP step (prove_is_basen r_tm (tl digit_tms) (tl digit_thms))
  in
  %
  Define a function to prove that a numeral isn't IS_BASEN.
  %
  letrec prove_isnt_basen r_tm digit_tms digit_thms =
    let digit = hd digit_tms in
    let thm = hd digit_thms in
    if (rand o concl o hd) digit_thms = "F" then
      let digit_list = mk_list (tl digit_tms, ": num") in
        MP (SPECL [r_tm; digit; digit_list] isnt_basen_basecase) thm
    else
      let step =
        SPECL [r_tm;digit] isnt_basen_unfold_1 in
      MATCH_MP step (prove_isnt_basen r_tm (tl digit_tms) (tl digit_thms))
  in
  %
  Take apart the numeral to get its digits.
  Then prove theorems comparing each digit to the radix.
  Then check the legality of the digits, and either
    prove that it is or prove that it isn't IS_BASEN.
  %
  \ tm.
  (
  let (is_basen, r_tm), digits_tm = (dest_comb # I) (dest_comb tm) in
  if not (is_basen = "IS_BASEN") then fail else
  let digit_tms = fst (dest_list digits_tm) in
  let prove_lt_radix digit_tm =
    fast_LT_CONV (mk_binary_comb "$<" digit_tm r_tm) in
  let digit_thms = map prove_lt_radix digit_tms in
  let digit_okay digit_thm = rand (concl digit_thm) = "T" in
  if forall digit_okay digit_thms then
    prove_is_basen r_tm digit_tms digit_thms
  else
    prove_isnt_basen r_tm digit_tms digit_thms
  ) ? failwith `IS_BASEN_CONV`;;


%
-------------------------------------------------------------------------------
IS_NORMALIZED_CONV : conv

Synopsis:

Proves that a list of digits is normalized (that is, that it has no leading
zeros).

Description:

If m is a list of digits, and m is empty or the first digit of m is nonzero,
then IS_NORMALIZED_CONV "m" returns the theorem:

        |- IS_NORMALIZED m = T

and if the first digit of m is zero, then IS_NORMALIZED_CONV "m" returns the
theorem:

        |- IS_NORMALIZED m = F

Failure:

The argument to IS_NORMALIZED_CONV must be a list of type num list, and either
the list must be empty or the first element must be a numeric constant added
with CONS.

Examples:

#IS_NORMALIZED_CONV "IS_NORMALIZED [2;3;5;0]";;
|- IS_NORMALIZED [2;3;5;0] = T

#IS_NORMALIZED_CONV "IS_NORMALIZED [0;2;3;5;0]";;
|- IS_NORMALIZED [0;2;3;5;0] = F

#IS_NORMALIZED_CONV "IS_NORMALIZED []";;
|- IS_NORMALIZED [] = T

See also:

IS_BASEN_CONV, BASEN_NORMALIZE_CONV.
-------------------------------------------------------------------------------
%

let IS_NORMALIZED_CONV =
  let basen_is_normalized_nil =
    PROVE (
      "IS_NORMALIZED [] = T",
      REWRITE_TAC [IS_NORMALIZED_NIL]) in
  \ tm.
  ( let xs_tm = dest_unary_comb "IS_NORMALIZED" tm in
    if xs_tm = "[]: num list" then
      basen_is_normalized_nil
    else
      let head, tail = dest_cons xs_tm in
      let result = fast_LT_CONV (mk_comb ("$< 0", head)) in
      SUBS [result] (SPECL [head; tail] IS_NORMALIZED_CONS)
  ) ? failwith `IS_NORMALIZED_CONV`;;


%
-------------------------------------------------------------------------------
ONCE_BASEN_NORMALIZE_CONV : conv
BASEN_NORMALIZE_CONV : conv

Synopsis:

Proves that a numeral is equal to itself with leading zeros removed.

Description:

If m is a list of base-r digits including some leading zeros, and n is the same
list with leading zeros removed, then BASEN_NORMALIZE_CONV "BASEN r m" returns
the theorem:

        |- BASEN r m = BASEN r n

and ONCE_BASEN_NORMALIZE_CONV returns a similar theorem, but with only the one
leading zero removed.

Failure:

Both fail if the argument is already normalized.  (The compound conversion
REPEATC ONCE_BASEN_NORMALIZE_CONV can be used to normalize without failure.)
The argument must be of the form "BASEN r [...]", and the radix must be a
numeric constant with a value of at least 2, and all elements of the digit list
must be numeric constants less than the radix.


Examples:

#BASEN_NORMALIZE_CONV "BASEN 16 [0;12;0;0]";;
|- BASEN 16 [0;12;0;0] = BASEN 16 [12;0;0]

#BASEN_NORMALIZE_CONV "BASEN 16 [0;0;0;0;3]";;
|- BASEN 16 [0;0;0;0;3] = BASEN 16 [3]

#BASEN_NORMALIZE_CONV "BASEN 8 [7;7;5;3;4]";;
|- BASEN 8 [7;7;5;3;4] = BASEN 8 [7;7;5;3;4]

See also:

IS_NORMALIZED_CONV, IS_BASEN_CONV, BASEN_DENORMALIZE_CONV.
-------------------------------------------------------------------------------
%

let ONCE_BASEN_NORMALIZE_CONV basen_x =
  let r_tm, xs_tm = dest_basen basen_x in
  let hd_x, tl_xs = dest_cons xs_tm in
  if hd_x = "0" then
    SPECL [r_tm; tl_xs] BASEN_CONS_0
  else
    fail;;

let BASEN_NORMALIZE_CONV =
  CHANGED_CONV (REPEATC ONCE_BASEN_NORMALIZE_CONV);;


%
-------------------------------------------------------------------------------
BASEN_DENORMALIZE_CONV : conv

Synopsis:

Proves that a numeral is equal to itself with additional leading zeros added.

Description:

If m is a list of base-r digits, and n is a non-negative integer, and p is the
same list as m but with n leading zeros added, then BASEN_DENORMALIZE_CONV n
"BASEN r m" returns the theorem:

        |- BASEN r m = BASEN r p

Failure:

The term argument to BASEN_DENORMALIZE_CONV must be of the form
"BASEN r [...]".


Examples:

#BASEN_DENORMALIZE_CONV 2 "BASEN 16 [12;0;0]";;
|- BASEN 16 [12;0;0] = BASEN 16 [0;0;12;0;0]

#BASEN_DENORMALIZE_CONV (-2) "BASEN 16 [3]";;
|- BASEN 16 [3] = BASEN 16 [3]

#BASEN_DENORMALIZE_CONV 0 "BASEN 8 [7;7;5;3;4]";;
|- BASEN 8 [7;7;5;3;4] = BASEN 8 [7;7;5;3;4]

See also:

IS_NORMALIZED_CONV, IS_BASEN_CONV, BASEN_NORMALIZE_CONV.
-------------------------------------------------------------------------------
%

let ONCE_BASEN_DENORMALIZE_CONV =
  PURE_ONCE_REWRITE_CONV [GSYM BASEN_CONS_0];;

let BASEN_DENORMALIZE_CONV n =
  funpow n ($THENC ONCE_BASEN_DENORMALIZE_CONV) ALL_CONV;;


%
-------------------------------------------------------------------------------
BASEN_COMPARE_CONV : conv

Synopsis:

Given a comparison of two numerals, returns a theorem relating their values
with "<", ">", or "=".

Description:

Given a term of the form "BASEN r [...] op BASEN r [...]", returns a theorem
of the form
        |- ( BASEN r [...] ?? BASEN r [...] ) = T
where ?? is "<" or ">" or "=".  Note that op from the input term is ignored.

Examples:

#BASEN_COMPARE_CONV "BASEN 10 [1;2;3] < BASEN 10 [3;4;5]";;
|- (BASEN 10[1;2;3]) < (BASEN 10[3;4;5]) = T

#BASEN_COMPARE_CONV "BASEN 10 [7;8;9] < BASEN 10 [3;4;5]";;
|- (BASEN 10[7;8;9]) > (BASEN 10[3;4;5]) = T

Failures:

Fails if the numerals' radices are different, or if any element of either
list is not a numeric constant, or is not less than the radix, or if the
radix is 0 or 1.

See also:

BASEN_EQ_CONV, BASEN_LT_CONV, BASEN_LE_CONV, BASEN_GT_CONV, BASEN_GE_CONV.
-------------------------------------------------------------------------------
%

let BASEN_COMPARE_CONV =
  let basen_eq_basecase =
    PROVE (
      "! r x. ((BASEN r x) = (BASEN r x)) = T",
      REWRITE_TAC []) in
  let basen_lt_basecase =
    PROVE (
      "! r x_hd y_hd x_tl y_tl.
        ((x_hd < y_hd) = T) ==>
        ((1 < r) = T) ==>
        (IS_BASEN r x_tl = T) ==>
        (IS_BASEN r y_tl = T) ==>
        ((LENGTH x_tl = LENGTH y_tl) = T) ==>
        ( ((BASEN r (CONS x_hd x_tl)) < (BASEN r (CONS y_hd y_tl)) = T) /\
          ((LENGTH (CONS x_hd x_tl) = LENGTH (CONS y_hd y_tl)) = T) )",
      REWRITE_TAC [BASEN; LENGTH] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
      EXISTS_TAC "((SUC x_hd) * (r EXP (LENGTH (y_tl: num list))))" THEN
      CONJ_TAC THENL
      [
        IMP_RES_TAC BASEN_LESS_EXP_LENGTH THEN
        UNDISCH_TAC "(BASEN r x_tl) < (r EXP (LENGTH x_tl))" THEN
        ASM_REWRITE_TAC [MULT;ADD_MONO_LESS]
      ;
        MATCH_MP_TAC ADDR_GREATER_EQ THEN
        UNDISCH_TAC "x_hd < y_hd" THEN
        REWRITE_TAC [LESS_EQ; LESS_MONO_MULT]
      ]) in
  let basen_lt_unfold_1 =
    PROVE (
      "! r x_hd x_tl y_tl.
        ( ((BASEN r x_tl) < (BASEN r y_tl) = T) /\
          ((LENGTH x_tl = LENGTH y_tl) = T) ) ==>
        ( ((BASEN r (CONS x_hd x_tl)) < (BASEN r (CONS x_hd y_tl)) = T) /\
          ((LENGTH (CONS x_hd x_tl) = LENGTH (CONS x_hd y_tl)) = T) )",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [BASEN; ADD_MONO_LESS; LENGTH]) in
  let basen_gt_basecase =
    PROVE (
      "! r x_hd y_hd x_tl y_tl.
        ((x_hd > y_hd) = T) ==>
        ((1 < r) = T) ==>
        (IS_BASEN r x_tl = T) ==>
        (IS_BASEN r y_tl = T) ==>
        ((LENGTH x_tl = LENGTH y_tl) = T) ==>
        ( ((BASEN r (CONS x_hd x_tl)) > (BASEN r (CONS y_hd y_tl)) = T) /\
          ((LENGTH (CONS x_hd x_tl) = LENGTH (CONS y_hd y_tl)) = T) )",
      REWRITE_TAC [GREATER;BASEN;LENGTH] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
      EXISTS_TAC "((SUC y_hd) * (r EXP (LENGTH (y_tl: num list))))" THEN
      CONJ_TAC THENL
      [
        IMP_RES_TAC BASEN_LESS_EXP_LENGTH THEN
        UNDISCH_TAC "(BASEN r y_tl) < (r EXP (LENGTH y_tl))" THEN
        ASM_REWRITE_TAC [MULT;ADD_MONO_LESS]
        ;
        MATCH_MP_TAC ADDR_GREATER_EQ THEN
        UNDISCH_TAC "y_hd < x_hd" THEN
        REWRITE_TAC [LESS_EQ; LESS_MONO_MULT]
      ]) in
  let basen_gt_unfold_1 =
    PROVE (
      "! r x_hd x_tl y_tl.
        ( ((BASEN r x_tl) > (BASEN r y_tl) = T) /\
          ((LENGTH x_tl = LENGTH y_tl) = T) ) ==>
        ( ((BASEN r (CONS x_hd x_tl)) > (BASEN r (CONS x_hd y_tl)) = T) /\
          ((LENGTH (CONS x_hd x_tl) = LENGTH (CONS x_hd y_tl)) = T))",
      REWRITE_TAC [GREATER] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [BASEN; ADD_MONO_LESS; LENGTH]) in
  let basen_shorten_x_eq =
    PROVE (
      "! r x y. (((BASEN r (CONS 0 x)) = (BASEN r y)) = T) ==>
        (((BASEN r x) = (BASEN r y)) = T)",
      REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let basen_shorten_x_lt =
    PROVE (
      "! r x y. (((BASEN r (CONS 0 x)) < (BASEN r y)) = T) ==>
        (((BASEN r x) < (BASEN r y)) = T)",
      REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let basen_shorten_x_gt =
    PROVE (
      "! r x y. (((BASEN r (CONS 0 x)) > (BASEN r y)) = T) ==>
        (((BASEN r x) > (BASEN r y)) = T)",
      REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let basen_shorten_y_eq =
    PROVE (
      "! r x y. (((BASEN r x) = (BASEN r (CONS 0 y))) = T) ==>
        (((BASEN r x) = (BASEN r y)) = T)",
      REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let basen_shorten_y_lt =
    PROVE (
      "! r x y. (((BASEN r x) < (BASEN r (CONS 0 y))) = T) ==>
        (((BASEN r x) < (BASEN r y)) = T)",
      REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let basen_shorten_y_gt =
    PROVE (
      "! r x y. (((BASEN r x) > (BASEN r (CONS 0 y))) = T) ==>
        (((BASEN r x) > (BASEN r y)) = T)",
      REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  %
  Define a function to take two lists of the same length, and return three
  lists.  The first list returned is the prefix that was identical in the two
  input lists.  The other lists returned are the suffixes of the two input
  lists (and they are either empty, or differ in the first element).
  %
  letrec split_diffs xys x_tms y_tms =
    if x_tms = [] then
      (xys, [], [])
    else if (hd x_tms) = (hd y_tms) then
      split_diffs ((hd x_tms). xys) (tl x_tms) (tl y_tms)
    else
      (xys, x_tms, y_tms) in
  \ tm.
  ( let (op, r_tm, basen_r_x, xs_tm, x_tms, basen_r_y, ys_tm, y_tms) =
      dest_binary_basen_comb tm in
  %
  -----------------------------------------------------------------------------
  Compare the lengths of the numerals,
  remember which was shorter,
  zero-extend the shorter, and
  save the number of digits by which it was extended.
  -----------------------------------------------------------------------------
  %
  let x = length x_tms in
  let y = length y_tms in
  let x_shorter = x < y in
  let long_x_tms = lengthen "0" (y-x) x_tms in
  let long_y_tms = lengthen "0" (x-y) y_tms in
  let amount_lengthened = absolute_value (x-y) in
  %
  -----------------------------------------------------------------------------
  Define a rule that shortens the numeral in the result theorem back to the
  original length.
  -----------------------------------------------------------------------------
  %
  let shorten long_thm relation =
    let shorten_x, shorten_y =
      if relation = `=` then
        (basen_shorten_x_eq, basen_shorten_y_eq)
      else if relation = `<` then
        (basen_shorten_x_lt, basen_shorten_y_lt)
      else
        (basen_shorten_x_gt, basen_shorten_y_gt)
      in
    let shorten = MATCH_MP (if x_shorter then shorten_x else shorten_y) in
    funpow amount_lengthened shorten long_thm in
  %
  -----------------------------------------------------------------------------
  Find the most significant digit in which the numerals differ, and
  split the numerals into the initial digits that are identical in both,
  and the sublists that are different.
  -----------------------------------------------------------------------------
  %
  let xys, x_diffs, y_diffs =
    split_diffs [] long_x_tms long_y_tms in
  %
  -----------------------------------------------------------------------------
  If the numerals are the same, prove an equality theorem on the extended
  lists, then return a shortened form of that theorem.
  -----------------------------------------------------------------------------
  %
  if x_diffs = [] then
    let long_thm =
      SPECL [r_tm;mk_list (rev xys,": num")] basen_eq_basecase in
    shorten long_thm `=`
  else
  %
  -----------------------------------------------------------------------------
  Otherwise, the numerals are different.
  Prove theorems saying the sublists differ and their lengths are the same.
  -----------------------------------------------------------------------------
  %
  let hd_x_diff = hd x_diffs in
  let hd_y_diff = hd y_diffs in
  let tl_x_diffs = mk_list (tl x_diffs,": num") in
  let tl_y_diffs = mk_list (tl y_diffs,": num") in
  let mk_length tm = mk_comb ("LENGTH: num list -> num", tm) in
  let cons_tm = mk_binary_comb "CONS: num -> num list -> num list" in
  let x_diffs_tm = cons_tm hd_x_diff tl_x_diffs in
  let y_diffs_tm = cons_tm hd_y_diff tl_y_diffs in
  let relation =
    if int_of_term hd_x_diff < int_of_term hd_y_diff then `<` else `>` in
  let basen_ne_lemma =
    let comparison =
      mk_binary_comb "<" (mk_length tl_x_diffs) (mk_length tl_y_diffs) in
    if relation = `<` then
      ( (C MP (LENGTH_COMPARE_CONV comparison)) o
        (C MP (IS_BASEN_CONV (mk_binary_comb "IS_BASEN" r_tm tl_y_diffs))) o
        (C MP (IS_BASEN_CONV (mk_binary_comb "IS_BASEN" r_tm tl_x_diffs))) o
        (C MP (LT_CONV (mk_comb ("$< 1", r_tm)))) o
        (C MP (fast_LT_CONV (mk_binary_comb "<" hd_x_diff hd_y_diff))) o
        (SPECL [r_tm;hd_x_diff;hd_y_diff;tl_x_diffs;tl_y_diffs])
      ) basen_lt_basecase
    else
      ( (C MP (LENGTH_COMPARE_CONV comparison)) o
        (C MP (IS_BASEN_CONV (mk_binary_comb "IS_BASEN" r_tm tl_y_diffs))) o
        (C MP (IS_BASEN_CONV (mk_binary_comb "IS_BASEN" r_tm tl_x_diffs))) o
        (C MP (LT_CONV (mk_comb ("$< 1", r_tm)))) o
        (C MP (fast_GT_CONV (mk_binary_comb ">" hd_x_diff hd_y_diff))) o
        (SPECL [r_tm;hd_x_diff;hd_y_diff;tl_x_diffs;tl_y_diffs])
      ) basen_gt_basecase
    in
  %
  -----------------------------------------------------------------------------
  Repeatedly extend that theorem until it says the whole numerals differ.
  -----------------------------------------------------------------------------
  %
  let step_thm =
    if relation = `<` then
      SPEC r_tm basen_lt_unfold_1
    else
      SPEC r_tm basen_gt_unfold_1
    in
  letrec prove_basen_ne xys xs ys step_thm basen_ne_lemma =
    if xys = [] then basen_ne_lemma else
    let new_basen_ne_lemma =
      ( (C MP basen_ne_lemma) o
        (SPECL [hd xys; xs; ys])
      ) step_thm in
    let new_xys = tl xys in
    let new_xs = cons_tm (hd xys) xs in
    let new_ys = cons_tm (hd xys) ys in
    prove_basen_ne new_xys new_xs new_ys step_thm new_basen_ne_lemma in
  let long_thm = CONJUNCT1
    (prove_basen_ne xys x_diffs_tm y_diffs_tm step_thm basen_ne_lemma) in
  %
  -----------------------------------------------------------------------------
  Return the shortened theorem.
  -----------------------------------------------------------------------------
  %
  shorten long_thm relation
  ) ? failwith `BASEN_COMPARE_CONV`;;



%
-------------------------------------------------------------------------------
BASEN_EQ_CONV : conv
BASEN_LT_CONV : conv
BASEN_LE_CONV : conv
BASEN_GT_CONV : conv
BASEN_GE_CONV : conv

Synopsis:

Given a term comparing two numerals, returns a theorem saying whether the
comparison is true or false.

Description:

Given a term of the form "BASEN r [...] op BASEN r [...]", where op is the
relation in the name of the conversion, returns a theorem of the form
|- (BASEN r [...] op BASEN r [...]) = b, where b is "T" or "F".

Failure:

The argument must be of the expected form, and the radix of the two numerals
must be the same, and the radix must be a numeric constant that is at least
2, and all elements of the digit lists must be numeric constants, and must be
less than the radix.

Examples:

#BASEN_EQ_CONV "BASEN 10 [3;4;5] = BASEN 10 [3;4;5]";;
|- (BASEN 10 [3;4;5] = BASEN 10 [3;4;5]) = T

#BASEN_LT_CONV "BASEN 2 [1;1;1;1] < BASEN 2 [1;1;1;0]";;
|- (BASEN 2[1;1;1;1]) < (BASEN 2[1;1;1;0]) = F

#BASEN_GE_CONV "BASEN 16 [8;10;14] >= BASEN 16 [12;4]";;
|- (BASEN 16[8;10;14]) >= (BASEN 16[12;4]) = T

See also:

BASEN_COMPARE_CONV.
-------------------------------------------------------------------------------
%

let BASEN_EQ_CONV tm =
  ( COMPARE_EQ_RULE o BASEN_COMPARE_CONV o (assert is_eq) ) tm
  ? failwith `BASEN_EQ_CONV`;;


let BASEN_LT_CONV tm =
  ( COMPARE_LT_RULE o BASEN_COMPARE_CONV o (assert is_lt) ) tm
  ? failwith `BASEN_LT_CONV`;;


let BASEN_LE_CONV tm =
  ( COMPARE_LE_RULE o BASEN_COMPARE_CONV o (assert is_le) ) tm
  ? failwith `BASEN_LE_CONV`;;


let BASEN_GT_CONV tm =
  ( COMPARE_GT_RULE o BASEN_COMPARE_CONV o (assert is_gt) ) tm
  ? failwith `BASEN_GT_CONV`;;


let BASEN_GE_CONV tm =
  ( COMPARE_GE_RULE o BASEN_COMPARE_CONV o (assert is_ge) ) tm
  ? failwith `BASEN_GE_CONV`;;


%
-------------------------------------------------------------------------------
Define fast_add, which takes two ints, n and m, with nonnegative values, as
input and returns a theorem stating what their sum is.  Do it by table lookup
for small inputs (0 <= n <= (max_radix EXP 2) - 1, 0 <= m <= max_radix - 1).
-------------------------------------------------------------------------------
%

let fast_add =
  %
  -----------------------------------------------------------------------------
  Prove a lemma that will make creation of the lookup table much faster.
    |- ! n.
        (n +  0 = n) /\
        (n +  1 = (SUC n)) /\
        (n +  2 = (SUC (SUC n))) /\
        ...
        (n +  max_radix = (SUC (SUC (SUC ... n))))
  -----------------------------------------------------------------------------
  %
  let next_row_lemma =
    let add_a_row x (sucs_tm, tms) =
      let left_half = mk_comb ("$+ n", term_of_int x) in
      let right_half = mk_comb ("SUC", sucs_tm) in
      (right_half, (mk_eq (left_half, right_half)) . tms) in
    let goal = mk_forall ("n: num", list_mk_conj (rev (snd
      (rev_itlist add_a_row (upto max_radix) ("n: num", ["n + 0 = n"]))))) in
    let num_convs = map (num_CONV o term_of_int) (upto max_radix) in
    PROVE (goal,
      REWRITE_TAC (append num_convs [GSYM ADD_SUC;ADD_CLAUSES]) ) in
  %
  -----------------------------------------------------------------------------
  Create a lookup table, in which element (m+1) of element (n+1) of the table
  is the theorem |- n + m = <n+m>.
  -----------------------------------------------------------------------------
  %
  let fast_add_table =
    let get_seeds n =
      let f x = fast_num_CONV (term_of_int (x + n)) in
      map f (upto max_radix) in
    let mk_row n =
      let this_row_lemma = SPEC (term_of_int n) next_row_lemma in
      CONJUNCTS (rev_itlist (SUBS o listify o SYM) (get_seeds n) this_row_lemma) in
    map mk_row (zero_upto (max_radix * (max_radix-1))) in
  %
  -----------------------------------------------------------------------------
  Define the fast_add function to try a table lookup, and if that fails, to
  fall back on ADD_CONV.
  -----------------------------------------------------------------------------
  %
  \n m.
    ( el (m+1) (el (n+1) fast_add_table)
    ) ? ADD_CONV (mk_binary_comb "$+" (term_of_int n) (term_of_int m));;


%
-------------------------------------------------------------------------------
For any non-negative x y z, return the theorem |- <x+y+z> = <x> + <y> + <z>
and do it particularly fast if x and y are less than max_radix, and z <= 1.
-------------------------------------------------------------------------------
%

let fast_add_with_carry =
  %
  -----------------------------------------------------------------------------
  Given |- (<n> + <m>) + <c> = <p>
  prove |- (<SUC n)) + <m>) + <c> = <SUC p>
  -----------------------------------------------------------------------------
  %
  let next_in_row_lemma =
    PROVE (
      "! x y z sum. ((x + y) + z = sum) ==> (((SUC x) + y) + z = (SUC sum))",
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [GSYM (ONCE_REWRITE_RULE [ADD_SYM] ADD_SUC)]) in
  let prove_next_in_table n p base_thm step_thm =
    let next_thm = (MATCH_MP step_thm base_thm) in
    let add1 n = (SYM o fast_num_CONV o term_of_int) (n+1) in
    if n = p then
      SUBS_OCCS [[1;2], add1 p] next_thm
    else
      SUBS_OCCS [[1], add1 p; [1], add1 n] next_thm in
  %
  -----------------------------------------------------------------------------
  Given lim and |- (0 + <m>) + <c> = <p>
  prove         |- (0 + <m>) + <c> = <p>
  through       |- (<lim-1> + <m>) + <c> = <p+lim-1>
  -----------------------------------------------------------------------------
  %
  letrec mk_row lim thm =
    let n = (int_of_term o rand o rator o rand o rator o rand o rator o concl) thm in
    let p = (int_of_term o rand o concl) thm in
    if n < lim then
      let next_thm = prove_next_in_table n p thm next_in_row_lemma in
      thm . (mk_row lim next_thm)
    else
      [thm] in
  %
  -----------------------------------------------------------------------------
  Given |- (<n> + <m>) + <c> = <p>
  prove |- (<n) + <m+1>) + <c> = <p+1>
  -----------------------------------------------------------------------------
  %
  let next_in_column_lemma =
    PROVE (
      "! x y z sum. ((x + y) + z = sum) ==> ((x + (SUC y)) + z = (SUC sum))",
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [GSYM ADD_SUC] THEN
      ASM_REWRITE_TAC [GSYM (ONCE_REWRITE_RULE [ADD_SYM] ADD_SUC)]) in
  letrec mk_column lim thm =
    let m = (int_of_term o rand o rand o rator o rand o rator o concl) thm in
    let p = (int_of_term o rand o concl) thm in
    if m < lim then
      let next_thm = prove_next_in_table m p thm next_in_column_lemma in
      thm . (mk_column lim next_thm)
    else
      [thm] in
  %
  -----------------------------------------------------------------------------
  Create a table containing the theorems |- (<x> + <y>) + <z> = <x+y+z>
  for all 0 <= x < max_radix, 0 <= y < max_radix, 0 <= y <= 1.
  -----------------------------------------------------------------------------
  %
  let full_add_table =
    let zero_zero_zero = PROVE ("(0 + 0) + 0 = 0", REWRITE_TAC [ADD_CLAUSES]) in
    let zero_zero_one  = PROVE ("(0 + 0) + 1 = 1", REWRITE_TAC [ADD_CLAUSES]) in
    let mk_half_table thm =
      map (mk_row (max_radix - 1)) (mk_column (max_radix - 1) thm) in
    [mk_half_table zero_zero_zero; mk_half_table zero_zero_one] in
  %
  -----------------------------------------------------------------------------
  Try to do a full add by table lookup, but if that fails, fall back on
  ADD_CONV.
  -----------------------------------------------------------------------------
  %
  \ x y z.
  ( (el (x+1) (el (y+1) (el (z+1) full_add_table) ) ) )
  ?
  let [x_tm;y_tm;z_tm] = map term_of_int [x;y;z] in
  let half_sum_thm = ADD_CONV (mk_binary_comb "+" x_tm y_tm) in
  let half_sum = rand (concl half_sum_thm) in
  let full_sum_thm = ADD_CONV (mk_binary_comb "+" half_sum z_tm) in
  SUBS_OCCS [[1],SYM half_sum_thm] full_sum_thm;;


%
-------------------------------------------------------------------------------
Define a function from three integers n, x, y to the theorem
|- ((n * x) + y) DIV r, and do it by table lookup where n and x and y are
positive integers less than r, and r is less than max_radix.
-------------------------------------------------------------------------------
%

let fast_mul_with_carry =
  %
  -----------------------------------------------------------------------------
  Prove a lemma that will make creation of the lookup table much faster.
    |- ! n.
        (n *  0 = 0) /\
        (n *  1 = n) /\
        (n *  2 = (n + n)) /\
        ...
        (n * <max_radix-1> = ((...((n + n) + n) + ... + n) + n))",
  -----------------------------------------------------------------------------
  %
  let fast_mul_table_lemma =
    let add_a_row x (pluses_tm, tms) =
      let left_half = mk_comb ("$* n", term_of_int (x+1)) in
      let right_half = mk_comb (mk_comb ("+", pluses_tm), "n: num") in
      (right_half, (mk_eq (left_half, right_half)) . tms) in
    let goal = mk_forall ("n: num", list_mk_conj (rev (snd
      (rev_itlist add_a_row (upto (max_radix-2))
        ("n: num", ["n * 1 = n";"n * 0 = 0"]))))) in
    PROVE (goal,
      let convs = map (fast_num_CONV o term_of_int) (upto max_radix) in
      REWRITE_TAC (append convs [MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC])) in
  %
  -----------------------------------------------------------------------------
  Create a table containing the theorems |- <n> * <m> = <n*m>
  for all 0 <= n < max_radix, 0 <= m < max_radix.
  -----------------------------------------------------------------------------
  %
  let fast_mul_table =
    let mk_row n =
      let add_multiple m = fast_add (m*n) n in
      let this_row_lemma = SPEC (term_of_int n) fast_mul_table_lemma in
      let multiples = map add_multiple (zero_upto (max_radix-1)) in
      CONJUNCTS (rev_itlist (SUBS o listify) multiples this_row_lemma) in
    map mk_row (zero_upto (max_radix-1)) in
  %
  -----------------------------------------------------------------------------
  Define a function that takes two integers and returns a theorem saying
  what their product is.  Do it by table lookup for positive integers less
  than max_radix.
  -----------------------------------------------------------------------------
  %
  let fast_mul n m =
    ( el (m+1) (el (n+1) fast_mul_table)
    ) ? MUL_CONV (mk_binary_comb "$*" (term_of_int n) (term_of_int m)) in
  %
  -----------------------------------------------------------------------------
  Define the function using lambda, so all the tables are precomputed, rather
  than being recomputed each time this function is invoked.
  -----------------------------------------------------------------------------
  %
  \ n x y.
    let prod = fast_mul n x in
    let sum = fast_add (n*x) y in
    SUBS_OCCS [[1],SYM prod] sum;;


%
-------------------------------------------------------------------------------
Define prove_div_mod, which takes x and y and returns theorems saying what
x DIV y and x MOD y are.  Do it by table lookup if y is an accelerated radix
and x is less than y squared.
-------------------------------------------------------------------------------
%

let fast_div_mod =
  %
  -----------------------------------------------------------------------------
  Create the top row in the div_mod table.
  -----------------------------------------------------------------------------
  %
  let div_mod_base_lemma =
    PROVE (
      "! r n. (n < r = T) ==> ((n DIV r = 0) /\ (n MOD r = n))",
      let case_rule =
          ( (REWRITE_RULE [MULT_CLAUSES; ADD_CLAUSES]) o
            (SPEC "0") o
            UNDISCH o
            (SPECL ["r: num";"n:num"])
          ) in
      ONCE_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THENL
      [ ACCEPT_TAC (case_rule DIV_MULT); ACCEPT_TAC (case_rule MOD_MULT) ]) in
  let mk_top_row r =
    let r_tm = term_of_int r in
    let top_row_lemma = SPEC r_tm div_mod_base_lemma in
    let top_row_rule r_tm n =
      let n_tm = term_of_int n in
      let radix_less = fast_LT_CONV (mk_binary_comb "$<" n_tm r_tm) in
      MP (SPEC n_tm top_row_lemma) radix_less in
    map (top_row_rule r_tm) (zero_upto (r-1)) in
  %
  -----------------------------------------------------------------------------
  Given one row in the div_mod table, create the next row.
  -----------------------------------------------------------------------------
  %
  let div_mod_step_lemma =
    PROVE (
      "! r n m p.
        (0 < r = T) ==>
        ((n DIV r = m) /\ (n MOD r = p)) ==>
        (((n + r) DIV r = (m + 1)) /\ ((n + r) MOD r = p))",
      REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THENL
      [
        MATCH_MP_TAC (SPECL ["r: num"; "n+r"; "m + 1"] DIV_UNIQUE) THEN
        EXISTS_TAC "n MOD r" THEN
        REWRITE_TAC [RIGHT_ADD_DISTRIB;MULT_CLAUSES;SYM (ASSUME "n DIV r = m")] THEN
        SUBST_TAC [SPECL ["((n DIV r) * r) + r"; "n MOD r"] ADD_SYM] THEN
        REWRITE_TAC [ADD_ASSOC; EQ_MONO_ADD_EQ] THEN
        SUBST_TAC [SPECL ["n MOD r";"(n DIV r) * r"] ADD_SYM] THEN
        ACCEPT_TAC (SPEC "n: num" (UNDISCH (SPEC "r: num" DIVISION)))
      ;
        REWRITE_TAC [SYM (ASSUME "n MOD r = p")] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN
        ACCEPT_TAC (
          ( (REWRITE_RULE [MULT_CLAUSES]) o
            (SPECL ["1"; "n: num"]) o
            UNDISCH o
            (SPEC "r: num")
          ) MOD_TIMES)
      ]) in
  let add_next_row r table =
    let prev_row = last table in
    let r_tm = term_of_int r in
    let next_in_column_lemma =
      SPEC r_tm div_mod_step_lemma in
    let next_in_column_rule r r_tm thm =
      let div_tm, mod_tm = dest_conj (concl thm) in
      let n_tm = (rand o rator o fst o dest_eq) div_tm in
      let m_tm = rand div_tm in
      let p_tm = rand mod_tm in
      let radix_less = fast_LT_CONV (mk_comb ("$< 0", r_tm)) in
      let long_thm =
        MP (MP (SPECL [n_tm;m_tm;p_tm] next_in_column_lemma) radix_less) thm in
      let n = int_of_term n_tm in
      let m = int_of_term m_tm in
      SUBS_OCCS [[1;2], fast_add n r; [1], fast_add m 1] long_thm in
    let this_row = map (next_in_column_rule r r_tm) prev_row in
    table @ [this_row] in
  %
  -----------------------------------------------------------------------------
  Make an entire row.
  -----------------------------------------------------------------------------
  %
  let mk_row r =
    let rad_r_thms =
      funpow (r-1) (add_next_row r) [mk_top_row r] in
    map CONJ_PAIR (flat rad_r_thms) in
  %
  -----------------------------------------------------------------------------
  Make a row for each radix that is to be accelerated, and leave an empty row
  for other radices.
  -----------------------------------------------------------------------------
  %
  let conditionally_mk_row r =
    if mem r radices then mk_row r else [] in
  let div_mod_table =
    map conditionally_mk_row (tl (upto max_radix)) in
  %
  -----------------------------------------------------------------------------
  Try to get the div and mod theorems by table lookup, but if that fails, fall
  back on DIV_CONV and MOD_CONV.
  -----------------------------------------------------------------------------
  %
  \ x y.
  ( el (x+1) (el (y-1) div_mod_table) )
  ?
  ( let x_tm = term_of_int x in
    let y_tm = term_of_int y in
    let x_mod_y_tm = mk_binary_comb "MOD" x_tm y_tm in
    let x_div_y_tm = mk_binary_comb "DIV" x_tm y_tm in
    (DIV_CONV x_div_y_tm, MOD_CONV x_mod_y_tm) );;


%
-------------------------------------------------------------------------------
BASEN_ADD_CONV

Synopsis:

Proves the result of adding one numeral to another.

Description:

If m and n are lists of digits in base r, and p is the list of digits in the
base-r numeral representing the sum of m and n, then BASEN_ADD_CONV returns
the theorem:

        |- (BASEN r m + BASEN r n) = BASEN r p

Note:

Assumes the addend or augend are normalized.  If they are not, the resulting
theorem expresses them normalized anyway.

Failure:

The argument to BASEN_ADD_CONV must be of the form "BASEN r [...] + BASEN r
[...]", and the radix of the two numerals must be the same, and the radix must
be a numeric constant that is at least 2, and all elements of the digit lists
must be numeric constants, and must be less than the radix.

Examples:

#BASEN_ADD_CONV "BASEN 10 [3;4;5] + BASEN 10 [3;4;5]";;
|- BASEN 10 [3;4;5] + BASEN 10 [3;4;5] = BASEN 10 [6;9;0]

#BASEN_ADD_CONV "BASEN 2 [1;1;1;1] + BASEN 2 [1;1;1;0]";;
|- BASEN 2 [1;1;1;1] + BASEN 2 [1;1;1;0]) = BASEN 2 [1;1;1;0;1]

#BASEN_ADD_CONV "BASEN 16 [8;10;14] + BASEN 16 [12;4]";;
|- BASEN 16 [8;10;14] + BASEN 16 [12;4]) = BASEN 16 [9;7;2]

See also:

BASEN_SUC_CONV.
-------------------------------------------------------------------------------
%

let basen_add_basecase =
  PROVE (
    "! r. ((BASEN r []) + (BASEN r []) = (BASEN r [0])) /\
      (LENGTH ([]: num list) = LENGTH ([]: num list)) /\
      (LENGTH ([]: num list) = LENGTH ([]: num list))",
    REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]);;

let basen_add_step_lemma =
  PROVE (
    "! r. 0 < r ==> ! x y xs ys z zs.
      ( ((BASEN r xs) + (BASEN r ys) = (BASEN r (CONS z zs))) /\
        (LENGTH xs = LENGTH ys) /\
        (LENGTH xs = LENGTH zs)
      ) ==>
      ( ((BASEN r (CONS x xs)) + (BASEN r (CONS y ys)) =
          (BASEN r (CONS (((x + y) + z) DIV r) (CONS (((x + y) + z) MOD r) zs)))) /\
        (LENGTH (CONS x xs) = LENGTH (CONS y ys)) /\
        (LENGTH (CONS x xs) = LENGTH (CONS (((x + y) + z) MOD r) zs))
      )",
    let add_assoc_lemma =
      PROVE (
        "! x xs y ys. (x + xs) + (y + ys) = (xs + ys) + (x + y)",
        REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (ADD_ASSOC,ADD_SYM))) in
    let div_mod_lemma =
      ( GEN_ALL o
        SYM o
        CONJUNCT1 o
        SPEC_ALL o
        UNDISCH_ALL o
        (SPEC "r: num")
      ) DIVISION in
    GEN_TAC THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC [BASEN] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC "LENGTH (xs: num list) = LENGTH (ys: num list)" THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    ASM_REWRITE_TAC [LENGTH] THEN
    ONCE_REWRITE_TAC [add_assoc_lemma] THEN
    REWRITE_TAC [LENGTH; EXP; MULT_ASSOC] THEN
    ONCE_REWRITE_TAC [
      SPEC
        "((((x + y) + z) DIV r) * r) * (r EXP (LENGTH (zs: num list)))"
          ADD_ASSOC] THEN
    ASM_REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB] THEN
    ONCE_ASM_REWRITE_TAC [div_mod_lemma] THEN
    ONCE_REWRITE_TAC [
      GEN_ALL (SYM (SPECL ["m: num"; "BASEN r zs"; "p: num"] ADD_ASSOC))] THEN
    ONCE_REWRITE_TAC [SPEC "BASEN r zs" ADD_SYM] THEN
    REWRITE_TAC [ADD_ASSOC; EQ_MONO_ADD_EQ] THEN
    REWRITE_TAC [MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB] THEN
    SUBST_TAC [SPECL ["z: num"; "x + y"] ADD_SYM] THEN
    REFL_TAC);;

let PURE_BASEN_ADD_CONV tm =
  (
  %
  -----------------------------------------------------------------------------
  Take the term apart and verify that it's a sum of basen numerals.
  -----------------------------------------------------------------------------
  %
  let (op, r_tm, basen_r_x, xs_tm, x_tms, basen_r_y, ys_tm, y_tms) =
    dest_binary_basen_comb tm in
  if not (op = "+") then fail else
  %
  -----------------------------------------------------------------------------
  Specialize the theorems that depend on the radix.
  -----------------------------------------------------------------------------
  %
  let basecase = SPEC r_tm basen_add_basecase in
  let zero_less_radix =
    REWRITE_RULE [] (LT_CONV (mk_binary_comb "$<" "0" r_tm)) in
  let add_step_lemma = MATCH_MP basen_add_step_lemma zero_less_radix in
  let r = int_of_term r_tm in
  %
  -----------------------------------------------------------------------------
  Zero-extend the shorter of the addend and the augend, so they're the same
  length, and define a rule to restore it in the resulting theorem.
  -----------------------------------------------------------------------------
  %
  let length_diff = (length x_tms) - (length y_tms) in
  let x_tms =
    if length_diff < 0 then lengthen "0" (-length_diff) x_tms else x_tms in
  let y_tms =
    if length_diff < 0 then y_tms else lengthen "0" length_diff y_tms in
  let renormalize_conv =
    funpow (absolute_value length_diff) ($THENC ONCE_BASEN_NORMALIZE_CONV) ALL_CONV in
  let renormalize_operand_rule =
    if length_diff < 0 then
      (CONV_RULE o RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) renormalize_conv
    else
      (CONV_RULE o RATOR_CONV o RAND_CONV o RAND_CONV) renormalize_conv
    in
  %
  -----------------------------------------------------------------------------
  Define a rule that extends a theorem about the sum of two basen numerals
  into a theorem about a sum of two numerals that are each one digit longer.
  -----------------------------------------------------------------------------
  %
  let add_rule (x_tm, y_tm) thm =
    let z_tm =
      (fst o dest_cons o rand o rand o fst o dest_conj o concl) thm in
    let x = int_of_term x_tm in
    let y = int_of_term y_tm in
    let z = int_of_term z_tm in
    let xyz_thm = fast_add_with_carry x y z in
    let div_thm, mod_thm = fast_div_mod (x+y+z) r in
    ( (SUBS [div_thm;mod_thm]) o
      (SUBS [xyz_thm]) o
      (MATCH_MP (SPECL [x_tm;y_tm] add_step_lemma))
    ) thm in
  %
  -----------------------------------------------------------------------------
  Extend the base case with all the operands' digits, then renormalize the
  lengthened operand.
  -----------------------------------------------------------------------------
  %
  let full_sum_thm = itlist2 add_rule (x_tms, y_tms) basecase in
  renormalize_operand_rule (CONJUNCT1 full_sum_thm)
  ) ? failwith `PURE_BASEN_ADD_CONV`;;

%----------------------------------------------------------------------------%
% Sufficient postnormalization forced by |REPEATC ONCE_BASEN_NORMALIZE_CONV| %
% rather than previous |ONCE_BASEN_NORMALIZE_CONV ORELSEC ALL_CONV|; in the  %
% old version |BASEN_ADD_CONV "BASEN 10 [0;0;1;0;0] + BASEN 10 [0;0;6;0;8]"| %
% returned a denormalized result, for example. [JRH 94.01.29]                %
%----------------------------------------------------------------------------%

let BASEN_ADD_CONV tm =
  let norm_conv = REPEATC ONCE_BASEN_NORMALIZE_CONV in
  ( (PURE_BASEN_ADD_CONV THENC norm_conv) tm )
  ? failwith `BASEN_ADD_CONV`;;


%
-------------------------------------------------------------------------------
BASEN_SUC_CONV

Synopsis:

Converts the successor function on a numeral into an add-one in the same radix.

Description:

If m is a list of digits in base r, and m is a list of digits in base-r,
then BASEN_SUC_CONV "SUC (BASEN r m)" returns the theorem:

        |- SUC (BASEN r m) = BASEN r m + BASEN r [1]

Failure:

The argument to BASEN_SUC_CONV must be of the form "SUC (BASEN r [...])",
and the radix must be a numeric constant that is at least 2, and all elements
of the digit lists must be numeric constants, and must be less than the radix.

Examples:

#BASEN_SUC_CONV "SUC (BASEN 10 [3;4;5])";;
|- SUC(BASEN 10[3;4;5]) = BASEN 10[3;4;6]

#BASEN_SUC_CONV "SUC (BASEN 2 [1;1;1;1])";;
|- SUC(BASEN 2[1;1;1;1]) = BASEN 2[1;0;0;0;0]

#BASEN_SUC_CONV "SUC (BASEN 16 [8;10;14])";;
|- SUC(BASEN 16[8;10;14]) = BASEN 16[8;10;15]

See also:

BASEN_ADD_CONV, BASEN_PRE_CONV.
-------------------------------------------------------------------------------
%

let PURE_BASEN_SUC_CONV =
  let basen_suc =
    PROVE (
      "! r m. SUC (BASEN r m) = BASEN r m + BASEN r [1]",
      let MULT_RIGHT_1 = theorem `arithmetic` `MULT_RIGHT_1` in
      REWRITE_TAC [BASEN; LENGTH; EXP; MULT; MULT_RIGHT_1; ADD1; ADD_0]) in
  \ tm.
  ( let (op, r_tm, basen_r_x, xs_tm, x_tms) = dest_unary_basen_comb tm in
    if not (op = "SUC") then fail else
    SPECL [r_tm; xs_tm] basen_suc
  ) ? failwith `PURE_BASEN_SUC_CONV`;;

let BASEN_SUC_CONV =
  PURE_BASEN_SUC_CONV THENC BASEN_ADD_CONV;;


%
-------------------------------------------------------------------------------
BASEN_SUB_CONV : conv

Synopsis:

Proves the result of subtracting one numeral from another.

Description:

If m and n are lists of digits in base r, and p is the list of digits in the
base-r numeral representing the sum of m and n, then BASEN_SUB_CONV returns
the theorem:

        |- (BASEN r m - BASEN r n) = BASEN r p

Failure:

The argument to BASEN_SUB_CONV must be of the form "BASEN r [...] - BASEN r
[...]", and the radix of the two numerals must be the same, and the radix must
be a numeric constant that is at least 2, and all elements of the digit lists
must be numeric constants, and must be less than the radix.

Examples:

#BASEN_SUB_CONV "BASEN 10 [3;4;5] - BASEN 10 [3;4;5]";;
|- BASEN 10 [3;4;5] - BASEN 10 [3;4;5] = BASEN 10 []

#BASEN_SUB_CONV "BASEN 2 [1;1;1;1] - BASEN 2 [1;1;1;0]";;
|- BASEN 2 [1;1;1;1] - BASEN 2 [1;1;1;0]) = BASEN 2 [1]

#BASEN_SUB_CONV "BASEN 16 [10;14] - BASEN 16 [8;4]";;
|- BASEN 16 [10;14] - BASEN 16 [8;4]) = BASEN 16 []

Comments:

This is whole-number arithmetic, so subtracting a large number from a small
number returns 0.

See also:

BASEN_PRE_CONV.
-------------------------------------------------------------------------------
%

%
-------------------------------------------------------------------------------
Given terms of the appropriate forms, prove the theorem
        |- (BASEN r [....]) - (BASEN r [....]) = BASEN r [...]
-------------------------------------------------------------------------------
%

let BASEN_SUB_CONV =
  let sub_equal =
    PROVE (
      "! r x. x - x = (BASEN r [])",
      REWRITE_TAC [SUB_EQUAL_0; BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let sub_less =
    PROVE (
      "! r x y. (x < y = T) ==> (x - y = BASEN r [])",
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [SUB_EQ_0; LESS_OR_EQ; BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let sub_greater =
    PROVE (
      "! x y diff. (y + diff = x) ==> (x - y = diff)",
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ADD_EQ_IMP_SUB_EQ THEN
      ASM_REWRITE_TAC []) in
  \ tm.
  ( let (op, r_tm, basen_x, xs_tm, x_tms, basen_y, ys_tm, y_tms) =
      dest_binary_basen_comb tm in
    if not (op = "-") then fail else
    let x = int_of_basen basen_x in
    let y = int_of_basen basen_y in
    if x = y then
      SPECL [r_tm; basen_x] sub_equal
    else if x < y then
      let comparison = BASEN_LT_CONV (mk_binary_comb "<" basen_x basen_y) in
      MP (SPECL [r_tm; basen_x; basen_y] sub_less) comparison
    else
      let r = int_of_term r_tm in
      let basen_diff = basen_of_int (r, x-y) in
      let sum_thm = BASEN_ADD_CONV (mk_binary_comb "+" basen_y basen_diff) in
      MP (SPECL [basen_x; basen_y; basen_diff] sub_greater) sum_thm
  ) ? failwith `BASEN_SUB_CONV`;;


%
-------------------------------------------------------------------------------
BASEN_PRE_CONV

Synopsis:

Converts the predecessor function on a numeral into a subtract-one in the same
radix.

Description:

If m is a list of digits in base r, and m is a list of digits in base-r,
then BASEN_PRE_CONV "PRE (BASEN r m)" returns the theorem:

        |- PRE (BASEN r m) = BASEN r m - BASEN r [1]

Failure:

The argument to BASEN_PRE_CONV must be of the form "PRE (BASEN r [...])",
and the radix must be a numeric constant that is at least 2, and all elements
of the digit lists must be numeric constants, and must be less than the radix.

Examples:

#BASEN_PRE_CONV "PRE (BASEN 10 [3;4;5])";;
|- PRE(BASEN 10[3;4;5]) = BASEN 10[3;4;4]

#BASEN_PRE_CONV "PRE (BASEN 10 [])";;
|- PRE(BASEN 10[]) = BASEN 10[]

#BASEN_PRE_CONV "PRE (BASEN 2 [1;1;1;1])";;
|- PRE(BASEN 2[1;1;1;1]) = BASEN 2[1;1;1;0]

#BASEN_PRE_CONV "PRE (BASEN 16 [8;0;0])";;
|- PRE(BASEN 16[8;0;0]) = BASEN 16[7;15;15]

See also:

BASEN_SUB_CONV, BASEN_SUC_CONV.
-------------------------------------------------------------------------------
%

let PURE_BASEN_PRE_CONV =
  let basen_pre =
    PROVE (
      "! r m. PRE (BASEN r m) = BASEN r m - BASEN r [1]",
      let MULT_RIGHT_1 = theorem `arithmetic` `MULT_RIGHT_1` in
      REWRITE_TAC [BASEN; LENGTH; EXP; MULT; MULT_RIGHT_1; PRE_SUB1; ADD_0]) in
  \ tm.
  ( let (op, r_tm, basen_r_x, xs_tm, x_tms) = dest_unary_basen_comb tm in
    if not (op = "PRE") then fail else
    SPECL [r_tm; xs_tm] basen_pre
  ) ? failwith `PURE_BASEN_PRE_CONV`;;

let BASEN_PRE_CONV =
  PURE_BASEN_PRE_CONV THENC BASEN_SUB_CONV;;


%
-------------------------------------------------------------------------------
BASEN_MUL_CONV : conv

Synopsis:

Proves the result of multiplying one numeral by another.

Description:

If m and n are lists of digits in base r, and p is the list of digits in the
base-r numeral representing the sum of m and n, then BASEN_MUL_CONV returns
the theorem:

        |- (BASEN r m * BASEN r n) = BASEN r p

Failure:

The argument to BASEN_MUL_CONV must be of the form "BASEN r [...] * BASEN r
[...]", and the radix of the two numerals must be the same, and the radix must
be a numeric constant that is at least 2, and all elements of the digit lists
must be numeric constants, and must be less than the radix.

Examples:

#BASEN_MUL_CONV "BASEN 10 [3;4;5] * BASEN 10 [3;4;5]";;
|- BASEN 10 [3;4;5] * BASEN 10 [3;4;5] = BASEN 10 [1;1;9;0;2;5]

#BASEN_MUL_CONV "BASEN 2 [1;1;1;1] * BASEN 2 [1;1;1;0]";;
|- BASEN 2 [1;1;1;1] * BASEN 2 [1;1;1;0]) = BASEN 2 [1;1;0;1;0;0;1;0]

#BASEN_MUL_CONV "BASEN 16 [1;0] * BASEN 16 [4]";;
|- BASEN 16 [1;0] * BASEN 16 [4]) = BASEN 16 [4;0]
-------------------------------------------------------------------------------
%

%
Consider long multiplication as done by hand:

            1 2 3
          * 4 5 6
          -------
            7 3 8
          6 1 5
        4 9 2
        =========
        5 6 0 8 8

This consists of multiplying a multidigit numeral by a single digit (for each
of several single digits), and then adding a bunch of partial products.
Multiplying a numeral by a single digit is fairly straightforward.  The add
is more interesting.  Note that each successive partial product is shifted
left one digit with respect to the preceding one.  The BASEN function happens
to express exactly this kind of shifted sum.  Thus, the sum of partial
products can be expressed in terms of the partial products in this way:

        BASEN 10 [ 492; 608; 738 ]

more precisely, since the partial products themselves are numerals:

        BASEN 10 [ BASEN 10 [4;9;2]; BASEN 10 [6;0;8]; BASEN 10 [7;3;8] ]

If there's a procedure for combining two adjacent partial products, it can
be used repeatedly to get:

        BASEN 10 [BASEN 10 [5;6;0;8;8]]

and then a simple identity turns that into the desired result:

        BASEN 10 [5;6;0;8;8]

It probably doesn't make sense to build a function to add many partial
products all at once, rather than two at a time.  So there are really
intermediate subtotals, like this:

            1 2 3
          * 4 5 6
          -------
            7 3 8
          6 1 5
        ---------
          6 8 8 8
        4 9 2
        =========
        5 6 0 8 8

In order to keep the expressions short, which makes everything faster, the
partial products should be summed as they are produced.  If the BASEN
representation is to be used, though, that means they have to be generated
from the most-significant down, or they won't stay adjacent.  Top-down is
easy enough:

            1 2 3
          * 4 5 6
          -------
        4 9 2
          6 1 5
        ---------
        5 5 3 5
            7 3 8
        =========
        5 6 0 8 8

That's the algorithm.  Start with the multiplicand (123).  Multiply by the
first digit of the multiplier, giving the theorem:

        BASEN 10 [1;2;3] * BASEN 10 [4] = BASEN 10 [4;9;2]

Then by the second digit of the multiplier:

        BASEN 10 [1;2;3] * BASEN 10 [5] = BASEN 10 [6;1;5]

(Note that caching these results is very likely to be worthwhile for multipliers
with many digits, since the chance of finding the same multiplier digit again is
1/radix, for each digit.)

Now MATCH_MP with this theorem:

        ! x r ys zs.
          x * (BASEN r ys) = BASEN r zs  ==>
        ! y more_zs.
          x * (BASEN r [y]) = BASEN r more_zs  ==>
          x * (BASEN r (SNOC y ys)) = BASEN r [BASEN r zs; BASEN r more_zs]

to combine the two:

        BASEN 10 [1;2;3] * BASEN 10 (SNOC 5 [4]) =
        BASEN 10 [ BASEN 10 [4;9;2]; BASEN 10 [6;1;5] ]

Unfortunately, this means the multiplier is growing by adding digits at the
bottom.  The SNOC list will have to be changed into a CONS list later.
Now add the adjacent partial products to reduce the partial product to an
un-nested numeral:

        BASEN 10 [1;2;3] * BASEN 10 (SNOC 5 [4]) =
        BASEN 10 [5;5;3;5]

and repeat for each of the remaining multiplier digits all the steps described
for the second digit.

        BASEN 10 [1;2;3] * BASEN 10 (SNOC 6 (SNOC 5 [4])) =
        BASEN 10 [5;6;0;8;8]

Finally, convert the SNOC list to a CONS list.

        BASEN 10 [1;2;3] * BASEN 10 [4;5;6] = BASEN 10 [5;6;0;8;8]
%

%
Given a term of the form
  "(BASEN r xs) * (BASEN r [n])"
return the theorem
  |- (BASEN r xs) * (BASEN r [n]) = BASEN r <xs*n>
%

let basen_mul_basecase =
  PROVE (
    "! r n. ((BASEN r []) * (BASEN r [n]) = (BASEN r [0])) /\
        (LENGTH ([]: num list) = LENGTH ([]: num list))",
    REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]);;

let basen_mul_step_lemma =
  PROVE (
    "! r. (0 < r = T) ==> ! n x xs y ys.
      ( ((BASEN r xs) * (BASEN r [n]) = (BASEN r (CONS y ys))) /\
        (LENGTH xs = LENGTH ys)
      ) ==>
      ( ((BASEN r (CONS x xs)) * (BASEN r [n]) =
         (BASEN r (CONS (((n * x) + y) DIV r)
                  (CONS (((n * x) + y) MOD r) ys)))) /\
        (LENGTH (CONS x xs) = LENGTH (CONS (((n * x) + y) MOD r) ys))
      )",
    let lemma2 =
      ( GEN_ALL o
        SYM o
        CONJUNCT1 o
        SPEC_ALL o
        UNDISCH_ALL o
        (SPEC "r: num")
      ) DIVISION in
    REWRITE_TAC [BASEN_DIGIT_EQ_DIGIT] THEN
    GEN_TAC THEN
    DISCH_TAC THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [
        BASEN;
        EXP;
        LENGTH;
        MULT_ASSOC;
        ADD_ASSOC;
        GSYM RIGHT_ADD_DISTRIB;
        lemma2] THEN
    ASM_REWRITE_TAC [
        BASEN;
        RIGHT_ADD_DISTRIB;
        GSYM MULT_ASSOC;
        GSYM ADD_ASSOC;
        EQ_MONO_ADD_EQ] THEN
    ONCE_REWRITE_TAC[SPECL ["r EXP (LENGTH (ys: num list))"] MULT_SYM] THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    SUBST_TAC [SPECL ["x: num";"n: num"] MULT_SYM] THEN
    REFL_TAC);;

let PURE_BASEN_MUL_BY_DIGIT_CONV tm =
  %
  -----------------------------------------------------------------------------
  Take apart a term of the form "BASEN r xs * BASEN r [y]".
  -----------------------------------------------------------------------------
  %
  let basen_r_x, basen_r_n = dest_binary_comb "$*" tm in
  let r_tm, xs_tm = dest_basen basen_r_x in
  let ns_tm = snd (dest_basen basen_r_n) in
  let x_tms = fst (dest_list xs_tm) in
  let [n_tm] = fst (dest_list ns_tm) in
  %
  -----------------------------------------------------------------------------
  Specialize the theorems that depend on the radix.
  -----------------------------------------------------------------------------
  %
  let r = int_of_term r_tm in
  let n = int_of_term n_tm in
  let base_thm = SPECL [r_tm;n_tm] basen_mul_basecase in
  let radix_lemma = fast_LT_CONV (mk_comb ("$< 0", r_tm)) in
  let step_lemma =
    ( (SPEC n_tm) o
      (C MP radix_lemma) o
      (SPEC r_tm)
    ) basen_mul_step_lemma in
  %
  -----------------------------------------------------------------------------
  Define a rule that extends a basen multiply theorem by one digit.
  -----------------------------------------------------------------------------
  %
  let cons_rule x_tm thm =
    let (xs_tm, (z_tm, zs_tm)) =
      (((rand o rand o rator) # (dest_cons o rand)) o
        dest_eq o fst o dest_conj o snd o strip_forall o concl) thm in
    let x = int_of_term x_tm in
    let z = int_of_term z_tm in
    let nx_plus_z = fast_mul_with_carry n x z in
    let (nx_plus_z_div_r, nx_plus_z_mod_r) = fast_div_mod ((n*x)+z) r in
    ( (SUBS [nx_plus_z_div_r; nx_plus_z_mod_r]) o
      (SUBS [nx_plus_z]) o
      (C MP thm) o
      (SPECL [x_tm; xs_tm; z_tm; zs_tm])
    ) step_lemma in
  %
  -----------------------------------------------------------------------------
  Extend the base theorem with every digit in the multiplicand, and return the
  interesting part of the theorem.
  -----------------------------------------------------------------------------
  %
  CONJUNCT1 (itlist cons_rule x_tms base_thm);;


%
Given a digit term and a theorem of the form:
  |- (BASEN r xs) * (BASEN r ys) = BASEN r zs
return a theorem of the form
  |- (BASEN r xs) * (BASEN r (SNOC y ys)) =
        BASEN r [BASEN r zs; <BASEN r xs * y>]
%

let basen_mul_sum_basecase =
  PROVE (
    "! r x. BASEN r [BASEN r x] = BASEN r x",
    GEN_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [BASEN; LENGTH; EXP; MULT_CLAUSES; ADD_CLAUSES]);;

let basen_mul_sum_step_lemma =
  PROVE (
    "! r x1 x2 xs.
      BASEN r (CONS (BASEN r x1) (CONS (BASEN r x2) xs)) =
      BASEN r (CONS (((BASEN r x1) * r) + (BASEN r x2)) xs)",
    REWRITE_TAC [
        BASEN;
        RIGHT_ADD_DISTRIB;
        EQ_MONO_ADD_EQ;
        LENGTH;
        EXP;
        MULT_ASSOC;
        ADD_ASSOC]);;

let basen_extend_mul_lemma =
  PROVE (
    "! x r y more_zs.
      (x * (BASEN r [y]) = BASEN r more_zs)  ==>
      ! ys zs.
        (x * (BASEN r ys) = BASEN r zs)  ==>
        (x * (BASEN r (SNOC y ys)) = BASEN r [BASEN r zs; BASEN r more_zs])",
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [BASEN_SNOC; LEFT_ADD_DISTRIB] THEN
    SUBST_TAC [SYM (SPECL ["r: num"; "y: num"] BASEN_DIGIT_EQ_DIGIT)] THEN
    ASM_REWRITE_TAC [
        basen_mul_sum_basecase;
        basen_mul_sum_step_lemma;
        MULT_ASSOC;
        BASEN_DIGIT_EQ_DIGIT]);;

let PURE_BASEN_MUL_EXTEND_RULE y_tm thm =
  %
  -----------------------------------------------------------------------------
  Take apart a theorem of the form
    |- BASEN r xs * BASEN r ys = BASEN r zs.
  -----------------------------------------------------------------------------
  %
  let mply = (fst o dest_eq o concl) thm in
  let basen_r_xs, basen_r_ys = dest_binary_comb "$*" mply in
  let r_tm, xs_tm = dest_basen basen_r_xs in
  %
  -----------------------------------------------------------------------------
  Create a theorem stating the result of multiplying "BASEN r xs" by the
  given digit.
  -----------------------------------------------------------------------------
  %
  let basen_r_y = mk_basen r_tm [y_tm] in
  let mply' = mk_binary_comb "$*" basen_r_xs basen_r_y in
  let mply'_thm = PURE_BASEN_MUL_BY_DIGIT_CONV mply' in
  %
  -----------------------------------------------------------------------------
  Use that to extend the original theorem.
  -----------------------------------------------------------------------------
  %
  let extend_with_y_lemma = MATCH_MP basen_extend_mul_lemma mply'_thm in
  MATCH_MP extend_with_y_lemma thm;;


%
Given a term of the form:
  "BASEN r [BASEN r zs; BASEN r more_zs]"
Return a theorem of the form:
  |- BASEN r [BASEN r zs; BASEN r more_zs] = BASEN r [<zs * r + more_zs>]
%

let basen_mul_combine_pps_basecase =
  PROVE (
    "! r y. (BASEN r [BASEN r []; BASEN r [y]] = BASEN r [0;y]) /\
        (LENGTH [y] = SUC (LENGTH ([]: num list))) /\
        (LENGTH [y] = SUC (LENGTH ([]: num list)))",
    REWRITE_TAC [BASEN; EXP; MULT_CLAUSES; ADD_CLAUSES; LENGTH]);;

let basen_mul_combine_pps_step_lemma =
  PROVE (
    "! r. 0 < r ==> ! x y xs ys z zs.
      ( (BASEN r [BASEN r xs; BASEN r ys] = BASEN r (CONS z zs)) /\
        (LENGTH ys = SUC (LENGTH xs)) /\
        (LENGTH zs = SUC (LENGTH xs))
      ) ==>
      ( (BASEN r [BASEN r (CONS x xs); BASEN r (CONS y ys)] =
          (BASEN r (CONS (((x + y) + z) DIV r) (CONS (((x + y) + z) MOD r) zs)))) /\
        (LENGTH (CONS y ys) = SUC (LENGTH (CONS x xs))) /\
        (LENGTH (CONS (((x + y) + z) MOD r) zs) = SUC (LENGTH (CONS x xs)))
      )",
    let add_assoc_lemma =
      PROVE (
        "!a b c d. ((a + b) + c) + d = (a + c) + (b + d)",
        REPEAT GEN_TAC THEN CONV_TAC (AC_CONV (ADD_ASSOC,ADD_SYM))) in
    let div_mod_lemma =
      ( GEN_ALL o
        SYM o
        CONJUNCT1 o
        SPEC_ALL o
        UNDISCH_ALL o
        (SPEC "r: num")
      ) DIVISION in
    REWRITE_TAC [basen_mul_sum_step_lemma; BASEN_DIGIT_EQ_DIGIT] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [LENGTH] THEN
    ASM_REWRITE_TAC [BASEN; RIGHT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC] THEN
    REWRITE_TAC [LENGTH;EXP;MULT_ASSOC] THEN
    REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [GSYM MULT_ASSOC; GSYM (CONJUNCT2 EXP)] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SPECL ["r: num";"SUC(LENGTH (xs: num list))"] (CONJUNCT2 EXP)] THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [div_mod_lemma] THEN
    REWRITE_TAC [SPEC "x * (r EXP (LENGTH (xs: num list)))" RIGHT_ADD_DISTRIB] THEN
    SUBST_TAC [SPECL [
             "(x * (r EXP (LENGTH (xs: num list)))) * r";
             "(BASEN r xs) * r";
             "y * (r EXP (SUC(LENGTH (xs:num list))))";
             "BASEN r ys"] add_assoc_lemma] THEN
    ASM_REWRITE_TAC [EXP; BASEN] THEN
    SUBST_TAC [SPECL ["x*(r EXP(LENGTH(xs:num list)))";"r:num"] MULT_SYM] THEN
    SUBST_TAC [SPECL ["r:num";"x: num";"r EXP (LENGTH (xs:num list))"] MULT_ASSOC] THEN
    SUBST_TAC [SPECL ["r:num";"x: num"] MULT_SYM] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    REWRITE_TAC [GSYM (CONJUNCT2 EXP)] THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    REWRITE_TAC [ADD_ASSOC; GSYM RIGHT_ADD_DISTRIB]);;


let PURE_BASEN_MUL_COMBINE_PPS_CONV tm =
  %
  -----------------------------------------------------------------------------
  Take apart a term of the form "BASEN r [BASEN r xs; BASEN r ys]".
  -----------------------------------------------------------------------------
  %
  let r_tm, basen_basen = dest_basen tm in
  let [basen_r_xs; basen_r_ys] = fst (dest_list basen_basen) in
  let x_tms = fst (dest_list (rand basen_r_xs)) in
  let y_tms = fst (dest_list (rand basen_r_ys)) in
  %
  -----------------------------------------------------------------------------
  The add rule will extend both addend and augend by one digit, so the number
  of digits by which each is to be extended must be the same.  The augend (ys)
  will have a digit stripped off by the basecase, so it has to start off one
  digit longer.  If necessary, zero-extend the augend until it's one digit
  longer than the addend.  Then, if necessary, zero-extend the addend until
  it's only one digit shorter than the augend.
  -----------------------------------------------------------------------------
  %
  let y_length = max (length x_tms + 1) (length y_tms) in
  let y_growth = max 0 (y_length - length y_tms) in
  let y_tms = lengthen "0" y_growth y_tms in
  let x_length = max (length x_tms) (y_length - 1) in
  let x_growth = max 0 (x_length - length x_tms) in
  let x_tms = lengthen "0" x_growth x_tms in
  %
  -----------------------------------------------------------------------------
  Define a rule that restores the xs and ys in the resulting theorem.
  -----------------------------------------------------------------------------
  %
  let renormalize_conv growth =
    funpow growth ($THENC ONCE_BASEN_NORMALIZE_CONV) ALL_CONV in
  let fix_xs_conv = renormalize_conv x_growth in
  let fix_ys_conv = renormalize_conv y_growth in
  let fix_xs_ys_conv =
    RAND_CONV (RATOR_CONV (RAND_CONV fix_ys_conv)) THENC
    RATOR_CONV (RAND_CONV fix_xs_conv) in
  let renormalize_operands_rule =
    CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV fix_xs_ys_conv))) in
  %
  -----------------------------------------------------------------------------
  Specialize the theorems that depend on the radix.
  -----------------------------------------------------------------------------
  %
  let r = int_of_term r_tm in
  let radix_less = REWRITE_RULE [] (fast_LT_CONV (mk_comb ("$< 0", r_tm))) in
  let add_basecase =
    SPECL [r_tm; last y_tms] basen_mul_combine_pps_basecase in
  let add_step_lemma =
    MATCH_MP basen_mul_combine_pps_step_lemma radix_less in
  %
  -----------------------------------------------------------------------------
  Define a rule that extends a theorem about the sum of two partial products
  into a theorem about a sum of two partial products that are each one digit
  longer.
  -----------------------------------------------------------------------------
  %
  let add_rule (x_tm, y_tm) thm =
    let z_tm =
      (fst o dest_cons o rand o rand o fst o dest_conj o concl) thm in
    let x = int_of_term x_tm in
    let y = int_of_term y_tm in
    let z = int_of_term z_tm in
    let xy_plus_z = fast_add_with_carry x y z in
    let div_thm, mod_thm = fast_div_mod ((x+y)+z) r in
    ( (SUBS [div_thm;mod_thm]) o
      (SUBS [xy_plus_z]) o
      (MATCH_MP (SPECL [x_tm; y_tm] add_step_lemma))
    ) thm in
  %
  -----------------------------------------------------------------------------
  Extend the base case (which includes the final y digit) with all the
  operands' digits except the final y digit, then renormalize the operands.
  -----------------------------------------------------------------------------
  %
  let pps_thm = itlist2 add_rule (x_tms, butlast y_tms) add_basecase in
  renormalize_operands_rule (CONJUNCT1 pps_thm);;


%
Given a digit term (y), and a theorem of the form:
  |- BASEN r xs * BASEN r ys = BASEN r zs
return a theorem of the form
  |- (BASEN r xs) * (BASEN r (SNOC y ys)) = BASEN r <zs*r + y>
%

let BASEN_MUL_COMBINE_PPS_CONV =
  PURE_BASEN_MUL_COMBINE_PPS_CONV THENC
  REPEATC ONCE_BASEN_NORMALIZE_CONV;;

let BASEN_MUL_EXTEND_RULE y_tm =
  (CONV_RULE (RAND_CONV BASEN_MUL_COMBINE_PPS_CONV)) o
  (PURE_BASEN_MUL_EXTEND_RULE y_tm);;


%
Given a term of the form:
  |- BASEN r xs * BASEN r [...]
return a theorem of the form
  |- BASEN r xs * BASEN r (SNOC ...) = BASEN r zs
%

let basen_mul_basecase =
  PROVE (
    "! r x. x * BASEN r [] = BASEN r []",
    REWRITE_TAC [BASEN; MULT_CLAUSES]);;


let BASEN_MUL_SNOC_CONV tm =
  let (op, r_tm, basen_x, xs_tm, x_tms, basen_y, ys_tm, y_tms) =
    dest_binary_basen_comb tm in
  if not (op = "*") then fail else
  let mul_basecase = SPECL [r_tm; basen_x] basen_mul_basecase in
  rev_itlist BASEN_MUL_EXTEND_RULE y_tms mul_basecase;;


%
Given a term of the form:
  |- BASEN r xs * BASEN r [...]
return a theorem of the form
  |- BASEN r xs * BASEN r [...] = BASEN r zs
%

%----------------------------------------------------------------------------%
% Prenormalization added [JRH 94.01.29]                                      %
%                                                                            %
% Previously the resuting theorem would not always match the input term if   %
% that term involved denormalized arguments. Furthermore, such cases are now %
% quite a bit faster, since wasteful cycles in the main algorithm are        %
% avoided.                                                                   %
%----------------------------------------------------------------------------%

let STEP_BASEN_MUL_CONV =
  let norm1_conv = RAND_CONV(REPEATC ONCE_BASEN_NORMALIZE_CONV) in
  let snoc_to_cons_multiplier =
    CONV_RULE((RATOR_CONV o funpow 3 RAND_CONV) CONS_OF_SNOC_CONV) in
  let prenorm_conv = RATOR_CONV norm1_conv THENC norm1_conv in
  \tm. let nth = prenorm_conv tm in
       let th = snoc_to_cons_multiplier(BASEN_MUL_SNOC_CONV(rhs(concl nth))) in
       nth TRANS th;;

%----------------------------------------------------------------------------%
% Recursive O(n^log_2(3) version added; previous version renamed             %
% STEP_BASEN_MUL_CONV.            [JRH 94.01.30]                             %
%----------------------------------------------------------------------------%

let BASEN_MUL_CONV =
  letrec strip_op op tm =
    (let l,r = dest_binary_comb op tm in (strip_op op l)@(strip_op op r)) ?
    [tm] in
  let mk_op op = curry mk_comb o curry mk_comb op in
  let AC_CANON_CONV(ass,sym) tm =
    let op = (fst o strip_comb o rhs o snd o strip_forall o concl) sym in
    let ulist = strip_op op tm in
    if length ulist < 2 then fail else
    let olist = sort $<< ulist in
    if olist = ulist then fail else
    EQT_ELIM(AC_CONV(ass,sym) (mk_eq(tm,end_itlist (mk_op op) olist))) in
  let BASEN_MAP0 = PROVE
   ("!b (l:num list). BASEN b (MAP (\k. 0) l) = 0",
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[MAP; BASEN; MULT_CLAUSES; ADD_CLAUSES]) in
  let BASEN_APPEND_MAP0 = PROVE
   ("!b p (q:num list).
       BASEN b(APPEND p (MAP (\k. 0) q)) = (b EXP (LENGTH q)) * BASEN b p",
    REWRITE_TAC
     [BASEN_MAP0; BASEN_APPEND; LENGTH_MAP; ADD_CLAUSES; MULT_CLAUSES]) in
  let [recth1; recth2; recth3; recth4] = (CONJUNCTS o PROVE)
   ("((LENGTH x0 = LENGTH y0) /\
      (MAP (\k. 0) x0 = zl) /\
      (APPEND d zl = d') /\
      (APPEND p1 zl = p1') /\
      (APPEND x1 x0 = x) /\
      (APPEND y1 y0 = y) /\
      (BASEN b x0 + BASEN b dx = BASEN b x1) /\
      (BASEN b y0 + BASEN b dy = BASEN b y1) /\
      (BASEN b p1' + BASEN b p0 = BASEN b m) /\
      (BASEN b p2 + BASEN b d = BASEN b m) /\
      (BASEN b d' + BASEN b m = BASEN b res) /\
      (BASEN b x0 * BASEN b y0 = BASEN b p0) /\
      (BASEN b x1 * BASEN b y1 = BASEN b p1) /\
      (BASEN b dx * BASEN b dy = BASEN b p2)
          ==> (BASEN b x * BASEN b y = BASEN b res)) /\
     ((LENGTH x0 = LENGTH y0) /\
      (MAP (\k. 0) x0 = zl) /\
      (APPEND d zl = d') /\
      (APPEND p1 zl = p1') /\
      (APPEND x1 x0 = x) /\
      (APPEND y1 y0 = y) /\
      (BASEN b x1 + BASEN b dx = BASEN b x0) /\
      (BASEN b y0 + BASEN b dy = BASEN b y1) /\
      (BASEN b p1' + BASEN b p0 = BASEN b m) /\
      (BASEN b p2 + BASEN b m = BASEN b d) /\
      (BASEN b d' + BASEN b m = BASEN b res) /\
      (BASEN b x0 * BASEN b y0 = BASEN b p0) /\
      (BASEN b x1 * BASEN b y1 = BASEN b p1) /\
      (BASEN b dx * BASEN b dy = BASEN b p2)
          ==> (BASEN b x * BASEN b y = BASEN b res)) /\
     ((LENGTH x0 = LENGTH y0) /\
      (MAP (\k. 0) x0 = zl) /\
      (APPEND d zl = d') /\
      (APPEND p1 zl = p1') /\
      (APPEND x1 x0 = x) /\
      (APPEND y1 y0 = y) /\
      (BASEN b x0 + BASEN b dx = BASEN b x1) /\
      (BASEN b y1 + BASEN b dy = BASEN b y0) /\
      (BASEN b p1' + BASEN b p0 = BASEN b m) /\
      (BASEN b p2 + BASEN b m = BASEN b d) /\
      (BASEN b d' + BASEN b m = BASEN b res) /\
      (BASEN b x0 * BASEN b y0 = BASEN b p0) /\
      (BASEN b x1 * BASEN b y1 = BASEN b p1) /\
      (BASEN b dx * BASEN b dy = BASEN b p2)
          ==> (BASEN b x * BASEN b y = BASEN b res)) /\
     ((LENGTH x0 = LENGTH y0) /\
      (MAP (\k. 0) x0 = zl) /\
      (APPEND d zl = d') /\
      (APPEND p1 zl = p1') /\
      (APPEND x1 x0 = x) /\
      (APPEND y1 y0 = y) /\
      (BASEN b x1 + BASEN b dx = BASEN b x0) /\
      (BASEN b y1 + BASEN b dy = BASEN b y0) /\
      (BASEN b p1' + BASEN b p0 = BASEN b m) /\
      (BASEN b p2 + BASEN b d = BASEN b m) /\
      (BASEN b d' + BASEN b m = BASEN b res) /\
      (BASEN b x0 * BASEN b y0 = BASEN b p0) /\
      (BASEN b x1 * BASEN b y1 = BASEN b p1) /\
      (BASEN b dx * BASEN b dy = BASEN b p2)
          ==> (BASEN b x * BASEN b y = BASEN b res))",
    REPEAT CONJ_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (ASSUME_TAC o SYM)) THEN
    TRY(UNDISCH_TAC "BASEN b m = (BASEN b p2) + (BASEN b d)") THEN
    ASM_REWRITE_TAC[BASEN_APPEND_MAP0] THEN REWRITE_TAC[BASEN_APPEND] THEN
    ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ADD_CLAUSES] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN TRY(DISCH_THEN(ASSUME_TAC o SYM)) THEN
    REWRITE_TAC[GSYM ADD_ASSOC; GSYM MULT_ASSOC] THENL
     (let tac =
        MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL EQ_MONO_ADD_EQ)))) THEN
        EXISTS_TAC
          "(b EXP (LENGTH (x0:num list))) * (BASEN b dx * BASEN b dy)" THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[ADD_ASSOC] THEN
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) []
         [GSYM LEFT_ADD_DISTRIB] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM MULT_ASSOC] in
     [tac; ALL_TAC; ALL_TAC; tac]) THEN
    CONV_TAC(DEPTH_CONV(AC_CANON_CONV(MULT_ASSOC,MULT_SYM))) THEN
    CONV_TAC(AC_CONV(ADD_ASSOC,ADD_SYM))) in
  let [zero_tm; mult_tm; basen_tm; rep_tm; app_tm; len_tm; map_tm] =
       ["0"; "$*"; "BASEN";
        "REPLICATE:num->num->(num)list";
        "APPEND:(num list) -> (num list) -> (num list)";
        "LENGTH:(num)list->num"; "MAP (\k:num. 0)"] in
  let REFL_0 = REFL zero_tm in
  let MAP0_THM = PROVE
   ("(MAP (\k:num. 0) [] = []) /\
     (MAP (\k:num. 0) (CONS h t) = CONS 0 (MAP (\k:num. 0) t))",
    REWRITE_TAC[MAP] THEN BETA_TAC THEN REWRITE_TAC[]) in
  let mk_nlist tlist = mk_list(tlist,":num") in
  let padout n btm =
    let op,lis = dest_comb btm in
    let tml,ty = dest_list lis in
    mk_comb(op,mk_list(append (replicate "0" (n - length tml)) tml,ty)) in
  let norm_cnv = REPEATC ONCE_BASEN_NORMALIZE_CONV in
  let norm2_cnv = RATOR_CONV(RAND_CONV norm_cnv) THENC (RAND_CONV norm_cnv) in
  letrec BASEN_MUL_CONV tm =
    let _,[tm1;tm2] = (assert (curry$= mult_tm) # I) (strip_comb tm) in
    let basetm = rator tm1 in
    if not rator tm2 = basetm then failwith `Different bases` else
    let _,base = (assert (curry$=basen_tm) # int_of_term) (dest_comb basetm) in
    let th = norm2_cnv tm in
    let tm' = concl th in
    if not $= (dest_eq tm') then th TRANS (BASEN_MUL_CONV (rhs tm')) else
    let [lis1;lis2] = map (fst o dest_list o rand) [tm1; tm2] in
    let [len1;len2] = map length [lis1;lis2] in
    let n = ((max len1 len2) + 1) / 2 in
    if not (len1 > n & len2 > n & n > 7) then STEP_BASEN_MUL_CONV tm else
    let bpow = funpow n (curry$* base) 1 in
    let lis1a,lis1b = chop_list (len1 - n) lis1
    and lis2a,lis2b = chop_list (len2 - n) lis2 in
    let x0 = int_of_basen (mk_comb(rator tm1,mk_nlist lis1b))
    and x1 = int_of_basen (mk_comb(rator tm1,mk_nlist lis1a))
    and y0 = int_of_basen (mk_comb(rator tm1,mk_nlist lis2b))
    and y1 = int_of_basen (mk_comb(rator tm1,mk_nlist lis2a)) in
    let dx = absolute_value(x1 - x0)
    and dy = absolute_value(y1 - y0) in
    let p0 = x0 * y0
    and p1 = x1 * y1
    and p2 = dx * dy in
    let  m = bpow * p1 + p0 in
    let  d = (x1 < x0 = y1 < y0) => m - p2 | m + p2 in
    let res = bpow * d + m in
    let tof = curry basen_of_int base in
    let [x0t; y0t] = map (padout n o tof) [x0; y0] in
    let mxt,Mxt = x0 < x1 => (x0t,tof x1) | (tof x1,x0t)
    and myt,Myt = y0 < y1 => (y0t,tof y1) | (tof y1,y0t) in
    let zl_tm = mk_nlist(replicate zero_tm n) in
    let cth = end_itlist CONJ
     [let th = PURE_REWRITE_CONV[LENGTH; INV_SUC_EQ]
       (mk_eq(mk_comb(len_tm,rand x0t),mk_comb(len_tm,rand y0t))) in
      EQ_MP (SYM th) REFL_0;
      PURE_REWRITE_CONV[MAP0_THM] (mk_comb(map_tm,rand x0t));
      APPEND_CONV(mk_op app_tm (rand(tof d)) zl_tm);
      APPEND_CONV(mk_op app_tm (rand(tof p1)) zl_tm);
      APPEND_CONV(mk_op app_tm (rand(tof x1)) (rand x0t));
      APPEND_CONV(mk_op app_tm (rand(tof y1)) (rand y0t));
      (BASEN_ADD_CONV(mk_op "$+" mxt (tof dx))) TRANS
        (SYM(REPEATC ONCE_BASEN_NORMALIZE_CONV Mxt));
      (BASEN_ADD_CONV(mk_op "$+" myt (tof dy))) TRANS
        (SYM(REPEATC ONCE_BASEN_NORMALIZE_CONV Myt));
      BASEN_ADD_CONV(mk_op "$+" (tof (bpow * p1)) (tof p0));
      (x1 < x0 = y1 < y0) =>
        BASEN_ADD_CONV(mk_op "$+" (tof p2) (tof d)) |
        BASEN_ADD_CONV(mk_op "$+" (tof p2) (tof m));
      BASEN_ADD_CONV(mk_op "$+" (tof (bpow * d)) (tof m));
      BASEN_MUL_CONV(mk_op "$*" x0t y0t);
      BASEN_MUL_CONV(mk_op "$*" (tof x1) (tof y1));
      BASEN_MUL_CONV(mk_op "$*" (tof dx) (tof dy))] in
    let elth = y0 < y1 => (x0 < x1 => recth1 | recth2) |
                          (x0 < x1 => recth3 | recth4) in
    MATCH_MP elth cth in
  BASEN_MUL_CONV;;

%
-------------------------------------------------------------------------------
BASEN_DIV_CONV : conv
BASEN_MOD_CONV : conv

Synopsis:

Proves the result of dividing one numeral by another, or taking the modulus
of one numeral by another.

Description:

If m and n are lists of digits in base r, and p is the list of digits in the
base-r numeral representing the sum of m and n, then BASEN_DIV_CONV returns
the theorem:

        |- (BASEN r m DIV BASEN r n) = BASEN r p

and BASEN_MOD_CONV returns the theorem:

        |- (BASEN r m MOD BASEN r n) = BASEN r p

Failure:

The argument term must be of the form "BASEN r [...] <DIV or MOD> BASEN r
[...]", and the radix of the two numerals must be the same, and the radix must
be a numeric constant that is at least 2, and all elements of the digit lists
must be numeric constants, and must be less than the radix, and the divisor
must be nonzero.

Examples:

#BASEN_DIV_CONV "BASEN 10 [3;4;5] DIV BASEN 10 [3;4;5]";;
|- BASEN 10 [3;4;5] DIV BASEN 10 [3;4;5] = BASEN 10 [1]

#BASEN_DIV_CONV "BASEN 2 [1;1;1;1] DIV BASEN 2 [1;1;1;0]";;
|- BASEN 2 [1;1;1;1] DIV BASEN 2 [1;1;1;0]) = BASEN 2 [1]

#BASEN_DIV_CONV "BASEN 16 [8;10;14] DIV BASEN 16 [12;4]";;
|- BASEN 16 [8;10;14] DIV BASEN 16 [12;4]) = BASEN 16 [11]

#BASEN_MOD_CONV "BASEN 10 [3;4;5] MOD BASEN 10 [3;4;5]";;
|- BASEN 10 [3;4;5] MOD BASEN 10 [3;4;5] = BASEN 10 []

#BASEN_MOD_CONV "BASEN 2 [1;1;1;1] MOD BASEN 2 [1;1;1;0]";;
|- BASEN 2 [1;1;1;1] MOD BASEN 2 [1;1;1;0]) = BASEN 2 [1]

#BASEN_MOD_CONV "BASEN 16 [8;10;14] MOD BASEN 16 [12;4]";;
|- BASEN 16 [8;10;14] MOD BASEN 16 [12;4]) = BASEN 16 [4;2]
-------------------------------------------------------------------------------
%

%
Prove some theorems about DIV and MOD that should be in arith theory.
%

let LESS_DIV =
  ( (GENL ["n: num"; "k: num"]) o
    DISCH_ALL o
    (REWRITE_RULE [MULT_CLAUSES; ADD_CLAUSES]) o
    (SPEC "0") o
    UNDISCH_ALL o
    (SPECL ["n: num"; "k: num"])
  ) DIV_MULT;;

let LESS_DIV_MOD =
  GENL ["n: num"; "k: num"] (DISCH_ALL
    (LIST_CONJ (map (UNDISCH_ALL o SPEC_ALL) [LESS_DIV; LESS_MOD])));;

%
Prove a lemma for the case when the dividend is less than the divisor.
%

let less_divmod_thm =
  PROVE (
    "! dividend divisor r. ((BASEN r []) * divisor) + dividend = dividend",
    REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]);;


let basen_divmod_conv div_or_mod tm =
  %
  -----------------------------------------------------------------------------
  Take apart the term and verify that it's a DIV or MOD.
  -----------------------------------------------------------------------------
  %
  let (op, r_tm, dividend_tm, xs_tm, x_tms, divisor_tm, ys_tm, y_tms) =
    dest_binary_basen_comb tm in
  if not (op = div_or_mod) then fail else
  %
  -----------------------------------------------------------------------------
  Convert the dividend and divisor into numbers.
  -----------------------------------------------------------------------------
  %
  let radix = int_of_term r_tm in
  let dividend = int_of_basen dividend_tm in
  let divisor = int_of_basen divisor_tm in
  if divisor = 0 then failwith `basen_divmod_conv --- division by zero` else
  %
  -----------------------------------------------------------------------------
  Check for the special case of a dividend less than the divisor, and when
  it occurs, return the theorem:
    |- ((0 * divisor) + dividend = dividend) /\ (dividend < divisor = T)
  -----------------------------------------------------------------------------
  %
  if dividend < divisor then
    let less_thm =
      BASEN_LT_CONV (mk_binary_comb "<" dividend_tm divisor_tm) in
    let divmod_thm =
      SPECL [dividend_tm; divisor_tm; r_tm] less_divmod_thm in
    CONJ divmod_thm less_thm
  else
  %
  -----------------------------------------------------------------------------
  Compute the quotient and remainder.
  -----------------------------------------------------------------------------
  %
  let quotient = dividend / divisor in
  let addend = divisor * quotient in
  let remainder = dividend - addend in
  %
  -----------------------------------------------------------------------------
  Convert the quotient and remainder into terms.
  -----------------------------------------------------------------------------
  %
  let quotient_tm = basen_of_int (radix, quotient) in
  let addend_tm = basen_of_int (radix, addend) in
  let remainder_tm = basen_of_int (radix, remainder) in
  %
  -----------------------------------------------------------------------------
  Prove the theorems:
    |- <quotient*divisor> + remainder = dividend
    |- quotient * divisor = <quotient*divisor>
    |- (quotient * divisor) + remainder = dividend
    |- remainder < divisor = T
  -----------------------------------------------------------------------------
  %
  let sum_thm = BASEN_ADD_CONV (mk_binary_comb "+" addend_tm remainder_tm) in
  let prod_thm = BASEN_MUL_CONV (mk_binary_comb "*" quotient_tm divisor_tm) in
  let divmod_thm = SUBS_OCCS [[1], SYM prod_thm] sum_thm in
  let less_thm = BASEN_LT_CONV (mk_binary_comb "<" remainder_tm divisor_tm) in
  %
  -----------------------------------------------------------------------------
  Return the theorem:
    |- ((quotient * divisor) + remainder = dividend) /\ (remainder < divisor = T)
  -----------------------------------------------------------------------------
  %
  CONJ divmod_thm less_thm;;


let BASEN_DIV_CONV =
  let div_lemma = PROVE (
    "!dividend divisor quotient remainder.
      ((quotient * divisor) + remainder = dividend) /\ (remainder < divisor = T) ==>
        (dividend DIV divisor = quotient)",
    REPEAT GEN_TAC
    THEN SUBST_TAC [ISPECL ["(quotient * divisor) + remainder";"dividend:num"] EQ_SYM_EQ]
    THEN REWRITE_TAC []
    THEN DISCH_TAC
    THEN POP_ASSUM (
      ASSUME_TAC o (EXISTS (
          "?remainder. (dividend = (quotient * divisor) + remainder) /\
            remainder < divisor","remainder: num")))
      THEN ACCEPT_TAC (UNDISCH (SPECL
          ["divisor: num";"dividend: num";"quotient: num"]
          DIV_UNIQUE))) in
  \ tm.
  ( MATCH_MP div_lemma (basen_divmod_conv "DIV" tm)
  ) ? failwith `BASEN_DIV_CONV`;;

let BASEN_MOD_CONV =
  let mod_lemma = PROVE (
    "!dividend divisor quotient remainder.
      ((quotient * divisor) + remainder = dividend) /\ (remainder < divisor = T) ==>
        (dividend MOD divisor = remainder)",
    REPEAT GEN_TAC
    THEN SUBST_TAC [ISPECL ["(quotient * divisor) + remainder";"dividend:num"] EQ_SYM_EQ]
    THEN REWRITE_TAC []
    THEN DISCH_TAC
    THEN POP_ASSUM (
      ASSUME_TAC o (EXISTS (
          "?quotient. (dividend = (quotient * divisor) + remainder) /\
            remainder < divisor","quotient: num")))
      THEN ACCEPT_TAC (UNDISCH (SPECL
          ["divisor: num";"dividend: num";"remainder: num"]
          MOD_UNIQUE))) in
  \ tm.
  ( MATCH_MP mod_lemma (basen_divmod_conv "MOD" tm)
  ) ? failwith `BASEN_MOD_CONV`;;



%
-------------------------------------------------------------------------------
BASEN_EXP_CONV : conv

Synopsis:

Proves the result of raising one numeral to the power specified by another.

Description:

If m and n are lists of digits in base r, and p is the list of digits in the
base-r numeral representing the sum of m and n, then BASEN_EXP_CONV returns
the theorem:

        |- (BASEN r m EXP BASEN r n) = BASEN r p

Failure:

The argument to BASEN_EXP_CONV must be of the form "BASEN r [...] EXP BASEN r
[...]", and the radix of the two numerals must be the same, and the radix must
be a numeric constant that is at least 2, and all elements of the digit lists
must be numeric constants, and must be less than the radix.

Examples:

#BASEN_EXP_CONV "BASEN 10 [2] EXP BASEN 10 [1;2]";;
|- BASEN 10 [2] EXP BASEN 10 [1;2] = BASEN 10 [4;0;9;6]

#BASEN_EXP_CONV "BASEN 2 [1;1] EXP BASEN 2 [1;0]";;
|- BASEN 2 [1;1] EXP BASEN 2 [1;0]) = BASEN 2 [1;0;0;1]

#BASEN_EXP_CONV "BASEN 16 [1;0] EXP BASEN 16 [4]";;
|- BASEN 16 [1;0] EXP BASEN 16 [4]) = BASEN 16 [1;0;0;0;0]
-------------------------------------------------------------------------------
%

%
Knuth describes this algorithm (which he calls the S-and-X method) in The Art
of Computer Programming, volume 2, section 4.6.3 (Evaluation of Powers).
%

let BASEN_EXP_CONV =
  let basen_exp_zero =
    PROVE (
      "! r x. x EXP (BASEN r []) = BASEN r [1]",
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [BASEN; LENGTH; EXP; MULT_CLAUSES; ADD_CLAUSES; num_CONV "1"]) in
  let basen_exp_one =
    PROVE (
      "! r x. x EXP (BASEN r [1]) = x",
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [BASEN; LENGTH; EXP; MULT_CLAUSES; ADD_CLAUSES; num_CONV "1"]) in
  let basen_exp_0bit =
    PROVE (
      "! x y n.
        (x EXP n = y) ==> (x EXP (n+n) = y*y)",
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [EXP_ADD]) in
  let basen_exp_1bit =
    PROVE (
      "! r x y n.
        (x EXP n = y) ==> (x EXP ((n+n)+(BASEN r [1])) = (y*y)*x)",
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [EXP_ADD; basen_exp_one]) in
  \ tm.
  (
  %
  -----------------------------------------------------------------------------
  Take apart the input term and check that it's an exponentiation.
  -----------------------------------------------------------------------------
  %
  let (op, r_tm, basen_x, xs_tm, x_tms, basen_n, ns_tm, n_tms) =
    dest_binary_basen_comb tm in
  if not (op = "EXP") then fail else
  %
  -----------------------------------------------------------------------------
  Get a binary representation of the exponent.
  -----------------------------------------------------------------------------
  %
  let all_n_bits = numeral_of_int (2, int_of_basen basen_n) in
  %
  -----------------------------------------------------------------------------
  Handle the special case of a zero exponent.
  -----------------------------------------------------------------------------
  %
  if all_n_bits = [] then
    SPECL [r_tm; basen_x] basen_exp_zero
  else
  %
  -----------------------------------------------------------------------------
  Specialize the two step-theorems now, rather than in the loop.
  -----------------------------------------------------------------------------
  %
  let bit1_thm = SPECL [r_tm; basen_x] basen_exp_1bit in
  let bit0_thm = SPEC basen_x basen_exp_0bit in
  %
  -----------------------------------------------------------------------------
  Compute initial values for other pieces of loop state.
  -----------------------------------------------------------------------------
  %
  let init_thm = SPECL [r_tm; basen_x] basen_exp_one in
  let basen_1 = mk_binary_comb "BASEN" r_tm "[1]" in
  %
  -----------------------------------------------------------------------------
  Given a theorem of the form:
    |- BASEN <r> <x> EXP BASEN <r> <n> = BASEN <r> <y>
  return a theorem of the form:
    |- BASEN <r> <x> EXP BASEN <r> <n+n+1> = BASEN <r> <y*y*x>
  -----------------------------------------------------------------------------
  %
  let exp1_rule thm =
    let old_n, old_y = (rand # I) (dest_eq (concl thm)) in
    let nn1 = mk_binary_comb "+" (mk_binary_comb "+" old_n old_n) basen_1 in
    let yyx = mk_binary_comb "*" (mk_binary_comb "*" old_y old_y) basen_x in
    let nn1_thm = (ONCE_DEPTH_CONV BASEN_ADD_CONV THENC BASEN_ADD_CONV) nn1 in
    let yyx_thm = (ONCE_DEPTH_CONV BASEN_MUL_CONV THENC BASEN_MUL_CONV) yyx in
    SUBS [nn1_thm; yyx_thm] (MP (SPECL [old_y; old_n] bit1_thm) thm) in
  %
  -----------------------------------------------------------------------------
  Given a theorem of the form:
    |- BASEN <r> <x> EXP BASEN <r> <n> = BASEN <r> <y>
  return a theorem of the form:
    |- BASEN <r> <x> EXP BASEN <r> <n+n> = BASEN <r> <y*y>
  -----------------------------------------------------------------------------
  %
  let exp0_rule thm =
    let old_n, old_y = (rand # I) (dest_eq (concl thm)) in
    let nn = mk_binary_comb "+" old_n old_n in
    let yy = mk_binary_comb "*" old_y old_y in
    let nn_thm = BASEN_ADD_CONV nn in
    let yy_thm = BASEN_MUL_CONV yy in
    SUBS [nn_thm; yy_thm] (MP (SPECL [old_y; old_n] bit0_thm) thm) in
  %
  -----------------------------------------------------------------------------
  Apply the appropriate rule depending on the next exponent bit.
  -----------------------------------------------------------------------------
  %
  let exp_bit_rule b =
    if b = 0 then
      exp0_rule
    else
      exp1_rule
    in
  %
  -----------------------------------------------------------------------------
  Apply that function for every exponent bit after the first.
  -----------------------------------------------------------------------------
  %
  rev_itlist exp_bit_rule (tl all_n_bits) init_thm
  ) ? failwith `BASEN_EXP_CONV`;;


%
-------------------------------------------------------------------------------
BASEN_CONV : conv

Synopsis:

Proves what the numeric value of a numeral is.

Note:

This function should be deleted once numerals are integrated into the parser
and pretty printer, since numeric constants will then no longer be used
outside the numeral library.

Description:

If m is a list of base-r digits, with a value of n, then BASEN_CONV
"BASEN r m" returns the theorem:

        |- BASEN r m = n

Failure:

The argument to BASEN_CONV must be of the form "BASEN r [...]", the radix
must be a numeric constant with a value of at least 2, and all elements of the
digit list must be numeric constants less than r.

Examples:

#BASEN_CONV "BASEN 2 [1;0;0;0;0;0]";;
|- BASEN 2 [1;0;0;0;0;0] = 32

#BASEN_CONV "BASEN 10 [2;6;5]";;
|- BASEN 10 [2;6;5] = 265

#BASEN_CONV "BASEN 16 [12;0;0]";;
|- BASEN 16 [12;0;0] = 3072

See also:

dest_basen, BASEN_OF_NUM_CONV, int_of_basen.
-------------------------------------------------------------------------------
%

let BASEN_CONV tm =
  ( let basen_r_tm, digits_tm = dest_comb tm in
    let basen_tm, r_tm = dest_comb basen_r_tm in
    if not (basen_tm = "BASEN") then fail else
    let digit_tms = fst (dest_list digits_tm) in
    let digit_values = map int_of_term digit_tms in
    let r_value = int_of_term r_tm in
    let tm_value = int_of_numeral (r_value, digit_values) in
    let value_tm = term_of_int tm_value in
    let snoc_lemma = SNOC_OF_CONS_CONV digits_tm in
    PROVE (
      mk_eq (tm,value_tm),
      SUBST_TAC [snoc_lemma] THEN
      REWRITE_TAC [BASEN_SNOC] THEN
      ONCE_REWRITE_TAC [BASEN] THEN
      REDUCE_TAC)
  ) ? failwith `BASEN_CONV`;;



%
-------------------------------------------------------------------------------
BASEN_OF_NUM_CONV : conv

Synopsis:

Proves what the numeral is that represents a given numeric value in a given
radix.

Note:

This should be deleted once numerals are integrated into the parser and pretty
printer, since numeric constants will then no longer be used outside the
numeral library.

Description:

If m and r are numeric constants, and n is a list of base-r digits with a value
of m (in base r), then BASEN_OF_NUM_CONV "r" "m" returns the theorem:

        |- BASEN_DIGITS r m = n

Failure:

The radix must be a numeric constant with a value of at least 2, and the value
must be a numeric constant.

Examples:

#BASEN_OF_NUM_CONV "2" "32";;
|- 32 = BASEN 2 [1;0;0;0;0;0]

#BASEN_OF_NUM_CONV "10" "265";;
|- 265 = BASEN 10 [2;6;5]

#BASEN_OF_NUM_CONV "16" "3072";;
|- 3072 = BASEN 16 [12;0;0]

See also:

mk_basen, BASEN_CONV, basen_of_int.
-------------------------------------------------------------------------------
%

let BASEN_OF_NUM_CONV (r_tm: term) (value_tm: term) =
  ( let tm_value = int_of_term value_tm in
    let r_value = int_of_term r_tm in
    let digit_values = numeral_of_int (r_value, tm_value) in
    let digit_tms = map term_of_int digit_values in
    let digits_tm = mk_list (digit_tms, ": num") in
    let basen_r_digits_tm = mk_binary_comb "BASEN" r_tm digits_tm in
    let snoc_lemma = SNOC_OF_CONS_CONV digits_tm in
    PROVE (
      mk_eq (value_tm, basen_r_digits_tm),
      SUBST_TAC [snoc_lemma] THEN
      REWRITE_TAC [BASEN_SNOC] THEN
      ONCE_REWRITE_TAC [BASEN] THEN
      REDUCE_TAC)
  ) ? failwith `BASEN_OF_NUM_CONV`;;



%
-------------------------------------------------------------------------------
NUM_ARITH_CONV : conv
NUM_ARITH_RULE : thm -> thm
NUM_ARITH_TAC : tac

Synopsis:

Reduce all expressions of numerals as much as possible (except don't convert
to or from numeric constants).

Description:

Given a term (or theorem, or goal) containing functions of BASEN numerals,
replace the expressions with their values whenever possible.  As long as an
expression sticks to a single radix, the arithmetic functions +, -, *, /,
MOD, EXP, SUC, PRE, <, >, <=, >=, and = can be reduced.

As a rough guide, reduction of an expression involving +, -, PRE, SUC, <, >,
<=, >=, or = will take about 10 inferences per digit.  Reduction of an
expression involving *, /, or MOD will take about 10 inferences per digit,
squared.  Expressions involving EXP will take about 10 inferences per digit,
cubed.

Examples:

#g "((BASEN 10 [2;3;4;5] * BASEN 10 [5;1]) - BASEN 10 [1;0;0;0;0;0]) >
     BASEN 10 [4;5;7;8;9] DIV BASEN 10 [2;4]";;
#"(((BASEN 10[2;3;4;5]) * (BASEN 10[5;1])) - (BASEN 10[1;5;4;7;9;4])) >
 ((BASEN 10[4;5;7;8;9]) DIV (BASEN 10[2;4]))"

() : void
Run time: 0.0s

#e NUM_ARITH_TAC;;
OK..
goal proved
|- (((BASEN 10[2;3;4;5]) * (BASEN 10[5;1])) - (BASEN 10[1;0;0;0;0;0])) >
   ((BASEN 10[4;5;7;8;9]) DIV (BASEN 10[2;4]))

Previous subproof:
goal proved
() : void
Run time: 5.6s
Intermediate theorems generated: 1386

#NUM_ARITH_CONV "BASEN 10 [2] EXP (BASEN 10 [2] EXP BASEN 10 [8])";;
;;; GC
;;; GC
;;; GC
;;; GC
|- (BASEN 10[2]) EXP ((BASEN 10[2]) EXP (BASEN 10[8])) =
   BASEN
   10
   [1;1;5;7;9;2;0;8;9;2;3;7;3;1;6;1;9;5;4;2;3;5;7;0;9;8;5;0;0;8;6;8;7;9;
    0;7;8;5;3;2;6;9;9;8;4;6;6;5;6;4;0;5;6;4;0;3;9;4;5;7;5;8;4;0;0;7;9;1;
    3;1;2;9;6;3;9;9;3;6]
Run time: 476.6s
Garbage collection time: 17.5s
Intermediate theorems generated: 83450

See also:

REDUCE_CONV.
-------------------------------------------------------------------------------
%

%
Normalization *must* be done first, because many of the other conversions
don't work on unnormalized inputs.
%

let NUM_ARITH_CONV =
  let once_num_arith_conv = end_itlist $ORELSEC
      [ BASEN_NORMALIZE_CONV;
        BASEN_ADD_CONV;
        BASEN_SUB_CONV;
        BASEN_MUL_CONV;
        BASEN_DIV_CONV;
        BASEN_MOD_CONV;
        BASEN_EXP_CONV;
        BASEN_EQ_CONV;
        BASEN_LT_CONV;
        BASEN_LE_CONV;
        BASEN_GT_CONV;
        BASEN_GE_CONV;
        IS_BASEN_CONV;
        IS_NORMALIZED_CONV;
        BASEN_SUC_CONV;
        BASEN_PRE_CONV ] in
  DEPTH_CONV once_num_arith_conv;;

let NUM_ARITH_RULE = CONV_RULE NUM_ARITH_CONV;;

let NUM_ARITH_TAC = CONV_TAC NUM_ARITH_CONV;;
