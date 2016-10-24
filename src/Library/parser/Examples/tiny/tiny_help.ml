%
  load in the prog_logic library.
%

load_library `prog_logic88`;;

%
  Define the action symbols in terms of antiquotation.
%

let mk_plus (lhs,rhs) = "^lhs + ^rhs";;

let mk_minus (lhs,rhs) = "^lhs - ^rhs";;

let mk_mult (lhs,rhs) = "^lhs * ^rhs";;

let mk_neq (lhs,rhs) = "~(^lhs = ^rhs)";;

let mk_gt (lhs,rhs) = "^lhs > ^rhs";;

let mk_gte (lhs,rhs) = "^lhs >= ^rhs";;

let mk_lt (lhs,rhs) = "^lhs < ^rhs";;

let mk_lte (lhs,rhs) = "^lhs <= ^rhs";;

let mk_seq (lhs,rhs) = "MK_SEQ(^lhs,^rhs)";;

let mk_assign (lhs,rhs) = "MK_ASSIGN(^lhs,^rhs)";;

let mk_while (cond,com) = "MK_WHILE(^cond,^com)";;

let mk_if1 (cond,com) = "MK_IF1(^cond,^com)";;

let mk_if2 (cond,com1,com2) = "MK_IF2(^cond,^com1,^com2)";;

let mk_assert (thing) = "MK_ASSERT (^thing)";;

let mk_variant (thing) = "MK_VARIANT (^thing)";;

let mk_invariant (thing) = "MK_INVARIANT (^thing)";;

let mk_spec (P,C,Q) = "MK_SPEC(^P,^C,^Q)";;

let mk_t_spec (P,C,Q) = "T_SPEC(^P,^C,^Q)";;

% 
  Take a HOL expression (term), and convert to its semantic
  representation.
%

let mk_semantic (expr) = trans_term "s:string->num" expr;;

%
  Make the various primitive parts of the terms in question.
%

let mk_variable_name (var) = 
    if mem (hd (explode var)) (words `1 2 3 4 5 6 7 8 9 0`) then
       failwith `ERROR: integers not allowed as variable names.`
    else mk_const((concatl [`\``;var;`\``]),":string");; 

let is_int (thing) = 
   if can int_of_string thing then
      mk_const (thing,":num")
   else
      failwith (concat `ERROR: `
               (concat thing ` is not a :num.`));;

let mk_variable (var) = 
    if mem var [`T`;`F`] then
       failwith (concat `ERROR: `
                (concat var ` cannot be a variable of type ":num".`))
    else if mem (hd (explode var)) (words `1 2 3 4 5 6 7 8 9 0`) then
       is_int (var)
    else 
       mk_var(var,":num");;


