% File: mk_RCbounded1.ml
   Bounded nondeterminism: definitions
%


% --- chains and continuity (bounded nondeterminism) --- %

let uchain_DEF = new_definition(`uchain_DEF`,
  "uchain (Q:num->^pred) = (!n. (Q n) implies (Q(SUC n)))");;

let ulimit_DEF = new_definition(`ulimit_DEF`,
  "ulimit (Q:num->^pred) = \s. ?n. Q n s");;

let ucontinuous_DEF = new_definition(`ucontinuous_DEF`,
  "ucontinuous (f:^ptrans12) =
    (!(Q:num->^pred1). uchain Q ==> (f (ulimit Q) = ulimit(\n. f (Q n))))");;


% --- chain of approximation for iteration --- %

let H_DEF = new_prim_rec_definition(`H_DEF`,
  "(H (g:^pred) (c:^ptrans) 0 q = (not g) andd q) /\ 
   (H g c (SUC n) q = ((not g) andd q) or (g andd (c(H g c n q))))");;


% --- backward data refinement --- %

let dual_DEF = new_definition(`dual_DEF`,
   "dual (c:^ptrans12) q = not (c (not q))");;

let bwdref_DEF = new_definition(`bwdref_DEF`,  % backward dataref %
   "bwdref (r:^arel) c c' =
       ((dual(abst r)) seq c) ref (c' seq (dual(abst r)))");;


% --- definitions needed for continuity arguments --- %

let max_DEF = new_prim_rec_definition(`max_DEF`,
    "(max (N:num->num) 0 = N 0) /\
     (max N (SUC n) = ((max N n < N(SUC n)) => N(SUC n) | max N n))");;

let finite_DEF = new_definition(`finite_DEF`,
   "finite (A:*->bool) = 
    (?f n. (!a. A a ==> ?i. i<n /\ (f i = a)))");;

