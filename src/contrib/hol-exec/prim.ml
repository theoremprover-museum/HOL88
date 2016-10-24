% File "prim.ml": primitive definitions for hol-eval %
% sree@cs.ubc.ca %

% These don't work:
letrec pair_el n pair =
       if (n=1) then (fst pair)
       else
          pair_el (n-1) ((snd pair):* # **);;

let dest n cons_var = 
   if (n = 0) then (fst cons_var) 
   else
       if ((snd cons_var) = ()) then
          (fst cons_var) 
       else 
          if ((fst (snd cons_var)) = ()) then
             if (n=1) then (fst cons_var) 
             else  (snd cons_var)
          else 
             (pair_el n (fst (snd cons_var)));;
%

let suc n = n+1;;
let ml_suc n = n+1;;
let deSUC cons_var = cons_var - 1;;

let deHEAD cons_var = hd cons_var;;
let deTAIL cons_var = tl cons_var;;

% How do we define destructors for STRING %
let STRING a s = a ^ s;;
let deASCII cons_var = hd (explode cons_var);;
let deSTRING cons_var = implode (tl (explode cons_var));;

%
let NULL l1 = (null l1);;
let CONS h t = h.t;;
let SUC n = n+1;;
%

let ml_cons h t = h.t;;
let cons h t = h.t;;
let NIL = [];;

let F = false;;
let T = true;;
let string_APPEND s1 s2 = concat s1 s2;;

%
let forallbv n pred = pred (variable_vector "" n);
%

% PAIR, LET and UNCURRY defs%
let FIX_PAIR x y = (x,y);;
%
let FST pair = fst pair;; 
let SND pair = snd pair;;
let LET = (\f. (\x. f x));;
%

let ml_let = (\f. (\x. f x));;

%
let UNCURRY f pair  = 
    (f (FST pair) (SND pair));;
%

let ml_uncurry f pair  = 
    (f (fst pair) (snd pair));;


% Other defs%
% COND DOES NOT WORK! because of order of evaluation,
  when used in recursive functions - it goes into 
  infinite loop: arguments y and z are evaluated before
  COND is evaluated

let COND x y z = (if x then y else z);;
%
let FIX_IMP x y = if x then y else true;;
let FIX_AND x y = (x & y);;
let FIX_OR x y = (x or y);;
let FIX_NOT x = (not x);;

let FIX_PLUS x y = x + y;;
let FIX_MINUS x y = 
	if (x > y) then (x - y) else 0;;
let FIX_MULT x y = x * y;;
%
let DIV x y = x/y;;
let MOD x y = x - (y * (x/y));; 
%

let ml_div x y = x/y;;
let ml_mod x y = x - (y * (x/y));; 
%
letrec EXP base exp = COND (exp = 0) 1 (base * (EXP base (exp-1)));;
let pow x y = EXP x y;;
%
letrec ml_exp base exp = if (exp = 0) then 1 
			 else (base * (ml_exp base (exp-1)));;
let pow x y = ml_exp x y;;

letrec Log n =
	let half_n = n/2 in
	if (n=1) then 0 
	else (1+ Log (half_n));;

let FIX_GT x y = x > y;;
let FIX_LT x y = x < y;;

% Agrain typing prohibits this
let FIX_EQ x y =
    (COND (atom x) (x=y)
      (COND (empty y) (empty x) 
        ((hd x) = (dest 0 y))));;
%
 
let FIX_EQ x y = (x=y);;           
% List defs%
%
let MAP f list = map f list;;
letrec APPEND x y = 
      COND (null x) y 
        ((hd x).(APPEND (tl x) y));;

let LENGTH l = length l;;
%
let ml_map f list = map f list;;
letrec ml_append x y = 
      if (null x) then y 
      else ((hd x).(ml_append (tl x) y));;

let ml_length l = length l;;


let FIX_COMPOSE f g = f o g;;





