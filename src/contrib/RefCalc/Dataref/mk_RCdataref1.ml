% File: mk_RCdataref1.ml %

% The Data refinement calculus %


% --- abstraction and representation commands --- %

let abst_DEF = new_definition  % abstraction command %
  (`abst_DEF`,
   "abst (r:(*a#*c#*s)->bool) (q:^apred) =
     (\(k,u). ?a. r(a,k,u) /\ q(a,u))");;

let repr_DEF = new_definition  % representation command %
  (`repr_DEF`,
   "repr (r:(*a#*c#*s)->bool) (q:^cpred) =
     (\(a,u). !k. r(a,k,u) ==> q(k,u))");;


% ----- the data refinement relation ----- %

let dataref_DEF = new_definition(`dataref_DEF`,
   "dataref (r:(*a#*c#*s)->bool) c c' =
    ((abst r) seq c) ref (c' seq (abst r))");;

