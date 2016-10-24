% File: mk_RCpredicate1.ml %

% Refinement Calculus theory of predicates: definitions %


% --- basic definitions --- %

let false_DEF = new_definition(`false_DEF`,"false = \(u:^state).F");;

let true_DEF = new_definition(`true_DEF`,"true = \(u:^state).T");;

let not_DEF = new_definition(`not_DEF`,"not (p:^pred) = \u. ~p u");;

let and_DEF = new_infix_definition(`and_DEF`,
   "$andd (p:^pred) q = \u. p u /\ q u");;

let or_DEF = new_infix_definition(`or_DEF`,
   "$or (p:^pred) q = \u. p u \/ q u");;

let imp_DEF = new_infix_definition(`imp_DEF`,
   "$imp (p:^pred) q = \u. p u ==> q u");;

let implies_DEF = new_infix_definition(`implies_DEF`,
   "$implies (p:^pred) q = !u. p u ==> q u");;


% --- general conjunction and disjunction of predicates --- %

let glb_DEF = new_definition (`glb_DEF`,
   "glb (P:^pred->bool) = \u. !p. P p ==> p u");;

let lub_DEF = new_definition (`lub_DEF`,
   "lub (P:^pred->bool) = \u. ?p. P p /\ p u");;


% --- monotonic functions on predicates --- %

let monotonic_DEF = new_definition (`monotonic_DEF`,
   "monotonic (f:^pred1->^pred2) = !p q. p implies q ==> f p implies f q");;

% --- fixpoints operators for functions on predicates --- %

let fix_DEF = new_definition (`fix_DEF`,
  "fix (f:^pred->^pred) = glb(\p. (f p) implies p)");;

let gfix_DEF = new_definition (`gfix_DEF`,
  "gfix (f:^pred->^pred) = lub(\p. p implies (f p))");;
