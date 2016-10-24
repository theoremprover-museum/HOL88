% File: mk_RCcommand1.ml %

% THE REFINEMENT CALCULUS theory RCcommands: definitions %


% ----- the refinement relation ----- %

let ref_DEF = new_infix_definition(`ref_DEF`,  
   "$ref (c:^ptrans12) c' = !q. (c q) implies (c' q)");;


% --- auxiliary commands useful for reasoning ---  %

let guard_DEF = new_definition 
  (`guard_DEF`,
  "guard (b:^pred) q = b imp q");;

let dch_DEF = new_infix_definition  % binary demonic choice %
  (`dch_DEF`,
  "$dch (c1:^ptrans12) (c2:^ptrans12) q = (c1 q) andd (c2 q)");;

let Dch_DEF = new_definition  % general demonic choice %
  (`Dch_DEF`,
  "Dch (C:^ptrans12->bool) q = glb (\p.?c. C c /\ (p = c q))");;

let ach_DEF = new_infix_definition  % binary angelic choice %
  (`ach_DEF`,
  "$ach (c1:^ptrans12) (c2:^ptrans12) q = (c1 q) or (c2 q)");;

let Ach_DEF = new_definition  % general angelic choice %
  (`Ach_DEF`,
  "Ach (C:^ptrans12->bool) q = lub (\p.?c. C c /\ (p = c q))");;

let mu_DEF = new_definition  % recursion %
  (`mu_DEF`,
   "mu (f:^ptrans12->^ptrans12) = Dch(\c. monotonic c /\ (f c) ref c)");;

let dolib_DEF = new_definition  
  (`dolib_DEF`,
   "dolib (g:^pred) c q =
         gfix(\p.(g andd (c p)) or ((not g) andd q))");;


% --- essential commands (names for predicate transformers) --- %

let abort_DEF = new_definition(`abort_DEF`,"(abort:^ptrans12) q = false");;

let assert_DEF = new_definition  
  (`assert_DEF`,
  "assert (p:^pred) q = p andd q");;

let nondass_DEF = new_definition  % demonic miraculous assignment %
  (`nondass_DEF`,
   "nondass (P:^state1->^state2->bool) (q:^pred2) = 
       \u. (!u'. P u u' ==> q u')");;

let assign_DEF = new_definition  % assignment: state-state function %
  (`assign_DEF`,
   "assign (e:^state1->^state2) (q:^pred2) =  \u. q(e u)");;

let skip_DEF = new_definition  % skip command %
  (`skip_DEF`,"skip (q:^pred) = q");;

let seq_DEF = new_infix_definition  % sequential composition %
  (`seq_DEF`,
  "$seq (c1:^ptrans23) (c2:^ptrans12) q = c1(c2 q)");;

let cond_DEF = new_definition  % if-else-command %
  (`cond_DEF`,
   "cond (g:^pred2) (c1:^ptrans12) c2 q = 
     (g andd (c1 q)) or ((not g) andd (c2 q))");;

let do_DEF = new_definition  % do as a recursion %
  (`do_DEF`,
   "do (g:^pred) (c:^ptrans) = 
      mu (\x. cond g (c seq x) skip)");;

let block_DEF = new_definition  % initialized block with vartype ":*" %
  (`block_DEF`,
   "block p (c:^eptrans) q =  \v. !(x:*). p(x,v) ==> c (\(x,v). q v)(x,v)");;


% --- "healthiness" properties of commands--- %

let strict_DEF = new_definition(`strict_DEF`,
 "strict (c:^ptrans12) = (c false = false)");;

let terminating_DEF = new_definition(`terminating_DEF`,
 "terminating (c:^ptrans12) = (c true = true)");;

let biconjunctive_DEF = new_definition(`biconjunctive_DEF`,
 "biconjunctive (c:^ptrans12) = 
  (!p q. c(p andd q) = (c p) andd (c q))");;

let uniconjunctive_DEF = new_definition(`uniconjunctive_DEF`,
 "uniconjunctive (c:^ptrans12) = 
  !P. c(glb P) = glb (\q. ?p. P p /\ (q = c p))");;

let conjunctive_DEF = new_definition(`conjunctive_DEF`,
 "conjunctive (c:^ptrans12) = 
  !P. (?p.P p) ==> (c(glb P) = glb (\q. ?p. P p /\ (q = c p)))");;


% --- monotonic function on predicate transformers --- %

let pmonotonic_DEF = new_definition(`pmonotonic_DEF`,
 "pmonotonic (f:^ptrans12->^ptrans34) =
  (!c c'. monotonic c /\ monotonic c' /\ c ref c' ==> (f c) ref (f c'))");;

let mono_mono_DEF = new_definition(`mono_mono_DEF`,
 "mono_mono(f:^ptrans12->^ptrans34) = !c. monotonic c ==> monotonic(f c)");;

let regular_DEF = new_definition(`regular_DEF`,
 "regular(f:^ptrans12->^ptrans34) =  pmonotonic f /\ mono_mono f");;

