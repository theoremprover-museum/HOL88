% File: mk_RCactsys1.ml
   Action systems: definitions
%


% --- auxiliary definitions --- %

let EVERY2_DEF = new_list_rec_definition(`EVERY2_DEF`,
  "(EVERY2 (P:*->**->bool) [] yl = T) /\
   (EVERY2 P (CONS x xl) yl = P x (HD yl) /\ EVERY2 P xl (TL yl))");;


% --- new commands --- %

let magic_DEF = new_definition(`magic_DEF`,"(magic:^ptrans12) q = true");;

let ldch_DEF =   % demonic choice over a list %
 new_recursive_definition false list_Axiom `ldch_DEF`
  "(ldch [] = (magic:^ptrans12)) /\
   (ldch (CONS c cl) = c dch (ldch cl))";;

let lguard_DEF =   % the guard disjunction of an action list %
 new_recursive_definition false list_Axiom `lguard_DEF`
  "(lguard [] = (false:^pred)) /\
   (lguard (CONS (a:^action) al) = (FST a) or (lguard al))";;

let if2_DEF =   % guarded conditional %
  new_definition(`if2_DEF`,
   "if2 (g1:^pred2,c1:^ptrans12) (g2,c2) q = 
     (g1 or g2) andd (g1 imp (c1 q)) andd (g2 imp (c2 q))");;

let lif_DEF =   % multi-branch if with action list %
 new_recursive_definition false list_Axiom `lif_DEF`
  "(lif [] = (abort:^ptrans)) /\
   (lif (CONS (a:^action) al) =
      if2 a (lguard al,lif al))";;

let ldo_DEF =   % multi-branch do with action list %
 new_definition(`ldo_DEF`,
  "ldo (al:(^action)list) = do (lguard al) (lif al)");;

