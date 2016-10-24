%----------------------------------------------------------------

   File:         group_def.ml

   Description:  

   Defines groups as an extension of monoids.  Proves 2 theorems
   about groups.

   Author:       (c) P. J. Windley 1992

   Modification History:

   02JUN92 [PJW] --- Original file released.

   15JUN92 [PJW] --- Added sticky type flag.

   
----------------------------------------------------------------%

set_flag(`sticky`,true);;

loadf `abs_theory`;;

% flip an equailty thm %
let SYM_RULE =
  (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)) ? failwith `SYM_RULE`;;

system `/bin/rm group_def.th`;;

new_theory `group_def`;;

new_abstract_parent `monoid_def`;;

let GROUP = new_abstract_representation `group`
   [
    (`fn`,":* -> * -> *")
   ;
    (`id`,":*")
   ;
    (`inv`,":* -> *")
   ];;

new_theory_obligations
   (`IS_GROUP`,
    "!g:(*)group . IS_GROUP g = 
	(!x:* .fn g x (id g) = x) /\
	(!x:* .fn g (id g) x = x) /\
	(!x:* .fn g x (inv g x) = (id g)) /\
	(!x:* .fn g (inv g x) x = (id g)) /\
	(! x y z:*. (fn g x (fn g y z)) = (fn g (fn g x y) z))");;


let GROUP_EXTENDS_MONOID = ABS_TAC_PROOF
   (([],
     "! g:(*)group . IS_MONOID(monoid (fn g) (id g))"),
    EXPAND_THOBS_TAC `monoid_def`
    THEN ASM_REWRITE_TAC []
   );;

let IDENTITY_UNIQUE = 
    instantiate_abstract_theorem `monoid_def` `IDENTITY_UNIQUE` 
        ["m","monoid (fn (g:(*)group)) (id (g:(*)group))"]
        [GROUP_EXTENDS_MONOID];;

(type_of o hd o frees o concl o DISCH_ALL) IDENTITY_UNIQUE;;

save_thm (`IDENTITY_UNIQUE`,IDENTITY_UNIQUE);;

let LEFT_CANCELLATION = prove_abs_thm
   (`LEFT_CANCELLATION`,
     "! (g:(*)group) (x y a:*) . 
      ((fn g) a x = ((fn g) a y)) ==> (x = y)",
    REPEAT STRIP_TAC
    THEN ACCEPT_TAC (
      let t1 = (ASSUME "!x y z. fn g x(fn g y z) = fn g(fn g x y)z") and
          t2 = (ASSUME "!x. fn g(inv g x)x = id g") and
          t3 = (ASSUME "!x. fn g(id g) x  = x") and
          t4 = (ASSUME "fn g a x = fn g a y") in
      SYM_RULE (
      REWRITE_RULE [t1;t2;t3] (
      REWRITE_RULE [t2;t3;t4] (
      ISPECL ["(inv g a)";"a";"x"] t1))))
   );;


let INVERSE_INVERSE_LEMMA = prove_thm
   (`INVERSE_INVERSE_LEMMA`,
    "!(g:(*)group) . IS_GROUP(g) ==> !a .(((inv g) ((inv g) a)) = a)",
    STRIP_THOBS_TAC
    THEN GEN_TAC
    THEN ACCEPT_TAC (
	let t1 = ASSUME "!x. fn g x(inv g x) = id g" and
	    t2 = ASSUME "!x. fn g (inv g x)x = id g" in
	let LC_LEMMA = 
	      ISPECL ["inv g (inv g a)";
		      "a";"inv g a"] LEFT_CANCELLATION in
        MATCH_MP
	    LC_LEMMA
	    (TRANS (ISPEC "(inv g) a" t1) 
		   (SYM_RULE (ISPEC "a" t2))))
   );;

let ALTERNATE_INVERSE_INVERSE_LEMMA = TAC_PROOF
   (([],
    "!(g:(*)group)  . IS_GROUP(g) ==> ! a .(((inv g) ((inv g) a)) = a)"),
    STRIP_THOBS_THEN (\thm .
        let thl = CONJUNCTS thm in
        MAP_EVERY ASSUME_TAC thl THEN
        GEN_TAC THEN
        MATCH_MP_TAC (ISPECL ["inv g (inv g a)";
		      "a";"inv g a"] LEFT_CANCELLATION) THEN
        REWRITE_TAC thl)
  );;

close_theory();;
