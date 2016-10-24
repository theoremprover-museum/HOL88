%----------------------------------------------------------------

   File:         monoid_def.ml

   Description:  

   Defines monoids as an abstrac structure.  Proves 2 theorems
   about monoids.

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

system `/bin/rm monoid_def.th`;;

new_theory `monoid_def`;;

let MONOID = new_abstract_representation `monoid`
   [
    (`op`,":* -> * -> *")
   ;
    (`e`,":*")
   ];;

new_theory_obligations
   (`IS_MONOID`,
    "!m:(*)monoid . IS_MONOID m = 
	(!x:* .op m x (e m) = x) /\
	(!x:* .op m (e m) x = x) /\
	(! x y z:*. (op m x (op m y z)) = (op m (op m x y) z))");;


g
"! (m:(*)monoid) (f:*) .
       (!(a:*) .(op m a f = a) /\ (op m f a = a)) ==> (f = (e m))";;


e(
REPEAT STRIP_TAC
);;

e(
ASSUME_TAC (
  CONV_RULE SYM_CONV (
  CONJUNCT1 (
  SPEC "e (m:(*)monoid)" (
  ASSUME "!a. (op m a f = a) /\ (op m f a = a)"))))
);;


e(
SUBST1_TAC (ASSUME "e m = op m(e m)f")
);;

e(
ASM_REWRITE_TAC []
);;

  

let IDENTITY_UNIQUE = ABS_TAC_PROOF
   (([],"! (m:(*)monoid) (f:*) .
       (!(a:*) .(op m a f = a) /\ (op m f a = a)) ==> (f = (e m))"),
    REPEAT GEN_TAC
    THEN STRIP_GOAL_THEN (\thm .
        SUBST1_TAC (
	SYM_RULE (
	CONJUNCT1 (
	SPEC "e (m:(*)monoid)" thm))))
    THEN ASM_REWRITE_TAC []
   );;

save_thm (`IDENTITY_UNIQUE`,IDENTITY_UNIQUE);;

let OP_DETERMINES_IDENTITY = ABS_TAC_PROOF
   (([],
     "! m1 (m2:(*)monoid) . (op m1 = (op m2)) ==> (e m1 = (e m2))"),
    REPEAT STRIP_TAC
    THEN let t1 = ASSUME "!x:*. op m1 (e m1) x = x" in
	 SUBST_TAC (map SYM_RULE [SPEC "e m2:*" t1])
    THEN let t2 = ASSUME "!x:*. op m2 x (e m2) = x" in
	 SUBST_TAC (map SYM_RULE [SPEC "e m1:*" t2])
    THEN ASM_REWRITE_TAC []
  );;

save_thm (`OP_DETERMINES_IDENTITY`,OP_DETERMINES_IDENTITY);;


close_theory();;
