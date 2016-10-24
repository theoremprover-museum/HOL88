% File: RCpredicate_ex1.ml

 Proof of simple predicate truths

%

g "!p:^pred. (!x. ~p x) ==> (p = false)";;
e(RT[false_DEF] THEN REPEAT STRIP_TAC);;
e(FUN_TAC);;
e(ART[]);;
let simplethm1 = top_thm();;


let simplethm2 = prove
 ("!p:^pred. false or p = p",PRED_TAUT_TAC);;
