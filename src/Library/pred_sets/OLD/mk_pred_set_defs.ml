%<
FILE: mk_pred_set_defs.ml

AUTHOR:	Ton Kalker

DATE:	10 july 1989

COMMENT: a preliminary version
         of set theory!
         Should in the end be fitted
         in with a standarized HOL
         set theory.
         The constant "empty set" is
         borrowed from "fixpoints" where
         is is called BOT.
>%

new_theory `pred_sets`;; 

% --------------------------------------------------------------------- %
% Load the fixpoints library.		                 [TFM 90.12.02]	%
% --------------------------------------------------------------------- %

load_library `fixpoints`;;

% --------------------------------------------------------------------- %
% LHS_CONV conv "OP t1 t2" applies conv to t1				%
% --------------------------------------------------------------------- %
let LHS_CONV = RATOR_CONV o RAND_CONV ;;

let TOP =
    new_definition
    (`TOP`,
     "TOP = \x:*.T");;  
                    
let MEMBER =
    new_infix_definition
    (`MEMBER`,
    "MEMBER a (A:*->bool) = A a");;

let SING =
    new_definition
     (`SING`,
      "SING (a:*) = (\x.x = a)");;

let UNION =
    new_infix_definition
    (`UNION`,                             
    "UNION IN (OUT:*->bool) = \a.((IN a) \/ (OUT a))");;

let INTERSECT =
    new_infix_definition
    (`INTERSECT`,
    "INTERSECT A (B:*->bool) = \a.((A a) /\ (B a))");;   

let DELETE = 
    new_infix_definition
    (`DELETE`,
    "DELETE A (B:*->bool) = \a.((A a) /\ ~(B a))");;

let DIFF =
    new_infix_definition
    (`DIFF`,
    "DIFF A (B:*->bool) = \a.(((A a) /\ ~(B a)) \/ (~(A a) /\ (B a)))");;   

let SUBSET =
    new_infix_definition
     (`SUBSET`,
      "SUBSET A (B:*->bool) = (!a. (A a) ==> (B a))");;  

let SUPSET =
    new_infix_definition
     (`SUPSET`,
      "SUPSET A (B:*->bool) = (!a. (B a) ==> (A a))");;

let DISJOINT =
    new_definition
     (`DISJOINT`,
      "DISJOINT A B  = (!a:*.~((A a) /\ (B a)))");;

let PSUBSET = 
    new_infix_definition(`PSUBSET`,
      "PSUBSET A (B:*->bool) = ~(A = B) /\ (A SUBSET B)");;

let PSUPSET = 
   new_infix_definition(`PSUPSET`,
      "PSUPSET A (B:*->bool) = ~(A = B) /\ (A SUPSET B)");;

let GINTERSECT = new_definition(`GINTERSECT`,
          "GINTERSECT (SS:(*->bool)->bool) x = !X.(SS X) ==> (X x)");;

let GUNION = new_definition(`GUNION`,
          "GUNION (SS:(*->bool)->bool) x = ?X.(SS X) /\ (X x)");;

let FUN_TY_DEF =  
    new_infix_definition
    (`FUN_TY_DEF`,
    "--> (A:*->bool) (B:*->bool) f = !x.((A x) ==> (B (f x)))");;

new_special_symbol `-->>`;;

new_special_symbol `>-->`;;   

new_special_symbol `<-->`;;

let FUN_ONTO =
    new_infix_definition
    (`FUN_ONTO`,
    " -->> (A:*->bool) (B:*->bool) f = ((!x.((A x) ==> (B (f x)))) /\
                                  (!x.(B x) ==> (?y.(A y) /\ (x = (f y)))))");;

let FUN_ONE_ONE =
    new_infix_definition
    (`FUN_ONE_ONE`,
    ">--> (A:*->bool) (B:*->bool) f = ((!x.((A x) ==> (B (f x)))) /\  
                                       (! x y.((A x) /\ (A y) /\ ((f x) = (f y)))
                                               ==> (x = y)))");; 

let FUN_ISO = 
    new_infix_definition
    (`FUN_ISO`,
    "<--> A (B:*->bool) f = (((A >--> B) f) /\ ((A -->> B) f)  )");;  

let FUN_INV =
    new_definition
    (`FUN_INV`,
    "FINV A B f (y:*):* = ((B y) /\ (?x.((A x) /\ (y = (f x))))) => 
                                    (@x.((A x) /\ (y = (f x)))) | @x.A x");; 

let PINVERSE =
    new_definition
    (`PINVERSE`,
    "PINVERSE (A,B) f (g:*->*) = ((A --> B) f) /\
                                  ((B --> A) g) /\
                                  (!x:*.((A x) ==> (((g o f) x) = x)))");;  

let INVERSE =
    new_definition
    (`INVERSE`,
    "INVERSE (A,B) f (g:*->*) = (PINVERSE (A,B) f g) /\ (PINVERSE (B,A) g f)");;  

let IMAGE =
    new_definition
    (`IMAGE`,
    "IMAGE (f:*->*) (A:*->bool) a  = (?b.((A b) /\ (a = (f b))))");;   


