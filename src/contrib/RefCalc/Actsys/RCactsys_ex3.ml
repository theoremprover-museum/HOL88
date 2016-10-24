% File: RCactsys_ex3.ml

 example of total correctness of action system with unbounded nondeterminism 
  This example uses a list of guarded commands
  and a well-founded order other than usual one.
  The loop is
    DO x=0 -> x:>0
    [] x>1 -> x:=x-1
    OD
  where x:>0 means that x is assigned an arbitrar value greater than 0.
  The partial order used on the natural numbers simply orders them as
    1 < 2 < ... < 0
  (this ordering was proved to be well-founded in the theory wellf).
  We prove that this loop terminates under precondition x=0.
%

let ALIST = "[((\x.x=0) , nondass (\(x:num) x'.x'>0)) 
             ;((\x.x>1) , assign (\x:num.x-1))
             ]";;
let LOOP = "ldo ^ALIST";;
let P = "\x:num. x=0";;
let Q = "\x:num. T";;

let INV = "\x:num. T";;
let BOUND = "\x:num.x";;
let po = "\x y. 0 < x /\ (x < y \/ (y = 0))";;
let sty = ":num";;

let thm = prove("correct ^P ^LOOP ^Q",
   MATCH_MP_TAC (INST_TYPE[":num",":*"] correct_ldo_wellf)
   THEN EXISTS_TAC INV THEN EXISTS_TAC po THEN 
   EXISTS_TAC BOUND THEN REPEAT CONJ_TAC THENL
   [EVERY_MAPSND_mono_TAC
   ;ACCEPT_TAC wellf_0_grt
   ;PORT[implies_DEF] THEN BETA_TAC THEN RT[]
   ;PORT[implies_DEF] THEN BETA_TAC THEN RT[]
   ;PRT[EVERY_DEF] THEN PBETA_TAC THEN RT[] THEN CONJ_TAC THENL
    [GEN_TAC THEN nondass_correct_TAC [] THEN PRT[and_DEF] THEN BETA_TAC THEN
     GEN_TAC THEN BOUND_TAC THEN RT[GREATER]
    ;GEN_TAC THEN assign_correct_TAC [] THEN LPRT[GREATER;and_DEF] THEN
     BETA_TAC THEN GEN_TAC THEN BOUND_TAC THEN ART[GSYM SUB_LESS_0] THEN
     IMP_RES_TAC M_LESS_0_LESS THEN RT[GSYM PRE_SUB1] THEN
     IMP_RES_TAC PRE_K_K THEN ART[]
   ]]);;
