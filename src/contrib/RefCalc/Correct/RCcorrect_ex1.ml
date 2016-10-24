% File: RCcorrect_ex1.ml

  Three examples of total correctness proofs for loops

  In all examples,
     LOOP  is the loop
     P     is the precondition
     Q     is the postcondition
     INV   is the invariant
     BOUND is the bound (variant) function
     sty   is the type of the state space
%


% example 1: addition by repeated incrementation %
let GRD = "\(x:num,y:num). x>0";;
let BOD = "assign (\(x:num,y:num).(x-1,y+1))";;
let LOOP = "do ^GRD ^BOD";;
let P = "\(x:num,y:num). (x=X) /\ (y=Y)";;
let Q = "\(x:num,y:num). (y=X+Y)";;

let INV = "\(x:num,y:num). x+y=X+Y";;
let BOUND = "\(x:num,y:num).x";;
let sty = ":num#num";;

let do_ex1 = prove
  ("correct ^P ^LOOP ^Q",
   do_correct_TAC INV BOUND [] THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN
    CASE_TAC "FST(u:^sty)" num_CASES [GREATER;LESS_REFL;LESS_0;ADD]
   ;GEN_TAC THEN assign_correct_TAC [] THEN PRT[and_DEF;GREATER] THEN
    P_PGEN_TAC"(x1,y1):^sty" THEN PBETA_TAC THEN RT[GSYM PRE_SUB1] THEN
    CASE_TAC "x1:num" num_CASES [GSYM ADD1;LESS_REFL;LESS_0;PRE] THEN
    PORT[ADD_CLAUSES] THEN BOUND_TAC THEN ART[LESS_SUC_REFL]
   ]);;


% example 2: multiplication by repeated addition 1 %
let LOOP = "do (\(x:num,r:num). x>0) (assign (\(x,r).(x-1,r+Y)))";;
let P = "\(x:num,r:num). (x=X) /\ (r=0)";;
let Q = "\(x:num,r:num). r=X*Y";;

let INV = "\(x:num,r:num). (x<=X) /\ (r=(X-x)*Y)";;
let BOUND = "\(x:num,r:num).x";;
let sty = ":num#num";;

let do_ex2 = prove
  ("correct ^P ^LOOP ^Q",
   do_correct_TAC INV BOUND [LESS_OR_EQ;SUB_EQUAL_0;MULT] THENL
   [UNDISCH_TAC "~(FST(u:^sty)) > 0" THEN
    CASE_TAC "FST(u:^sty)" num_CASES [GREATER;LESS_REFL;LESS_0;SUB_0]
   ;GEN_TAC THEN assign_correct_TAC [] THEN LPRT[and_DEF;and_DEF] THEN
    P_PGEN_TAC"(x1,r1):^sty" THEN PBETA_TAC THEN RT[GSYM PRE_SUB1] THEN
    CASE_TAC "x1:num" num_CASES [GREATER;LESS_REFL;LESS_0;PRE] THEN
    CASE_TAC "X:num" num_CASES [GREATER;NOT_SUC_LESS_EQ_0;LESS_EQ_MONO] THEN
    PORT[SUB_MONO_EQ] THEN BOUND_TAC THEN RT[LESS_SUC_REFL] THEN
    ASSUME_TAC(SPEC "n':num" LESS_EQ_SUC_REFL) THEN 
    IMP_RES_TAC LESS_EQ_TRANS THEN ART[] THEN
    UNDISCH_TAC "n <= n'" THEN PORT[GSYM NOT_LESS] THEN DISCH_TAC THEN
    ART[SUB;MULT]
   ]);;



% example 3: linear search  %
% NB: this example uses the more_arithmetic library
  If you load it, the more_arithmetic theory will become a parent of the
  present theory.
load_library `more_arithmetic`;;
%
let GRD = "\i:num. ~(A i = (X:num))";;
let BOD = "assign (\i:num.i+1)";;
let LOOP = "do ^GRD ^BOD";;
let P = "\i:num. (i=0) /\ (?j. (j<N) /\ (A j = (X:num)))";;
let Q = "\i:num. A i = (X:num)";;

let INV = "\i:num. ?j.(i<=j) /\ (j<N) /\ (A j = (X:num))";;
let BOUND = "\i:num. N-i";;
let sty = ":num";;

let PRE_LESS_REFL = prove("!m.(0<m) ==> (PRE m < m)",
  INDUCT_TAC THENL[RT[NOT_LESS_0];LPORT[PRE;LESS_SUC_REFL] THEN RT[]]);;

let do_ex3 = prove("correct ^P ^LOOP ^Q",
  do_correct_TAC INV BOUND [] THENL
  [EXISTS_TAC "j:num" THEN ART[ZERO_LESS_EQ]
  ;GEN_TAC THEN assign_correct_TAC[] THEN PRT[and_DEF] THEN 
   GEN_TAC THEN BETA_TAC THEN BOUND_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC "j:num" THEN ART[GSYM ADD1] THEN 
    POP_ASSUM MP_TAC THEN ASSUM_LIST(\l.MP_TAC(PORR[LESS_OR_EQ](el 3 l))) THEN
    STRIP_TAC THEN ART[GSYM LESS_EQ]
   ;PORT[GSYM ADD1] THEN IMP_RES_TAC M_LESS_0_LESS THEN
    IMP_RES_TAC SUB_SUC_PRE_SUB THEN ART[GSYM PRE_SUB] THEN
    MATCH_MP_TAC PRE_LESS_REFL THEN IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
    IMP_RES_TAC SUB_SUC THEN ART[LESS_0]
  ]]);;    
  
