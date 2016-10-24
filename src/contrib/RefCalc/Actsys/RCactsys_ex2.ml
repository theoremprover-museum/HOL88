% File: RCactsys_ex2.ml

  Correctness of a two-dimensional search algorithm
  Uses more_arithmetic library

%


% preliminary definitions and lemmas %

load_library `more_arithmetic`;;

let MAX_EQ = prove("MAX x x = x",LRT[MAX_DEF;LESS_EQ_REFL]);;
let lemma1 = prove
 ("(a=MIN x y) /\ (b=MAX x y) ==> (((a=x)/\(b=y)) \/ ((a=y)/\(b=x)))", 
  LPORT[MIN_DEF;MAX_DEF] THEN ASM_CASES_TAC "x<=y" THEN REPEAT
  STRIP_TAC THEN ART[]);;
let lemma2 = prove
 ("((MAX x y) <= (MIN x y)) ==> (y=x) /\ (MAX x y = x) /\ (MIN x y = x)", 
  LPORT[MIN_DEF;MAX_DEF] THEN ASM_CASES_TAC "x<=y" THEN ART[] THEN
  POP_ASSUM MP_TAC THEN PORT[LESS_OR_EQ] THEN REPEAT STRIP_TAC
  THEN ART[] THEN IMP_RES_TAC LESS_ANTISYM);;


% the example : a 2-dimensional square search algorithm %

% Assume that f and X are given and that f i j = X for some i and j.
  We prove that the loop
     DO (i<j) /\ ~(f i j = X) /\ ~(f j i = X) -> i  :=i+1
     [] (i=j) /\ ~(f i j = X)                 -> i,j:=0,j+1
     OD
  is totally correct under precondition
     P: (i=0) /\ (j=0)
  and postcondition
     Q: (f i j = X) \/ (f j i = X)
%

let ASSUM = "?i' j'. ((f:num->num->num)i' j' = X)";;
let ALIST = "[((\(i:num,j:num).(i<j) /\ ~(f i j = (X:num)) /\ ~(f j i = X))
               , assign (\(i,j). (SUC i,j)))
             ;((\(i:num,j:num).(i = j) /\ ~(f i j = X))
               , assign (\(i,j). (0,SUC j)))
             ]";;
let LOOP = "ldo ^ALIST";;
let P = "\(i,j). (i=0) /\ (j=0)";;
let Q = "\(i:num,j:num). (f i j = (X:num)) \/ (f j i = (X:num))";;

let INV = "\(i:num,j:num). ( i<=j ) /\ (j <= MAX i' j') /\
  ((j = MAX i' j') ==> i <= MIN i' j')";;
let BOUND = "\(i:num,j:num).
  ((MAX i' j')*((MAX i' j')-j)) + ((MAX i' j') - i)";;
let sty = ":num#num";;

let thm = prove("^ASSUM ==> correct ^P ^LOOP ^Q",
   STRIP_TAC THEN MATCH_MP_TAC correct_ldo THEN
   EXISTS_TAC INV THEN EXISTS_TAC BOUND THEN REPEAT CONJ_TAC THENL
   [EVERY_MAPSND_mono_TAC
   ;PORT[implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN
    ART[ZERO_LESS_EQ]
   ;LPRT[implies_DEF;lguard_DEF;and_DEF;or_DEF;not_DEF;false_DEF] THEN
    PBETA_TAC THEN RT[DE_MORGAN_THM] THEN P_PGEN_TAC "(a,b):^sty" THEN
    PBETA_TAC THEN LRT[DE_MORGAN_THM;NOT_CLAUSES] THEN
    REPEAT STRIP_TAC THEN ART[] THEN UNDISCH_TAC "a<=b" THEN ART[LESS_OR_EQ]
   ;RT[EVERY_DEF] THEN PBETA_TAC THEN CONJ_TAC THENL
    [GEN_TAC THEN assign_correct_TAC [] THEN PRT[and_DEF] THEN
     P_PGEN_TAC "(a,b):^sty" THEN PBETA_TAC THEN RT[] THEN
     REPEAT STRIP_TAC THEN ART[] THENL 
     [IMP_RES_TAC LESS_OR
     ;RES_TAC THEN POP_ASSUM(MP_TAC o PORR[LESS_OR_EQ]) THEN STRIP_TAC THEN
      IMP_RES_TAC LESS_OR THEN UNDISCH_TAC "~((f:num->num->num)a b = X)" THEN
      UNDISCH_TAC "~((f:num->num->num)b a = X)" THEN
      IMP_RES_TAC lemma1 THEN ART[]
     ;POP_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_LESS_EQ_TRANS THEN
      PORT[ADD_SYM] THEN MATCH_MP_TAC LESS_MONO_ADD THEN
      IMP_RES_TAC M_LESS_0_LESS THEN IMP_RES_TAC SUB_SUC_PRE_SUB THEN
      ART[GSYM PRE_SUB] THEN MATCH_MP_TAC PRE_K_K THEN ART[GSYM SUB_LESS_0]
     ]
    ;GEN_TAC THEN assign_correct_TAC [] THEN PRT[and_DEF] THEN
     P_PGEN_TAC "(a,b):^sty" THEN PBETA_TAC THEN RT[] THEN
     REPEAT STRIP_TAC THEN ART[ZERO_LESS_EQ] THENL 
     [ASSUM_LIST(\l.MP_TAC(PORR[LESS_OR_EQ](el 5 l))) THEN STRIP_TAC THEN
      IMP_RES_TAC LESS_EQ THEN RES_TAC THEN POP_ASSUM MP_TAC THEN ART[] THEN
      DISCH_TAC THEN IMP_RES_TAC lemma2 THEN
      UNDISCH_TAC "(f:num->num->num) i' j' = X" THEN
      UNDISCH_TAC "~((f:num->num->num) a b = X)" THEN ART[] THEN
      REPEAT STRIP_TAC THEN RES_TAC
     ;POP_ASSUM (SUBST1_TAC o SYM) THEN PORT[SUB_0] THEN
      ASSUM_LIST(\l.MP_TAC(PORR[LESS_OR_EQ](el 4 l))) THEN STRIP_TAC THENL
      [IMP_RES_TAC SUB_SUC THEN POP_ASSUM SUBST1_TAC THEN
       LPORT[MULT_CLAUSES;ADD_SYM] THEN
       MATCH_MP_TAC(PORR[ADD_SYM]LESS_ADD_NONZERO) THEN
       IMP_RES_TAC LESS_EQ_LESS_TRANS THEN IMP_RES_TAC NOT_SUB_0
      ;RES_TAC THEN POP_ASSUM MP_TAC THEN ART[] THEN
       DISCH_TAC THEN IMP_RES_TAC lemma2 THEN
       UNDISCH_TAC "(f:num->num->num) i' j' = X" THEN
       UNDISCH_TAC "~((f:num->num->num) a b = X)" THEN ART[] THEN
       REPEAT STRIP_TAC THEN RES_TAC
   ]]]]);;
