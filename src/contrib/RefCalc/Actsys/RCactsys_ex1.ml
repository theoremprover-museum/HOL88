% File: RCactsys_ex1.ml

  Example : correctness of 2-sequence welfare crook loop 
%

% Assume that f and g are strictly ascending sequences and that
  f i = g j for some i and j.
  We prove that the loop
    DO f i < g j -> i:=i+1
    [] g j < f i -> j:=j+1
    OD
  is totally correct with respect to precondition
    P: (i=0) /\ (j=0)
  and postcondition
    Q: f i = g j
%

let ASSUM = "(!i. (f i) < (f(SUC i))) /\
             (!j. (g j) < (g(SUC j))) /\
             (?i' j'. (f i' = g j') /\
                      (!i j. (f i = g j) ==> (i'<=i) /\ (j'<=j)))";;
let ALIST = "[((\(i:num,j:num).(f i)<(g j))
               , assign (\(i,j). (SUC i,j))) 
             ;((\(i:num,j:num).(g j)<(f i))
               , assign (\(i,j). (i,SUC j)))
             ]";;
let LOOP = "ldo ^ALIST";;
let P = "\(i,j). (i=0) /\ (j=0)";;
let Q = "\(i:num,j:num). (f:num->num) i = g j";;

let INV = "\(i:num,j:num). (i<=i') /\ (j<=j')";;
let BOUND = "\(i:num,j:num).(i'-i)+(j'-j)";;
let sty = ":num#num";;

% a lemma about monotonic sequences %

let mono_seq_lemma1 = prove
 ("(!i. (f i) < (f(SUC i))) ==> (!i j. i < j ==> (f i) < (f j))",
  STRIP_TAC THEN GEN_TAC THEN GEN_TAC THEN DISCH_THEN (\th. MP_TAC
   (MATCH_MP (PORR[SYM(SPEC_ALL ADD1)] LESS_ADD_1) th)) THEN 
  STRIP_TAC THEN POP_ASSUM (\th.PORT[th]) THEN 
  SPEC_TAC("p:num","p:num") THEN INDUCT_TAC THENL
  [ART[ADD_CLAUSES]
  ;POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o 
   PORR[SYM(C2(C2(C2 ADD_CLAUSES)))] o SPEC "i+SUC p") THEN
   DISCH_TAC THEN POP_ASSUM_LIST (ASSUME_TAC o LIST_CONJ)
   THEN POP_ASSUM (\th. ACCEPT_TAC (MATCH_MP LESS_TRANS th))
  ]);;

let PRE_LESS_SELF = prove
 ("(0<m) ==> (PRE m < m)",
  SPEC_TAC ("m:num","m:num") THEN INDUCT_TAC
  THENL[RT[NOT_LESS_0];LPORT[PRE;LESS_SUC_REFL] THEN RT[]]);;

let crook = prove("^ASSUM ==> correct ^P ^LOOP ^Q",
   STRIP_TAC THEN MATCH_MP_TAC correct_ldo THEN
   EXISTS_TAC INV THEN EXISTS_TAC BOUND THEN REPEAT CONJ_TAC THENL
   [EVERY_MAPSND_mono_TAC
   ;PORT[implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN
    ART[ZERO_LESS_EQ]
   ;LPRT[implies_DEF;lguard_DEF;or_DEF;and_DEF;false_DEF;not_DEF] THEN
    P_PGEN_TAC "(x,y):^sty" THEN PBETA_TAC THEN
    RT[DE_MORGAN_THM] THEN PBETA_TAC THEN PORT[NOT_LESS] THEN 
    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
   ;RT[EVERY_DEF] THEN PBETA_TAC THEN CONJ_TAC THENL
    [GEN_TAC THEN assign_correct_TAC [] THEN PRT[and_DEF] THEN
     P_PGEN_TAC "(a,b):^sty" THEN PBETA_TAC THEN RT[] THEN BOUND_TAC THEN
     POP_ASSUM MP_TAC THEN POP_ASSUM(MP_TAC o PORR[LESS_OR_EQ]) THEN 
     POP_ASSUM(MP_TAC o PORR[LESS_OR_EQ]) THEN STRIP_TAC THENL
     [REPEAT DISCH_TAC THEN IMP_RES_TAC LESS_EQ THEN ART[] THEN
      MATCH_MP_TAC LESS_MONO_ADD THEN IMP_RES_TAC M_LESS_0_LESS THEN
      IMP_RES_TAC SUB_SUC_PRE_SUB THEN ART[GSYM PRE_SUB] THEN
      MATCH_MP_TAC PRE_LESS_SELF THEN ART[GSYM SUB_LESS_0]
     ;STRIP_TAC THEN ART[LESS_REFL] THEN IMP_RES_TAC mono_seq_lemma1 THEN
      DISCH_TAC THEN IMP_RES_TAC LESS_ANTISYM
     ]
    ;GEN_TAC THEN assign_correct_TAC [] THEN PRT[and_DEF] THEN
     P_PGEN_TAC "(a,b):^sty" THEN PBETA_TAC THEN RT[] THEN BOUND_TAC THEN
     POP_ASSUM MP_TAC THEN POP_ASSUM(MP_TAC o PORR[LESS_OR_EQ]) THEN 
     POP_ASSUM(MP_TAC o PORR[LESS_OR_EQ]) THEN 
     DISCH_THEN (\t. STRIP_TAC THEN MP_TAC t) THENL
     [REPEAT DISCH_TAC THEN IMP_RES_TAC LESS_EQ THEN ART[] THEN
      PORT[ADD_SYM] THEN MATCH_MP_TAC LESS_MONO_ADD THEN
      IMP_RES_TAC M_LESS_0_LESS THEN
      IMP_RES_TAC SUB_SUC_PRE_SUB THEN ART[GSYM PRE_SUB] THEN
      MATCH_MP_TAC PRE_LESS_SELF THEN ART[GSYM SUB_LESS_0]
     ;STRIP_TAC THEN ART[LESS_REFL] THEN IMP_RES_TAC mono_seq_lemma1 THEN
      POP_ASSUM MP_TAC THEN ART[] THEN REPEAT DISCH_TAC THEN
      IMP_RES_TAC LESS_ANTISYM
     ]
   ]]);;

