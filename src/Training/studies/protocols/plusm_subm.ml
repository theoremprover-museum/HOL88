%----------------------------------------------------------------------------%
% plusm_subm theory                                                          %
% completed 2 June 1989                                                      %
% rebuilt 10 August 1989 %
% rebuilt 18 March 1991 %
% USES : Tom Melham's Integer theory                                         %
%----------------------------------------------------------------------------%


new_theory`plusm_subm`;;

new_parent`int`;; 
load_definitions`int`;;
load_theorems`int`;;

new_parent`myarith`;;
let less_than_one_is_0 = theorem`myarith``less_than_one_is_0`;;
let SUC_0 = theorem`myarith``SUC_0`;;


loadf`mytactics`;;

%----------------------------------------------------------------------------%
% DEFINITIONS                                                                %
%----------------------------------------------------------------------------%

let plusm = 
new_definition(
 `plusm`,
 "plusm(a:num,b:num,m:num) = 
       (ABS (( ((Int a) MODI m) plus ((Int b) MODI m) ) MODI m)) ");;

let N =
new_prim_rec_definition(
  `N`,
  "(N 0 m = 0) /\
   (N (SUC n) m = ( (N n m = 0) => (N n m)+m-1 | (N n m)-1 ))" 
);;

let subm=
new_definition(
 `subm`,
 "subm(a:num,b:num,m:num) = plusm(a,N b m,m)");;


let MOD_MOD = 
prove_thm(
  `MOD_MOD`,
  "!n:num. Int 0 << Int n ==> !a:int. (((a MODI n) MODI n) = (a MODI n))",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC MOD_Less THEN
  POP_ASSUM (ASSUME_TAC o SPEC "a:int") THEN
  IMP_RES_TAC Leq_MOD THEN
  POP_ASSUM (ASSUME_TAC o SPEC "a:int") THEN
  IMP_RES_TAC MOD_ID );;

let MOD_0 = 
prove_thm(
  `MOD_0`,
  "!n:num. Int 0 << Int n ==> ((Int 0) MODI n = (Int 0))",
   ASSUME_TAC (GEN_ALL (SPECL ["n:num";"Int 0"] MOD_ID)) THEN
   POP_ASSUM (ASSUME_TAC o (REWRITE_RULE[Leq_REFL])) THEN
   ASM_REWRITE_TAC[] );;

let Add_MOD_MOD =
prove_thm(
  `Add_MOD_MOD`,
  "!m:num. Int 0 << Int m ==> !a b:int. 
        ( ((a plus (b MODI m)) MODI m) = ((a plus b) MODI m) ) /\
        ( (((a MODI m) plus b) MODI m) = ((a plus b) MODI m))",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC MOD_MOD THEN
  IMP_RES_TAC Add_MOD THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  POP_ASSUM (ASSUME_TAC o (GEN_ALL o SYM o SPEC_ALL)) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_WITH 2 );;

let Leq_LESS_OR_EQ =
prove_thm(
  `Leq_LESS_OR_EQ`,
  "!m:num. Int 0 Leq Int m = 0 <= m",
   REWRITE_TAC[int_LESS_EQ_DEF;Int_less_num_less;LESS_OR_EQ] THEN
   REPEAT STRIP_TAC THEN
   DISJ_CASES_TAC (SPEC "m:num" num_CASES) THENL
   [ ASM_REWRITE_TAC[] ;
     POP_ASSUM (ASSUME_TAC o SELECT_RULE) THEN
     ONCE_ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[LESS_0] ] );;
      
let Int_abs =
prove_thm(
  `Int_abs`,
  "!i:int.  Int 0 Leq i ==>  (Int(ABS i)=i)",
  REPEAT STRIP_TAC THEN IMP_RES_TAC Int_Leq_IMP THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[abs_DEF] );;

let Int_abs_MOD =
prove_thm(
  `Int_abs_MOD`,
  "!m:num. Int 0 << Int m ==> 
      !i:int. ( Int(ABS(i MODI m)) = (i MODI m) )",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC Leq_MOD THEN
  POP_ASSUM (ASSUME_TAC o SPEC "i:int" ) THEN
  IMP_RES_TAC Int_abs );;


%----------------------------------------------------------------------------%
% Proof that MOD-n is a commutative group :                                  %
%----------------------------------------------------------------------------%

let plusm_assoc =
prove_thm(
  `plusm_assoc`,
  "!m:num. Int 0 << Int m ==>
    !a b c:num.  (plusm(a,plusm(b,c,m),m) = plusm(plusm(a,b,m),c,m))",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC Add_MOD_MOD THEN
   IMP_RES_TAC Add_MOD THEN
   IMP_RES_TAC Int_abs_MOD THEN
   ASM_REWRITE_TAC[plusm;plus_ASSOC] );;


let identity_0 =
prove_thm(
 `identity_0`,
 "!a m:num. (Int 0 << Int m) /\ a<m
    ==> ( plusm(a,0,m) = a )",
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o 
     REWRITE_RULE [SYM (SPECL ["a:num";"m:num"] Int_less_num_less)]) THEN
  let th = REWRITE_RULE [ADD_CLAUSES] (SPECL ["0";"a:num"] LESS_EQ_ADD) in
  ASSUME_TAC th THEN
  POP_ASSUM (ASSUME_TAC o 
     REWRITE_RULE [SYM (SPEC "a:num" Leq_LESS_OR_EQ)]) THEN
  IMP_RES_TAC Add_MOD THEN
  IMP_RES_TAC MOD_ID THEN
  ASM_REWRITE_TAC[plusm;plus_ID;abs_DEF] );;


let inverse_N =
prove_thm(
  `inverse_N`,
  "!a m:num. Int 0 << Int m ==> (plusm(a,N a m,m) = 0)",
  INDUCT_TAC THENL
  [ REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPECL ["0";"m:num"] Int_less_num_less) THEN
    PURE_ASSUM_REWRITE_TAC 1 2 THEN
    IMP_RES_TAC (SPECL ["0";"m:num"] identity_0) THEN
    ASM_REWRITE_TAC[N] ;

    REPEAT STRIP_TAC THEN RES_TAC THEN
    UNDISCH_TAC  "plusm(a,N a m,m) = 0" THEN
    IMP_RES_TAC Add_MOD THEN
    ASM_REWRITE_TAC[plusm;plus_THM] THEN
    REWRITE_TAC[N] THEN
    ASM_CASES_TAC "N a m = 0" THENL
    [ ASM_REWRITE_TAC[ADD1;SYM (SPEC_ALL ADD_ASSOC);ADD_CLAUSES] THEN
      MP_TAC (SPECL ["0";"m:num"] Int_less_num_less) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      POP_ASSUM (\th. ASSUME_TAC th THEN
                      ASSUME_TAC(REWRITE_RULE [LESS_EQ;SYM SUC_0] th)) THEN
      IMP_RES_TAC SUB_ADD THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM (SPEC_ALL (CONJUNCT1 plus_THM))] THEN
      UNDISCH_TAC "!i j. ((i MODI m) plus (j MODI m)) MODI m = 
        (i plus j) MODI m" THEN DISCH_TAC THEN 
      POP_ASSUM(ASSUME_TAC o SYM o SPECL ["Int a";"Int m"]) THEN
      IMP_RES_TAC (theorem`int``MOD_EQ_0`) THEN
      POP_ASSUM (ASSUME_TAC o SPEC "Int 1") THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [times_ID]) THEN
      ASM_REWRITE_TAC[plus_ID] THEN
      IMP_RES_TAC MOD_MOD THEN POP_ASSUM(\th. REWRITE_TAC[th]);

      ASM_REWRITE_TAC[ADD1;SYM (SPEC_ALL ADD_ASSOC);ADD_CLAUSES] THEN
      POP_ASSUM (ASSUME_TAC o 
         REWRITE_RULE [SYM (SPEC "N a m" less_than_one_is_0);
                       NOT_LESS]) THEN
      IMP_RES_TAC SUB_ADD THEN
      ASM_REWRITE_TAC[] ]] );;


let plusm_commutative =
 prove_thm(
  `plusm_commutative`,
  "!a b m:num. plusm(a,b,m) = plusm(b,a,m)",
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[plusm] THEN
  ASSUME_TAC (SPECL ["(Int a) MODI m";"(Int b) MODI m"] plus_COMM) THEN
  PURE_ASM_REWRITE_TAC []  THEN
  REFL_TAC );;

%----------------------------------------------------------------------------%
% plusm subm theorems for protocol proof                                     %
%----------------------------------------------------------------------------%

let plusm_eq_plus =
prove_thm(
  `plusm_eq_plus`,
  "!a b m.  (0<m /\ (a+b)<m ) ==> ( plusm(a,b,m) = (a+b) )",
  REWRITE_TAC [SYM (SPEC_ALL Int_less_num_less)] THEN
  REPEAT STRIP_TAC THEN 
  let th = REWRITE_RULE [ADD_CLAUSES] (SPECL ["0";"a+b"] LESS_EQ_ADD) in
  ASSUME_TAC th THEN
  POP_ASSUM (ASSUME_TAC o 
     REWRITE_RULE [SYM (SPEC "a+b" Leq_LESS_OR_EQ)]) THEN
  IMP_RES_TAC MOD_ID THEN
  IMP_RES_TAC Add_MOD THEN
  ASM_REWRITE_TAC [plusm;plus_THM;abs_DEF] );;
 

let plusm_subm =
prove_thm(  
 `plusm_subm`,
 "!a b m:num. (0<m  /\ a<m) ==> (plusm(subm(a,b,m),b,m) = a )",
 REPEAT STRIP_TAC THEN
 USE_F_ASM_TAC ASSUME_TAC 
    (REWRITE_RULE [SYM (SPEC_ALL Int_less_num_less)]) 2 THEN  
 IMP_RES_TAC plusm_assoc THEN
 POP_ASSUM(ASSUME_TAC o (GEN_ALL o SYM o SPEC_ALL)) THEN
 IMP_RES_TAC (SPEC "b:num" inverse_N) THEN
 POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [plusm_commutative])  THEN
 IMP_RES_TAC identity_0 THEN
 ASM_REWRITE_TAC[subm] );;

let subm_plusm =
prove_thm(
 `subm_plusm`,
  "!m:num. 0<m ==> !a b c:num. 
     (subm(plusm(a,b,m),c,m) = plusm(subm(a,c,m),b,m))",
 REWRITE_TAC [SYM (SPEC_ALL Int_less_num_less)] THEN  
 REPEAT STRIP_TAC THEN 
 IMP_RES_TAC plusm_assoc THEN
 REWRITE_TAC[subm] THEN
 POP_ASSUM(ASSUME_TAC o (GEN_ALL o SYM o SPEC_ALL)) THEN
 ASM_REWRITE_TAC[] THEN
 REWRITE_TAC [SPECL ["b:num";"N c m"] plusm_commutative]
);;

let plusm_sub_sub =
prove_thm(
 `plusm_sub_sub`,
 "!a b c m:num. (0<m /\ a<m) ==>
  (plusm( subm(a,b,m) , subm(b,c,m) , m) = subm(a,c,m) )",
 REPEAT STRIP_TAC THEN 
 USE_F_ASM_TAC ASSUME_TAC 
    (REWRITE_RULE [SYM (SPEC_ALL Int_less_num_less)]) 2 THEN
 REWRITE_TAC[subm] THEN
 IMP_RES_TAC plusm_assoc THEN
 POP_ASSUM(ASSUME_TAC o (GEN_ALL o SYM o SPEC_ALL)) THEN
 ASM_REWRITE_TAC[] THEN
 POP_ASSUM(ASSUME_TAC o SYM o SPECL ["N b m";"b:num";"N c m"]) THEN
 ASM_REWRITE_TAC[] THEN
 IMP_RES_TAC (SPEC "b:num" inverse_N) THEN
 REWRITE_TAC [SPECL ["N b m";"b:num"] plusm_commutative] THEN
 ASM_REWRITE_TAC[] THEN
 IMP_RES_TAC plusm_assoc THEN
 IMP_RES_TAC identity_0 THEN
 ASM_REWRITE_TAC[] );;


let Num_less_int_less = GEN_ALL(SYM( SPEC_ALL Int_less_num_less));;

let plusm_less_m =
prove_thm(
 `plusm_less_m`,
 "!a b m:num. 0 < m ==> plusm(a,b,m) < m",
 REPEAT STRIP_TAC THEN
 POP_ASSUM (ASSUME_TAC o REWRITE_RULE [Num_less_int_less] ) THEN
 IMP_RES_TAC MOD_Less THEN
 IMP_RES_TAC Int_abs_MOD THEN
 ASM_REWRITE_TAC[plusm;Num_less_int_less] );;

let plusm_0 =
prove_thm(
  `plusm_0`,
  "!a b m. 0<m ==> ( plusm(0,plusm(a,b,m),m) = plusm(a,b,m) )",
  REPEAT STRIP_TAC THEN IMP_RES_TAC plusm_less_m THEN
  POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
  MP_TAC (SPECL ["0";"m:num"] Num_less_int_less) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  IMP_RES_TAC identity_0  THEN
  ONCE_REWRITE_TAC [plusm_commutative] THEN ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC plusm_commutative );;

let subm_self =
prove_thm(
 `subm_self`,
  "!m:num. 0<m ==> (!r:num. (subm(r,r,m) = 0))",
  REWRITE_TAC [Num_less_int_less;subm] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC inverse_N THEN
  ASM_REWRITE_TAC[] );;

let plus_1_sub =
prove_thm(
  `plus_1_sub`,
  "!r m :num. 1<m ==> (subm(plusm(r,1,m),r,m) = 1)",
  REPEAT STRIP_TAC THEN
  USE_F_ASM_TAC ASSUME_TAC (REWRITE_RULE [SUC_0]) 1 THEN
  IMP_RES_TAC SUC_LESS THEN
  IMP_RES_TAC subm_plusm THEN
  IMP_RES_TAC subm_self THEN
  USE_F_ASM_TAC ASSUME_TAC (REWRITE_RULE [Num_less_int_less]) 3 THEN
  IMP_RES_TAC identity_0 THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE[plusm_commutative]) THEN
  ASM_REWRITE_TAC[] );;

let plusm_eq =
prove_thm(
  `plusm_eq`,
 "!a m x y:num.
    ( x = y ) ==> ( plusm(x,a,m) = plusm(y,a,m) )",
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] );;

let inverse_N1 =
prove_thm(
  `inverse_N1`,
  "!m:num. (Int 0) << (Int m) ==> (!a:num. plusm(a,N a m,m) = 0)",
 REPEAT STRIP_TAC THEN IMP_RES_TAC inverse_N THEN ASM_REWRITE_TAC[]);;

let change_sides =
prove_thm(
  `change_sides`,
  "!a b c m:num. b<m /\ 0<m /\ (subm(plusm(a,b,m),c,m)=0) 
 ==> 
  (b = subm(c,a,m))",

 REWRITE_TAC [subm] THEN REPEAT STRIP_TAC THEN
 IMP_RES_TAC plusm_eq THEN
 POP_ASSUM (ASSUME_TAC o SYM o (SPECL ["plusm(c,N a m,m)";"m:num"])) THEN
 POP_ASSUM MP_TAC THEN IMP_RES_TAC plusm_0 THEN 
 POP_ASSUM(\th. REWRITE_TAC[th]) THEN
 IMP_RES_TAC (REWRITE_RULE [ONCE_REWRITE_RULE[EQ_SYM_EQ] 
              Num_less_int_less] plusm_assoc) THEN
 POP_ASSUM(\th. REWRITE_TAC[th]) THEN
 IMP_RES_TAC plusm_less_m THEN 
 POP_ASSUM(ASSUME_TAC o SPECL ["a:num";"b:num"]) THEN
 IMP_RES_TAC (REWRITE_RULE [ONCE_REWRITE_RULE[EQ_SYM_EQ] 
              Num_less_int_less] plusm_subm) THEN
 UNDISCH_TAC "!b'. plusm(subm(plusm(a,b,m),b',m),b',m) = plusm(a,b,m)" THEN
 DISCH_TAC THEN POP_ASSUM(ASSUME_TAC o SPEC "c:num") THEN
 POP_ASSUM(ASSUME_TAC o REWRITE_RULE[subm]) THEN
 POP_ASSUM(\th. REWRITE_TAC[th]) THEN
 IMP_RES_TAC (REWRITE_RULE [ONCE_REWRITE_RULE[EQ_SYM_EQ] 
              Num_less_int_less] subm_plusm) THEN
 POP_ASSUM(ASSUME_TAC o SPECL["a:num";"b:num";"a:num"]) THEN
 POP_ASSUM(ASSUME_TAC o REWRITE_RULE[subm]) THEN
 POP_ASSUM(\th. REWRITE_TAC[th]) THEN
 IMP_RES_TAC subm_self THEN 
 POP_ASSUM(\th. REWRITE_TAC[REWRITE_RULE[subm]th]) THEN
 DISCH_TAC THEN POP_ASSUM(\th. REWRITE_TAC[th]) THEN
 IMP_RES_TAC (REWRITE_RULE[ADD_CLAUSES] 
              (SPECL ["0";"b:num";"m:num"] plusm_eq_plus)) THEN
 POP_ASSUM(ASSUME_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC );;

close_theory();;

quit();;
