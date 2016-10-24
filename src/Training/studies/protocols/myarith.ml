%----------------------------------------------------------------------------%
% myarith THEORY   2/v/89, 22/v/89, 7/8/89 , 18/3/91                           %
%----------------------------------------------------------------------------%

% extend_theory`myarith`;; %
% load_theorems`myarith`;; %
% loadf`mytactics`;;  %

new_theory `myarith`;;

loadf`mytactics`;;

let ADD_GREATER_EQ = 
prove_thm(
  `ADD_GREATER_EQ`,
  "!m n. (m+n) >= m",
  ASM_REWRITE_TAC[GREATER_OR_EQ;GREATER] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ASM_REWRITE_TAC[(SYM (SPEC_ALL LESS_OR_EQ));LESS_EQ_ADD] );;

let EQ_SUM = ADD_SYM;;

let NOT_LESS_AND_GREATER = 
prove_thm(
  `NOT_LESS_AND_GREATER`,
  "!n m. n<m ==> ~(m<n)",
GEN_TAC THEN 
INDUCT_TAC THENL
[ ASM_REWRITE_TAC[NOT_LESS_0] ;
  ASM_REWRITE_TAC[LESS_THM] THEN
  STRIP_TAC THENL
   [ ASM_REWRITE_TAC[NOT_LESS;LESS_OR_EQ;LESS_SUC_REFL] ;
     IMP_RES_TAC LESS_SUC THEN
      ASM_REWRITE_TAC[NOT_LESS;LESS_OR_EQ] ] ]);;

let NOT_LESS_OR_EQ = 
prove_thm(
  `NOT_LESS_OR_EQ`,
  "!m n. ~(m<=n) = (n<m)",
  REPEAT GEN_TAC THEN
  REWRITE_TAC [LESS_OR_EQ;(CONJUNCT2 (SPEC_ALL DE_MORGAN_THM))] THEN
  ASM_CASES_TAC "n<m" THENL
   [ IMP_RES_TAC NOT_LESS_AND_GREATER THEN
     IMP_RES_TAC LESS_NOT_EQ THEN
     POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [EQ_SYM_EQ])) THEN
     ASM_REWRITE_TAC[] ;

     REWRITE_TAC [(SYM (CONJUNCT2 (SPEC_ALL DE_MORGAN_THM)))] THEN
     USE_F_ASM_TAC ASSUME_TAC  (REWRITE_RULE [NOT_LESS;LESS_OR_EQ]) 1 THEN
     ASM_REWRITE_TAC[] ] );;


let SUB_SELF=
prove_thm(
  `SUB_SELF`,
  "!m. m-m = 0",
  REWRITE_TAC[SUB_EQ_0;LESS_OR_EQ]);;


let ADD_SUB = 
prove_thm(
  `ADD_SUB`,
  "!m n. (m+n)-m = n",
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (SPEC_ALL LESS_EQ_ADD) THEN
  POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [SPEC_ALL ADD_SYM])) THEN
  POP_ASSUM (ASSUME_TAC o (MP (SPECL ["n:num";"m:num";"n+m"] ADD_EQ_SUB))) THEN
  POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE [ADD_SYM])) THEN
  POP_ASSUM (ASSUME_TAC o (SYM o (REWRITE_RULE[]))) THEN
  ASM_REWRITE_TAC[] );;



let SUB_ADD_SELF = 
prove_thm(
  `SUB_ADD_SELF`,
  "!m n. ~(m<n) ==> ( ((m-n)+n)=m )" ,
   ASM_REWRITE_TAC[(SYM (SPEC_ALL NOT_LESS_OR_EQ));SUB_ADD]  );;

% let SUB_ADD =   see arithmetic!%
%  "!n m. n<=m ==> ( ((m-n)+n) = m )" %

let GREATER_AND_LESS_EQ =
prove_thm(
  `GREATER_AND_LESS_EQ`,
  "!m n. ((m<=n) /\ (n<=m)) ==> (m=n)",

  REWRITE_TAC[LESS_OR_EQ] THEN
  REPEAT STRIP_TAC THENL
   [ UNDISCH_TAC "m<n" THEN
     ASM_REWRITE_TAC[IMP_DISJ_THM] THEN
     DISJ1_TAC  THEN
     ASM_REWRITE_TAC[NOT_LESS;LESS_OR_EQ] ;
     ONCE_ASM_REWRITE_TAC[] THEN 
     ONCE_REWRITE_TAC[EQ_REFL] ] 
);;


let GREATER_OR_EQ_LESS_OR_EQ =
prove_thm(
 `GREATER_OR_EQ_LESS_OR_EQ`,
 "!m n. (m >= n) = (n <= m)",
 REPEAT GEN_TAC THEN
 REWRITE_TAC [GREATER_OR_EQ;GREATER;LESS_OR_EQ] THEN
 ASM_CASES_TAC "(n<m) \/ (m=n)" THENL
   [ POP_ASSUM DISJ_CASES_TAC THEN
       ASM_REWRITE_TAC[] %twice% ;
     ASM_REWRITE_TAC[] THEN
       ONCE_ASM_REWRITE_TAC[EQ_SYM_EQ]  THEN
       ASM_REWRITE_TAC[] ]);;

let ADD_MONO_LESS =
prove_thm(
  `ADD_MONO_LESS`,
  "!m n p. (m+p) < (m+n) = (p<n)",
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ONCE_REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
  REWRITE_TAC[] );;


let ADD_MONO_LESS_EQ =  
prove_thm(
  `ADD_MONO_LESS_EQ`,
  "!m n p.  (m+n)<=(m+p) = (n<=p)",
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC[LESS_EQ_MONO_ADD_EQ]);;


let SMALLER_SUM = 
prove_thm(
  `SMALLER_SUM`,
  "!m n p. (m<p /\ n<p) ==> ~( ((m+n)-p) > m)",
REPEAT STRIP_TAC THEN
POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GREATER])) THEN
ASM_CASES_TAC "(m+n)<=p" THENL
 [ POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [(SYM (SPEC_ALL SUB_EQ_0))])) THEN
   ASSUM_LIST(\thl. ASSUME_TAC 
      (REWRITE_RULE  [(el 1 thl);LESS_OR_EQ]  (el 2 thl))) THEN
   POP_ASSUM (ASSUME_TAC o (REWRITE_RULE[NOT_LESS_0])) THEN
   FALSITY_TAC ;

   POP_ASSUM(ASSUME_TAC o (REWRITE_RULE [NOT_LESS_OR_EQ])) THEN
   IMP_RES_TAC (SPEC "p:num" (SPEC "(m+n)-p" (SPEC "m:num" 
      LESS_MONO_ADD))) THEN
   IMP_RES_TAC (SPEC "m+n" (SPEC "p:num" LESS_IMP_LESS_OR_EQ)) THEN
   IMP_RES_TAC (SPEC "p:num" (SPEC "m+n" SUB_ADD)) THEN
   ASSUM_LIST(\thl. ASSUME_TAC 
     (REWRITE_RULE  [(el 2 thl)]  (el 5 thl))) THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [ADD_MONO_LESS])) THEN
  UNDISCH_TAC "n<p" THEN
  UNDISCH_TAC "p<n" THEN
  REWRITE_TAC [IMP_DISJ_THM;NOT_CLAUSES;
        (SYM (CONJUNCT1 (SPEC_ALL DE_MORGAN_THM)));LESS_ANTISYM] ] );;


let SUC_0=
prove_thm(
 `SUC_0`,
 "1 = (SUC 0)",
 ASM_REWRITE_TAC[ADD1;ADD_CLAUSES]);;

let less_than_one_is_0 = 
prove_thm(
  `less_than_one_is_0`,
  "!a:num. (a<1) = (a=0)",
   REWRITE_TAC[SUC_0;LESS_THM;NOT_LESS_0]);;


let not_1_even =
prove_thm(
 `not_1_even`,
 "!n:num. ~(1 = n+n )" ,
 INDUCT_TAC THENL
  [ REWRITE_TAC[ADD_CLAUSES;SUC_0;SUC_ID] ;
    REWRITE_TAC[ADD;SUC_0;INV_SUC_EQ;ADD_CLAUSES] THEN
    ASSUME_TAC (SPEC "n+n" LESS_0) THEN
    IMP_RES_TAC LESS_NOT_EQ ]
);;


let LESS_LESS_EQ_TRANS = 
prove_thm(
  `LESS_LESS_EQ_TRANS`,
  "!m n p. m<=n /\ n<p ==> m<p",
  REPEAT STRIP_TAC THEN
  USE_F_ASM_TAC DISJ_CASES_TAC (REWRITE_RULE[LESS_OR_EQ]) 2 THENL
   [ IMP_RES_TAC LESS_TRANS ;
     ASM_REWRITE_TAC[] ] 
);;


let SYM_ADD1=(SYM (SPEC_ALL ADD1));;

let NOT_LESS_SUB = 
prove_thm(
  `NOT_LESS_SUB`,
  "!m n. ~( m < (m-n) )"  ,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC "m<=n" THENL
    [ LAST_ASM_REWRITE_TAC (SYM (SPEC_ALL SUB_EQ_0)) THEN
      ASM_REWRITE_TAC[NOT_LESS_0] ;
      LAST_ASM_REWRITE_TAC NOT_LESS_OR_EQ THEN
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
      IMP_RES_TAC SUB_ADD THEN
      ASM_REWRITE_TAC[NOT_LESS;
        (SYM (SPEC "n:num" (SPEC "m:num" (SPEC "m-n" LESS_EQ_MONO_ADD_EQ))));
        LESS_EQ_ADD] ] );;


let SUC_NOT_0 = 
prove_thm(
  `SUC_NOT_0`,
  "!n. ~(SUC n = 0)",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC EQ_LESS THEN
  LAST_ASM_REWRITE_TAC NOT_LESS_0 THEN
  FALSITY_TAC );;

let SUM_LESS = 
prove_thm(
  `SUM_LESS`,
  "!m n p. (m+n)<p ==> ( m<p /\ n<p )",
  REPEAT STRIP_TAC THENL
   [ ASSUME_TAC (SPEC_ALL LESS_EQ_ADD) THEN
     IMP_RES_TAC LESS_LESS_EQ_TRANS ;
     ASSUME_TAC (SPEC "m:num" (SPEC "n:num" LESS_EQ_ADD)) THEN
     POP_ASSUM( ASSUME_TAC o (ONCE_REWRITE_RULE[ADD_SYM]) ) THEN
     IMP_RES_TAC LESS_LESS_EQ_TRANS ]
);;

let LESS_LESS_MONO = 
prove_thm(
  `LESS_LESS_MONO`,
  "!m n p q. (m<p /\ n<q) ==> ( (m+n)<(p+q) )",
  REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_MONO_ADD THEN
  POP_ASSUM (MP_TAC o SPEC "n:num") THEN
  POP_ASSUM (ASSUME_TAC o SPEC "p:num") THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE[ADD_SYM]) THEN
  DISCH_TAC THEN IMP_RES_TAC LESS_TRANS );;

let ADD_BOTH_SIDES = 
prove_thm(
  `ADD_BOTH_SIDES`,
  "!m n p. (m=n) = ( (m+p)=(n+p) )",
    REWRITE_TAC[EQ_MONO_ADD_EQ] );;

let SUB_BOTH_SIDES = 
prove_thm(
  `SUB_BOTH_SIDES`,
  "!m n p. (m=n) ==> ( (m-p)=(n-p) )",
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] );;

let SUB_LESS_BOTH_SIDES = 
prove_thm(
  `SUB_LESS_BOTH_SIDES`,
  "!m n p. ((p<=m) /\ (m<n)) ==> ( (m-p) < (n-p) )",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[
    SYM(SPEC "p:num" (SPEC "n-p" (SPEC "m-p" LESS_MONO_ADD_EQ)))] THEN
  IMP_RES_TAC 
      (SPEC "n:num" (SPEC "m:num" (SPEC "p:num" LESS_LESS_EQ_TRANS))) THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[] );;

let ADD_ASSOC1 = SYM (SPEC_ALL ADD_ASSOC);;

let ADD_SUB_ASSOC = 
prove_thm(
  `ADD_SUB_ASSOC`,
  "!m n p. p<=n ==> ((m+(n-p))=((m+n)-p))",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC SUB_ADD THEN
  ONCE_REWRITE_TAC[
    (SPEC "p:num" (SPEC "(m+n)-p" (SPEC "m+(n-p)" ADD_BOTH_SIDES)))] THEN
  ASM_REWRITE_TAC[ADD_ASSOC1] THEN
  ASSUME_TAC (SPEC "m:num" (SPEC "n:num" LESS_EQ_ADD)) THEN
  IMP_RES_TAC (SPEC "n+m" (SPEC "n:num" (SPEC "p:num" LESS_EQ_TRANS))) THEN
  POP_ASSUM (ASSUME_TAC o (ONCE_REWRITE_RULE[ADD_SYM])) THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[] );;


let less_sub_imp_sum_less = 
prove_thm(
 `less_sub_imp_sum_less`,
 "!i:num. !m:num.  ( i<(m-1)  /\  1<m ) ==> (i+1)<m " ,
  ONCE_REWRITE_TAC
    [SYM (SPEC "1" (SPEC "m-1" (SPEC "i:num" LESS_MONO_ADD_EQ)))] THEN
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC SUB_ADD THEN
  PURE_ASSUM_REWRITE_TAC 6 1 THEN
  ASM_REWRITE_TAC[]  );;

let less_twice_imp_less_sub =
prove_thm(
  `less_twice_imp_less_sub`,
  "!a:num. !b:num. !m:num.
     ( a<m /\ b<m /\ m<=(a+b) ) ==> ( ((a+b)-m) < m )" ,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL ["a:num";"b:num";"m:num";"m:num"] 
           LESS_LESS_MONO) THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN
   MP_TAC (SPECL ["(a+b)-m";"m:num";"m:num"] LESS_MONO_ADD_EQ)
   THEN IMP_RES_TAC SUB_ADD THEN
   ASM_REWRITE_TAC[] );;


let  not_less_imp_add_1_less_or_eq =
prove_thm(
  `not_less_imp_add_1_less_or_eq` ,
  "!a:num. !b:num. ~a<b ==> b<=(a+1)" , 
  REWRITE_TAC [NOT_LESS; SYM( SPEC_ALL ADD1)] THEN
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (SPEC "a:num" LESS_SUC_REFL) THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC LESS_EQ_TRANS );;


let LESS_EQ_MONO_EQ =
prove_thm(
  `LESS_EQ_MONO_EQ`,
  "!m n. (SUC m <= SUC n) = (m <= n)",
  REWRITE_TAC[LESS_OR_EQ;INV_SUC_EQ;LESS_MONO_EQ] );;

let NOT_0_AND_MORE =
prove_thm(
 `NOT_0_AND_MORE`,
 "!x:num. ~( (x=0) /\ (0<x) )",
  REPEAT STRIP_TAC THEN UNDISCH_TAC "0<x" THEN ASM_REWRITE_TAC[LESS_REFL]);;

let LESS_OR_EQ_0 =
prove_thm(
  `LESS_OR_EQ_0`,
  "!n:num. 0 <= n",
  REWRITE_TAC[LESS_OR_EQ] THEN
  ONCE_REWRITE_TAC [DISJ_SYM] THEN
  REWRITE_TAC [LESS_0_CASES] );;


let SUB_MONO_EQ = %from tfm%
    prove_thm
    (`SUB_MONO_EQ`,
     "!n m. (SUC n) - (SUC m) = (n - m)",
     INDUCT_TAC THENL
     [REWRITE_TAC [SUB;LESS_0];
      ASM_REWRITE_TAC [SUB;LESS_MONO_EQ]]);;

let SUB_PLUS =  %from tfm%
   prove_thm
   (`SUB_PLUS`,
    "!a b c. a - (b + c) = (a - b) - c",
    REPEAT INDUCT_TAC THEN
    REWRITE_TAC [SUB_0;ADD_CLAUSES;SUB_MONO_EQ] THEN
    ASSUM_LIST (REWRITE_TAC o (map (SYM o SPEC_ALL))) THEN
    REWRITE_TAC [ADD_CLAUSES]);;


let LESS_PRE =
prove_thm(
 `LESS_PRE`,
 "!i m:num. ( i < (m-1) ) ==> (i < m)",
 GEN_TAC THEN INDUCT_TAC THEN
 REWRITE_TAC[SUB_0;NOT_LESS_0;SYM (SPEC_ALL PRE_SUB1);PRE;LESS_SUC]);;


let PRE_LESS_LESS_SUC = 
prove_thm(
 `PRE_LESS_LESS_SUC`,
 "!i:num. !m:num.  ( i<(m-1)  /\  0<m ) ==> (i+1)<m " ,
 GEN_TAC THEN INDUCT_TAC THEN
 REWRITE_TAC[LESS_REFL;LESS_0;SYM(SPEC_ALL PRE_SUB1);
               SYM(SPEC_ALL ADD1);PRE;LESS_MONO_EQ] );;


let SUB_LESS_OR = %from tfm arith %
    prove_thm
    (`SUB_LESS_OR`,
     "!m n. n < m ==> n <= (m - 1)",
     REPEAT GEN_TAC THEN
     DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [SYM (SPEC_ALL PRE_SUB1)] THEN
     REWRITE_TAC [PRE;num_CONV "1";ADD_CLAUSES;LESS_EQ_ADD]);;

let ONE_LESS_0_LESS =
prove_thm(
 `ONE_LESS_0_LESS`, 
 "!m. 1<m ==> 0<m",
  REWRITE_TAC [SUC_0] THEN
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (SPEC "0" LESS_SUC_REFL) THEN
  IMP_RES_TAC LESS_TRANS);;

let useful_lemma =
prove_thm( 
 `useful_lemma`,
 "!a b c n:num. 0<c /\  a<=(b-n) ==> ( (a-c) <= (b-SUC n) )",
REPEAT INDUCT_TAC THEN 
let th1 = (REWRITE_RULE [SYM (SPEC_ALL NOT_LESS_OR_EQ)] LESS_0) in
  ASM_REWRITE_TAC[LESS_REFL;SUB_0;th1;LESS_0] THEN  
ASM_REWRITE_TAC[SUB_MONO_EQ;LESS_EQ_MONO_EQ;SUB_0;LESS_OR_EQ_0] THEN
STRIP_TAC THEN
let th2 = (REWRITE_RULE [NOT_LESS] NOT_LESS_SUB) in
  ASSUME_TAC (SPECL ["a:num";"c:num"] th2) THEN
IMP_RES_TAC LESS_EQ_TRANS THEN
IMP_RES_TAC OR_LESS THEN
IMP_RES_TAC SUB_LESS_OR THEN 
POP_ASSUM (ASSUME_TAC o REWRITE_RULE 
   [SYM (SPEC_ALL SUB_PLUS);SYM(SPEC_ALL ADD1)]) THEN
IMP_RES_TAC LESS_EQ_TRANS );;


close_theory();;

quit();;
