
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         sub.ml                                                     %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION : Theorems dealing with substraction 	   	             %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theories of 				     %
%                                                                            %
%   Richard J.Boulton							     %
%   Rachel Cardell-Oliver						     %
%   Paul Curzon							 	     %
%   Elsa L Gunter							     %
%   Wim Ploegaerts							     %
%                                                                            %
%****************************************************************************%
%                                                                            %
% PC 21/4/93                                                                 %
%     Removed dependencies on several external files/theories                %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%****************************************************************************%
%                                                                            %
%  DEPENDANCIES :                                                            %
%                                                                            %
%      suc                                 for theorems about SUC            %
%      ineq                                for theorems about inequalities   %
%      add                                 for theorems about addition       %
%      zero_ineq                           for theorems about 0              %
%      num_convs                           for num conversions               %
%                                                                            %
%****************************************************************************%

system `rm -f sub.th`;;

new_theory `sub`;;

new_parent `add`;;
new_parent `zero_ineq`;;

loadt `num_convs`;;

% PC 22-4-92 These are no longer used%
%loadf `tools`;;%
%loadf (library_pathname() ^ `/group/start_groups`);;%
%autoload_defs_and_thms `ineq`;;%


let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy)) in

  autoload_defs_and_thms `suc`;
  autoload_defs_and_thms `add`;
  autoload_defs_and_thms `zero_ineq`;;


%============================================================================%
%									     %
% 		     Theorems dealing with substraction			     %
%									     %
%============================================================================%

%<WP>%
let SUB_SUC_PRE_SUB = prove_thm (
  `SUB_SUC_PRE_SUB`,
  "! n m . (0 < n) ==> (n - (SUC m) = (PRE n) - m)",
  INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0;SUB_MONO_EQ;PRE]
);;

%<-------------------------------------------------------------------------->%

%<WP>%
let ADD_SUC = SYM (el 4 (CONJUNCTS ADD_CLAUSES));;

%<WP>%
let SUB_SUC = prove_thm (
  `SUB_SUC`,
   "! k m .  (m < k ) ==> ( k - m = SUC (k - SUC m) ) ",
  REPEAT GEN_TAC THEN
  SUBST_TAC [SYM (SPECL ["k:num";"m:num"] SUB_MONO_EQ)] THEN
  DISCH_THEN \thm .  
               let thm' = MATCH_MP  LESS_SUC_NOT thm in
               ACCEPT_TAC (REWRITE_RULE [thm'] 
                      (SPECL ["k:num";"SUC m"] (CONJUNCT2 SUB)))
);;

%<-------------------------------------------------------------------------->%

%<ELG>%
let SUB_LESS_TO_LESS_ADDR = prove_thm(`SUB_LESS_TO_LESS_ADDR`,
"!m n p.((p<=m)==>(((m-p)<n)=(m<(n+p))))",
((REPEAT GEN_TAC) THEN
 DISCH_TAC THEN
 (REWRITE_TAC
  [(SYM(SPECL["m-p";"n:num";"p:num"]LESS_MONO_ADD_EQ));
   (UNDISCH_ALL(SPECL["m:num";"p:num"]SUB_ADD))])));;

%SUB_LESS_TO_LESS_ADDR = 
 |- !m:num n:num p:num. p <= m ==> ((m - p) < n = m < (n + p))%

%<-------------------------------------------------------------------------->%

%<ELG>%

let SUB_LESS_TO_LESS_ADDL = prove_thm(`SUB_LESS_TO_LESS_ADDL`,
"!m n p.((n<=m)==>(((m-n)<p)=(m<(n+p))))",
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL["m:num";"p:num";"n:num"]SUB_LESS_TO_LESS_ADDR))));;


%SUB_LESS_TO_LESS_ADDL = 
 |- !m:num n:num p:num. n <= m ==> ((m - n) < p = m < (n + p))%
%<-------------------------------------------------------------------------->%

%<ELG>%

% This theorem could be strengthened; see SUB_LEFT_LESS       [RJB 92.09.29] %
let LESS_SUB_TO_ADDR_LESS = prove_thm(`LESS_SUB_TO_ADDR_LESS`,
"!m n p.((p<=m)==>((n<(m-p))=(n+p)<m))",
((REPEAT GEN_TAC) THEN
 DISCH_TAC THEN
 (REWRITE_TAC
  [(SYM(SPECL["n:num";"m-p";"p:num"]LESS_MONO_ADD_EQ));
   (UNDISCH_ALL(SPECL["m:num";"p:num"] SUB_ADD))])));;

%LESS_SUB_TO_ADDR_LESS = 
 |- !m:num n:num p:num. p <= m ==> (n < (m - p) = (n + p) < m)%


%<-------------------------------------------------------------------------->%

%<ELG>%
let LESS_SUB_TO_ADDL_LESS = prove_thm(`LESS_SUB_TO_ADDL_LESS`,
"!m n p.((n<=m)==>((p<(m-n))=((n+p)<m)))",
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL["m:num";"p:num";"n:num"]LESS_SUB_TO_ADDR_LESS))));;

%LESS_SUB_TO_ADDL_LESS = 
 |- !m:num n:num p:num. n <= m ==> (p < (m - n) = (n + p) < m)%

%<-------------------------------------------------------------------------->%

%<ELG>%

let SUC_SUB = prove_thm (`SUC_SUB`,
"!m n.(((m<n)==>(((SUC m)-n)=0))/\(~(m<n)==>(((SUC m)-n)=SUC(m-n))))",
%New proof by PC 22-4-93%
((REPEAT GEN_TAC) THEN
 (ASM_CASES_TAC "m<n") THEN
 (ASM_REWRITE_TAC[SUB])));;

%((REPEAT GEN_TAC) THEN (ASM_CASES_TAC "m<n") THEN%
% (ASM_REWRITE_TAC%
%  [((REWRITE_RULE [COND_DEF] (CONJUNCT2 SUB)) and_then%
%    CONV_RULE(DEPTH_CONV BETA_CONV))])%
%THENL%
% [((SELECT_TAC "@x.x=0") THEN (EXISTS_TAC "0") THEN REFL_TAC);%
%  ((SELECT_TAC"@x.x=SUC(m-n)")THEN(EXISTS_TAC"SUC(m-n)")THEN REFL_TAC)]));;%

%SUC_SUB = 
 |- !m:num n:num.
     (m < n ==> ((SUC m) - n = 0)) /\
     (~m < n ==> ((SUC m) - n = SUC(m - n)))%


%<--------------------------------------------------------------------------->%

%<WP>%
% Name change to avoid clash with 1.12 arithmetics SUB_SUB %

let LESS_SUB_BOUND = PROVE
  ("!k l . (k < l) ==> ((l - k) <= l)",
   REWRITE_TAC[SUB_LESS_EQ]
);;

let SUB_SUB_ID = prove_thm (
  `SUB_SUB_ID`,
  "!k l . (l < k) ==> (k - (k - l) = l)",
  REPEAT GEN_TAC THEN 
  DISCH_THEN \thm .
      CONV_TAC ((NUM_EQ_PLUS_CONV "k-l" ) THENC
                (RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV ADD_SYM)))) THEN
      MAP_EVERY  SUBST1_TAC  (map (\t . MATCH_MP SUB_ADD t)
                     [MATCH_MP LESS_SUB_BOUND thm;
                      MATCH_MP LESS_IMP_LESS_OR_EQ thm]) THEN
  REFL_TAC
);;

%<--------------------------------------------------------------------------->%

%<WP>%
let LESS_SUB_IMP_INV = prove_thm (
  `LESS_SUB_IMP_INV`,
  "!k l . (0 < k - l) ==> (l < k)",
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN 
  REWRITE_TAC [NOT_LESS;GSYM SUB_EQ_0;SUB_0]
);;

%============================================================================%
%									     %
% 				Simplications				     %
%									     %
%============================================================================%

%<ELG>%
let LESS_EQ_ADD_SUB1 =prove_thm (`LESS_EQ_ADD_SUB1`,
"!m n p.((p <= n) ==> (m+(n-p)=(m+n)-p))",
((REPEAT GEN_TAC) THEN (SPEC_TAC ("m:num", "m:num")) THEN INDUCT_TAC THENL
 [(REWRITE_TAC [(CONJUNCT1 ADD)]);
  ((REWRITE_TAC [(CONJUNCT2 ADD)]) THEN
   DISCH_TAC THEN
   (ASSUME_TAC (SPECL ["p:num";"n:num";"m:num"] ADDL_GREATER_EQ)) THEN
   (ASSUME_TAC (snd(EQ_IMP_RULE(SPECL ["m+n";"p:num"] NOT_LESS)))) THEN
   RES_TAC THEN RES_TAC THEN
   (ASM_REWRITE_TAC [(UNDISCH_ALL(CONJUNCT2(SPECL["m+n";"p:num"]SUC_SUB)))])
  )]));;

%LESS_EQ_ADD_SUB1 =
      |- !m:num n:num p:num. p <= n ==> (m + (n - p) = (m + n) - p)%


%<-------------------------------------------------------------------------->%

%<ELG>%
let LESS_EQ_SUB_ADD=prove_thm (`LESS_EQ_SUB_ADD`,
"!m n p. p <= m ==> ((m-p)+n = (m+n)-p)",
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL["n:num";"m:num";"p:num"]LESS_EQ_ADD_SUB1))));;

%LESS_EQ_SUB_ADD =
    |- !m:num n:num p:num. p <= m ==> ((m - p) + n = (m + n) - p)%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Paul Curzon                                                %
%   DATE:         June 1991                                                  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% See also SUB_LESS_TO_LESS_ADDL and SUB_LESS_TO_LESS_ADDR %

let GREATER_EQ_SUB_LESS_TO_ADD = prove_thm (
  `GREATER_EQ_SUB_LESS_TO_ADD`,
  "!n m p. (p >= n) ==> (((p - n) < m) = (p < (n + m)))",
 (REWRITE_TAC
    [SYM (SPEC "n:num" (SPEC "m:num" (SPEC "p - n" LESS_MONO_ADD_EQ)))]) THEN
 (REPEAT STRIP_TAC) THEN
 (POP_ASSUM (\th .ASSUME_TAC
    (MP  (SPEC "n:num" (SPEC "p:num" SUB_ADD)) 
          (REWRITE_RULE[SPEC "n:num" (SPEC "p:num" GREATER_EQ)]
                       th)))) THEN
 (SUBST_TAC[SPEC_ALL ADD_SYM]) THEN
 (ASM_REWRITE_TAC[]));;

% ********************************************************************** %
let SUB_GREATER_EQ_ADD = prove_thm (
  `SUB_GREATER_EQ_ADD`,
  "!n m p. (p >= n) ==> (((p - n) >= m) = (p >= (n + m)))",
 (REWRITE_TAC[
      SYM (SPEC "n:num" (SPEC "p-n" (SPEC "m:num" 
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]) THEN
 (REPEAT STRIP_TAC) THEN
 (POP_ASSUM (\th .ASSUME_TAC
     (MP  (SPEC "n:num" (SPEC "p:num" SUB_ADD)) 
          (REWRITE_RULE[SPEC "n:num" (SPEC "p:num" GREATER_EQ)]
                       th)))) THEN
 (SUBST_TAC[(SPEC_ALL ADD_SYM)]) THEN
 (ASM_REWRITE_TAC[]));;



% ********************************************************************** %
% |- !n m p. n <= p ==> (m <= (p - n) = (n + m) <= p) %


let SUB_LE_ADD =  save_thm(`SUB_LE_ADD`,
         REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);;
% ************************************************************************ %
let NOT_SUB_0 = prove_thm (`NOT_SUB_0`,
   "!m n . m < n ==> ~(n - m = 0)",
 (REWRITE_TAC[SUB_EQ_0]) THEN
 (REPEAT STRIP_TAC) THEN
 (IMP_RES_TAC LESS_EQ_ANTISYM));;

% ************************************************************************ %
%New proof by PC 22-4-93%
let  NOT_0_SUB = prove_thm( `NOT_0_SUB`,
    "! m n  . (~ (m - n = 0)) ==> ~ (m = 0)",
 (REPEAT STRIP_TAC) THEN
 (CONTR_TAC 
     (REWRITE_RULE [ASSUME "m = 0"; SUB_0]
                   (ASSUME "~(m - n = 0)") ))
);;

% (REPEAT STRIP_TAC) THEN%
% (POP_ASSUM%
%     (\th . ASSUME_TAC (REWRITE_RULE [th] (ASSUME "~(m - n = 0)")))) THEN%
% (POP_TAC (REWRITE_RULE[SUB_0])) THEN%
% (POP_ASSUM  CONTR_TAC));;%
% ************************************************************************ %
% see also PRE_K_K %

let SUB_1_LESS = prove_thm(`SUB_1_LESS`,
     "! m n . ((~ (m = 0)) /\ (m < SUC n)) ==> ((m - 1) < n)",
%New proof by PC 22-4-93%
 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC[
      (ONCE_REWRITE_RULE[ADD_SYM]
           (REWRITE_RULE [ADD1] (ASSUME "m < SUC n")));
      MATCH_MP (SPECL["1";"n:num"] GREATER_EQ_SUB_LESS_TO_ADD)
               (MATCH_MP NOT_EQ_0 (ASSUME "~ (m = 0)"))]));;


% (REPEAT STRIP_TAC) THEN%
% (POP_TAC (REWRITE_RULE [ADD1])) THEN%
% (IMP_RES_TAC NOT_EQ_0) THEN%
% (IMP_RES_TAC (SPECL["1";"n:num"] GREATER_EQ_SUB_LESS_TO_ADD)) THEN%
% POP_JUNK_TAC THEN%
% POP_JUNK_TAC THEN%
% POP_REWRITE_TAC THEN%
% (ONCE_REWRITE_TAC[ADD_SYM]) THEN%
% (ASM_REWRITE_TAC[]));;%

% ************************************************************************ %
let  SUB_1_LESS_EQ = prove_thm(`SUB_1_LESS_EQ`,
   "! m n. (m < n) ==> ((n - 1) >= m)",
%New proof by PC 22-4-93%
 GEN_TAC THEN
 INDUCT_TAC THENL
 [
 (REWRITE_TAC[SUB_0;GREATER_EQ;LESS_IMP_LESS_OR_EQ]);

 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC[SUC_SUB1;GREATER_EQ;LESS_OR_EQ]) THEN
 (DISJ_CASES_TAC (REWRITE_RULE[LESS_THM](ASSUME "m < SUC n") )) THEN
 (ASM_REWRITE_TAC[])]);;

% GEN_TAC THEN%
% INDUCT_TAC THENL%
% [%
% (REWRITE_TAC[SUB_0;GREATER_EQ;LESS_IMP_LESS_OR_EQ]);%
% (REPEAT STRIP_TAC) THEN%
% (REWRITE_TAC[SUC_SUB1;GREATER_EQ;LESS_OR_EQ]) THEN%
% (POP_TAC (REWRITE_RULE[LESS_THM])) THEN%
% (POP_ASSUM (DISJ_CASES_TAC)) THEN%
% POP_REWRITE_TAC]);;%
% ************************************************************************* %
let ADD_LESS_EQ_SUB = save_thm(`ADD_LESS_EQ_SUB`,
   GSYM (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD));;


%****************************************************************************%
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%



let PRE_SUB_SUC = prove_thm(`PRE_SUB_SUC`,
  "!m n. (m < n) ==> (PRE (n - m) = (n - (SUC m)))",
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [SUB_0;PRE];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [SUB;SUB_MONO_EQ] THEN
    IMP_RES_TAC (REWRITE_RULE [] (CONTRAPOS (SPEC_ALL LESS_SUC_NOT))) THEN
    ASM_REWRITE_TAC [PRE]]);;
%----------------------------------------------------------------------------%

%****************************************************************************%
%                                                                            %
% AUTHOR        : Rachel Cardell-Oliver                                      %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%


let LESS_PRE = prove_thm(`LESS_PRE`,
 "!i m:num. ( i < (m-1) ) ==> (i < m)",
 GEN_TAC THEN INDUCT_TAC THEN
 REWRITE_TAC[SUB_0;NOT_LESS_0;SYM (SPEC_ALL PRE_SUB1);PRE;LESS_SUC]);;



let PRE_LESS_LESS_SUC = prove_thm( `PRE_LESS_LESS_SUC`,
 "!i:num. !m:num.  ( i<(m-1)  /\  0<m ) ==> (i+1)<m " ,
 GEN_TAC THEN INDUCT_TAC THEN
 REWRITE_TAC[LESS_REFL;LESS_0;SYM(SPEC_ALL PRE_SUB1);
               SYM(SPEC_ALL ADD1);PRE;LESS_MONO_EQ] );;

let SUB_PRE_SUB_1 = 
prove_thm(
  `SUB_PRE_SUB_1`,
  "!a b:num.(0<b) ==> (((a-(PRE b))-1) = (a-b))",
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [(SYM (SPEC_ALL SUB_PLUS));PRE_SUB1] THEN
  IMP_RES_TAC LESS_OR THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [SYM SUC_0])) THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[] );;


%less_sub_imp_sum_less --> LESS_SUB_IMP_SUM_LESS PC%
let LESS_SUB_IMP_SUM_LESS = prove_thm(`LESS_SUB_IMP_SUM_LESS`,
 "!i:num. !m:num.  ( i<(m-1)  /\  1<m ) ==> (i+1)<m " ,
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (SPECL ["i:num";"m-1";"1"] LESS_MONO_ADD_EQ) THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC SUB_ADD THEN
  POP_ASSUM(\thm. ONCE_REWRITE_TAC[SYM thm]) THEN
  ASM_REWRITE_TAC[]  );;


let SUB_SELF= SUB_EQUAL_0;;

let ADD_SUB_SYM = save_thm(`ADD_SUB_SYM`,
    ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB);;

let SUB_ADD_SELF = prove_thm(`SUB_ADD_SELF`,
  "!m n. ~(m<n) ==> ( ((m-n)+n)=m )" ,
   REWRITE_TAC[NOT_LESS;SUB_ADD]  );;




let SMALLER_SUM = prove_thm(`SMALLER_SUM`,
  "!m n p. (m<p /\ n<p) ==> ~( ((m+n)-p) > m)",
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GREATER])) THEN
  ASM_CASES_TAC "(m+n)<=p" THENL
  [ POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM SUB_EQ_0])) THEN
    UNDISCH_TAC "m < ((m + n) - p)" THEN ASM_REWRITE_TAC[NOT_LESS_0] ;

% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
%    POP_ASSUM(ASSUME_TAC o (REWRITE_RULE [NOT_LESS_EQ_LESS])) THEN %
    POP_ASSUM(ASSUME_TAC o (REWRITE_RULE [NOT_LESS_EQUAL])) THEN
    IMP_RES_TAC (SPEC "p:num" (SPEC "(m+n)-p" (SPEC "m:num" 
      LESS_MONO_ADD))) THEN
    POP_ASSUM(\thm. MP_TAC thm) THEN
    IMP_RES_TAC (SPEC "m+n" (SPEC "p:num" LESS_IMP_LESS_OR_EQ)) THEN
    IMP_RES_TAC (SPEC "p:num" (SPEC "m+n" SUB_ADD)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [ADD_MONO_LESS])) THEN
    UNDISCH_TAC "n<p" THEN
    UNDISCH_TAC "p<n" THEN
    REWRITE_TAC [IMP_DISJ_THM;NOT_CLAUSES;
        (SYM (CONJUNCT1 (SPEC_ALL DE_MORGAN_THM)));LESS_ANTISYM] ] );;




let NOT_LESS_SUB = prove_thm(`NOT_LESS_SUB`,
  "!m n. ~( m < (m-n) )"  ,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC "m<=n" THENL
   [ POP_ASSUM(\thm. REWRITE_TAC[REWRITE_RULE[GSYM SUB_EQ_0]thm;NOT_LESS_0]);
% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
%     POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LESS_EQ_LESS]) THEN%
     POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LESS_EQUAL]) THEN
     IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
     IMP_RES_TAC SUB_ADD THEN
     REWRITE_TAC[NOT_LESS] THEN
     ONCE_REWRITE_TAC[GSYM(SPECL["m-n";"m:num";"n:num"]LESS_EQ_MONO_ADD_EQ)]
     THEN ASM_REWRITE_TAC[LESS_EQ_ADD] ] );;



let SUB_BOTH_SIDES = prove_thm(`SUB_BOTH_SIDES`,
  "!m n p. (m=n) ==> ( (m-p)=(n-p) )",
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] );;

let SUB_LESS_BOTH_SIDES = prove_thm(`SUB_LESS_BOTH_SIDES`,
  "!m n p. ((p<=m) /\ (m<n)) ==> ( (m-p) < (n-p) )",
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[
    SYM(SPEC "p:num" (SPEC "n-p" (SPEC "m-p" LESS_MONO_ADD_EQ)))] THEN
  IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[] );;


%New proof by PC 22-4-93%
let LESS_TWICE_IMP_LESS_SUB =prove_thm(`LESS_TWICE_IMP_LESS_SUB`,
  "!a:num. !b:num. !m:num.
     ( a<m /\ b<m /\ m<=(a+b) ) ==> ( ((a+b)-m) < m )" ,
   REPEAT STRIP_TAC THEN
   (ACCEPT_TAC
    (REWRITE_RULE [ADD_SUB_SYM]
     (MATCH_MP SUB_LESS_BOTH_SIDES
      (CONJ (ASSUME"m <= (a + b)")
         (MATCH_MP LESS_LESS_MONO 
            (CONJ (ASSUME"a < m")  (ASSUME"b < m") ))))))
);;

%   REPEAT STRIP_TAC THEN%
%   IMP_RES_TAC LESS_LESS_MONO THEN%
%   FILTER_IMP_RES_TAC "((a + b) - m) < ((m + m) - m)" SUB_LESS_BOTH_SIDES THEN%
%   POP_ASSUM ( ASSUME_TAC o (REWRITE_RULE [ADD_SUB_SYM])) THEN%
%   ASM_REWRITE_TAC[] );;%


let SUB_LESS_EQ_SUB_SUC = prove_thm(`SUB_LESS_EQ_SUB_SUC`,
 "!a b c n:num. 0<c /\  a<=(b-n) ==> ( (a-c) <= (b-SUC n) )",
REPEAT INDUCT_TAC THEN 
% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
%let th1 = (REWRITE_RULE [SYM (SPEC_ALL NOT_LESS_EQ_LESS)] LESS_0) in%
let th1 = (REWRITE_RULE [SYM (SPEC_ALL NOT_LESS_EQUAL)] LESS_0) in
  ASM_REWRITE_TAC[LESS_REFL;SUB_0;th1;LESS_0] THEN  
ASM_REWRITE_TAC[SUB_MONO_EQ;LESS_EQ_MONO;SUB_0;ZERO_LESS_EQ] THEN
STRIP_TAC THEN
let th2 = (REWRITE_RULE [NOT_LESS] NOT_LESS_SUB) in
  ASSUME_TAC (SPECL ["a:num";"c:num"] th2) THEN
IMP_RES_TAC LESS_EQ_TRANS THEN
IMP_RES_TAC OR_LESS THEN
IMP_RES_TAC SUB_LESS_OR THEN 
POP_ASSUM (ASSUME_TAC o REWRITE_RULE 
   [SYM (SPEC_ALL SUB_PLUS);SYM(SPEC_ALL ADD1)]) THEN
IMP_RES_TAC LESS_EQ_TRANS );;


let SUB_EQ_SUB_ADD_SUB = prove_thm(`SUB_EQ_SUB_ADD_SUB`,
  "!a b c. ( (a<=b) /\ (b<=c) )  ==> ( (c-a) = ( (c-b)+(b-a) ))",
  REPEAT STRIP_TAC THEN
  REWRITE_TAC 
    [(SYM (SPECL ["c-a";"(c-b)+(b-a)";"a:num"] EQ_MONO_ADD_EQ))] THEN
  IMP_RES_TAC LESS_EQ_TRANS THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC [(SYM (SPEC_ALL ADD_ASSOC))]  );;


let ADD_EQ_IMP_SUB_EQ =prove_thm(`ADD_EQ_IMP_SUB_EQ`,
  "!a b c:num. (a=(b+c)) ==> ((a-b)=c)",
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL ["b:num";"c:num"] LESS_EQ_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL ["c:num";"b:num";"a:num"] ADD_EQ_SUB) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_REWRITE_TAC[] );;


let SUB_GREATER_0 = prove_thm(`SUB_GREATER_0`, 
  "!a b:num. a<b ==> ( (b-a)>0 )",
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [
% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
%            (SYM (SPEC_ALL NOT_LESS_EQ_LESS))])) THEN %
            (SYM (SPEC_ALL NOT_LESS_EQUAL))])) THEN
  DISJ_CASES_TAC (SPECL ["b-a"] LESS_0_CASES) THENL
  [ POP_ASSUM (ASSUME_TAC o ((REWRITE_RULE [SUB_EQ_0]) o SYM)) THEN 
    UNDISCH_TAC "b<=a" THEN
    ASM_REWRITE_TAC[] ;
    ASM_REWRITE_TAC[GREATER] ] );;
 
let LESS_EQ_SUB_1 = prove_thm(`LESS_EQ_SUB_1`,
  "!a b.  a<=b ==> ((a-1) <= (b-1))" ,
   REPEAT STRIP_TAC THEN
   POP_ASSUM (DISJ_CASES_TAC o (REWRITE_RULE [LESS_OR_EQ])) THENL
   [ IMP_RES_TAC SUB_LESS_OR THEN
     ASSUME_TAC 
       (REWRITE_RULE [NOT_LESS] (SPECL ["a:num";"1"] NOT_LESS_SUB)) THEN
     IMP_RES_TAC LESS_EQ_TRANS ;
     ASM_REWRITE_TAC[LESS_EQ_REFL] ] );;


let SUB_LESS_EQ_SUB1  = prove_thm(`SUB_LESS_EQ_SUB1`,
  "!x:num. x>0 ==> (!a:num. (a-x) <= (a-1))" ,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GREATER])) THEN
  IMP_RES_TAC (SPECL ["a:num";"a:num";"x:num";"0"] SUB_LESS_EQ_SUB_SUC) THEN
  POP_ASSUM (ASSUME_TAC o 
     (REWRITE_RULE [SUB_0;LESS_EQ_REFL;(SYM SUC_0)])) THEN
  ASM_REWRITE_TAC[] );;


close_theory();;
