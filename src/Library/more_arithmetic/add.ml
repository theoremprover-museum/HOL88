
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         add.ml                                                     %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION   : Theorems about addition      		             %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theories of 				     %
%                                                                            %
%   Mike Benjamin							     %
%   Rachel Cardell-Oliver						     %
%   Paul Curzon							 	     %
%   Elsa L Gunter							     %
%   Philippe Leveilley							     %
%   Wim Ploegaerts							     %
%                                                                            %
%****************************************************************************%
% PC 12/8/92                                                                 %
% LESS_EQ_ADD2                                                               %
% Moved to main system by JRH                                                %
% Variable names changed                                                     %
% Equality swapped round                                                     %
% Name changed to LESS_EQUAL_ADD                                             %
% Now |- !m n. m <= n ==> (?p. n = m + p)                                    %
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
%      num_convs                           for num conversions               %
%                                                                            %
%****************************************************************************%

system `rm -f add.th`;;

new_theory `add`;;

new_parent `suc`;;

% PC 22-4-92 These are no longer used%
%loadf `tools`;;%
%autoload_defs_and_thms `ineq`;;%

let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy)) in

   autoload_defs_and_thms `suc`;;

loadf `num_convs`;;

%<-------------------------------------------------------------------------->%

%<PL>%
let LESS_LESS_EQ =
    prove_thm (`LESS_LESS_EQ`,
    	       "!a b. (a < b) = ((a + 1) <= b)",
	       REWRITE_TAC [SYM (SPEC_ALL ADD1); LESS_EQ]);;


%<-------------------------------------------------------------------------->%

%<PL>%
let ADD_SUC_0 =
save_thm (`ADD_SUC_0`,
	  (CONV_RULE (DEPTH_CONV num_CONV))
	  (REWRITE_RULE [SPECL ["m:num";"1"] ADD_SYM] ADD1));;
%<-------------------------------------------------------------------------->%

%<PL>%
let LESS_EQ_MONO_ADD_EQ0 =
    save_thm (`LESS_EQ_MONO_ADD_EQ0`,
	      GEN_ALL (SYM (SUBS [SPECL ["m:num";"p:num"] ADD_SYM;
                                  SPECL ["n:num";"p:num"] ADD_SYM]
                                 (SPEC_ALL LESS_EQ_MONO_ADD_EQ))));;

%<-------------------------------------------------------------------------->%

%<PL>%
let LESS_EQ_MONO_ADD_EQ1 =
    save_thm (`LESS_EQ_MONO_ADD_EQ1`,
	      GEN_ALL (REWRITE_RULE [ADD]
	                            (SPECL ["m:num";"0:num";"p:num"]
	                                   LESS_EQ_MONO_ADD_EQ)));;


%<-------------------------------------------------------------------------->%

%<PL>%
let LESS_EQ_ADD1 =
    save_thm (`LESS_EQ_ADD1`,
	      GEN_ALL (REWRITE_RULE [ADD;ZERO_LESS_EQ]
	                            (SPECL ["0:num";"n:num";"p:num"]
	                                   LESS_EQ_MONO_ADD_EQ)));;

%<-------------------------------------------------------------------------->%

%<PL>%
let ADD_SYM_ASSOC =
    prove_thm (`ADD_SYM_ASSOC`,
	       "! a b c. a + (b + c) = b + (a + c)",
	       REPEAT GEN_TAC THEN
	       REWRITE_TAC [ADD_ASSOC] THEN
	       SUBST_TAC [SPECL ["a:num";"b:num"] ADD_SYM] THEN
	       REWRITE_TAC []);;
%<-------------------------------------------------------------------------->%

%<PL>%
let LESS_EQ_SPLIT =
    save_thm (`LESS_EQ_SPLIT`,
              GEN_ALL(
	      let asm_thm = ASSUME "(m + n) <= p"
	      in
	      DISCH_ALL
	       (CONJ
		(MP (SPECL ["n:num";"m+n";"p:num"] LESS_EQ_TRANS)
       		    (CONJ (SUBS [SPECL ["n:num";"m:num"] ADD_SYM]
		                (SPECL ["n:num";"m:num"] LESS_EQ_ADD))
                          asm_thm))
	        (MP (SPECL ["m:num";"m+n";"p:num"] LESS_EQ_TRANS)
                    (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm)))));;
       
%============================================================================%
%									     %
% 			 inequalities in assumptions			     %
%									     %
%============================================================================%


%<ELG>%
let ADDL_GREATER = prove_thm (`ADDL_GREATER`,
"!m n p.m<n==>m<(p+n)",
(GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN
 (ASM_REWRITE_TAC (CONJUNCTS ADD_CLAUSES)) THEN
 RES_TAC THEN
 (ASM_REWRITE_TAC[(UNDISCH_ALL(SPECL ["m:num";"(p+n)"] LESS_SUC))])));;

%ADDL_GREATER = |- !m:num n:num p:num. m < n ==> m < (p + n)%

%<-------------------------------------------------------------------------->%

%<ELG>%
let ADDL_GREATER_EQ = prove_thm (`ADDL_GREATER_EQ`,
"!m n p. m <= n ==> m <= p+n",
((REPEAT GEN_TAC) THEN DISCH_TAC THEN
 (ASSUME_TAC (REWRITE_RULE [(CONJUNCT1(CONJUNCT2 ADD_CLAUSES))]
  (SPECL ["m:num";"0";"n:num";"p:num"] LESS_EQ_LESS_EQ_MONO))) THEN
 (ASSUME_TAC (REWRITE_RULE [(SPECL ["m:num";"n:num"] NOT_LESS)]
  (SPEC "p:num" NOT_LESS_0))) THEN RES_TAC THEN
 (SUBST_TAC [(SPECL ["p:num";"n:num"] ADD_SYM)]) THEN
 (FIRST_ASSUM ACCEPT_TAC)));;

%ADDL_GREATER_EQ = |- !m:num n:num p:num. m <= n ==> m <= (p + n)%

%<-------------------------------------------------------------------------->%

%<ELG>%
let ADDR_GREATER = save_thm(`ADDR_GREATER`,
    PURE_ONCE_REWRITE_RULE[ADD_SYM]ADDL_GREATER);;

%ADDR_GREATER = |- !m:num n:num p:num. m < n ==> m < (n + p)%


%<-------------------------------------------------------------------------->%

%<ELG>%
let ADDR_GREATER_EQ = save_thm(`ADDR_GREATER_EQ`,
    PURE_ONCE_REWRITE_RULE[ADD_SYM]ADDL_GREATER_EQ);;

%ADDR_GREATER_EQ = |- !m:num n:num p:num. m <= n ==> m <= (n + p)%


%<-------------------------------------------------------------------------->%

%<WP>%
let LESS_LESS_MONO = prove_thm (`LESS_LESS_MONO`,
  "!m n p q . ((m < p) /\ (n < q)) ==> ((m + n) < (p + q))",
  REPEAT GEN_TAC THEN
  DISCH_THEN \t . 
    let [t1;t2] = CONJUNCTS t in
      ASSUME_TAC (CONV_RULE (NUM_LESS_PLUS_CONV "q:num") t1) THEN
      ASSUME_TAC 
      (SPEC "m:num" 
       (GEN_ALL 
	(CONV_RULE ((NUM_LESS_PLUS_CONV "r:num") THENC
		    (ONCE_DEPTH_CONV (REWR_CONV ADD_SYM))) t2)))
      THEN
      IMP_RES_TAC LESS_TRANS
);;


%<WP>% 
let LESS_LESS_EQ_MONO = prove_thm (
  `LESS_LESS_EQ_MONO`,
   "(!m n p q . ((m < p) /\ (n <= q)) ==> ((m + n) < (p + q))) /\ 
    (!m n p q . ((m <= p) /\ (n < q)) ==> ((m + n) < (p + q)))",
  REWRITE_TAC [LESS_OR_EQ;DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC LESS_LESS_MONO THEN
  FIRST_ASSUM \t. (SUBST_TAC [t] ? NO_TAC) THEN
  ((REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
    FIRST_ASSUM ACCEPT_TAC) ORELSE
   (ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [LESS_MONO_ADD_EQ] THEN 
    FIRST_ASSUM ACCEPT_TAC))
);;



%<-------------------------------------------------------------------------->%

%<WP>%
let ADD_EQ_LESS_IMP_LESS = prove_thm (
  `ADD_EQ_LESS_IMP_LESS`,
  " !n m k l . ((k + m = l + n) /\ (k < l)) ==> (n < m)",
  REPEAT GEN_TAC THEN 
  ASM_CASES_TAC "n < m" THEN
  POP_ASSUM \t . 
        REWRITE_TAC [t] THEN
        DISCH_THEN \thm . 
          let [t1;t2] = CONJUNCTS thm in
           MP_TAC
              (MATCH_MP (CONJUNCT1 LESS_LESS_EQ_MONO)
                (CONJ t2 (REWRITE_RULE [NOT_LESS] t))) THEN
           REWRITE_TAC [t1;LESS_REFL]
);;







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Paul Curzon                                                %
%   DATE:         June 1991                                                  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% ********************************************************************** %

let LESS_ADD_ASSOC = save_thm(`LESS_ADD_ASSOC`,
  (GEN_ALL (REWRITE_RULE
     [SYM (SPEC "d:num" (SPEC "c:num" (SPEC "b:num" ADD_ASSOC)))]
      (SPEC "d:num" (SPEC "b+c" (SPEC "a:num"  ADDR_GREATER))))));;

% LESS_ADD_ASSOC |- !a b c d. a < (b + c) ==> a < (b + (c + d)) %
% *************************************************************************** %
% |- !m n p. p >= (m + n) ==> p >= m /\ p >= n %

let GREATER_EQ_SPLIT = save_thm(`GREATER_EQ_SPLIT`,
    REWRITE_RULE [GSYM GREATER_EQ] LESS_EQ_SPLIT);;

% ************************************************************************* %

let LESS_TRANS_ADD = prove_thm(`LESS_TRANS_ADD`,
"!m n p q. 
   (m < n + p) /\ (p < q) ==> (m < n + q)",

 (REPEAT STRIP_TAC) THEN
 (IMP_RES_TAC  LESS_MONO_ADD) THEN
 (REWRITE_TAC[
  MATCH_MP (SPECL["m:num";"n+p"; "n+q"]LESS_TRANS)
  (CONJ (ASSUME "m < n + p")
        (ONCE_REWRITE_RULE[ADD_SYM]
           (SPEC "n:num" (ASSUME "!p'. (p + p') < (q + p')")) ))]));;

% (FILTER_IMP_RES_TAC %
%     "!p'. (p + p') < (q + p')"  LESS_MONO_ADD) THEN%
% (POP_TAC (SPEC "n:num")) THEN%
% (POP_TAC (ONCE_REWRITE_RULE[ADD_SYM])) THEN%
% (IMP_RES_TAC %
%   (SPECL["m:num";"n+p"; "n+q"]LESS_TRANS)));;%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Mike Benjamin                                              %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% PC 12/8/92                     %
% Moved to main system by JRH    %
% Variable names changed         %
% Equality swapped round         %
% Name changed to LESS_EQUAL_ADD %
% Now |- !m n. m <= n ==> (?p. n = m + p)   %



%   ***************************************************************************
    *                                                                         *
    *    If a number is less than or equal to another then another number     *
    *    can be added to make them equal.                                     *
    *                                                                         *
    *    LESS_EQ_ADD2 = |- !a b. a <= b ==> (?n. a + n = b)                   *
    *                                                                         *
    **************************************************************************%

%let LESS_EQ_ADD2 = prove_thm (`LESS_EQ_ADD2`,%
%"! (a:num) (b:num). (a <= b) ==> ? (n:num). a+n=b",%
%INDUCT_TAC%
%THENL [%
%GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC "b:num" THEN REWRITE_TAC [ADD_CLAUSES];%
%GEN_TAC THEN REWRITE_TAC [SYM_RULE LESS_EQ;%
%                          ADD_CLAUSES;ADD1;%
%                          SYM_RULE ADD_ASSOC;%
%                          SYM_RULE LESS_ADD_1]]);;%





%****************************************************************************%
%                                                                            %
% AUTHOR        : Rachel Cardell-Oliver                                      %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%


let ADD_GREATER_EQ = 
prove_thm(
  `ADD_GREATER_EQ`,
  "!m n. (m+n) >= m",
  ASM_REWRITE_TAC[GREATER_OR_EQ;GREATER] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ASM_REWRITE_TAC[(SYM (SPEC_ALL LESS_OR_EQ));LESS_EQ_ADD] );;


let ADD_MONO_LESS = prove_thm(`ADD_MONO_LESS`,
  "!m n p. (m+p) < (m+n) = (p<n)",
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ONCE_REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
  REWRITE_TAC[] );;

% see also LESS_EQ_MONO_ADD_EQ0 %
% Moved to main system by RJB on 92.09.28 %
%let ADD_MONO_LESS_EQ = prove_thm(`ADD_MONO_LESS_EQ`,%
%  "!m n p.  (m+n)<=(m+p) = (n<=p)",%
%  ONCE_REWRITE_TAC [ADD_SYM] THEN%
%  REWRITE_TAC[LESS_EQ_MONO_ADD_EQ]);;%


%not_1_even --> NOT_1_TWICE  PC%
let NOT_1_TWICE =
prove_thm(
 `NOT_1_TWICE`,
 "!n:num. ~(1 = n+n )" ,
 INDUCT_TAC THENL
  [ REWRITE_TAC[ADD_CLAUSES;SUC_0;SUC_ID] ;
    REWRITE_TAC[ADD;SUC_0;INV_SUC_EQ;ADD_CLAUSES] THEN
    ASSUME_TAC (SPEC "n+n" LESS_0) THEN
    IMP_RES_TAC LESS_NOT_EQ ]);;

let SUM_LESS = prove_thm( `SUM_LESS`,
  "!m n p. (m+n)<p ==> ( m<p /\ n<p )",
  REPEAT STRIP_TAC THENL
   [ ASSUME_TAC (SPEC_ALL LESS_EQ_ADD) THEN
     IMP_RES_TAC LESS_EQ_LESS_TRANS ;
     ASSUME_TAC (SPEC "m:num" (SPEC "n:num" LESS_EQ_ADD)) THEN
     POP_ASSUM( ASSUME_TAC o (ONCE_REWRITE_RULE[ADD_SYM]) ) THEN
     IMP_RES_TAC LESS_EQ_LESS_TRANS ]);;



let  NOT_LESS_IMP_LESS_EQ_ADD1 =prove_thm(
  `NOT_LESS_IMP_LESS_EQ_ADD1` ,
  "!a:num. !b:num. ~a<b ==> b<=(a+1)" , 
  REWRITE_TAC [NOT_LESS; SYM( SPEC_ALL ADD1)] THEN
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (SPEC "a:num" LESS_SUC_REFL) THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC LESS_EQ_TRANS );;


let NOT_ADD_LESS = prove_thm(`NOT_ADD_LESS`,
  "!m n. ~((m+n)<n)",
  REWRITE_TAC[NOT_LESS;ONCE_REWRITE_RULE[ADD_SYM]LESS_EQ_ADD] );;

let ADD_EQ_LESS_EQ = prove_thm(`ADD_EQ_LESS_EQ`,
  "!m n p. ((m+n)=p) ==> (m<=p)",
  REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
  ASM_REWRITE_TAC[LESS_EQ_ADD] );;

let SUC_LESS_N_LESS = prove_thm(`SUC_LESS_N_LESS`,
   "!m n.(m+1) < n ==> m < n",
   REPEAT STRIP_TAC THEN 
   ASSUME_TAC(SPECL ["m:num"] (REWRITE_RULE[ADD1]LESS_SUC_REFL)) THEN
   IMP_RES_TAC LESS_TRANS );;

 
%< ------------------------------------------------------------------- >%
%< An extra theorem by PC  >%
let  LESS_ADD1 =  prove_thm(`LESS_ADD1`,
 "!a . a < (a + 1)",
 (REWRITE_TAC[SPECL["m:num"; "0"] LESS_ADD_SUC; SUC_0]));;

close_theory();;
