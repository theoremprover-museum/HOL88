
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         ineq.ml                                                    %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION   : Arithmetic theorems about inequalities		     %
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
%                                                                            %
% PC 12/8/92                                                                 %
% LESS_EQ_LESS_TRANS                                                         %
% Moved to main system by JRH                                                %
% Split into 2 theorems                                                      %
% Now                                                                        %
% LESS_EQ_LESS_TRANS = |- !m n p. m <= n /\ n < p ==> m < p                  %
% LESS_LESS_EQ_TRANS = |- !m n p. m < n /\ n <= p ==> m < p                  %
%                                                                            %
% GREATER_EQ                                                                 %
% Moved to main system by JRH                                                %
% Variable names changed                                                     %
% Now |- !n m. n >= m = m <= n                                               %
%                                                                            %
% NOT_LESS_EQ_LESS                                                           %
% Moved to main system by JRH                                                %
% Variable names changed                                                     %
% Name changed to NOT_LESS_EQUAL                                             %
% Now |- !m n. ~m <= n = n < m                                               %
%                                                                            %
% NUM_DISJ_CASES                                                             %
% Moved to main system by JRH                                                %
% Name changed to LESS_LESS_CASES                                            %
% Order of disjuncts changed                                                 %
% Now  |- !m n. (m = n) \/ m < n \/ n < m                                    %
%                                                                            %
% LESS_EQ_CASES                                                              %
% Moved to main system by JRH                                                %
% Different variable names used                                              %
% Now  |- !m n. m <= n \/ n <= m                                             %
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
%      Library taut                        for PTAUT_PROVE                   %
%                                                                            %
%                                                                            %
%****************************************************************************%

system `rm -f ineq.th`;;

new_theory `ineq`;;


load_library `taut`;;

% PC 22-4-92 These are no longer used                                         %
%loadf `tools`;;%
%loadf (library_pathname() ^ `/group/start_groups`);;%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Wim Ploegaerts                                             %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%<-------------------------------------------------------------------------->%
% The theorems below need some tautologies which we prove first %
let NOT_EQ =  PTAUT_PROVE "!t1 t2. (t1 = t2) = (~t1 = ~t2)";;

% PC 22-4-92 These are no longer used                                         %
%let DISJ_ASSOC = PTAUT_PROVE "!t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3";;%
%                                                                             %
%let LEFT_CONJ_DISTRIB =                                                      %
%	      PTAUT_PROVE "!t1 t2 t3:bool.                                    %
%                   (t1 /\ (t2 \/ t3)) = ((t1 /\ t2) \/ (t1 /\ t3))";;        %
%                                                                             %
%let RIGHT_CONJ_DISTRIB =                                                     %
%	      PTAUT_PROVE "!t1 t2 t3:bool.                                    %
%                           ((t2 \/ t3) /\ t1) = ((t2 /\ t1) \/ (t3 /\ t1))";;%
%                                                                             %
%let LEFT_DISJ_CONJ =  PTAUT_PROVE "!a b . a /\ b \/ b = b";;                 %

%<-------------------------------------------------------------------------->%
% PC 12/8/92                                                %
% Moved to main system by JRH                               %
% Split into 2 theorems                                     %
% Now                                                       %
% LESS_EQ_LESS_TRANS = |- !m n p. m <= n /\ n < p ==> m < p %
% LESS_LESS_EQ_TRANS = |- !m n p. m < n /\ n <= p ==> m < p %

%WP 4-9-90%
% let LESS_EQ_LESS_TRANS = prove_thm (% 
%   `LESS_EQ_LESS_TRANS`,% 
%   "(! m n p . ((m <= n) /\ (n < p)) ==> (m < p)) /\ % 
%    (! m n p . ((m < n) /\ (n <= p)) ==> (m < p)) ",% 
%   REWRITE_TAC [LESS_OR_EQ] THEN% 
%   REPEAT STRIP_TAC THEN% 
%   IMP_RES_TAC LESS_TRANS THEN% 
%   ASM_REWRITE_TAC [] THEN% 
%   FIRST_ASSUM \thm . (SUBST_TAC [SYM thm]  ? NO_TAC) THEN% 
%   FIRST_ASSUM ACCEPT_TAC% 
% );;% 

%<-------------------------------------------------------------------------->%
% PC 12/8/92                     %
% Moved to main system by JRH    %
% Variable names changed         %
% Now |- !n m. n >= m = m <= n   %
%                                %
% see LESS_EQ_GREATER_EQ %
%<PL>%
%let GREATER_EQ =%
%    prove_thm (`GREATER_EQ`,%
%               "! a b:num. (a >= b) = (b <= a)",%
%	       REPEAT STRIP_TAC THEN%
% 	       REWRITE_TAC [GREATER_OR_EQ;LESS_OR_EQ;GREATER] THEN%
%	       SUBST_TAC [(SPECL%
%		            ["a:num";"b:num"]%
%		            (INST_TYPE [(":num",":*")] EQ_SYM_EQ))]%
%	       THEN REWRITE_TAC[]);;%

%<-------------------------------------------------------------------------->%

% PC 12/8/92                     %
% Moved to main system by JRH    %
% Variable names changed         %
% Name changed to NOT_LESS_EQUAL %
% Now |- !m n. ~m <= n = n < m   %
%                                %
%<PL>%
%let NOT_LESS_EQ_LESS =%
%    prove_thm (`NOT_LESS_EQ_LESS`,%
%    	       "!a b. (~(a <= b)) = (b < a)",%
%	       REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)]);;%


%<PL>%
% Moved to main system by RJB on 92.09.28 %
% Variable names changed                  %
% Now |- !m n. (m = n) = m <= n /\ n <= m %
%let EQ_LESS_EQ =%
%    prove_thm (`EQ_LESS_EQ`,%
%               "! a b : num . (a = b) = ((a <= b) /\ (b <= a))",%
%	       REPEAT STRIP_TAC THEN%
%	       REWRITE_TAC [LESS_OR_EQ;%
%	       		    LEFT_CONJ_DISTRIB;%
%			    RIGHT_CONJ_DISTRIB;%
%			    LESS_ANTISYM] THEN%
%	       SUBST_TAC [(SPECL%
%		            ["b:num";"a:num"]%
%		            (INST_TYPE [(":num",":*")] EQ_SYM_EQ))] THEN%
%	       REWRITE_TAC [INST [("((a:num) = b)","t1:bool");%
%	       			  ("b < a","t2:bool")]%
%	       			 (SPEC_ALL CONJ_SYM);%
%	       		    DISJ_ASSOC;%
%			    SYM (SPEC_ALL RIGHT_CONJ_DISTRIB);%
%	       		    LEFT_DISJ_CONJ]);;%

%<-------------------------------------------------------------------------->%

%<PL>%
let NOT_EQ_LESS_EQ =
    prove_thm (`NOT_EQ_LESS_EQ`,
               "! a b : num . ~(a = b) = ((a < b) \/ (b < a))",
	       REPEAT STRIP_TAC THEN
	       REWRITE_TAC [INST [("~((a:num) = b)","t1:bool");
	       			  ("((a < b) \/ (b < a))","t2:bool")]
				 (SPEC_ALL NOT_EQ);
			    DE_MORGAN_THM;
			    NOT_LESS] THEN
	       SUBST_TAC [SPECL ["b <= a";"a <= b"] CONJ_SYM] THEN
	       REWRITE_TAC [EQ_LESS_EQ]);;

			

%<-------------------------------------------------------------------------->%

% PC 12/8/92                              %
% Moved to main system by JRH             %
% Name changed to LESS_LESS_CASES         %
% Order of disjuncts changed              %
% Now  |- !m n. (m = n) \/ m < n \/ n < m %

%<WP>%
%let  NUM_DISJ_CASES  = prove_thm (%
%  `NUM_DISJ_CASES`,%
%  " ! m n . (m < n) \/ (m = n) \/ (n < m) ",%
%  REPEAT GEN_TAC THEN%
%  LEMMA_PROOF "! A B C . (A \/ (B \/ C)) = ((A \/ B) \/ C)"%
%                    [REPEAT GEN_TAC ; TAUT_TAC]  THEN%
%  ASM_REWRITE_TAC[SPEC_SYM LESS_OR_EQ] THEN%
%  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV  DISJ_SYM)) THEN%
%  REWRITE_TAC [LESS_CASES]%
%);;%




%============================================================================%
%									     %
% 			     less and less or eq			     %
%									     %
%============================================================================%


%<WP>%
let LESS_IS_NOT_LESS_OR_EQ = prove_thm ( 
  `LESS_IS_NOT_LESS_OR_EQ`,
  "! x y . (x < y) = ~(y <= x)",
  REPEAT GEN_TAC THEN 
  REWRITE_TAC [LESS_OR_EQ;DE_MORGAN_THM] THEN
  EQ_TAC  THENL
 [
  DISJ_CASES_THEN (\t.REWRITE_TAC [t]) (SPECL ["x:num";"y:num"]
        (REWRITE_RULE [DE_MORGAN_THM] LESS_ANTISYM)) THEN
  CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC LESS_NOT_EQ
 ;
  DISCH_THEN \t . ACCEPT_TAC (MATCH_MP LESS_CASES_IMP t)
 ]
);;



%============================================================================%
%									     %
% 				  Induction				     %
%									     %
%============================================================================%
%<ELG>%

let GEN_INDUCTION = prove_thm(`GEN_INDUCTION`,
"!P.(P 0 /\(!n.(!m.(m<n) ==> P m) ==> P n)) ==> !n.P n",
(GEN_TAC THEN 
 DISCH_TAC THEN
 GEN_TAC THEN
 (ACCEPT_TAC (
  let st1=TAC_PROOF((["P 0/\(!n.(!m.(m<n) ==> P m) ==> P n)"],
   "!n.(!m.(m<n) ==> P m)"),
  (INDUCT_TAC THEN
   GEN_TAC THENL
  [(REWRITE_TAC[NOT_LESS_0]);
   ((PURE_ONCE_REWRITE_TAC[LESS_THM]) THEN
    DISCH_TAC THEN
    (ASSUM_LIST (DISJ_CASES_TAC o hd)) THENL
    [((PURE_ONCE_REWRITE_TAC[(ASSUME "m = (n:num)")]) THEN
      (ASSUM_LIST(ACCEPT_TAC o(\thl.MP
       (SPEC "n:num" ((CONJUNCT2 o hd o tl o tl o tl) thl))
       ((hd o tl o tl)thl)))));
     (ASSUM_LIST(ACCEPT_TAC o (\thl.MP
      (SPEC "m:num" ((hd o tl o tl)thl)) (hd thl) )))])])) in
% ((SPEC "SUC n" st1) and_then (SPEC "n:num") and_then%
%  (\thm. MP thm (SPEC "n:num" LESS_SUC_REFL))) ))));;%
   (MP (SPEC "n:num" (SPEC "SUC n" st1))
            (SPEC "n:num" LESS_SUC_REFL))) )));;


%									     %
%  GEN_INDUCTION =							     %
%  |- !P:num -> bool.							     %
%      (P:num -> bool) 0 /\						     %
%      (!n:num.								     %
%        (!m:num. m < n ==> (P:num -> bool) m) ==> (P:num -> bool) n) ==>    %
%      (!n:num. (P:num -> bool) n)					     %
%									     %
%  GEN_INDUCTION =							     %
%  |- !P. P 0 /\ (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n)	     %
%									     %



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Paul Curzon                                                %
%   DATE:         June 1991                                                  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


let  GREATER_EQ_ANTISYM = prove_thm(`GREATER_EQ_ANTISYM`,
       "!n m . ~( n >= m /\ n < m)",
  (REWRITE_TAC [GREATER_EQ]) THEN
  (REPEAT STRIP_TAC) THEN
  (IMP_RES_TAC LESS_EQ_ANTISYM));;



% ************************************************************************* %
% A theorem by Paul Loewenstein %

let LESS_EQ_LESS_EQ_EQ = prove_thm(`LESS_EQ_LESS_EQ_EQ`,
  "!m n. m <= n /\ n <= m = (m = n)",
 REPEAT GEN_TAC THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  IMP_RES_TAC LESS_EQUAL_ANTISYM
 ;
  ASM_REWRITE_TAC [LESS_EQ_REFL]
 ]);;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Mike Benjamin                                              %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% PC 12/8/92                              %
% Moved to main system by JRH             %
% Different variable names used           %
% Now  |- !m n. m <= n \/ n <= m          %
%   ***************************************************************************
    *                                                                         *
    *    Numbers are totally ordered.                                         *
    *                                                                         *
    *    LESS_EQ_CASES = |- !x y. x <= y \/ y <= x                            *
    *                                                                         *
    **************************************************************************%

%let LESS_EQ_CASES  = prove_thm (`LESS_EQ_CASES`,  %
%"! (x:num) (y:num). (x <= y) \/ (y <= x)",%
%INDUCT_TAC%
%THENL [%
%  GEN_TAC%
%  THEN DISJ1_TAC%
%  THEN ASM_REWRITE_TAC [REWRITE_RULE [ADD_CLAUSES] (SPEC "y:num" (SPEC "0" LESS_EQ_ADD))];%
%  GEN_TAC%
%  THEN CUT_THM_TAC (SPEC "(x:num) = 0" (BOOL_CASES_AX))%
%  THEN DISJ_LEFT_TAC%
%  THENL [%
%    CUT_THM_TAC (SPEC "(y:num) = 0" (BOOL_CASES_AX))%
%    THEN DISJ_LEFT_TAC%
%    THENL [%
%      DISJ2_TAC%
%      THEN CUT_TAC "(x:num) = 0"%
%      THENL [%
%        ASM_REWRITE_TAC [];%
%        CUT_TAC "(y:num) = 0"%
%        THENL [%
%          ASM_REWRITE_TAC [];%
%          ASM_REWRITE_TAC []%
%          THEN REWRITE_TAC [LESS_EQ_SUC_REFL]%
%        ]%
%      ];%
%      DISJ1_TAC%
%      THEN CUT_TAC "~((y:num) = 0)"%
%      THENL [%
%        ASM_REWRITE_TAC [];%
%        IMP_RES_TAC (REWRITE_RULE [ADD_CLAUSES] (SPEC "y:num" (SPEC "0" LESS_ADD_NONZERO)))%
%        THEN CUT_TAC "(x:num) = 0"%
%        THENL [%
%          ASM_REWRITE_TAC [];%
%          CUT_TAC "(x:num) < (y:num)"%
%          THENL [%
%            S_REWRITE_TAC [1;2];%
%            REWRITE_TAC [SYM_RULE (SPEC "y:num" (SPEC "x:num" LESS_EQ))]%
%            THEN N_REWRITE_TAC 1%
%          ]%
%        ]%
%      ]%
%    ];%
%    CUT_TAC "~((x:num) = 0)"%
%    THENL [%
%      ASM_REWRITE_TAC [];%
%      FORALL_LEFT_TAC ("PRE (y:num)","y:num")%
%      THEN DISJ_LEFT_TAC%
%      THENL [%
%        CUT_THM_TAC (SPEC "(y:num) = 0" (BOOL_CASES_AX))%
%        THEN DISJ_LEFT_TAC%
%        THENL [%
%          CUT_TAC "(y:num) = 0"%
%          THENL [%
%            ASM_REWRITE_TAC [];%
%            ASM_REWRITE_TAC []%
%            THEN DISJ2_TAC%
%            THEN REWRITE_TAC [REWRITE_RULE [ADD_CLAUSES] (SPEC "SUC (x:num)" (SPEC "0" LESS_EQ_ADD))]%
%          ];%
%          DISJ1_TAC%
%            THEN IMP_RES_TAC (REWRITE_RULE [] (SPEC "y:num" (SPEC "PRE (y:num)" PRE_SUC_EQ)))%
%           THEN CUT_TAC "~((y:num) = 0)"%
%           THENL [%
%              ASM_REWRITE_TAC [];%
%              IMP_RES_TAC (REWRITE_RULE [ADD_CLAUSES] (SPEC "y:num" (SPEC "0" LESS_ADD_NONZERO)))%
%              THEN IMP_RES_TAC (REWRITE_RULE [SYM_RULE ADD1] (SPEC "y:num" (SPEC "PRE (y:num)" PRE_SUC_EQ)))%
%              THEN CUT_THM_TAC (REWRITE_RULE [SYM_RULE ADD1] %
%                  (SPEC "1" (SPEC "PRE (y:num)" (SPEC "x:num" LESS_EQ_MONO_ADD_EQ))))%
%              THEN N_REVERSE_TAC 2%
%              THEN ONCE_N_REWRITE_TAC 1%
%              THEN N_REWRITE_TAC 2%
%              THEN ACCEPT_ASM_TAC%
%           ]%
%        ];%
%        CUT_THM_TAC (SPEC "(y:num) = 0" (BOOL_CASES_AX))%
%        THEN DISJ_LEFT_TAC%
%        THENL [%
%          CUT_TAC "(y:num) = 0"%
%          THENL [%
%            ASM_REWRITE_TAC [];%
%            ASM_REWRITE_TAC []%
%            THEN DISJ2_TAC%
%            THEN REWRITE_TAC [REWRITE_RULE [ADD_CLAUSES] (SPEC "SUC (x:num)" (SPEC "0" LESS_EQ_ADD))]%
%          ];%
%          DISJ2_TAC%
%          THEN CUT_TAC "~((y:num) = 0)"%
%          THENL [%
%            ASM_REWRITE_TAC [];%
%            IMP_RES_TAC (REWRITE_RULE [ADD_CLAUSES] (SPEC "y:num" (SPEC "0" LESS_ADD_NONZERO)))%
%            THEN IMP_RES_TAC (REWRITE_RULE [] (SPEC "y:num" (SPEC "PRE (y:num)" PRE_SUC_EQ)))%
%            THEN CUT_THM_TAC (SYM_RULE (REWRITE_RULE [SYM_RULE ADD1] %
%                (SPEC "1" (SPEC "x:num" (SPEC "PRE (y:num)" LESS_EQ_MONO_ADD_EQ)))))%
%            THEN N_REVERSE_TAC 2%
%            THEN ONCE_N_REWRITE_TAC 1%
%            THEN N_REVERSE_TAC 2%
%            THEN ONCE_N_REWRITE_TAC 1%
%            THEN ACCEPT_ASM_TAC%
%          ]%
%        ]%
%      ]         %
%    ]%
%  ]%
%]);;%






%****************************************************************************%
%                                                                            %
% AUTHOR        : Rachel Cardell-Oliver                                      %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%





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



%< ------------------------------------------------------------------- >%


close_theory();;
