
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         odd_even.ml                                                %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION : Odd and Even 	   	 	   	                     %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%*********************************  HISTORY  ********************************%
%									     %
%									     %
% Author:       Wim Ploegaerts  (ploegaer@imec.be)			     %
%									     %
% Date:         Fri Feb  8 1991						     %
%									     %
% Organization: Imec vzw.						     %
%               Kapeldreef 75						     %
%               3001 Leuven - Belgium					     %
%									     %
%****************************************************************************%
%									     %
% Rewritten by PC 14/8/92 to take account of ODD and EVEN definitions        %
% placed in main system by JRH. The definitions ODD_NUM and EVEN_NUM are     %
% now called ODD and EVEN, respectively. Replicated theorems  have  been     %
% removed from the library (causing name changes). The names of others       %
% have been changed for consistency with the system theorems                 %
%									     %
% The theorem name changes are:						     %
%									     %
%        EVEN_NUM                 --> EVEN_EXISTS                            %
%        NUM_EVEN_MULT           -->  EVEN_IMPL_MULT                         % 
%        NUM_EVEN_ODD_PLUS_CASES --> EVEN_ODD_PLUS_CASES                     %
%        NUM_EVEN_ODD_SUC        --> EVEN_ODD_SUC                            %
%        NUM_EVEN_OR_ODD         --> EVEN_OR_ODD                             %
%        NUM_MULT_EVEN           --> MULT_EVEN                               %
%        NUM_MULT_ODD            --> MULT_ODD                                %
%        NUM_NOT_EVEN_AND_ODD    --> EVEN_AND_ODD                            %
%        NUM_NOT_EVEN_NOT_ODD    --> EVEN_ODD / ODD_EVEN                     %
%                                 (conjunct split and GSYM'd)                %
%        NUM_NOT_EVEN_ODD_SUC_EVEN_ODD  --> NOT_EVEN_ODD_SUC_EVEN_ODD        %
%        NUM_ODD_MULT                   --> ODD_IMPL_MULT                    %
%        ODD_NUM                        --> ODD_EXISTS                       %
%									     %
%****************************************************************************%
%                                                                            %
% PC 21/4/93                                                                 %
%     Removed dependencies on several external files/theories                %
%                                                                            %
%****************************************************************************%
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%  DEPENDANCIES :                                                            %
%                                                                            %
%                                                                            %
%****************************************************************************%

system `rm -f odd_even.th`;;

new_theory `odd_even`;;

%<--------------------------------------------------------------------------->%
let EVEN_ODD_0 = prove_thm (
 `EVEN_ODD_0`,
  "(EVEN 0) /\ ~(ODD 0)",
   REWRITE_TAC [ODD;EVEN]
);;

%<--------------------------------------------------------------------------->%

%
|- !n. (~EVEN(SUC n) = EVEN n) /\ (~ODD(SUC n) = ODD n)
%


let NOT_EVEN_ODD_SUC_EVEN_ODD = prove_thm (
 `NOT_EVEN_ODD_SUC_EVEN_ODD`,
  "!n. (~EVEN(SUC n) = EVEN n) /\ (~ODD(SUC n) = ODD n)",
   REWRITE_TAC [ODD;EVEN]
);;

%<--------------------------------------------------------------------------->%

let EVEN_ODD_SUC = prove_thm (
 `EVEN_ODD_SUC`,
  "!n. (EVEN(SUC n) = ODD n) /\ (ODD(SUC n) = EVEN n)",
   REWRITE_TAC [ODD;EVEN;GSYM ODD_EVEN;GSYM EVEN_ODD]
);;

%<--------------------------------------------------------------------------->%

let EVEN_ODD_PLUS_CASES = prove_thm (
  `EVEN_ODD_PLUS_CASES`,
  "!n m . (((ODD n) /\ (ODD m)) ==> (EVEN (n + m))) /\
          (((ODD n) /\ (EVEN m)) ==> (ODD (n + m))) /\
          (((EVEN n) /\ (EVEN m)) ==> (EVEN (n + m)))",
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [EVEN_ADD;ODD_ADD] THEN
  ASM_REWRITE_TAC [GSYM EVEN_ODD] THEN
  ASM_REWRITE_TAC [EVEN_ODD]
);;

%<--------------------------------------------------------------------------->%

let EVEN_IMPL_MULT = prove_thm (
  `EVEN_IMPL_MULT`,
  "! n m . (EVEN n) \/ (EVEN m) ==> (EVEN (n * m))",
  REWRITE_TAC [EVEN_MULT]
);;

%<--------------------------------------------------------------------------->%

let ODD_IMPL_MULT = prove_thm (
  `ODD_IMPL_MULT`,
  "! n m . (ODD n) /\ (ODD m) ==> (ODD (n * m))",
  REWRITE_TAC [ODD_MULT]
);;

%<--------------------------------------------------------------------------->%

%
MULT_ODD = |- !n m. ODD(n * m) ==> ODD n /\ ODD m 
%


let MULT_ODD = prove_thm (
   `MULT_ODD`,
   "!n m. ODD(n * m) ==> ODD n /\ ODD m",
    REWRITE_TAC [ODD_MULT]);;

%<--------------------------------------------------------------------------->%

%
MULT_EVEN = 
|- !n m. EVEN(n * m) ==> EVEN n \/ EVEN m
%

let MULT_EVEN = prove_thm (
   `MULT_EVEN`,
   "!n m. EVEN(n * m) ==> EVEN n \/ EVEN m",
    REWRITE_TAC [EVEN_MULT]);;

close_theory();;
