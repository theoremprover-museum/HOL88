%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         minmax.ml                                                  %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         June 1991                                                  %
%   DESCRIPTION:  Maximum and Minimum                                        %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is part of the more_arithmetic theory in the bags library by   %
%     Philippe Leveilley						     %
%   Conversion to HOL12 and editing was done by 			     %
%     Wim Ploegaerts						             %
%                                                                            %
%****************************************************************************%
%                                                                            %
% PC 21/4/93                                                                 %
%     Removed dependencies on several external files/theories                %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

system `rm -f min_max.th`;;

new_theory `min_max`;;

% PC 22-4-92 No longer used%
%loadf `tools`;;%

%============================================================================%
%									     %
% 			      MIN AND MAX by PL				     %
%									     %
%============================================================================%



let MAX_DEF = new_definition
    (`MAX_DEF`,
     "MAX n p = ((n <= p) => p | n)"
);;

let MAX_0 = prove_thm
    (`MAX_0`,
     "!n. MAX 0 n = n",
     REWRITE_TAC [MAX_DEF; ZERO_LESS_EQ]
);;
 

let MAX_SYM = prove_thm
    (`MAX_SYM`,
     "!n p. MAX n p = MAX p n",
     REPEAT GEN_TAC THEN
     ASM_CASES_TAC "n:num=p" THENL
     [ % n = p %
         ASM_REWRITE_TAC []
     ; % ~ n = p %
         REWRITE_TAC [MAX_DEF] THEN
         ASM_CASES_TAC "n <= p" THEN
         ASM_REWRITE_TAC [LESS_OR_EQ] THEN
         POP_ASSUM_LIST (\ [T1;T2].
            REWRITE_TAC [GSYM T2; REWRITE_RULE [GSYM NOT_LESS] T1])
     ]
);;

let MAX_REFL = prove_thm
    (`MAX_REFL`,
     "!n. MAX n n = n",
     REWRITE_TAC [MAX_DEF; LESS_OR_EQ]
);;

let MAX_SUC = prove_thm
    (`MAX_SUC`,
     "!n. MAX n (SUC n) = SUC n",
     REWRITE_TAC [MAX_DEF; LESS_EQ_SUC_REFL]
);;

let SUC_MAX = prove_thm
    (`SUC_MAX`,
     "!n p. MAX (SUC n) (SUC p) = SUC (MAX n p)",
     REPEAT GEN_TAC THEN
     REWRITE_TAC [MAX_DEF; LESS_EQ_MONO] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[]
);;

let MIN_DEF = new_definition
    (`MIN_DEF`,
     "MIN n p = ((n <= p) => n | p)"
);;

let MIN_0 = prove_thm
    (`MIN_0`,
     "!n. MIN 0 n = 0",
     REWRITE_TAC [MIN_DEF; ZERO_LESS_EQ]
);;

let MIN_SYM = prove_thm
    (`MIN_SYM`,
     "!n p. MIN n p = MIN p n",
     REPEAT GEN_TAC THEN
     ASM_CASES_TAC "n:num=p" THENL
     [ % n = p %
         ASM_REWRITE_TAC []
     ; % ~ n = p %
         REWRITE_TAC [MIN_DEF] THEN
         ASM_CASES_TAC "n <= p" THEN
         ASM_REWRITE_TAC [LESS_OR_EQ] THEN
         POP_ASSUM_LIST (\ [T1;T2].
            REWRITE_TAC [GSYM T2; REWRITE_RULE [GSYM NOT_LESS] T1])
     ]
);;

let MIN_REFL = prove_thm
    (`MIN_REFL`,
     "!n. MIN n n = n",
     REWRITE_TAC [MIN_DEF; LESS_OR_EQ]
);;

let MIN_SUC = prove_thm
    (`MIN_SUC`,
     "!n. MIN n (SUC n) = n",
     REWRITE_TAC [MIN_DEF; LESS_EQ_SUC_REFL]
);;


let SUC_MIN = prove_thm
    (`SUC_MIN`,
     "!n p. MIN (SUC n) (SUC p) = SUC (MIN n p)",
     REPEAT GEN_TAC THEN
     REWRITE_TAC [MIN_DEF; LESS_EQ_MONO] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[]
);;

close_theory();;
