
%______________________________________________________________________

file: more_arithmetic.ml

some more arithmetic theorems used in bags theory

author: Philippe Leveilley
June 1989

creates the theory `more_arithmetic`
which is needed to derive the therory `bags`
______________________________________________________________________%

% system `rm more_arithmetic.th`;; %

new_theory `more_arithmetic`;;

let SYM_RULE = 
    CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) 
    ? failwith `SYM_RULE`;;

% added RES_TAC to run with  hol12 - sk 91.01.25 %
let SUC_PRE = prove_thm
    (`SUC_PRE`,
     "!n. ~(n = 0) ==> (SUC (PRE n) = n)",
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (SPEC "PRE n" NOT_SUC) THEN
      IMP_RES_THEN (ASSUME_TAC o REWRITE_RULE [ADD_CLAUSES])
                   (SPEC "0" LESS_ADD_NONZERO) THEN
      IMP_RES_THEN (ASSUME_TAC o SYM_RULE) INV_PRE_EQ THEN
      RES_TAC THEN
      ASM_REWRITE_TAC [PRE]
  );;

let LESS_EQ_SUC_SUC = prove_thm
    (`LESS_EQ_SUC_SUC`,
     "!m n. SUC m <= SUC n = m <= n",
     REWRITE_TAC[LESS_OR_EQ; INV_SUC_EQ; LESS_MONO_EQ]
);;

let LESS_EQ_0 = prove_thm
   (`LESS_EQ_0`,
    "!n. 0 <= n",
    REWRITE_TAC [LESS_OR_EQ] THEN
    ONCE_REWRITE_TAC [DISJ_SYM] THEN
    REWRITE_TAC [LESS_0_CASES]
);;

let MAX_DEF = new_definition
    (`MAX_DEF`,
     "MAX n p = ((n <= p) => p | n)"
);;

let MAX_0 = prove_thm
    (`MAX_0`,
     "!n. MAX 0 n = n",
     REWRITE_TAC [MAX_DEF; LESS_EQ_0]
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
            REWRITE_TAC [SYM_RULE T2; REWRITE_RULE [SYM_RULE NOT_LESS] T1])
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
     REWRITE_TAC [MAX_DEF; LESS_EQ_SUC_SUC] THEN
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
     REWRITE_TAC [MIN_DEF; LESS_EQ_0]
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
            REWRITE_TAC [SYM_RULE T2; REWRITE_RULE [SYM_RULE NOT_LESS] T1])
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
     REWRITE_TAC [MIN_DEF; LESS_EQ_SUC_SUC] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[]
);;


quit();; % Needed for Common Lisp %
