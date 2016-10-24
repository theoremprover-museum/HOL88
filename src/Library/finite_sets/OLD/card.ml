%<_____________________________________________________________________
|                                                                      |
|                       TACTICS                                        |
%_____________________________________________________________________>%


%<   to change the goal "P==>Q" into "~Q==>~P"    >%

% --------------------------------------------------------------------- %
% revised, to remove dependency on taut library.	[TFM 91.01.24]	%
% load_library `taut`;;							%
% let CONTRAP_THM = TAUT_RULE "(P==>Q)=(~Q==>~P)";;			%
% let CONTRAP_TAC = ONCE_REWRITE_TAC[CONTRAP_THM];;			%
% --------------------------------------------------------------------- %

let CONTRAP_TAC = CONV_TAC (ONCE_DEPTH_CONV CONTRAPOS_CONV);;

%< ---------------------------------------------------------------------

   "( t => t1 | t2)"
   =====================
  {~t} "t2"     {t} "t1"  

DELETED: built-in COND_CASES_TAC now does this. [TFM 90.05.14]		

let COND_CASES_2_TAC = 
  COND_CASES_TAC 
  THENL
  [%< T >% POP_ASSUM (ASSUME_TAC o EQT_ELIM);
   %< F >% POP_ASSUM (ASSUME_TAC o NOT_INTRO o fst o EQ_IMP_RULE)]
;; 

--------------------------------------------------------------------- >%


%<______________________________________________________________________
|                                                                       |
|           giving a definition for cardinality                         |
|______________________________________________________________________>% 

let HAS_CARD = new_prim_rec_definition
    (`HAS_CARD`,
     "(HAS_CARD (s:(*)set) 0 = (s=EMPTY)) /\
      (HAS_CARD (s:(*)set) (SUC n) = 
                       (?x. x IN s /\ HAS_CARD (s DELETE x) n))");;

let CARD_DEF = new_definition
    (`CARD_DEF`,
     "CARD (s:(*)set) = (@n. HAS_CARD s n)");;

%<______________________________________________________________________
|                                                                       |
|                         useful lemmas                                 |
|______________________________________________________________________>%

let SELECT_0 = save_thm
    (`SELECT_0`,
     SELECT_RULE (EXISTS ("?n. n=0","0") (REFL "0")));;

%< it is the DELETE_ABSORPTION theorem 
   where (s DELETE x) and s have been swapped >%

let DELETE_ABS = prove_thm
   (`DELETE_ABS`,
    "!(x:*) s. ~(x IN s) ==> (s DELETE x = s)",
     REPEAT STRIP_TAC
     THEN REWRITE_TAC [SET_EQ; DELETE_MEMBER]
     THEN GEN_TAC
     THEN ASM_CASES_TAC "x':*=x"
     THEN ASM_REWRITE_TAC []);;


let MEMBER_IMP_NONEMPTY = prove_thm
    (`MEMBER_IMP_NONEMPTY`,
     "!(x:*) s. x IN s ==> ~(s = EMPTY)",
     REPEAT GEN_TAC
     THEN CONTRAP_TAC
     THEN REWRITE_TAC []
     THEN DISCH_TAC
     THEN ASM_REWRITE_TAC [IN]);;

let IN_DEL_IMP = save_thm
     (`IN_DEL_IMP`,
      GEN "y:*" (GEN "x:*" (snd (EQ_IMP_RULE (SPEC_ALL DELETE_MEMBER)))));;

let lemme3 = prove_thm
    (`lemme3`,
     "!(x:*) x' s. (x IN s /\ x' IN s) ==>
             (s DELETE x = EMPTY) ==> (s DELETE x' = EMPTY)",
     REPEAT GEN_TAC
     THEN STRIP_TAC
     THEN ASM_CASES_TAC "x':*=x"
     THENL [
       %< x'=x >%  ASM_REWRITE_TAC [];
       %< ~x'=x >%
           IMP_RES_TAC IN_DEL_IMP
           THEN IMP_RES_TAC MEMBER_IMP_NONEMPTY
           THEN ASM_REWRITE_TAC[]
     ]);;

let IN_INSERT= prove_thm
     (`IN_INSERT`,
      "!(x:*) s. x IN s ==>(!y. x IN (INSERT y s))",
      REPEAT STRIP_TAC 
      THEN ASM_REWRITE_TAC [IN]);;

let NOT_IN_SAME_SET= prove_thm
     (`NOT_IN_SAME_SET`,
      "!(x:*) y s. y IN s /\ ~x IN s ==> ~(x=y)",
      REPEAT GEN_TAC
      THEN ASM_CASES_TAC "(x:*)=y"
      THEN ASM_REWRITE_TAC[NOT_AND]);;

let lemme3a= prove_thm 
   (`lemme3a`,
    "!(x:*) x' s.
    x IN s /\ x' IN s ==> (s DELETE x' = EMPTY) ==> (s DELETE x = EMPTY)",
   ONCE_REWRITE_TAC[CONJ_SYM]
   THEN REWRITE_TAC[lemme3]);;

let NOT_SYM = prove_thm 
    (`NOT_SYM`,
      "!(x:*) y. ~(x=y) ==> ~(y=x)",
      REPEAT GEN_TAC
      THEN CONTRAP_TAC 
      THEN REWRITE_TAC [EQ_SYM]);;
   
let DEL_DEL = prove_thm
    (`DEL_DEL`,
     "!(x:*) x' s. (s DELETE x) DELETE x' = (s DELETE x') DELETE x ",
     REPEAT GEN_TAC
     THEN REWRITE_TAC [SET_EQ; DELETE_MEMBER]
     THEN GEN_TAC
     THEN EQ_TAC
     THEN STRIP_TAC
     THEN ASM_REWRITE_TAC[]
);;

let DISTINCT_SET = prove_thm
     (`DISTINCT_SET`,
      "!(x:*) s. ~(INSERT x s = EMPTY)",
      REPEAT GEN_TAC
      THEN ASSUME_TAC (SPEC_ALL SET_DISTINCT)
      THEN IMP_RES_TAC NOT_SYM);;





%<______________________________________________________________________
|                                                                       |
|          induction lemma for HAS_CARD definition                      |
|______________________________________________________________________>%

%<=================
 <  base step
 <=================>%

let CARD_EMPTY_lem = prove_thm
    (`CARD_EMPTY_lem`,
      "!n. HAS_CARD (EMPTY:(*)set) n = (n=0)",
      INDUCT_TAC
      THEN REWRITE_TAC [HAS_CARD;NOT_SUC;IN]);;


%<=================
   induction step
 <=================>%

%< we first prove that, when you remove an
 < element from a set, you decrease its
 < cardinal by one >%
     
let CARD_DEL = prove_thm
    (`CARD_DEL`,
     "!n (x:*) s.
      (x IN s /\ HAS_CARD s(SUC n) ==> HAS_CARD(s DELETE x)n) /\
      (x IN s /\ HAS_CARD(s DELETE x)n ==> HAS_CARD s(SUC n))",
     INDUCT_TAC
     THENL
     [ %<   base step >%
       REWRITE_TAC [HAS_CARD]
       THEN REPEAT STRIP_TAC
       THENL
           [IMP_RES_TAC lemme3a;
            EXISTS_TAC "x:*" 
                THEN ASM_REWRITE_TAC[] ];
      %<  inductive step  >%
        REWRITE_TAC [SPECL ["(s:(*)set)"; "SUC n"] (CONJUNCT2 HAS_CARD)]
        THEN REPEAT STRIP_TAC
        THEN POP_ASSUM MP_TAC
        THENL
        [ %< subgoal 1 >%
           ASM_CASES_TAC "x:*=x'"
           THENL
           [ %< x=x' >%
             ASM_REWRITE_TAC[];
            %< ~x=x' >%
             IMP_RES_TAC NOT_SYM
             THEN IMP_RES_TAC IN_DEL_IMP
             THEN DISCH_TAC
             THEN RES_TAC
             THEN REWRITE_TAC [HAS_CARD]
             THEN EXISTS_TAC "x':*"
             THEN ONCE_REWRITE_TAC [DEL_DEL]
             THEN ASM_REWRITE_TAC []
            ];
        %< subgoal 2 >%
             DISCH_TAC
             THEN EXISTS_TAC "x:*"
             THEN ASM_REWRITE_TAC[]
        ]
]
);;

%< rewriting the theorem above by  
   changing the double implication into an equivalence >%

let CARD_DEL_THM = prove_thm
     (`CARD_DEL_THM`,
      "!(x:*) s n. (x IN s) ==>
      (HAS_CARD s (SUC n) = HAS_CARD (s DELETE x) n)",
      REPEAT STRIP_TAC 
     THEN EQ_TAC
     THEN DISCH_TAC
     THEN (IMP_RES_TAC CARD_DEL)
     THEN ASM_REWRITE_TAC []);;
      

%< then follows the induction theorem for HAS_CARD >% 

let HAS_CARD_INDUCT= prove_thm
      (`HAS_CARD_INDUCT`,
       "!s (x:*). 
           ~x IN s ==> (!n. HAS_CARD (INSERT x s) (SUC n) = HAS_CARD s n)",
         REPEAT STRIP_TAC
         THEN ASSUME_TAC (SPEC_ALL COMPONENT)
         THEN IMP_RES_TAC CARD_DEL_THM
         THEN IMP_RES_TAC DELETE_ABS
         THEN ASM_REWRITE_TAC [DELETE]);;


%<______________________________________________________________________
|                                                                       |
|           the induction theorem for CARD definition                   |
|______________________________________________________________________>%

%< to prove that (CARD: s-> CARD s ) is a function, 
   we need to prove that there exists a unique n such 
   as (HAS_CARD s n) for a given set s           >%

%<  unique  >%

let UNIQUE_CARD = prove_thm
    (`UNIQUE_CARD`,
     "!(s:(*)set) n p. HAS_CARD s n ==> HAS_CARD s p ==> (n=p)",
     SET_INDUCT_2_TAC
     THEN REPEAT INDUCT_TAC
     THEN IMP_RES_TAC HAS_CARD_INDUCT  
     THEN ASM_REWRITE_TAC[CARD_EMPTY_lem; NOT_SUC; CONJUNCT1 HAS_CARD;
                          DISTINCT_SET; INV_SUC_EQ]
);;

%< exists >%

let CARD_EX = prove_thm
    (`CARD_EX`,
     "!s:(*)set. ?n. HAS_CARD s n",
     SET_INDUCT_2_TAC THENL
     [ %< base >%
          EXISTS_TAC "0"
          THEN REWRITE_TAC [HAS_CARD];
       %< induction step >%
          ASSUME_TAC (SELECT_RULE (ASSUME "?n. HAS_CARD (s:(*)set) n"))
          THEN EXISTS_TAC "SUC (@n. HAS_CARD (s:(*)set) n)"
          THEN REWRITE_TAC [HAS_CARD]
          THEN EXISTS_TAC "x:*"
          THEN ASM_REWRITE_TAC[DELETE;IN]
          THEN ASSUME_TAC DELETE_ABS 
          THEN RES_TAC
          THEN ASM_REWRITE_TAC[]
       ]
);;


%<=================
 <  base step
 <=================>%

let CARD_EMPTY = prove_thm
    (`CARD_EMPTY`,
     "CARD (EMPTY:(*)set) = 0",
     REWRITE_TAC [ CARD_DEF ; CARD_EMPTY_lem ; SELECT_0 ]);;

let EMPTY_0_EQ = prove_thm
    (`EMPTY_0_EQ`,
     "!s:(*)set. (CARD s = 0) = (s = EMPTY)",
     GEN_TAC
     THEN EQ_TAC THENL
     [ %<  ==>  >%
             REWRITE_TAC [ CARD_DEF ]
             THEN DISCH_TAC
             THEN ASSUME_TAC (SELECT_RULE (SPEC_ALL CARD_EX))
             THEN UNDISCH_TAC "HAS_CARD (s:(*)set)(@n. HAS_CARD s n)"
             THEN ASM_REWRITE_TAC [ HAS_CARD ];
        %<  <==  >%
             DISCH_TAC 
             THEN ASM_REWRITE_TAC [CARD_EMPTY]
        ]
);;


%<=================
   induction step
 <=================>%

%< when rewriting CARD_INDUCT_THM with the definition of HAS_CARD
   we will find "(@n. HAS_CARD (INSERT x s) n)=SUC ...". Therefore
   we need to prove that such an n is the SUC of something...       >%

%< ... first, n is not 0... >%

let INSERT_CARD = prove_thm
    (`INSERT_CARD`,
     "!(x:*) s n. HAS_CARD (INSERT x s) n ==> ~(n=0)",
     REPEAT GEN_TAC
     THEN ASM_CASES_TAC "n=0"
     THEN ASM_REWRITE_TAC[HAS_CARD;DISTINCT_SET;NOT_SUC]);;

%< ... hence there exists an n' such as (HAS_CARD s (SUC n')) 
   Thus, our n will be (SUC n')                             >%
  
let EX_SUC_CARD = prove_thm
    (`EX_SUC_CARD`,
     "!(x:*) s. ?n. HAS_CARD(INSERT x s)(SUC n)",
     REPEAT GEN_TAC
     THEN ASSUME_TAC (SELECT_RULE (SPEC "INSERT (x:*) s" CARD_EX))
     THEN IMP_RES_TAC INSERT_CARD
     THEN DISJ_CASES_TAC (SPEC "@n. HAS_CARD (INSERT (x:*) s) n" num_CASES)
     THENL [RES_TAC
            ;EXISTS_TAC "@n. (@n'. HAS_CARD (INSERT (x:*) s) n') = SUC n"
            THEN POP_ASSUM 
             (\t. ASM_REWRITE_TAC [SYM (SELECT_RULE t)])
            ]
);;

%< all the work is done, we just have to rewrite and
 < use the existence theorem through SELECT_RULE
 < Then we will have something like 
 <       "HAS_CARD s n = HAS_CARD s n'" 
 < which is solved by the uniqueness theorem           >%

% Proof rewritten for HOL version 1.12 		[TFM 91.01.23]	%

let CARD_INDUCT_THM = prove_thm
    (`CARD_INDUCT_THM`,
     "!(x:*) s. ~x IN s ==> (CARD (INSERT x s) = SUC (CARD s))",
     REPEAT STRIP_TAC
     THEN REWRITE_TAC[CARD_DEF] THEN
     IMP_RES_TAC HAS_CARD_INDUCT THEN
     FIRST_ASSUM (\th g. REWRITE_TAC [SYM(SPEC_ALL th)] g) 
     THEN ASSUME_TAC (SELECT_RULE (SPEC "INSERT (x:*) s" CARD_EX))
     THEN ASSUME_TAC (SELECT_RULE (SPEC_ALL EX_SUC_CARD))
     THEN IMP_RES_TAC UNIQUE_CARD
);;

%< as (INSERT x s = s) if x IN s we have Phil Windley's axiom with
   CARD_EMPTY and CARD_INDUCT_THM  >%

let CARD = prove_thm
   (`CARD`,
    "(CARD (EMPTY:(*)set) = 0) /\
     (!(x:*) s. CARD (INSERT x s) = (x IN s => CARD s | SUC (CARD s)))",
     REPEAT STRIP_TAC
     THENL 
     [%< first conjuction term >% REWRITE_TAC[CARD_EMPTY];
      %< second one >%
      COND_CASES_TAC
      THENL
        [%< x IN s >%
          IMP_RES_TAC ABSORPTION
          THEN  ASM_REWRITE_TAC[];
         %< ~ x IN s >%
          IMP_RES_TAC CARD_INDUCT_THM
         ]
      ]
);;


