%<
AUTHOR:	Ton Kalker

DATE: 	23 june 1989

COMMENT: theory of cardinals, showing the use
         of quotient constructs.

>%

new_theory `card`;; 
                   
%<We need `set` as a basis for `card`>%  

load_library `auxiliary`;;  

autoload_defs_and_thms `bool`;;

load_library `pred_sets`;;

load_library `taut`;; 

load_library `fixpoints`;;

load_library `quotient`;;

loadt`quotientfns`;;

load_library `well_order`;;

new_special_symbol `<<<`;;       

%<*************DEFINITIONS*********************************>%

let EQUI_POTENT = 
    new_definition
    (`EQUI_POTENT`,
      "EQUI_POTENT (A:*->bool) (B:*->bool) = ?f.(A <--> B) f");; 

let SLEQ = 
    new_infix_definition
    (`SLEQ`, 
     "SLEQ A (B:*->bool) = (?f.((A >--> B) f))");;  

%<*****************THEOREMS**************************************>%

let w1 = "REFLEX (EQUI_POTENT:(*->bool)->(*->bool)->bool)";;

let thm1 = 
   prove
    (w1,
    REWRITE_TAC [REFLEX] THEN
    BETA_TAC THEN 
    REWRITE_TAC[EQUI_POTENT] THEN
    GEN_TAC THEN
    EXISTS_TAC "I:*->*" THEN
    REWRITE_TAC[FUN_IDEN]);;   

let w2 = "SYMMETRY (EQUI_POTENT:(*->bool)->(*->bool)->bool)";;  

let thm2 = 
   prove
    (w2,
    REWRITE_TAC [SYMMETRY] THEN
    BETA_TAC THEN 
    REWRITE_TAC[EQUI_POTENT] THEN
    REPEAT GEN_TAC THEN
    EQ_TAC THEN 
    REPEAT STRIP_TAC THENL
    [EXISTS_TAC "FINV x y (f:*->*)";EXISTS_TAC "FINV y x (f:*->*)"] THEN
    IMP_RES_TAC ISO_FINV);;


let w3 = "TRANSITIVITY (EQUI_POTENT:(*->bool)->(*->bool)->bool)";;   

let thm3 = 
   prove
    (w3,
    REWRITE_TAC [TRANSITIVITY] THEN
    BETA_TAC THEN 
    REWRITE_TAC[EQUI_POTENT] THEN 
    REPEAT STRIP_TAC THEN
    EXISTS_TAC "(f':*->*) o (f:*->*)" THEN
    IMP_RES_TAC FUN_COMP);; 

let w = "EQUIVALENCE (EQUI_POTENT:(*->bool)->(*->bool)->bool)";; 

let EQUIVALENCE_CARD =
    save_thm
    (`EQUIVALENCE_CARD`,
     TAC_PROOF(
     ([],w),
     REWRITE_TAC[EQUIVALENCE] THEN
     BETA_TAC THEN
     REWRITE_TAC[thm1;thm2;thm3]));; 


let [thm_onto;thm_univ;thm_factor] = 
    define_quotient_type(`card`,EQUIVALENCE_CARD);;


%< Tactic that rewrites to conditions for defining
   factorization >%

let CARD_FACTOR_TAC = FACTOR_TAC [thm_onto] [thm_univ];;  

let CARD_LIFT_CONV = BASE_CHANGE_CONV thm_onto;;

let CARD_QUOTIENT_TAC =
     CONV_TAC (BASE_CHANGE_CONV thm_onto) THEN
     GEN_TAC;;
  


%<*************Defining canonical ordering**************************>%

let w = "?!L:(*)card#(*)card->bool.(UNCURRY $SLEQ) = L o (PROJ_card P PROJ_card)";;

let LEMMA1 = 
    prove(w,                        %<Here we use FACTOR_TAC>%
     CARD_FACTOR_TAC THEN
     REWRITE_TAC[UNCURRY_DEF;EQUI_POTENT;SLEQ] THEN 
     REPEAT STRIP_TAC THEN EQ_TAC THEN 
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC ISO_FINV THENL
     [SUB_ASSUM_TAC[1;3;4];SUB_ASSUM_TAC[2;3;5]] THEN
     FILTER_RULE_ASSUM_TAC[1;3] (CONJUNCT1 o (REWRITE_RULE[FUN_ISO])) THEN
     (2 TIMES (IMP_RES_TAC FUN_COMP)) THEN
     FILTER_ASSUM_TAC [1] (\tm.EXISTS_TAC (rand tm)) THEN
     ASM_REWRITE_TAC[]);; 

let LEMMA2 = 
    let th1 = (CONV_RULE (BINDER_CONV (SYM_CONV THENC FUN_EQ_CONV))) LEMMA1 in
    let th2 = (CONV_RULE (BINDER_CONV PROD_CONV)) th1 in
    let th3 = REWRITE_RULE[UNCURRY_DEF;o_DEF;P] th2 in
    let th4 = BETA_RULE th3 in
    let th5 = (CONV_RULE (BASE_CHANGE_CONV (fst(CONJ_PAIR CURRY_ISO)))) th4 in
    REWRITE_RULE[UNCURRY_DEF] th5;;

%<We define the ordering on the cardinals>% 

let [CLEQ;CLEQ_UNIQUE] = new_unique_specification `CLEQ` [`infix`,`<<<`] LEMMA2;;  

%<****************************THEOREMS******************************>% 

let w = "!a:(*)card.a <<< a";; 

let CLEQ_REFLEX =
    prove_thm(
    `CLEQ_REFLEX`,
     w,
     CARD_QUOTIENT_TAC THEN
     REWRITE_TAC[CLEQ;SLEQ] THEN
     EXISTS_TAC "I:*->*" THEN
     REWRITE_TAC[FUN_IDEN]);;   

let w = "!a b c:(*)card.((a <<< b) /\ (b <<< c)) ==> (a <<< c)";;

let CLEQ_TRANSITIVITY =
    prove_thm(
    `CLEQ_TRANSITIVITY`,
     w,
     (3 TIMES CARD_QUOTIENT_TAC) THEN
     REWRITE_TAC[CLEQ;SLEQ] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC FUN_COMP THEN
     FILTER_ASSUM_TAC [1] (\tm.EXISTS_TAC (rand tm)) THEN
     ASM_REWRITE_TAC[]);;


%<A preliminary for proving `<<<` to be a partial order:
  Note the use of the DEFINE tactic>% 

let w = "!A (B:*->bool).!f.
          (( B SUBSET A) /\ ((A >--> B) f))  
           ==>
          (?g.((A <--> B) g))";;
                
                                           
let SCHROEDER_BERNSTEIN_TAC =

REPEAT STRIP_TAC THEN 

%<First the basic definitions>%

DEFINE "D:*->bool = A DELETE B" THEN                           
DEFINE "fixfun = \V:*->bool. D UNION (IMAGE f V)" THEN 

%<Prove "fixfun" continuous>%
          
LEMMA_PROOF "CONTINUOUS (fixfun:(*->bool)->(*->bool))"             
           [SUB_ASSUM_TAC [1];                                   
            ASM_REWRITE_TAC[CONTINUOUS;CHAIN;LUB;UNION;IMAGE];
            SUB_ASSUM_TAC [];
            BETA_TAC THEN BETA_TAC;
            REPEAT STRIP_TAC;
            CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN STRIP_TAC;
            EQ_TAC THEN REPEAT STRIP_TAC THENL
                        [ASM_REWRITE_TAC[];
                         EXISTS_TAC "n:num" THEN
                         DISJ2_TAC THEN
                         EXISTS_TAC "b:*" THEN
                         ASM_REWRITE_TAC[];
                         ASM_REWRITE_TAC[];
                         DISJ2_TAC THEN
                         EXISTS_TAC "b:*" THEN
                         ASM_REWRITE_TAC[] THEN
                         EXISTS_TAC "n:num" THEN
                         ASM_REWRITE_TAC[]]
           ]   THEN  

%<Let E be the least fixpoint of fixfun>% 

DEFINE "E:*->bool = FIX fixfun" THEN                              

%<And check it's indeed a fixpoint>%

LEMMA_PROOF "fixfun (E:*->bool) = E"
            [SUB_ASSUM_TAC[1;2];
             IMP_RES_TAC FIX_THM;
             ASM_REWRITE_TAC[]] THEN 

%<Formulate a property>%

DEFINE "inA = \V:*->bool. V SUBSET A" THEN 

%<and check that E satisfies this property>%

LEMMA_PROOF "(inA:(*->bool)->bool) E"   
           [ASSUM_LIST (REWRITE_TAC o (sublist [3]));
            MATCH_MP_TAC SCOTT_INDUCTION_THM; 
            FILTER_ASSUM_TAC [7;8] UNDISCH_TAC;
            ASM_REWRITE_TAC
              [ADMITS_INDUCTION;FUN_ONE_ONE;SUBSET;BOT;UNION;DELETE;IMAGE;CHAIN;LUB];
            2 TIMES BETA_TAC;
            SUB_ASSUM_TAC []; 
            REWRITE_TAC[];
            REPEAT STRIP_TAC THENL
                 [RES_TAC; 
                  RES_TAC THEN
                  ASM_REWRITE_TAC[]]] THEN

%<Rewrite with definitions of fixfun and inA>%

REWRITE_RULE_ASSUM_TAC [3] [6;7] THEN
REWRITE_RULE_ASSUM_TAC [1] [2] THEN 

%<and remove these definitions>%

SUB_ASSUM_TAC [1;3;8;9] THEN
RULE_ASSUM_TAC BETA_RULE THEN 

%<Property of E: E closed under f>%

LEMMA_PROOF  "!x:*.(E x) ==> (E (f x))" 
             [SUB_ASSUM_TAC [2];
              REPEAT STRIP_TAC;
              FILTER_RULE_ASSUM_TAC [2]  (REWRITE_RULE [DELETE;UNION;IMAGE]);
              FILTER_RULE_ASSUM_TAC [2] (CONV_RULE FUN_EQ_CONV);
              RULE_ASSUM_TAC BETA_RULE;
              FILTER_RULE_ASSUM_TAC [2] (SPEC "(f:*->*) x:*");
              FILTER_RULE_ASSUM_TAC [2] SYM;
              ASM_REWRITE_TAC[];
              DISJ2_TAC;
              EXISTS_TAC "x:*";
              ASM_REWRITE_TAC[]] THEN  

%<Property of E: E contains D>%

LEMMA_PROOF "!x:*. ((A x) /\ ~(E x)) ==> (B x)"     
             [SUB_ASSUM_TAC[3];
              REPEAT STRIP_TAC;
              FILTER_RULE_ASSUM_TAC [3]  (REWRITE_RULE [DELETE;UNION;IMAGE]);
              FILTER_RULE_ASSUM_TAC [3] (CONV_RULE FUN_EQ_CONV);
              RULE_ASSUM_TAC BETA_RULE;
              FILTER_RULE_ASSUM_TAC [3] (SPEC "x:*");
              FILTER_RULE_ASSUM_TAC [3] SYM;
              REWRITE_RULE_ASSUM_TAC [1] [3;2];
              ASM_CASES_TAC "B (x:*):bool";
              FILTER_ASSUM_TAC [2] UNDISCH_TAC;
              ASM_REWRITE_TAC[]]   THEN  

%<Property of E: there are enough preimages in E>%
                                              
LEMMA_PROOF "!x:*.((E x) /\ (B x)) ==> (?b.(E b) /\ (x = (f b)))"  
             [SUB_ASSUM_TAC[4];
              REPEAT STRIP_TAC;
              FILTER_RULE_ASSUM_TAC [3]  (REWRITE_RULE [DELETE;UNION;IMAGE]);
              FILTER_RULE_ASSUM_TAC [3] (CONV_RULE FUN_EQ_CONV);
              RULE_ASSUM_TAC BETA_RULE; 
              FILTER_RULE_ASSUM_TAC [3] (SPEC "x:*");
              REWRITE_RULE_ASSUM_TAC [3] [1;2];
              ASM_REWRITE_TAC[]] THEN 

%<Define the candidate function g,
  set the task of verifying that g
  has the right properties, and
  rewrite with the definitions of
  the theory set>%

DEFINE "g:*->* = \x.(E x) => (f x) | x" THEN
EXISTS_TAC "g:*->*" THEN   
FILTER_ASSUM_TAC [5;7;8] UNDISCH_TAC  THEN
ASM_REWRITE_TAC [SUBSET;UNION;FUN_ISO;FUN_ONE_ONE;FUN_ONTO] THEN
BETA_TAC  THEN
BETA_TAC THEN
SUB_ASSUM_TAC [2;3;4] THEN  
REPEAT STRIP_TAC THENL  

%<Prove that g(A) contained in B,
  from injection part  >% 
  
          [ASM_CASES_TAC "E (x:*):bool" THEN
           RES_TAC THEN 
           ASM_REWRITE_TAC[];

%<Prove g is injective: split into 4 cases:
  x,y in/(not in) E >%

            MAP_EVERY ASM_CASES_TAC ["E (x:*):bool";"E (y:*):bool"] THEN
            REWRITE_RULE_ASSUM_TAC [3] [1;2]  THENL   

%<Both in E>%

                       [RES_TAC; 
 
%<Only 1 in E: uses closure property of E>%

                        SUB_ASSUM_TAC [1;2;3;12] THEN
                        RES_TAC THEN
                        FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN 
                        ASM_REWRITE_TAC[];
                        SUB_ASSUM_TAC [1;2;3;12] THEN
                        RES_TAC THEN
                        FILTER_ASSUM_TAC [3] UNDISCH_TAC THEN 
                        ASM_REWRITE_TAC[];

%<Both not in E>%
   
                        ASM_REWRITE_TAC[]]; 

%<Prove that g(A) contained in B,
  from surjection part  >% 
  
           ASM_CASES_TAC "E (x:*):bool" THEN
           RES_TAC THEN 
           ASM_REWRITE_TAC[];

%<Prove that B is contained in g(A),
  from surjection part>%

                 ASM_CASES_TAC "E (x:*):bool" THENL
                     [SUB_ASSUM_TAC[1;2;3;7] THEN
                      RES_TAC THEN 
                      SUB_ASSUM_TAC[1;6] THEN  
                      FILTER_STRIP_ASSUM_TAC [1] THEN
                      EXISTS_TAC "b:*";EXISTS_TAC "x:*"] THEN
                  RES_TAC THEN 
                  ASM_REWRITE_TAC[]];;


let SCHROEDER_BERNSTEIN_LEMMA = 
    prove(w,SCHROEDER_BERNSTEIN_TAC);;     

let w = "!A (B:*->bool).((A SLEQ B) /\ (B SLEQ A)) ==> (EQUI_POTENT A B)";;  

let ANTI_SYM_SLEQ =
   prove(
    w,  
    REPEAT GEN_TAC THEN
    REWRITE_TAC[SLEQ] THEN
    REPEAT STRIP_TAC THEN 

%<Set up the scene for using the main lemma >%

    DEFINE "D = IMAGE (f':*->*) B" THEN 

%<Prove that D is a subset of A >%
    
    IMP_RES_TAC FUN_TY THEN
    RULE_ASSUM_TAC (REWRITE_RULE[FUN_TY_IMAGE]) THEN
    FILTER_RULE_ASSUM_TAC [3] SYM THEN
    REWRITE_RULE_ASSUM_TAC [2] [3] THEN
    SUB_ASSUM_TAC [2;3;4;5] THEN

%<Prove D equi_potent with B >%

   LEMMA_PROOF "((B <--> D) (f':*->*))" 
                [REWRITE_TAC[FUN_ISO];
                 BETA_TAC;
                 FILTER_RULE_ASSUM_TAC [2] (REWRITE_RULE[SYM(SPEC_ALL ONTO_IMAGE)]);
                 ASM_REWRITE_TAC[];  
                 FILTER_ASSUM_TAC[2;3] UNDISCH_TAC;
                 REWRITE_TAC[FUN_ONE_ONE;FUN_ONTO];
                 BETA_TAC;
                 REPEAT STRIP_TAC;
                 RES_TAC] THEN  

%<Reduce to a problem on A >%

    DEFINE "(g:*->*) = f' o (f:*->*)" THEN  
    LEMMA_PROOF "((A >--> D) (g:*->*))"    
                 [FILTER_RULE_ASSUM_TAC [2] (BETA_RULE o (REWRITE_RULE[FUN_ISO])); 
                  FILTER_STRIP_ASSUM_TAC [2]; 
                  SUB_ASSUM_TAC[1;2;3;7];
                  IMP_RES_TAC  FUN_COMP; 
                  ASM_REWRITE_TAC[]] THEN 

%<Now use the MAIN_LEMMA >%
                                 
    IMP_RES_TAC SCHROEDER_BERNSTEIN_LEMMA THEN
    FILTER_STRIP_ASSUM_TAC [1] THEN 

%<Now we have A and D equi_potent and
  B and D equi_potent>%
                                           
%<and use transitivity of equi_potence>% 

  REWRITE_TAC[EQUI_POTENT] THEN
  SUB_ASSUM_TAC [1;5] THEN
  IMP_RES_TAC ISO_FINV THEN
  NEW_IMP_RES_TAC FUN_COMP THEN
  FILTER_ASSUM_TAC [4] (\tm.EXISTS_TAC (rand tm)) THEN 
  ASM_REWRITE_TAC[]);;

%<With the help of CARD_TAC it's now easy to prove that
  <<< is a partial order>% 

let w = "!a b:(*)card. ((a <<< b) /\ (b <<< a)) ==> (a = b)";;

let ANTI_SYM_CLEQ =
    prove_thm(
    `ANTI_SYM_CLEQ`,
     w,
    (2 TIMES CARD_QUOTIENT_TAC) THEN
    REWRITE_TAC[CLEQ;thm_univ;ANTI_SYM_SLEQ]);; 

let tm1 = "FUNC (A:*->bool) (B:*->bool) x = let (z,f) = (RESTRICT x (FUNC A B)) in
                         (?y.((B y) /\ (!w. ((w WLESS z) /\ (A w)) ==> (~(y = (f w)))))) => 
                         (@y.(((B y) /\ (!w. ((w WLESS z) /\ (A w)) ==> (~(y = (f w))))))) |
                             @y.(B y)";;

let FUNC = wo_rec_definition false `FUNC` tm1;; 

let w = "!f:*->*.!x:*.~((A -->> B) f) /\ ((A --> B) f)  ==> 
                                      (?z.(B z) /\ (!w.(w WLESS x) /\ (A w) ==> ~(z = f w)))";;

let LEMMA1 = prove(
    w,
    REWRITE_TAC[FUN_ONTO;FUN_TY_DEF;NOT_BOT] THEN
    REPEAT STRIP_TAC THEN 
    REWRITE_RULE_ASSUM_TAC [2] [1] THEN
    FILTER_RULE_ASSUM_TAC [2] (CONV_RULE NOT_FORALL_CONV) THEN
    FILTER_STRIP_ASSUM_TAC [2] THEN
    ASM_CASES_TAC "B (x':*):bool" THEN 
    REWRITE_RULE_ASSUM_TAC [2] [1] THENL
    [ALL_TAC;FILTER_ASSUM_LIST [2] (MAP_EVERY CONTR_TAC)] THEN
    FILTER_RULE_ASSUM_TAC [2] (CONV_RULE NOT_EXISTS_CONV) THEN
    EXISTS_TAC "x':*" THEN 
    REPEAT STRIP_TAC THENL
    [ASM_REWRITE_TAC[];
     FILTER_RULE_ASSUM_TAC [5] (SPEC "w:*") THEN
     REWRITE_RULE_ASSUM_TAC [5] [1;2] THEN
     ASM_REWRITE_TAC[]]);;  

let w = "~(B = BOT:*->bool) ==> ((A --> B) (FUNC A B))";; 

let USE_GOAL func termtac (asl,g) = termtac (func g) (asl,g);; 

let LEMMA2 = prove(w,
    REWRITE_TAC[FUN_TY_DEF;NOT_BOT] THEN
    DISCH_TAC THEN 
    TRANSFIN_INDUCT_TAC THEN
    REWRITE_TAC[FUNC] THEN
    REWRITE_TAC[LET_DEF;RESTRICT] THEN 
    BETA_TAC THEN
    REWRITE_TAC[UNCURRY_DEF] THEN 
    (2 TIMES BETA_TAC) THEN
    USE_GOAL (rand o rator o rator o rand) ASM_CASES_TAC THEN 
    ASM_REWRITE_TAC[] THENL
    [FILTER_RULE_ASSUM_TAC [1] SELECT_RULE THEN
     FILTER_STRIP_ASSUM_TAC [1];
     FILTER_RULE_ASSUM_TAC [4] SELECT_RULE THEN 
     ASM_REWRITE_TAC[]]);;  

let w = "(!w:*.
            w WLESS x /\ A w ==>
            ~(y' = (w WLESS x => FUNC A B w | LEAST TOP))) = 
         (!w. 
            w WLESS x /\ A w ==> 
            ~(y' = FUNC A B w))" ;; 

let LEMMA3 = prove(w,
    EQ_TAC THEN
    REPEAT STRIP_TAC THENL
    [RES_TAC THEN
     REWRITE_RULE_ASSUM_TAC [1] [5] THEN
     RES_TAC;
     REWRITE_RULE_ASSUM_TAC [1] [3] THEN
     RES_TAC]);;

let LEMMA4 = 
    let th1 = SPEC "x:*"(SPEC "B:*->bool"(SPEC "A:*->bool" FUNC)) in
    let th2 = REWRITE_RULE[LET_DEF;RESTRICT] th1 in
    let th3 = BETA_RULE th2 in
    let th4 = REWRITE_RULE[UNCURRY_DEF] th3 in
    (BETA_RULE o BETA_RULE) th4;;  

let LEMMA5 = REWRITE_RULE[LEMMA3] LEMMA4;;

let w = "!x y:*.~(B = BOT) /\ (~((A -->> B) (FUNC A B))) /\ (A y) /\ (A x) /\ (y WLESS x) 
                                  ==>  ~((FUNC A B y) = (FUNC A B x))";;

% --------------------------------------------------------------------- %
% Proof modified for new IMP_RES_TAC			[TFM 90.04.29]  %
% MB: this proof seems to be extremely sensitive to the ordering of     %
% assumptions.							        %
% --------------------------------------------------------------------- %

let LEMMA6 = prove(w,
    REPEAT STRIP_TAC THEN
    IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) LEMMA2 THEN 
    IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) LEMMA1 THEN 
    SUB_ASSUM_TAC [1;4;5;6;7] THEN
    ASSUME_TAC LEMMA5 THEN
    REWRITE_RULE_ASSUM_TAC [1] [2] THEN
    FILTER_RULE_ASSUM_TAC [2] SELECT_RULE THEN 
    FILTER_STRIP_ASSUM_TAC [2] THEN
    FILTER_RULE_ASSUM_TAC [3] SYM THEN
    REWRITE_RULE_ASSUM_TAC [1] [3] THEN
    RES_TAC THEN
    FILTER_RULE_ASSUM_TAC [6] SYM THEN 
    RES_TAC);;  

let w = "(~(B = BOT:*->bool)) /\ (~((A -->> B) (FUNC A B))) ==> ((A >--> B) (FUNC A B))";;

let LEMMA7 = prove(w,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[FUN_ONE_ONE] THEN
    IMP_RES_TAC (REWRITE_RULE[FUN_TY_DEF] LEMMA2) THEN
    ASM_REWRITE_TAC[] THEN 
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (SPEC_ALL WLESS_CASES) THENL
    [NEW_IMP_RES_TAC LEMMA6;
     FILTER_STRIP_ASSUM_TAC [1] THEN
     NEW_IMP_RES_TAC LEMMA6 THEN
     REWRITE_RULE_ASSUM_TAC [3] [11] THEN
     FILTER_ASSUM_LIST [3] (MAP_EVERY CONTR_TAC)]);; 

let w = "!A B:*->bool.(A SLEQ B) \/ (B SLEQ A)";;

let LEMMA8 = prove(w,
    REWRITE_TAC[SLEQ] THEN
    REPEAT GEN_TAC THEN 
    ASM_CASES_TAC "A = BOT:*->bool" THEN
    ASM_CASES_TAC "B = BOT:*->bool" THEN
    ASM_REWRITE_TAC[BOTTOM_LEFT] THEN
    ASM_CASES_TAC "((A -->> (B:*->bool)) (FUNC A B))" THENL
    [ALL_TAC;IMP_RES_TAC LEMMA7 THEN
             DISJ1_TAC THEN 
             EXISTS_TAC "FUNC A (B:*->bool)" THEN 
             ASM_REWRITE_TAC[]] THEN
    DISJ2_TAC THEN
    IMP_RES_TAC SURJ_FINV THEN
    IMP_RES_TAC FUN_TY THEN
    NEW_IMP_RES_TAC FUN_INV_TY THEN
    SUB_ASSUM_TAC [1;3;4] THEN
    FILTER_RULE_ASSUM_TAC [1] ((SPEC "FUNC A (B:*->bool)") o (SPEC "B:*->bool")) THEN
    IMP_RES_TAC INJ_SURJ_PINVERSE THEN
    EXISTS_TAC "FINV A B  (FUNC A (B:*->bool))" THEN
    ASM_REWRITE_TAC[]);;

let w = "!a b:(*)card.(a <<< b) \/ (b <<< a)";;

let LINEAR_CLEQ = prove_thm(
   `LINEAR_CLEQ`, 
    w,
    (2 TIMES CARD_QUOTIENT_TAC) THEN
    REWRITE_TAC[CLEQ;LEMMA8]);;



