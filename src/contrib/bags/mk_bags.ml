
%______________________________________________________________________

file: bags.ml
a theory for bags

author: Philippe Leveilley
June 1989

creates the theory `bags` whose parents are `HOL` and `more arithmetic
______________________________________________________________________%

% system `rm bags.th`;; %

new_theory `bags`;;

new_parent `more_arithmetic`;;

let autoload_defs_and_thms thy =
 map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
 ();;

autoload_defs_and_thms`more_arithmetic`;;

let ETA_TAC = CONV_TAC (DEPTH_CONV ETA_CONV);;

%< (\x. t1[x]) = (\x. t2[x])
   =========================  LAMDA_TAC
       !x t1[x] = t2[x]                         >%

let LAMBDA_TAC =
    CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
    BETA_TAC;;

load_library `taut`;;
let CONTRAP_THM = TAUT_PROVE "(P==>Q)=(~Q==>~P)";;
let CONTRAP_TAC = ONCE_REWRITE_TAC[CONTRAP_THM];;

let CONJ_DISJ_DISTRIB = TAUT_PROVE
       "!p q r. p /\ (q \/ r) = (p /\ q) \/ (p /\ r)";;

let DISJ_CONJ_DISTRIB = TAUT_PROVE
       "!p q r. p \/ (q /\ r) = (p \/ q) /\ (p \/ r)";;

let CONJ_DISJ_DISTRIB_2 = TAUT_PROVE
       "!p q r. (p \/ q) /\ r = (p /\ r) \/ (q /\ r)";;

let DISJ_CONJ_DISTRIB_2 = TAUT_PROVE
       "!p q r. (p /\ q) \/ r = (p \/ r) /\ (q \/ r)";;

let SYM_RULE =
    CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)
    ? failwith `SYM_RULE`;;





%<___________________________________________________________________
|                                                                   |
|                          LEMMAS                                   |
|__________________________________________________________________>%

let DISJ_ASSOC = prove_thm
    (`DISJ_ASSOC`,
     "!t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3",
     REPEAT GEN_TAC
     THEN EQ_TAC
     THEN REPEAT STRIP_TAC
     THEN ASM_REWRITE_TAC[]);;

let COND_LEM_1 = prove_thm
    (`COND_LEM_1`,
     "!s (t1:*) t2 u1 u2.
       ((s => t1 | t2) = (s => u1 | u2)) = (s => (t1 = u1) | (t2 = u2))",
     GEN_TAC THEN
     ASM_CASES_TAC "s:bool" THEN
     ASM_REWRITE_TAC[]
);;

let COND_LEM_2 = prove_thm
    (`COND_LEM_2`,
     "!t1 (t2:*). (t1 => t2 | t2 ) = t2",
     REPEAT GEN_TAC THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[]
);;

let COND_LEM_3 = prove_thm
    (`COND_LEM_3`,
     "!s (t1:num) t2 u1 u2.
       ((s => t1 | t2) <= (s => u1 | u2)) = (s => (t1 <= u1) | (t2 <= u2))",
     GEN_TAC THEN
     ASM_CASES_TAC "s:bool" THEN
     ASM_REWRITE_TAC[]
);;

%<___________________________________________________________________
|                                                                   |
|                   (*)bag TYPE DEFINITION                          |
|__________________________________________________________________>%

%< bags are represented as functions *->num
   the empty bag is the abstraction of (\x:*. 0)
   a bag s is  the abstraction of (\x:*. REP_bag x)
     thus b = {x:* / REP_bag b x > 0}
   both finite and infinite bags are represented              >%

%< there is a one-one onto relationship between bags and predicates >%

let IS_BAG_REP = new_definition
    (`IS_BAG_REP`,
     "IS_BAG_REP (b:*->num) = T");;

let IS_BAG_REP_2 = TAC_PROOF
    (([],"!b:*->num. IS_BAG_REP b"),
     REWRITE_TAC [IS_BAG_REP]);;

%< theorem proving there exists a bag >%

let BAG_REP_EX = prove_thm
     (`BAG_REP_EX`,
      "?b:*->num. IS_BAG_REP b",
      EXISTS_TAC "b:*->num" THEN
      REWRITE_TAC[IS_BAG_REP]);;

let bag_TY_DEF =
    new_type_definition
     (`bag`, "IS_BAG_REP:(*->num)->bool", BAG_REP_EX);;

%< defines (*)bag -> (*->num) bijections  >%

let bag_ISO_DEF =
    define_new_type_bijections
        `bag_ISO_DEF` `ABS_bag` `REP_bag` bag_TY_DEF;;

let R_11 = prove_rep_fn_one_one bag_ISO_DEF     and
    R_ONTO = prove_rep_fn_onto bag_ISO_DEF      and
    ABS_11   = prove_abs_fn_one_one bag_ISO_DEF and
    A_ONTO = prove_abs_fn_onto bag_ISO_DEF      and
    A_R = CONJUNCT1 bag_ISO_DEF                 and
    REP_ABS = CONJUNCT2 bag_ISO_DEF;;

map save_thm [(`R_11`,R_11); (`R_ONTO`,R_ONTO); (`A_ONTO`,A_ONTO)];;

let R_A = prove_thm
   (`R_A`,
    "!t:*->num. REP_bag (ABS_bag t) = t",
    GEN_TAC
    THEN ASSUME_TAC REP_ABS
    THEN ASSUME_TAC IS_BAG_REP
    THEN POP_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC []
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC[]
);;

let A_11 = prove_thm
     (`A_11`,
      "!(r:*->num) r'. (ABS_bag r = ABS_bag r') = (r = r')",
      REPEAT GEN_TAC
      THEN ASSUME_TAC (SPECL ["r:*->num"] IS_BAG_REP_2)
      THEN ASSUME_TAC (SPECL ["r':*->num"] IS_BAG_REP_2)
      THEN IMP_RES_TAC ABS_11
);;



%<___________________________________________________________________
|                                                                   |
|         BASIC DEFINITION AND PROPERTIES: EMPTY, IN, INSERT        |
|__________________________________________________________________>%

%< definition of {} denoted as EMPTY_BAG >%

let EMPTY_BAG_DEF = new_definition
    (`EMPTY_BAG_DEF`,
     "EMPTY_BAG = (ABS_bag \x:*. 0)");;

%< the member relation  x IN b >%

let IN_B_DEF = new_infix_definition
    (`IN_B_DEF`,
     "$IN_B (x:*) (b:(*)bag) = ~((REP_bag b) x = 0)");;

%< the insertion function  x INSERT {y,z} = {x,y,z} >%

let INSERT_B_DEF = new_infix_definition
     (`INSERT_B_DEF`,
      "INSERT_B (x:*) (b:(*)bag) =
         ABS_bag (\y. ((y = x) => SUC  (REP_bag b y)| REP_bag b y))");;

%< fundamental theorem about membership and INSERT_Bion
   directly follows from the definition                >%

let IN_B = prove_thm
     (`IN_B`,
      "(!x:*. x IN_B EMPTY_BAG = F) /\
       (!(x:*) y b. x IN_B (INSERT_B y b) = (x = y) \/ x IN_B b)",
       REPEAT STRIP_TAC
       THEN REWRITE_TAC [IN_B_DEF; EMPTY_BAG_DEF; INSERT_B_DEF; R_A]
       THEN BETA_TAC
       THEN COND_CASES_TAC
       THEN REWRITE_TAC [NOT_SUC]
);;

% x IN_B b ==> ~(b = {}) %

let MEMBER_IMP_NONEMPTY_BAG = prove_thm
    (`MEMBER_IMP_NONEMPTY_BAG`,
     "!(x:*) b. x IN_B b ==> ~(b = EMPTY_BAG)",
     REPEAT GEN_TAC
     THEN CONTRAP_TAC
     THEN REWRITE_TAC []
     THEN DISCH_TAC
     THEN ASM_REWRITE_TAC [IN_B]);;

%< x o (y o b) = y o (x o b) >%

let INSERT_B_ASSOC = prove_thm
   (`INSERT_B_ASSOC`,
    "!(x:*) y b. x INSERT_B (y INSERT_B b) = y INSERT_B (x INSERT_B b)",
    REPEAT GEN_TAC THEN
    REWRITE_TAC [INSERT_B_DEF; R_A; A_11] THEN
    BETA_TAC THEN
    LAMBDA_TAC THEN
    GEN_TAC THEN
    COND_CASES_TAC THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[]
);;


%_______________________________________________________________________
|                                                                      |
|                       EQUAL MULTIPLICITY                             |
|______________________________________________________________________%

% we have EQ_MULT A {A; A; B; C} {A; A; C; D; D}
  but not EQ_MULT A {A; A; A; B} {A; B; C}   %


let EQ_MULT_DEF = new_definition
    (`EQ_MULT_DEF`,
     "EQ_MULT x (b:(*)bag) c = (REP_bag b x = REP_bag c x)");;

% EQ_MULT X B C = EQ_MULT X C B %

let EQ_MULT_SYM = prove_thm
    (`EQ_MULT_SYM`,
     "!(x:*) b c. EQ_MULT x b c = EQ_MULT x c b",
     REPEAT GEN_TAC THEN
     REWRITE_TAC [EQ_MULT_DEF]  THEN
     EQ_TAC THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC []
);;


% !X Y B C.  EQ_MULT X {} {}
            ~EQ_MULT X {} (X o B)
             EQ_MULT X (Y o B) (Y o C) = EQ_MULT X B C
~(X = Y) ==> EQ_MULT X (Y o B) C = EQ_MULT X B C          %

let EQ_MULT = prove_thm
    (`EQ_MULT`,
     "(!x:*. EQ_MULT x EMPTY_BAG EMPTY_BAG = T)
      /\
      (!(b:(*)bag) x. ~(EQ_MULT x EMPTY_BAG (x INSERT_B b)))
      /\
      (!(x:*) y b c. EQ_MULT x(y INSERT_B b)(y INSERT_B c) = EQ_MULT x b c)
      /\
      (!(x:*) y b c.
        ~(x = y) ==> (EQ_MULT x (y INSERT_B b) c = EQ_MULT x b c))",
      REPEAT CONJ_TAC THEN
      REWRITE_TAC[EQ_MULT_DEF; EMPTY_BAG_DEF;
                  R_11; INSERT_B_DEF; R_A]  THEN
      BETA_TAC THENL
      [  % 2 %
            REWRITE_TAC [SYM_RULE NOT_SUC]
      ;   % 3 %
            REPEAT STRIP_TAC THEN
            COND_CASES_TAC THEN
            ASM_REWRITE_TAC [INV_SUC_EQ]
      ;  % 4 %
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC[]
      ]
);;


% EQ_MULT X B B %

let EQ_MULT_REFL = prove_thm
    (`EQ_MULT_REFL`,
     "!(x:*) b. EQ_MULT x b b",
      REWRITE_TAC [EQ_MULT_DEF]
);;


% EQ_MULT X B C ==> (X IN B = X IN C) %

let EQ_MULT_MEMBER = prove_thm
    (`EQ_MULT_MEMBER`,
     "!(x:*) b c. EQ_MULT x b c ==> (x IN_B b = x IN_B c)",
     REWRITE_TAC [EQ_MULT_DEF; IN_B_DEF] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC []
);;


% ~ X IN B ==> (!C EQ_MULT X B C = ~ X IN C) %

let EQ_MULT_NONMEMBER = prove_thm
    (`EQ_MULT_NONMEMBER`,
     "!(x:*) b. ~(x IN_B b) ==> (!c. EQ_MULT x b c = ~(x IN_B c))",
     ONCE_REWRITE_TAC [EQ_MULT_SYM] THEN
     REWRITE_TAC [EQ_MULT_DEF; IN_B_DEF] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC []
);;


%  B = C <==> !X. EQ_MULT X B C  %

let BAG_EQ = prove_thm
   (`BAG_EQ`,
    "!(b1:(*)bag) b2. (b1=b2) = (!x. EQ_MULT x b1 b2)",
    REPEAT GEN_TAC THEN
    REWRITE_TAC [EQ_MULT_DEF;
                 SYM
                   (FUN_EQ_CONV "REP_bag (b1:(*)bag) = REP_bag (b2:(*)bag)");
                 R_11]
);;

%_______________________________________________________________________
|                                                                      |
|                              COUNT                                   |
|______________________________________________________________________%


% COUNT B X denotes how many times X is in B %


let COUNT_DEF = new_definition
    (`COUNT_DEF`,
     "COUNT = (REP_bag:(*)bag->*->num)");;


% COUNT {} X = 0
  if (X = Y)  COUNT (Y o B) X = COUNT B X + 1
  otherwise     "      "    " = COUNT B X       %

let COUNT = prove_thm
    (`COUNT`,
     "(!x:*. COUNT EMPTY_BAG x = 0)
      /\
      (!(x:*) y b.  COUNT (y INSERT_B b) x =
                     ((x = y) => SUC (COUNT b x) | COUNT b x))",
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [COUNT_DEF; EMPTY_BAG_DEF; INSERT_B_DEF; R_A] THEN
     BETA_TAC THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [INV_SUC_EQ]
);;


% X IN B   ==>  ~COUNT B X = 0 %

let COUNT_MEMBER = prove_thm
    (`COUNT_MEMBER`,
     "!(x:*) b. x IN_B b = ~(COUNT b x = 0)",
     REWRITE_TAC [IN_B_DEF; COUNT_DEF]
);;


% B = C  <==> !X.  COUNT B X = COUNT C X  %

let COUNT_EQ = prove_thm
    (`COUNT_EQ`,
     "!(b:(*)bag) c. (b = c) = (!x. COUNT b x = COUNT c x)",
     REWRITE_TAC [BAG_EQ; EQ_MULT_DEF; COUNT_DEF]
);;


%< x IN (x o b) >%

let COMPONENT_B = prove_thm
   (`COMPONENT_B`,
    "!x:*. x IN_B (INSERT_B x b)",
    REWRITE_TAC [IN_B_DEF; INSERT_B_DEF; R_A] THEN
    BETA_TAC THEN
    REWRITE_TAC[NOT_SUC]
);;

%< x o b <> {} >%

let DISTINCT_BAG = prove_thm
    (`DISTINCT_BAG`,
     "!(x:*) b. ~(INSERT_B x b = EMPTY_BAG)",
     REPEAT GEN_TAC THEN
     REWRITE_TAC [INSERT_B_DEF; EMPTY_BAG_DEF; A_11] THEN
     LAMBDA_TAC THEN
     CONV_TAC NOT_FORALL_CONV THEN
     EXISTS_TAC "x:*" THEN
     REWRITE_TAC[NOT_SUC]
);;

let INSERTION = prove_thm
    (`INSERTION`,
     "!(x:*) b c. (x INSERT_B b = x INSERT_B c) = (b = c)",
     REWRITE_TAC [BAG_EQ; EQ_MULT]
);;

%___________________________________________________________________
|__________________________________________________________________%


% b <> {} ==> ?x. x IN_B b %
% we prove the contraposition : !x. ~ x IN_B b ==> b = {}
   where the not exists phrase was changed into a forall phrase %

let NONEMPTY_BAG_MEMBER = prove_thm
    (`NONEMPTY_BAG_MEMBER`,
     "!(b:(*)bag). ~(b = EMPTY_BAG) ==> (?x:*. x IN_B b)",
     GEN_TAC THEN
     CONTRAP_TAC THEN
     CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
     REWRITE_TAC [IN_B_DEF; BAG_EQ; EQ_MULT_DEF;
                  EMPTY_BAG_DEF; R_A]
     THEN DISCH_TAC THEN
     ASM_REWRITE_TAC []
);;

%  if x IN_B b, ? t. b = x o t and ~ x IN_B b %
% ABS_bag (\y. y IN_B b /\ ~(y=x)) will do  %

let MEMBER_DECOMP = prove_thm
    (`MEMBER_DECOMP`,
     "!(x:*) b. x IN_B b ==> (?c. b = x INSERT_B c)",
     REWRITE_TAC [IN_B_DEF; BAG_EQ; EQ_MULT_DEF; INSERT_B_DEF] THEN
     REPEAT STRIP_TAC THEN
     EXISTS_TAC "ABS_bag (\y:*. ((y = x) => PRE (REP_bag b y) | REP_bag b y))"
                THEN
     GEN_TAC THEN
     REWRITE_TAC [R_A] THEN
     BETA_TAC THEN
     COND_CASES_TAC THENL
     [  % x' = x %
          POP_ASSUM (\T. REWRITE_TAC [REWRITE_RULE [] T]) THEN
          IMP_RES_TAC SUC_PRE THEN
          ASM_REWRITE_TAC []
     ;  % ~ x' = x %
          ASM_REWRITE_TAC []
     ]
);;


%__________________________________________________________________
|                                                                 |
|                           SUBBAGS                               |
|_________________________________________________________________%

let SUBBAG_DEF = new_infix_definition
    (`SUBBAG`,
     "!b c. SUBBAG b c = (!(x:*). REP_bag b x <= REP_bag c x)"
);;


%  {} SUBBAG B  %

let SUBBAG_EMPTY = prove_thm
    (`SUBBAG_EMPTY`,
     "!(b:(*)bag). EMPTY_BAG SUBBAG b",
     REWRITE_TAC [SUBBAG_DEF; EMPTY_BAG_DEF; R_A] THEN
     BETA_TAC THEN
     REWRITE_TAC [LESS_OR_EQ]  THEN
     REPEAT GEN_TAC THEN
     ONCE_REWRITE_TAC [DISJ_SYM] THEN
     ACCEPT_TAC (SPEC "REP_bag b (x:*)" LESS_0_CASES)
);;


% (X o B) SUBBAG (X o C)  <==> B SUBBAG C  %

let SUBBAG_INSERT = prove_thm
    (`SUBBAG_INSERT`,
     "!(x:*) b c. (x INSERT_B b) SUBBAG (x INSERT_B c) = b SUBBAG c",
     REWRITE_TAC [INSERT_B_DEF; SUBBAG_DEF; R_A] THEN
     BETA_TAC THEN
     REPEAT GEN_TAC THEN
     REWRITE_TAC [COND_LEM_3; LESS_EQ_SUC_SUC; COND_LEM_2]
);;


% (X o B) SUBBAG C ==> X IN C  %

let SUBBAG_MEMBER = prove_thm
    (`SUBBAG_MEMBER`,
     "!(x:*) b c. (x INSERT_B b) SUBBAG c ==> x IN_B c",
     REWRITE_TAC[INSERT_B_DEF; SUBBAG_DEF; IN_B_DEF; R_A] THEN
     BETA_TAC THEN
     REPEAT STRIP_TAC THEN
     POP_ASSUM_LIST (\ [T1; T2].
                       MP_TAC (SPEC "(x:*)" T2) THEN
                       REWRITE_TAC [T1; LESS_OR_EQ; NOT_LESS_0; NOT_SUC])
);;


% B SUBBAG C  <==> !X. COUNT B X <= COUNT C X %

let SUBBAG_COUNT = prove_thm
    (`SUBBAG_COUNT`,
     "!(b:(*)bag) c. b SUBBAG c = (!x. COUNT b x <= COUNT c x)",
     REWRITE_TAC [SUBBAG_DEF; COUNT_DEF]
);;



let LESS_OR_EQ_ANTISYM1 = prove_thm
    (`LESS_OR_EQ_ANTISYM1`,
     "!n p. (n <= p /\ p <= n ) ==> (n = p)",
      REWRITE_TAC [LESS_OR_EQ] THEN
      REPEAT STRIP_TAC THENL
      [ IMP_RES_TAC LESS_ANTISYM
      ; ASM_REWRITE_TAC []
      ]
);;


%  B = C  <==>  B SUBBAG C /\ C SUBBAG B  %

let SUBBAG_EQ = prove_thm
    (`SUBBAG_EQ`,
     "!(b:(*)bag) c. (b = c) = (b SUBBAG c /\ c SUBBAG b)",
     REWRITE_TAC [BAG_EQ; EQ_MULT_DEF;
                  SUBBAG_DEF] THEN
     REPEAT GEN_TAC THEN
     EQ_TAC THEN
     REPEAT STRIP_TAC THENL
     [  ALL_TAC ; ALL_TAC
     ;  POP_ASSUM_LIST (MAP_EVERY (ASSUME_TAC o SPEC_ALL)) THEN
          IMP_RES_TAC LESS_OR_EQ_ANTISYM1] THEN
     ASM_REWRITE_TAC [LESS_OR_EQ]
);;


% PROPER SUBBAG %

let PSUBBAG_DEF = new_infix_definition
    (`PSUBBAG_DEF`,
     "PSUBBAG (b:(*)bag) c = b SUBBAG c /\ ~(b = c)"
);;


%__________________________________________________________________
|                                                                 |
|                      CHOICE AND REST                            |
|_________________________________________________________________%

let CHOICE_B_DEF = new_definition
    (`CHOICE_B_DEF`,
     "CHOICE_B (b:(*)bag) = (@x. x IN_B b)");;

let CHOICE_B_MEMBER = prove_thm
    (`CHOICE_B_MEMBER`,
     "!(b:(*)bag). ~(b = EMPTY_BAG) ==> (CHOICE_B b) IN_B b",
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [CHOICE_B_DEF] THEN
     IMP_RES_THEN (\T. REWRITE_TAC [SELECT_RULE T])
                  NONEMPTY_BAG_MEMBER
);;

let REST_B_DEF = new_definition
    (`REST_B_DEF`,
     "REST_B (b:(*)bag) = (@c. b = (CHOICE_B b) INSERT_B c)"
);;


%  ~(B = {})   ==>  B = (CHOICE B) o (REST B) %

let CHOICE_B_DECOMP = prove_thm
    (`CHOICE_B_DECOMP`,
     "!(b:(*)bag).
       ~(b = EMPTY_BAG) ==> (b = (CHOICE_B b) INSERT_B (REST_B b))",
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [REST_B_DEF] THEN
     IMP_RES_TAC CHOICE_B_MEMBER THEN
     IMP_RES_THEN (\T. REWRITE_TAC [SYM (SELECT_RULE T)])
                  MEMBER_DECOMP
);;


%__________________________________________________________________
|                                                                 |
|                              SUM                                |
|_________________________________________________________________%

% {A; B; B; C} SUM_B {A; C; C; D} = {A; A; B; B; C; C; C; D} %


let SUM_B_DEF = new_infix_definition
    (`SUM_B_DEF`,
     "SUM_B (b:(*)bag) c = ABS_bag (\x. REP_bag b x + REP_bag c x)"
);;


% {} SUM B = B
  (X o B) SUM C = X o (B SUM C)  %

let SUM_B = prove_thm
    (`SUM_B`,
     "(!(b:(*)bag). EMPTY_BAG SUM_B b = b)
      /\
      (!(x:*) b c. (x INSERT_B b) SUM_B c = x INSERT_B (b SUM_B c))",
      REWRITE_TAC [EMPTY_BAG_DEF; SUM_B_DEF; BAG_EQ; INSERT_B_DEF;
                   ADD_CLAUSES; EQ_MULT_DEF; R_A]    THEN
      BETA_TAC THEN
      REPEAT STRIP_TAC THENL
      [ % 1 %
          REFL_TAC
      ; % 2 %
          ASM_CASES_TAC "x'=(x:*)" THEN
          ASM_REWRITE_TAC [ADD_CLAUSES]
      ]
);;


%__________________________________________________________________
|                                                                 |
|                         UNION                                   |
|_________________________________________________________________%

% {A; A; B; C} U {A; B; D; D} = {A; A; B; C; D; D}  %


let UNION_B_DEF = new_infix_definition
    (`UNION_B_DEF`,
     "UNION_B (b:(*)bag) c = ABS_bag (\x. MAX (REP_bag b x) (REP_bag c x))"
);;


% {} U B = B %

let EMPTY_BAG_UNION = prove_thm
    (`EMPTY_BAG_UNION`,
     "!(b:(*)bag). EMPTY_BAG UNION_B b = b",
     REWRITE_TAC [BAG_EQ; EQ_MULT_DEF; UNION_B_DEF;
                  EMPTY_BAG_DEF; R_A] THEN
     BETA_TAC THEN
     REWRITE_TAC[MAX_0]
);;


% (X o B) U (X o C) = X o (B U C) %

let UNION_B_MEMBER_INSERT = prove_thm
    (`UNION_B_MEMBER_INSERT`,
     "!(x:*) b c.
         (x INSERT_B b) UNION_B (x INSERT_B c)
            = x INSERT_B (b UNION_B c)",
     REWRITE_TAC[UNION_B_DEF; INSERT_B_DEF; A_11; R_A] THEN
     LAMBDA_TAC THEN
     REPEAT GEN_TAC THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [SUC_MAX]
);;


% ~ X IN B  ==>  (X o B) U C = X o (B U C)  %

let UNION_B_NONMEMBER = prove_thm
    (`UNION_B_NONMEMBER`,
     "!(x:*) b c. ~ x IN_B c ==>
       ((x INSERT_B b) UNION_B c = x INSERT_B (b UNION_B c))",
     REWRITE_TAC[INSERT_B_DEF; UNION_B_DEF; IN_B_DEF; R_A; A_11] THEN
     LAMBDA_TAC THEN
     REPEAT STRIP_TAC THEN
     ASM_CASES_TAC "x'=(x:*)" THEN
     ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MAX_SYM] MAX_0]
);;


% COUNT (B U C) X = MAX (COUNT B X) (COUNT C X)  %

let UNION_COUNT = prove_thm
    (`UNION_COUNT`,
     "!(x:*) b c. COUNT (b UNION_B c) x = MAX (COUNT b x) (COUNT c x)",
     REWRITE_TAC [UNION_B_DEF; COUNT_DEF; R_A] THEN
     BETA_TAC THEN
     REPEAT GEN_TAC THEN
     REFL_TAC
);;


%__________________________________________________________________
|                                                                 |
|                        INTERSECTION                             |
|_________________________________________________________________%

% {A; B; B; B; C; C} INTER {B; C; C; D} = {B; C; C}  %


let INTER_B_DEF = new_infix_definition
    (`INTER_B_DEF`,
     "INTER_B (b:(*)bag) c = ABS_bag (\x. MIN (REP_bag b x) (REP_bag c x))"
);;


% {} INTER B = {} %

let EMPTY_BAG_INTER = prove_thm
    (`EMPTY_BAG_INTER`,
     "!(b:(*)bag). EMPTY_BAG INTER_B b = EMPTY_BAG",
     REWRITE_TAC [BAG_EQ; EQ_MULT_DEF; INTER_B_DEF;
                  EMPTY_BAG_DEF; R_A] THEN
     BETA_TAC THEN
     REWRITE_TAC[MIN_0]
);;


% (X o B) INTER (X o C) = X o (B INTER C)  %

let INTER_B_MEMBER_INSERT = prove_thm
    (`INTER_B_MEMBER_INSERT`,
     "!(x:*) b c.
         (x INSERT_B b) INTER_B (x INSERT_B c)
            = x INSERT_B (b INTER_B c)",
     REWRITE_TAC[INTER_B_DEF; INSERT_B_DEF; A_11; R_A] THEN
     LAMBDA_TAC THEN
     REPEAT GEN_TAC THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [SUC_MIN]
);;


% ~ X IN C  ==> (X o B) INTER C = B INTER C  %

let INTER_B_NONMEMBER = prove_thm
    (`INTER_B_NONMEMBER`,
     "!(x:*) b c. ~ x IN_B c ==>
       ((x INSERT_B b) INTER_B c = (b INTER_B c))",
     REWRITE_TAC[INSERT_B_DEF; INTER_B_DEF; IN_B_DEF; R_A; A_11] THEN
     LAMBDA_TAC THEN
     REPEAT STRIP_TAC THEN
     ASM_CASES_TAC "x'=(x:*)" THEN
     ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MIN_SYM] MIN_0]
);;


% COUNT (B INTER C) X = MIN (COUNT B X) (COUNT C X)  %

let INTER_COUNT = prove_thm
    (`INTER_COUNT`,
     "!(x:*) b c. COUNT (b INTER_B c) x = MIN (COUNT b x) (COUNT c x)",
     REWRITE_TAC [INTER_B_DEF; COUNT_DEF; R_A] THEN
     BETA_TAC THEN
     REPEAT GEN_TAC THEN
     REFL_TAC
);;

%________________________________________________________________________
|                                                                       |
|                       DEFINITION FOR FINITE BAGS                      |
|_______________________________________________________________________%

% HAS_CARD b n is true iff b contains n elements (regarding multiplicity)%

let HAS_CARD_B_DEF = new_prim_rec_definition
    (`HAS_CARD_B_DEF`,
     "(HAS_CARD_B (b:(*)bag) 0 = (b = EMPTY_BAG))
      /\
      (HAS_CARD_B (b:(*)bag) (SUC n) =
                 (?x c. (b = x INSERT_B c) /\ HAS_CARD_B c n))"
);;

% FINITE b iff there exists an n such that bcountains n elements %

let FINITE_B = new_definition
    (`FINITE_B`,
     "FINITE_B (b:(*)bag) = ?n. HAS_CARD_B b n");;

% deriving induction theorem for bags %

let BAG_INDUCT_LEMMA = prove_thm
    (`BAG_INDUCT_LEMMA`,
     "!f.
      f EMPTY_BAG /\
      (!(b:(*)bag).
            FINITE_B b ==> f b ==> (!x. f (x INSERT_B b)))
       ==> (!n c. HAS_CARD_B c n ==> f c)",
     REWRITE_TAC [FINITE_B] THEN
     GEN_TAC THEN
     STRIP_TAC THEN
     INDUCT_TAC THEN
     REWRITE_TAC [HAS_CARD_B_DEF] THEN
     REPEAT STRIP_TAC THENL
     [ % base case %
         ASM_REWRITE_TAC []
     ; % induction step %
         POP_ASSUM   (\T.
             ASSUME_TAC (EXISTS ("?n. HAS_CARD_B (c':(*)bag) n", "n:num") T)
             THEN ASSUME_TAC T) THEN
         RES_TAC THEN
         ASM_REWRITE_TAC[]
     ]
);;

let BAG_INDUCT = prove_thm
    (`BAG_INDUCT`,
     "!f.
     f EMPTY_BAG /\
     (!(b:(*)bag). FINITE_B b ==> f b ==> (!x. f (x INSERT_B b)))
      ==> (!c. FINITE_B c ==> f c)",
     GEN_TAC THEN
     STRIP_TAC THEN
     STRIP_TAC THEN
     REWRITE_TAC [FINITE_B] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC BAG_INDUCT_LEMMA
);;


%-----------------------------------------------
            BAG INDUCTION TACTIC
 ---------------------------------------------%

%<___________________________________________________
|       "!(s:(*)BAG).  P s"                          |
|   ==========================     BAG_INDUCT_TAC_1  |
| P EMPTY     P (x INSERT t)                         |
|             [ "FINITE t" ]                         |
|             [ "P t" ]                              |
|             [ "~x IN t"]                           |
|___________________________________________________>%

%<______________________________________
|  "P s"                               |
|  ======    trivial_tac "(\s. P s)s"  |
|    .                                 |
|_____________________________________>%

%<_____________________________________________________________
|    new_goal_tac thm substitutes this to the old goal:       |
|    "P EMPTY" if thm = ASSUME "~(\s. P s)EMPTY"              |
|     or "!t. P t ==> P (x INSERT t)"                         |
|        if thm = ASSUME "~(!t. P t ==> P (x INSERT t)"       |
|____________________________________________________________>%





%___________________________________________________________________________
|           t                 induct_cases_tac                             |
|  ======================     |- ~(P EMPTY /\ (!t x. P t ==> P (x INSERT t)|
|  (new_goal e1) (new_goal e2)         ~e1              ~e2                |
|__________________________________________________________________________%




%_____________________________________________________________________________
|   goal = "!b.FINITE b ==> P b"                                             |
|   bag = "(b:(*)bag)"                                                       |
|   imp = "FINITE b ==> P b"                                                 |
|   hyp = "FINITE b"                                                         |
|   conc = " P b "                                                           |
|   predicate = "\b. P b "                                                   |
|   induct_thm =                                                             |
|       |-  ~((\b. P b)EMPTY                                                 |
|             /\ (!t. (\b. P b)t ==> (!x. (\b. P b)(x INSERT t)))|
|         \/ (!b. FINITE b ==> (\b. P b)b)                                   |
|   FINITE_IMP_tac creates 2 goals                                           |
|        the first one will lead to the 2 induction goals                    |
|        the second one will be solved by trivial_tac                        |
|____________________________________________________________________________%

let BAG_INDUCT_TAC goal=
    let trivial_tac = (\t.
         REWRITE_TAC [CONV_RULE (DEPTH_CONV BETA_CONV) t])
    in
    let new_goal_tac thm =
       MP_TAC thm THEN                       %  thm ==> g"              %
       CONTRAP_TAC THEN                      %  ~g ==> ~thm             %
       DISCH_THEN (\T. ALL_TAC) THEN         %  ~thm                    %
       BETA_TAC THEN                         %  resolves \ expressions  %
       REWRITE_TAC[]
    in
    let induct_cases_tac thm =
         DISJ_CASES_THEN new_goal_tac (REWRITE_RULE [DE_MORGAN_THM] thm)
    in
    let (bag,imp) = dest_forall (snd goal) in
    let (hyp,conc) = dest_imp imp in
    let predicate = mk_abs (bag,conc) in
    let induct_thm = IMP_ELIM (SPEC predicate BAG_INDUCT)
    in
    (GEN_TAC THEN
    DISJ_CASES_THEN2 induct_cases_tac trivial_tac induct_thm
    THENL[ALL_TAC;
          GEN_TAC THEN
          DISCH_TAC THEN
          DISCH_TAC THEN
          GEN_TAC])
     goal;;


quit();; % Needed for Common Lisp %
