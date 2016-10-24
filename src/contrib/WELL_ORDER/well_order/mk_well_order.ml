%<  
FILE: mk_well_order.ml

AUTHOR: Ton Kalker

DATE: 10 july 1989

COMMENT: This file contains definitions
         and theorems proving that
         the existence of a choice function
         (as is automatic in HOL) implies the
         existence of a well-order and the
         other way around. 

         We start by defining a set of sets
         called WOC = (Well-Ordered Chain).
         In effect we prove that "WOC:(*->bool)->bool" can be
         viewed as the ordinals on ":*".
         That is, we prove that the subset ordering
         on WOC is linear and dense, and that
         the subset ordering on WOC is a well-order. 
         
         Next we define the canonical ordering on
         ":*" by embedding ":*" in the type defined
         by WOC via the function INWOC: "INWOC x" is
         defined as the smallest WOC set containing x.
         We prove that INWOC is an embedding, and
         it follows easily that the ordering on WOC
         pulled back to ":*" is a well-ordering.
         We call this well-ordering WLEQ and its
         associated choice function LEAST.
>%

new_theory `well_order`;; 

load_library `auxiliary`;;

load_library `set`;;  %<Needed for notions union,intersection>%

load_library `taut`;; %<TAUT_TAC is used>%

let BRANCH_PNTS = new_definition(`BRANCH_PNTS`,
          "BRANCH_PNTS (SS:(*->bool)->bool) X = 
                         let BS Y = ((SS Y) /\ (X PSUBSET Y)) in
                         ((SS X) /\ (GINTERSECT BS = X))");;

let LINEAR = new_definition(`LINEAR`,
          "LINEAR (SS:(*->bool)->bool) = !X Y.((SS X) /\ (SS Y)) ==>
                                              ((X SUBSET Y) \/
                                               (Y SUBSET X))");; 

let INTERSECT_CLOSED = new_definition(`INTERSECT_CLOSED`,
          "INTERSECT_CLOSED (SS:(*->bool)->bool) = 
                            !SB. (SB SUBSET SS) ==>
                                (SS (GINTERSECT SB))");;         

let UNION_CLOSED = new_definition(`UNION_CLOSED`,
          "UNION_CLOSED (SS:(*->bool)->bool) = 
                            !SB. (SB SUBSET SS) ==>
                                (SS (GUNION SB))");;         

%<Enlarging sets with one element>%

let NEXT_x = new_definition(`NEXT_x`,
          "NEXT_x (X:*->bool) = @x.(TOP DELETE X) x");; 

let NEXT = new_definition(`NEXT`,
          "NEXT (X:*->bool) = X UNION (SING (NEXT_x X))");; 

%<PWO = Partial Well-Order>%

let PWO= new_definition(`PWO`,
              "PWO (SS:(*->bool)->bool) = 
                  (!X.(SS X) ==> (SS (NEXT X))) /\
                  (INTERSECT_CLOSED SS) /\
                  (UNION_CLOSED SS)");; 
                            
%<WOC = smallest possible partial well-order; is indeed
        a partial well order, as is proved in thm1,thm2,thm5 and
        thm12>%

let WOC = new_definition(`WOC`,
              "WOC = 
                 GINTERSECT PWO:(*->bool)->bool");;  
                                   
%<PRUNE = cutting a branch at the smallest branch point
          of a PWO (which exists by thm8) and leaving a PWO 
          (proved in thm12)>%

let PRUNE = new_definition(`PRUNE`,
              "PRUNE (SS:(*->bool)->bool) X =
               let B = GINTERSECT (BRANCH_PNTS SS) in
               ((SS X) /\ ((X SUBSET B) \/ ((NEXT B) SUBSET X)))");; 
                                 

%<PREV = union of all smaller WOC sets>%

let PREV = new_definition(`PREV`,
          "PREV (X:*->bool) = (let SB Y = ((Y PSUBSET X) /\ (WOC Y)) in
                              (GUNION SB))");;

%<INWOC x = the smallest WOC set contaning x,
            existence proved in thm19>%

let INWOC = new_definition(`INWOC`,
          "INWOC (x:*) = GINTERSECT (\Y. (WOC Y) /\ (Y x))");;  

%<Canonical ordering defined by subset ordering 
  via INWOC>%
  
let WLEQ = new_infix_definition(`WLEQ`,
          "WLEQ x (y:*) = (INWOC x) SUBSET (INWOC y)");; 
                                                 
%<LEAST_WOC_SET = candidate representative for
  smallest element of a non-emtpy set>%

let LEAST_WOC_SET = new_definition(`LEAST_WOC_SET`,
          "LEAST_WOC_SET D = GINTERSECT 
                              (\Y.?x:*.((D x) /\ (Y = (INWOC x))))");; 

%<LEAST = choice function associated to WLEQ; it
          chooses the smallest element in a non-empty
          set. Proved in thm28 and thm29.>%

let LEAST = new_definition(`LEAST`,
            "LEAST (D:*->bool) = NEXT_x(PREV(LEAST_WOC_SET D))");;
                              
let w = "!SS X.(SS X) ==> (GINTERSECT SS) SUBSET (X:*->bool)";; 

let LB_THM = prove(w, 
             REWRITE_TAC[GINTERSECT;SUBSET] THEN 
             REPEAT STRIP_TAC THEN RES_TAC);;  

let w = "!SS Y.(!X:*->bool.(SS X) ==> (Y SUBSET X)) 
                   ==> (Y SUBSET (GINTERSECT SS))";;

let GLB_THM = prove(w,
              REWRITE_TAC[SUBSET;GINTERSECT] THEN
              REPEAT STRIP_TAC THEN
              RES_TAC);;

let w = "!SS TT:(*->bool)->bool.(SS SUBSET TT) 
                 ==> ( (GINTERSECT TT) SUBSET (GINTERSECT SS))";;  

let INTERSECT_MONOTONE_THM = prove(w,
              REWRITE_TAC[SUBSET;GINTERSECT] THEN
              REPEAT STRIP_TAC THEN
              (2 TIMES RES_TAC));;
 

let w = "!X Y Z:*->bool.((X SUBSET Y) /\ (Y SUBSET Z)) ==> (X SUBSET Z)";; 

let lemma1 = prove(w,
             REWRITE_TAC[SUBSET] THEN 
             REPEAT STRIP_TAC THEN 
             (2 TIMES RES_TAC));;  

let w = "!X Y Z:*->bool.((X SUBSET Y) /\ (Y PSUBSET Z)) ==> (X PSUBSET Z)";; 

let lemma2 = prove(w,
             REWRITE_TAC[PSUBSET;SUBSET] THEN 
             REPEAT STRIP_TAC THEN 
             (2 TIMES RES_TAC) THEN 
             FILTER_ASSUM_TAC [3] UNDISCH_TAC THEN 
             REWRITE_TAC[] THEN 
             (CONV_TAC FUN_EQ_CONV) THEN 
             REWRITE_RULE_ASSUM_TAC [3] [1] THEN
             GEN_TAC THEN 
             EQ_TAC THEN 
             REPEAT STRIP_TAC THEN 
             RES_TAC);;

let w = "!X Y Z:*->bool.((X PSUBSET Y) /\ (Y SUBSET Z)) ==> (X PSUBSET Z)";; 

let lemma3 = prove(w,
             REWRITE_TAC[PSUBSET;SUBSET] THEN 
             REPEAT STRIP_TAC THEN 
             (2 TIMES RES_TAC) THEN 
             FILTER_ASSUM_TAC [4] UNDISCH_TAC THEN 
             REWRITE_TAC[] THEN 
             (CONV_TAC FUN_EQ_CONV) THEN 
             FILTER_RULE_ASSUM_TAC [1] SYM THEN
             REWRITE_RULE_ASSUM_TAC [2] [1] THEN
             GEN_TAC THEN 
             EQ_TAC THEN 
             REPEAT STRIP_TAC THEN 
             RES_TAC);; 

let w = "!X:*->bool.~(X = TOP) ==> (X PSUBSET TOP) /\
                                   (X PSUBSET (NEXT X)) /\
                                   (~(X (NEXT_x X))) /\
                                   (NEXT X (NEXT_x X))";; 

let lemma4 = prove(w,
             REWRITE_TAC[PSUBSET;SUBSET;NEXT;NEXT_x;TOP;UNION;DELETE;SING] THEN 
             BETA_TAC THEN
             REPEAT STRIP_TAC THEN 
             ASM_REWRITE_TAC[] THENL
               [REWRITE_RULE_ASSUM_TAC [2] [1] THEN
                ASM_REWRITE_TAC[];
                RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV)) THEN
                RULE_ASSUM_TAC BETA_RULE THEN
                FILTER_RULE_ASSUM_TAC [2] (CONV_RULE NOT_FORALL_CONV) THEN
                FILTER_RULE_ASSUM_TAC [2] SELECT_RULE THEN
                FILTER_RULE_ASSUM_TAC [1] (SPEC "@x:*.~(X x)") THEN
                FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[]) THEN
                REWRITE_RULE_ASSUM_TAC [2] [1] THEN 
                ASM_REWRITE_TAC[];
                FILTER_RULE_ASSUM_TAC [2] 
                         (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV)) THEN
                FILTER_RULE_ASSUM_TAC [2] BETA_RULE THEN
                FILTER_RULE_ASSUM_TAC [2] (CONV_RULE NOT_FORALL_CONV) THEN
                FILTER_RULE_ASSUM_TAC [2] SELECT_RULE THEN 
                REWRITE_RULE_ASSUM_TAC [2] [1] THEN 
                ASM_REWRITE_TAC[]]);;  

let w = "!X:*->bool.((TOP SUBSET X) ==>( X = TOP))";; 

let lemma5 = prove(w,
             REWRITE_TAC[SUBSET;TOP] THEN
             REPEAT STRIP_TAC THEN 
             CONV_TAC FUN_EQ_CONV THEN 
             ASM_REWRITE_TAC[]);;  

let w = "!X Y:*->bool.((X SUBSET Y) /\ (Y SUBSET (NEXT X))) ==>
                     ((Y = X) \/ (Y = NEXT X))";;  

let lemma6 = prove(w,
             REWRITE_TAC[SUBSET;NEXT;UNION;SING] THEN 
             BETA_TAC THEN  
             REPEAT STRIP_TAC THEN 
             ASM_CASES_TAC "Y:*->bool = X" THEN 
             ASM_REWRITE_TAC[] THEN 
             CONV_TAC FUN_EQ_CONV THEN 
             BETA_TAC THEN 
             GEN_TAC THEN 
             EQ_TAC THEN 
             REPEAT STRIP_TAC THENL
                  [RES_TAC THEN ASM_REWRITE_TAC[];
                   RES_TAC;
                   FILTER_RULE_ASSUM_TAC [2] 
                        (CONV_RULE (RAND_CONV FUN_EQ_CONV)) THEN
                   FILTER_RULE_ASSUM_TAC [2] 
                        (CONV_RULE NOT_FORALL_CONV) THEN
                   FILTER_STRIP_ASSUM_TAC [2] THEN 
                   ASM_CASES_TAC "X (x':*):bool" THENL
                         [RES_TAC THEN 
                          REWRITE_RULE_ASSUM_TAC [3] [1;2] THEN
                          FILTER_ASSUM_LIST [3] (MAP_EVERY CONTR_TAC);
                          FILTER_RULE_ASSUM_TAC [4;5] (SPEC "x':*") THEN 
                          REWRITE_RULE_ASSUM_TAC [2] [1] THEN
                          REWRITE_RULE_ASSUM_TAC [4;5] [1;2] THEN
                          REWRITE_RULE_ASSUM_TAC [2] [4] THEN
                          SUB_ASSUM_TAC [2;3] THEN
                          ASM_REWRITE_TAC[]]]);; 

let w = "!SS SB (X:*->bool).((SS X) /\ 
                            (SB SUBSET SS) /\  
                            (!Y.(SB Y) ==> (X PSUBSET Y)) /\
                            ((GINTERSECT SB) = X)) ==>
                            (BRANCH_PNTS SS X)";;  

let lemma7 = prove(w,
             REWRITE_TAC [BRANCH_PNTS;LET_DEF] THEN BETA_TAC THEN
             REPEAT STRIP_TAC THEN 
             ASM_REWRITE_TAC[] THEN
             DEFINE "TT = \Y:*->bool.(SS Y) /\ (X PSUBSET Y)" THEN
             SUBGOAL_THEN "SB SUBSET (TT:(*->bool)->bool)" ASSUME_TAC THENL
              [ASM_REWRITE_TAC[SUBSET] THEN
               BETA_TAC THEN
               FILTER_RULE_ASSUM_TAC [4] (REWRITE_RULE[SUBSET]) THEN
               REPEAT STRIP_TAC THEN
               RES_TAC;ALL_TAC] THEN
             IMP_RES_TAC INTERSECT_MONOTONE_THM THEN
             FILTER_ASSUM_LIST [4] (REWRITE_TAC o (map SYM)) THEN
             REWRITE_RULE_ASSUM_TAC [2] [5] THEN
             SUB_ASSUM_TAC [2;3;4;6;7;8] THEN
             CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
             EQ_TAC THEN
             SPEC_TAC ("x:*","x:*") THEN 
             REWRITE_TAC
               [(CONV_RULE (BINDER_CONV(BINDER_CONV SYM_CONV))) SUBSET] THEN
             ASM_REWRITE_TAC[] THEN 
             MATCH_MP_TAC GLB_THM THEN
             GEN_TAC THEN BETA_TAC THEN 
             REWRITE_TAC[PSUBSET;SUBSET] THEN
             REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);; 

let w = "!X:*->bool.GINTERSECT (SING X) = X";; 

let lemma8 = prove(w,
            GEN_TAC THEN 
            CONV_TAC FUN_EQ_CONV THEN 
            REWRITE_TAC[GINTERSECT;SING] THEN
            BETA_TAC THEN GEN_TAC THEN
            EQ_TAC THEN 
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC[] THEN
            RULE_ASSUM_TAC ((REWRITE_RULE[]) o (SPEC "X:*->bool")) THEN 
            ASM_REWRITE_TAC[]);; 

let w = "!SS SB:(*->bool)->bool.GINTERSECT(SS UNION SB) =
                                ((GINTERSECT SS) INTERSECT 
                                 (GINTERSECT SB))";;  

let lemma9 = prove(w,
             REPEAT GEN_TAC THEN 
             CONV_TAC FUN_EQ_CONV THEN  
             REWRITE_TAC[GINTERSECT;UNION;INTERSECT] THEN
             BETA_TAC THEN
             GEN_TAC THEN 
             EQ_TAC THEN 
             REPEAT STRIP_TAC THEN 
             RES_TAC);;  

let w = "!X Y:*->bool.((X SUBSET Y) /\ (Y SUBSET X)) ==> (X = Y)";;

let lemma10 = prove(w,
              REWRITE_TAC[SUBSET] THEN
              REPEAT STRIP_TAC THEN
              CONV_TAC FUN_EQ_CONV THEN
              GEN_TAC THEN 
              EQ_TAC THEN STRIP_TAC THEN
              RES_TAC);;  

let w1 = "INTERSECT_CLOSED (WOC:(*->bool)->bool)";;  

let thm1 = prove(w1,
           REWRITE_TAC[INTERSECT_CLOSED] THEN
           GEN_TAC THEN
           DEFINE "X0:*->bool = GINTERSECT SB" THEN 
           RULE_ASSUM_TAC SYM THEN 
           ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[WOC;SUBSET;GINTERSECT] THEN
           REPEAT STRIP_TAC THEN
           SUBGOAL_THEN "!a:*->bool.(SB a) ==> (X a)" ASSUME_TAC THENL
           [REPEAT STRIP_TAC THEN RES_TAC;ALL_TAC] THEN
           FILTER_ASSUM_LIST [2] 
                          (MAP_EVERY 
                            (STRIP_ASSUME_TAC o  
                             (REWRITE_RULE[PWO;INTERSECT_CLOSED;SUBSET]))) THEN
           SUB_ASSUM_TAC [2;4;7] THEN
           RES_TAC THEN
           REWRITE_RULE_ASSUM_TAC [1] [4] THEN
           ASM_REWRITE_TAC[]);;

let w2 = "UNION_CLOSED (WOC:(*->bool)->bool)";;  
                                                 
let thm2 = prove(w2,
           REWRITE_TAC[UNION_CLOSED] THEN
           GEN_TAC THEN
           DEFINE "X0:*->bool = GUNION SB" THEN 
           RULE_ASSUM_TAC SYM THEN 
           ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[WOC;SUBSET;GINTERSECT] THEN
           REPEAT STRIP_TAC THEN
           SUBGOAL_THEN "!a:*->bool.(SB a) ==> (X a)" ASSUME_TAC THENL
           [REPEAT STRIP_TAC THEN RES_TAC;ALL_TAC] THEN
           FILTER_ASSUM_LIST [2] 
                          (MAP_EVERY 
                            (STRIP_ASSUME_TAC o  
                             (REWRITE_RULE[PWO;UNION_CLOSED;SUBSET]))) THEN
           SUB_ASSUM_TAC [1;4;7] THEN
           RES_TAC THEN
           REWRITE_RULE_ASSUM_TAC [1] [4] THEN
           ASM_REWRITE_TAC[]);;


let w3 = "(WOC:(*->bool)->bool) BOT";;

let thm3 = prove(w3,
           ASSUME_TAC (REWRITE_RULE[UNION_CLOSED] thm2) THEN
           SUBGOAL_THEN "BOT SUBSET (WOC:(*->bool)->bool)" ASSUME_TAC THENL
           [REWRITE_TAC[SUBSET;BOT];ALL_TAC] THEN
           RES_TAC THEN
           SUBGOAL_THEN "GUNION BOT = BOT:*->bool" ASSUME_TAC THENL
           [CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN
            GEN_TAC THEN 
            REWRITE_TAC[GUNION;BOT];ALL_TAC] THEN
           REWRITE_RULE_ASSUM_TAC [2] [1] THEN
           ASM_REWRITE_TAC[]);;


let w4 = "(WOC:(*->bool)->bool) TOP";;

let thm4 = prove(w4,
           ASSUME_TAC (REWRITE_RULE[INTERSECT_CLOSED] thm1) THEN
           SUBGOAL_THEN "BOT SUBSET (WOC:(*->bool)->bool)" ASSUME_TAC THENL
           [REWRITE_TAC[SUBSET;BOT];ALL_TAC] THEN
           RES_TAC THEN
           SUBGOAL_THEN "GINTERSECT BOT = TOP:*->bool" ASSUME_TAC THENL
           [CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN
            GEN_TAC THEN 
            REWRITE_TAC[GINTERSECT;BOT;TOP];ALL_TAC] THEN
           REWRITE_RULE_ASSUM_TAC [2] [1] THEN
           ASM_REWRITE_TAC[]);;
  

let w5 = "!X:*->bool.(WOC X) ==> (WOC (NEXT X))";; 

let thm5 = prove(w5,
           REWRITE_TAC[INTERSECT_CLOSED] THEN
           GEN_TAC THEN
           DEFINE "X0:*->bool = GINTERSECT SB" THEN 
           RULE_ASSUM_TAC SYM THEN 
           ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[WOC;GINTERSECT] THEN
           REPEAT STRIP_TAC THEN 
           RES_TAC THEN
           FILTER_ASSUM_LIST [2] 
                          (MAP_EVERY 
                            (STRIP_ASSUME_TAC o  
                             (REWRITE_RULE[PWO]))) THEN 
           RES_TAC);; 

let w6 = "!SS:(*->bool)->bool.(PWO SS) ==> (WOC SUBSET SS)";; 

let thm6 = prove(w6,
           REWRITE_TAC[WOC;SUBSET;GINTERSECT] THEN
           REPEAT STRIP_TAC THEN RES_TAC);; 

let asl7 = ["INTERSECT_CLOSED (SS:(*->bool)->bool)"];;
let w7 = "BRANCH_PNTS  (SS:(*->bool)->bool) TOP";;  
                                                    
let thm7 = TAC_PROOF(
           (asl7,w7),
           REWRITE_TAC [BRANCH_PNTS;LET_DEF] THEN
           BETA_TAC THEN
           CONJ_TAC THENL
                [RULE_ASSUM_TAC (REWRITE_RULE[INTERSECT_CLOSED]) THEN
                 SUBGOAL_THEN "BOT SUBSET (SS:(*->bool)->bool)" ASSUME_TAC THENL
                  [REWRITE_TAC[SUBSET;BOT];ALL_TAC] THEN
                 RES_TAC THEN
                 SUBGOAL_THEN "GINTERSECT BOT = TOP:*->bool" ASSUME_TAC THENL
                  [CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN
                   GEN_TAC THEN 
                   REWRITE_TAC[GINTERSECT;BOT;TOP];ALL_TAC] THEN
                 REWRITE_RULE_ASSUM_TAC [2] [1] THEN
                 ASM_REWRITE_TAC[];
                 CONV_TAC FUN_EQ_CONV THEN 
                 REWRITE_TAC[GINTERSECT;TOP;PSUBSET;SUBSET] THEN 
                 BETA_TAC THEN
                 REPEAT STRIP_TAC THEN
                 ASM_REWRITE_TAC[]]);;  

let asl8 = ["INTERSECT_CLOSED (SS:(*->bool)->bool)"];;
let w8 = "(BRANCH_PNTS  (SS:(*->bool)->bool) (GINTERSECT (BRANCH_PNTS SS)))";; 

let thm8 = TAC_PROOF(
           (asl8,w8),
            REWRITE_TAC[BRANCH_PNTS;LET_DEF] THEN
            BETA_TAC THEN 
            CONJ_TAC THENL
               [RULE_ASSUM_TAC (REWRITE_RULE[INTERSECT_CLOSED]) THEN
                ASSUM_LIST (MAP_EVERY MATCH_MP_TAC) THEN
                REWRITE_TAC[SUBSET;BRANCH_PNTS;LET_DEF] THEN
                BETA_TAC THEN
                REPEAT STRIP_TAC THEN 
                ASM_REWRITE_TAC[];ALL_TAC] THEN
            CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[GINTERSECT] THEN
            BETA_TAC THEN
            GEN_TAC THEN 
            EQ_TAC THEN           
            REPEAT STRIP_TAC THENL
               [NEW_IMP_RES_TAC LB_THM THEN
                SUB_ASSUM_TAC [3;4;5;6] THEN
                FILTER_RULE_ASSUM_TAC [2] 
                    (REWRITE_RULE[BRANCH_PNTS;LET_DEF])  THEN
                FILTER_RULE_ASSUM_TAC [2] BETA_RULE THEN
                FILTER_RULE_ASSUM_TAC [2] 
                    (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV)) THEN
                FILTER_RULE_ASSUM_TAC [2] (REWRITE_RULE[GINTERSECT]) THEN
                FILTER_RULE_ASSUM_TAC [2] BETA_RULE THEN 
                FILTER_STRIP_ASSUM_TAC [2] THEN
                FILTER_RULE_ASSUM_TAC [1] 
                     (CONV_RULE (BINDER_CONV SYM_CONV)) THEN
                ASM_REWRITE_TAC[] THEN
                REPEAT STRIP_TAC THEN 
                NEW_IMP_RES_TAC  lemma2 THEN
                NEW_RES_TAC;
                FILTER_RULE_ASSUM_TAC [1] 
                   (REWRITE_RULE[PSUBSET;SUBSET;GINTERSECT]) THEN
                NEW_RES_TAC]);; 

let w9 = "!SS.PRUNE (SS:(*->bool)->bool) SUBSET SS";; 

let thm9 = prove(w9,
           REWRITE_TAC[SUBSET;PRUNE;LET_DEF] THEN
           BETA_TAC THEN
           REPEAT STRIP_TAC THEN
           ASM_REWRITE_TAC[]);;  

let asl10 = ["INTERSECT_CLOSED (SS:(*->bool)->bool)";
             "~(GINTERSECT (BRANCH_PNTS SS:(*->bool)->bool) = TOP)"];;
let w10 = "PRUNE SS PSUBSET SS:(*->bool)->bool";; 

let thm10 =TAC_PROOF(
         (asl10,w10),
         DEFINE "B:*->bool = GINTERSECT (BRANCH_PNTS SS)" THEN
         FILTER_ASSUM_LIST [1] 
           (\asl.(ASSUME_TAC (REWRITE_RULE (map SYM asl) thm8))) THEN 
         ASSUME_TAC thm7 THEN
         FILTER_RULE_ASSUM_TAC [1;2] (REWRITE_RULE[BRANCH_PNTS;LET_DEF]) THEN
         FILTER_RULE_ASSUM_TAC [1;2] BETA_RULE THEN
         FILTER_RULE_ASSUM_TAC [1] CONJUNCT1 THEN
         FILTER_STRIP_ASSUM_TAC [2] THEN
         FILTER_RULE_ASSUM_TAC [1] (CONV_RULE FUN_EQ_CONV) THEN
         FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[GINTERSECT]) THEN
         FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
         FILTER_FILTER_RULE_ASSUM_TAC [6] [4] (REWRITE_RULE o (map SYM)) THEN
         FILTER_RULE_ASSUM_TAC [1] (SPEC "(NEXT_x B:*)") THEN
         IMP_RES_TAC lemma4 THEN
         REWRITE_RULE_ASSUM_TAC [5] [2] THEN
         FILTER_RULE_ASSUM_TAC [5] (CONV_RULE NOT_FORALL_CONV) THEN
         FILTER_STRIP_ASSUM_TAC [5] THEN
         SUBGOAL_THEN "(SS (X:*->bool)) /\ (B PSUBSET X) /\ ~(X (NEXT_x B))" 
                    STRIP_ASSUME_TAC THENL
         [SUB_ASSUM_TAC [1] THEN 
          FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN
          TAUT_TAC;ALL_TAC] THEN
         REWRITE_TAC [PRUNE;PSUBSET;SUBSET;LET_DEF] THEN
         BETA_TAC THEN 
         FILTER_RULE_ASSUM_TAC [11] SYM THEN
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
         FILTER_RULE_ASSUM_TAC [1] (CONV_RULE FUN_EQ_CONV) THEN
         FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[PRUNE;LET_DEF]) THEN
         FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
         REWRITE_RULE_ASSUM_TAC [1] [12] THEN
         FILTER_RULE_ASSUM_TAC [1] (SPEC "X:*->bool") THEN
         REWRITE_RULE_ASSUM_TAC [1] [4] THEN
         SUB_ASSUM_TAC [1;2;3;6;7;8] THEN
         FILTER_ASSUM_LIST [1] (MAP_EVERY DISJ_CASES_TAC) THENL
            [NEW_IMP_RES_TAC lemma2 THEN
             FILTER_ASSUM_TAC [2] UNDISCH_TAC  THEN
             REWRITE_TAC [PSUBSET;SUBSET];ALL_TAC] THEN
         FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN
         REWRITE_TAC[SUBSET] THEN 
         CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)  THEN
         CONV_TAC NOT_FORALL_CONV THEN
         EXISTS_TAC "NEXT_x B:*" THEN
         ASM_REWRITE_TAC[]);;  

let asl11 =["PWO (SS:(*->bool)->bool)"];;
let w11 = "PWO (PRUNE (SS:(*->bool)->bool))";;  

let thm11 = TAC_PROOF(
            (asl11,w11),
            FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN
            REWRITE_TAC[PWO;INTERSECT_CLOSED;UNION_CLOSED;PRUNE] THEN
            REWRITE_TAC[LET_DEF] THEN BETA_TAC THEN
            REPEAT STRIP_TAC THENL
%<1>%         [RES_TAC; 
%<2>%          ASM_CASES_TAC 
%<most>%       "(NEXT (X:*->bool)) SUBSET (GINTERSECT(BRANCH_PNTS SS))" THEN 
%<difficult>%  ASM_REWRITE_TAC[] THEN
%<part>%       ASM_CASES_TAC "X:*->bool = (GINTERSECT(BRANCH_PNTS SS))" THENL
                [ASM_REWRITE_TAC[SUBSET];ALL_TAC] THEN
               ASM_CASES_TAC "X:*->bool = TOP" THENL
                [ASM_REWRITE_TAC[NEXT;UNION;SING;TOP;SUBSET];ALL_TAC] THEN
               IMP_RES_TAC lemma4  THEN
               DEFINE "SB = (SING (GINTERSECT(BRANCH_PNTS SS))) UNION 
                            (SING (NEXT (X:*->bool)))" THEN
               SUBGOAL_THEN 
                   "GINTERSECT (SB:(*->bool)->bool) = X" ASSUME_TAC THENL
                 [ASM_REWRITE_TAC[lemma9;lemma8] THEN
                  SUB_ASSUM_TAC[4;7;8;9] THEN
                      SUBGOAL_THEN "(X:*->bool) SUBSET 
                         ((GINTERSECT(BRANCH_PNTS SS)) INTERSECT (NEXT X))"
                                   ASSUME_TAC THENL
                       [REWRITE_TAC[SUBSET;INTERSECT] THEN 
                        RULE_ASSUM_TAC (REWRITE_RULE[PSUBSET;SUBSET]) THEN
                        BETA_TAC THEN 
                        REPEAT STRIP_TAC THEN RES_TAC;ALL_TAC] THEN
                      SUBGOAL_THEN 
                        "((GINTERSECT(BRANCH_PNTS SS)) INTERSECT (NEXT X)) 
                        SUBSET (NEXT (X:*->bool))" ASSUME_TAC THENL
                       [REWRITE_TAC[SUBSET;INTERSECT] THEN 
                        RULE_ASSUM_TAC (REWRITE_RULE[PSUBSET;SUBSET]) THEN
                        BETA_TAC THEN 
                        REPEAT STRIP_TAC THEN RES_TAC;ALL_TAC] THEN
                  IMP_RES_TAC lemma6 THEN
                  SUB_ASSUM_TAC [1;9] THEN 
                  RULE_ASSUM_TAC (REWRITE_RULE[INTERSECT;SUBSET]) THEN
                  FILTER_RULE_ASSUM_TAC [1]  
                        ( BETA_RULE o (CONV_RULE FUN_EQ_CONV)) THEN
                  FILTER_RULE_ASSUM_TAC [2] (CONV_RULE NOT_FORALL_CONV) THEN
                  FILTER_STRIP_ASSUM_TAC [2] THEN
                  FILTER_RULE_ASSUM_TAC [2] (SPEC "a:*") THEN
                  FILTER_ASSUM_TAC [1;2] UNDISCH_TAC THEN 
                  TAUT_TAC;ALL_TAC] THEN  
               SUBGOAL_THEN "SB SUBSET (SS:(*->bool)->bool)" ASSUME_TAC THENL
                  [ASM_REWRITE_TAC[SUBSET;UNION;SING] THEN
                   BETA_TAC THEN
                   IMP_RES_TAC 
                     (((REWRITE_RULE[INTERSECT_CLOSED]) o DISCH_ALL) thm8)
                                                           THEN
                   RES_TAC THEN
                   FILTER_RULE_ASSUM_TAC [2] 
                          (REWRITE_RULE[BRANCH_PNTS;LET_DEF]) THEN
                   FILTER_RULE_ASSUM_TAC [2] BETA_RULE THEN
                   FILTER_STRIP_ASSUM_TAC [2] THEN
                   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
               SUBGOAL_THEN "!Y:*->bool.(SB Y) ==> (X PSUBSET Y)" 
                             ASSUME_TAC THENL
                  [ASM_REWRITE_TAC[UNION;SING] THEN BETA_TAC THEN
                   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
                   ASM_REWRITE_TAC[PSUBSET];ALL_TAC] THEN
               IMP_RES_TAC lemma7 THEN
               SUB_ASSUM_TAC [1;24;26] THEN
               IMP_RES_TAC LB_THM THEN
               IMP_RES_TAC lemma10 THEN
               RES_TAC;
%<3>%          RES_TAC;
%<4>%          SUBGOAL_THEN "(X:*->bool) SUBSET (NEXT X)" ASSUME_TAC THENL
                 [REWRITE_TAC [NEXT;UNION;SUBSET] 
                  THEN BETA_TAC THEN TAUT_TAC;ALL_TAC] THEN
               NEW_IMP_RES_TAC lemma1 THEN
               ASM_REWRITE_TAC[];  
%<5>%          ASSUME_TAC thm9 THEN
               FILTER_RULE_ASSUM_TAC [1] (SPEC "SS:(*->bool)->bool") THEN
               NEW_IMP_RES_TAC lemma1 THEN
               RES_TAC;
%<6>%          FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[SUBSET;PRUNE;LET_DEF]) THEN
               FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
               ASM_CASES_TAC  "?X:*->bool.(SB X) /\ 
                             (X SUBSET (GINTERSECT(BRANCH_PNTS SS)))" THENL
                  [DISJ1_TAC THEN
                   FILTER_STRIP_ASSUM_TAC [1] THEN
                   IMP_RES_TAC LB_THM THEN
                   IMP_RES_TAC lemma1;
                   DISJ2_TAC THEN
                   FILTER_RULE_ASSUM_TAC [1] (CONV_RULE NOT_EXISTS_CONV) THEN
                   MATCH_MP_TAC GLB_THM THEN
                   REPEAT STRIP_TAC THEN
                   REWRITE_TAC [SUBSET] THEN
                   RES_TAC THEN
                   FILTER_RULE_ASSUM_TAC [4] (REWRITE_RULE[SUBSET]) THEN 
                   RES_TAC];
%<7>%          ASSUME_TAC (SPEC "SS:(*->bool)->bool" thm9) THEN
               IMP_RES_TAC lemma1 THEN RES_TAC;
%<8>%          FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[SUBSET;PRUNE;LET_DEF]) THEN
               FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
               ASM_CASES_TAC  "!X:*->bool.(SB X) ==> 
                             (X SUBSET (GINTERSECT(BRANCH_PNTS SS)))" THENL
                   [DISJ1_TAC THEN  
                    REWRITE_TAC[GUNION;SUBSET] THEN
                    REPEAT STRIP_TAC THEN
                    FILTER_RULE_ASSUM_TAC [3] (REWRITE_RULE[SUBSET]) THEN 
                    SUB_ASSUM_TAC[1;2;3] THEN
                    RES_TAC;
                    DISJ2_TAC THEN
                    FILTER_RULE_ASSUM_TAC [1] (CONV_RULE NOT_FORALL_CONV) THEN
                    FILTER_STRIP_ASSUM_TAC [1] THEN
                    ASM_CASES_TAC "SB (X:*->bool):bool" THEN 
                    REWRITE_RULE_ASSUM_TAC [2] [1] THENL
                    [ALL_TAC;FILTER_ASSUM_LIST [2] (MAP_EVERY CONTR_TAC)] THEN
                    RES_TAC THENL
                     [FILTER_RULE_ASSUM_TAC [5] (REWRITE_RULE[SUBSET]) THEN
                      RES_TAC;ALL_TAC] THEN
                    REWRITE_TAC [SUBSET;GUNION] THEN
                    REPEAT STRIP_TAC THEN
                    EXISTS_TAC "X:*->bool" THEN 
                    RES_TAC THEN ASM_REWRITE_TAC[]]]);;


let w12 = "PWO (WOC:(*->bool)->bool)";;

let thm12 = prove(w12,
            REWRITE_TAC[PWO;thm1;thm2;thm5]);;

let w13 = "(BRANCH_PNTS WOC = (SING (TOP:*->bool))) = 
           ((GINTERSECT (BRANCH_PNTS WOC)) = TOP:*->bool)";; 

let thm13 = prove(w13,
            ASSUME_TAC thm1 THEN
            IMP_RES_TAC (DISCH_ALL thm7) THEN
            EQ_TAC THEN 
            STRIP_TAC THEN 
            MATCH_MP_TAC lemma10 THEN 
            CONJ_TAC THENL
             [REWRITE_TAC[SUBSET;TOP];
              ASM_REWRITE_TAC[lemma8;SUBSET];
              FILTER_RULE_ASSUM_TAC [1] (CONV_RULE FUN_EQ_CONV) THEN
              FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[GINTERSECT;TOP]) THEN
              REWRITE_TAC[SUBSET;SING;TOP] THEN 
              REPEAT STRIP_TAC THEN
              BETA_TAC THEN
              CONV_TAC FUN_EQ_CONV THEN 
              BETA_TAC THEN 
              REWRITE_TAC[] THEN
              GEN_TAC THEN
              RES_TAC;
              REWRITE_TAC[SUBSET;SING] THEN BETA_TAC THEN
              REPEAT STRIP_TAC THEN
              ASM_REWRITE_TAC[]]);;   

let w14 = "BRANCH_PNTS WOC = (SING (TOP:*->bool))";;  

let thm14 = prove(w14,
            REWRITE_TAC[thm13] THEN
            ASM_CASES_TAC "GINTERSECT(BRANCH_PNTS WOC) = TOP:*->bool" THEN
            ASM_REWRITE_TAC[] THEN
            ASSUME_TAC thm12 THEN
            ASSUME_TAC thm1 THEN
            IMP_RES_TAC (DISCH_ALL thm10) THEN
            IMP_RES_TAC (DISCH_ALL thm11) THEN
            IMP_RES_TAC thm6 THEN
            FILTER_RULE_ASSUM_TAC [4] (REWRITE_RULE[PSUBSET]) THEN
            FILTER_STRIP_ASSUM_TAC [4] THEN
            IMP_RES_TAC lemma10 THEN
            RES_TAC);; 

let w15 = "!SB:(*->bool)->bool.((SB SUBSET WOC) /\ ~(SB = BOT)) ==>
                              (SB (GINTERSECT SB))";; 

let thm15 = prove(w15,
            GEN_TAC THEN 
            DEFINE "B:*->bool = GINTERSECT SB" THEN
            ASM_CASES_TAC "SB (B:*->bool):bool" THENL
            [FILTER_RULE_ASSUM_TAC [2] SYM THEN 
             ASM_REWRITE_TAC[];ALL_TAC] THEN
            REPEAT STRIP_TAC THEN
            IMP_RES_TAC (REWRITE_RULE[INTERSECT_CLOSED] thm1) THEN
            FILTER_RULE_ASSUM_TAC [5] SYM THEN
            REWRITE_RULE_ASSUM_TAC [1] [5] THEN
            SUBGOAL_THEN "!Y:*->bool.(SB Y) ==> (B PSUBSET Y)" 
                         ASSUME_TAC THENL
            [REWRITE_TAC[PSUBSET] THEN
             REPEAT STRIP_TAC THENL
               [REWRITE_RULE_ASSUM_TAC [6] [1] THEN
                RES_TAC;
                IMP_RES_TAC LB_THM THEN
                REWRITE_RULE_ASSUM_TAC [4] [10] THEN
                ASM_REWRITE_TAC[]];ALL_TAC] THEN
            IMP_RES_TAC lemma7 THEN
            SUB_ASSUM_TAC [1;8;9;10;11;12;13] THEN
            ASSUME_TAC ((CONV_RULE FUN_EQ_CONV) thm14) THEN
            FILTER_RULE_ASSUM_TAC [1] (BETA_RULE o (REWRITE_RULE[SING])) THEN
            REWRITE_RULE_ASSUM_TAC [2] [1] THEN
            REWRITE_RULE_ASSUM_TAC [3] [2] THEN
            FILTER_RULE_ASSUM_TAC [5] 
              (CONV_RULE((RAND_CONV FUN_EQ_CONV) THENC NOT_FORALL_CONV)) THEN
            FILTER_STRIP_ASSUM_TAC [5] THEN
            FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[BOT]) THEN
            RES_TAC THEN
            FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[PSUBSET]) THEN
            FILTER_STRIP_ASSUM_TAC [1] THEN
            IMP_RES_TAC lemma5 THEN
            FILTER_RULE_ASSUM_TAC [1] (CONV_RULE SYM_CONV) THEN
            RES_TAC);; 

let w16 = "!SB:(*->bool)->bool.(LINEAR SB) = 
              (!X Y.let ST = (SING X) UNION (SING Y) in
                   ( ((SB X) /\ (SB Y)) ==> (ST (GINTERSECT ST))))";;


let thm16 = prove(w16, 
            REWRITE_TAC[LINEAR;LET_DEF] THEN 
            BETA_TAC THEN
            REWRITE_TAC[lemma8;lemma9] THEN
            REWRITE_TAC[SING;UNION;INTERSECT;SUBSET] THEN 
            BETA_TAC THEN
            GEN_TAC THEN 
            EQ_TAC THEN 
            REPEAT STRIP_TAC THENL 
             [CONV_TAC (LHS_CONV FUN_EQ_CONV) THEN
              CONV_TAC (RAND_CONV FUN_EQ_CONV) THEN
              BETA_TAC THEN
              FILTER_RULE_ASSUM_TAC [3] 
                ((SPEC "Y:*->bool") o (SPEC "X:*->bool")) THEN 
              RES_TAC THEN 
              SUB_ASSUM_TAC [1] THENL
              [DISJ1_TAC;DISJ2_TAC] THEN
              GEN_TAC THEN
              EQ_TAC THEN 
              REPEAT STRIP_TAC THEN
              RES_TAC THEN 
              ASM_REWRITE_TAC[];
              FILTER_RULE_ASSUM_TAC [3] 
                ((SPEC "Y:*->bool") o (SPEC "X:*->bool")) THEN 
              RES_TAC THEN 
              SUB_ASSUM_TAC [1] THENL 
              [DISJ1_TAC;DISJ2_TAC] THEN
              RULE_ASSUM_TAC ((CONV_RULE (BINDER_CONV SYM_CONV)) o 
                               BETA_RULE o 
                              (CONV_RULE FUN_EQ_CONV)) THEN
              GEN_TAC THEN 
              ONCE_ASM_REWRITE_TAC[] THEN 
              TAUT_TAC]);;

let w17 = "LINEAR (WOC:(*->bool)->bool)";;

let thm17 = prove(w17,
            REWRITE_TAC[thm16;LET_DEF] THEN
            BETA_TAC THEN
            REPEAT GEN_TAC THEN
            DEFINE "ST = (SING (X:*->bool)) UNION (SING Y)" THEN
            RULE_ASSUM_TAC SYM THEN
            ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THEN
            FILTER_RULE_ASSUM_TAC [3] (CONV_RULE FUN_EQ_CONV) THEN
            FILTER_RULE_ASSUM_TAC [3] (REWRITE_RULE[UNION;SING]) THEN
            FILTER_RULE_ASSUM_TAC [3] BETA_RULE THEN
            FILTER_RULE_ASSUM_TAC [3] (CONV_RULE (BINDER_CONV SYM_CONV)) THEN
            SUBGOAL_THEN "~(ST = BOT:(*->bool)->bool)" ASSUME_TAC THENL
              [CONV_TAC ((RAND_CONV FUN_EQ_CONV) THENC 
                          NOT_FORALL_CONV) THEN
               REWRITE_TAC[BOT] THEN 
               EXISTS_TAC "X:*->bool" THEN
               ASM_REWRITE_TAC[];ALL_TAC] THEN
            SUBGOAL_THEN "ST SUBSET (WOC:(*->bool)->bool)" ASSUME_TAC THENL
              [ASM_REWRITE_TAC [SUBSET] THEN
               REPEAT STRIP_TAC THEN 
               ASM_REWRITE_TAC[];ALL_TAC] THEN
            IMP_RES_TAC thm15);;

let w = "!X:*->bool.(WOC (PREV X)) /\ ((PREV X) SUBSET X)";;

let lemma11 = prove(w,
              GEN_TAC THEN 
              REWRITE_TAC[PREV;LET_DEF] THEN 
              BETA_TAC THEN
              DEFINE "SB = \Y:*->bool.(Y PSUBSET X) /\ (WOC Y)" THEN
              RULE_ASSUM_TAC SYM THEN
              ASM_REWRITE_TAC[] THEN 
              RULE_ASSUM_TAC SYM THEN 
              SUBGOAL_THEN "(SB:(*->bool)->bool) SUBSET WOC" ASSUME_TAC THENL
               [ASM_REWRITE_TAC[SUBSET] THEN 
                BETA_TAC THEN
                TAUT_TAC;ALL_TAC] THEN
              IMP_RES_TAC (REWRITE_RULE[UNION_CLOSED] thm2) THEN 
              ASM_REWRITE_TAC[] THEN
              REWRITE_TAC[GUNION;PSUBSET;SUBSET] THEN
              BETA_TAC THEN
              REPEAT STRIP_TAC THEN
              RES_TAC);; 

let w18 = "!X:*->bool.(WOC X) ==> 
                      (((PREV X) = X) \/ ((NEXT (PREV X)) = X))";;

let thm18 = prove(w18, 
            GEN_TAC THEN 
            ASM_CASES_TAC "PREV (X:*->bool) = X" THEN 
            ASM_REWRITE_TAC[] THEN
            STRIP_ASSUME_TAC (SPEC "X:*->bool" lemma11) THEN
            IMP_RES_TAC thm5 THEN
            STRIP_TAC THEN
            SUBGOAL_THEN "PREV (X:*->bool) PSUBSET X" ASSUME_TAC THENL
            [ASM_REWRITE_TAC[PSUBSET];ALL_TAC] THEN
            IMP_RES_TAC (((SPEC "NEXT(PREV (X:*->bool))") o
                           (SPEC "X:*->bool") o 
                            REWRITE_RULE[LINEAR]) thm17) THEN
            SUB_ASSUM_TAC [1;5;6;7;8;9;10] THENL
            [IMP_RES_TAC lemma6 THENL
                  [FILTER_RULE_ASSUM_TAC [1] SYM THEN RES_TAC;
                   FILTER_RULE_ASSUM_TAC [1] SYM THEN ASM_REWRITE_TAC[]];
             ALL_TAC] THEN
            ASM_CASES_TAC "PREV (X:*->bool) = TOP" THENL
             [REWRITE_RULE_ASSUM_TAC [3;8] [1] THEN
              FILTER_RULE_ASSUM_TAC [3] (REWRITE_RULE[PSUBSET]) THEN
              FILTER_STRIP_ASSUM_TAC[3] THEN
              IMP_RES_TAC lemma5 THEN 
              FILTER_RULE_ASSUM_TAC [1] SYM THEN 
              RES_TAC;ALL_TAC] THEN
            IMP_RES_TAC lemma4 THEN
            SUB_ASSUM_TAC [3;6;7;8;9;10;11;12] THEN
            ASM_CASES_TAC "NEXT(PREV (X:*->bool)) = X" THEN 
            ASM_REWRITE_TAC[] THEN
            SUBGOAL_THEN "NEXT(PREV (X:*->bool)) PSUBSET X" ASSUME_TAC THENL
            [ASM_REWRITE_TAC[PSUBSET];ALL_TAC] THEN
            SUBGOAL_THEN "NEXT(PREV (X:*->bool)) SUBSET (PREV X)"
                                                  ASSUME_TAC THENL
            [REWRITE_TAC[SUBSET] THEN
             REPEAT STRIP_TAC THEN 
             REWRITE_TAC[PREV;LET_DEF] THEN 
             BETA_TAC THEN
             REWRITE_TAC[GUNION] THEN 
             BETA_TAC THEN
             EXISTS_TAC "NEXT(PREV (X:*->bool))" THEN
             ASM_REWRITE_TAC[];ALL_TAC] THEN   
             FILTER_RULE_ASSUM_TAC [4] (REWRITE_RULE[PSUBSET]) THEN 
             FILTER_STRIP_ASSUM_TAC [4] THEN 
             IMP_RES_TAC lemma10 THEN
             RES_TAC);;

let w19 = "!x:*.(WOC (INWOC x)) /\ (INWOC x) x";;   

let thm19 = prove(w19,
            GEN_TAC THEN
            DEFINE "SB = \Y.(WOC Y) /\ (Y (x:*))" THEN  
            SUBGOAL_THEN "SB (GINTERSECT (SB:(*->bool)->bool))" 
                                                   ASSUME_TAC THENL
            [MATCH_MP_TAC thm15 THEN
             ASM_REWRITE_TAC[SUBSET] THEN 
             BETA_TAC THEN
             REPEAT STRIP_TAC THEN 
             ASM_REWRITE_TAC[] THEN
             FILTER_RULE_ASSUM_TAC [1] (CONV_RULE FUN_EQ_CONV) THEN
             FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
             FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[BOT]) THEN
             FILTER_RULE_ASSUM_TAC [1] (SPEC "TOP:*->bool") THEN
             FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[thm4;TOP]) THEN
             FILTER_ASSUM_LIST [1] (MAP_EVERY CONTR_TAC);ALL_TAC] THEN
             REWRITE_TAC[INWOC;LET_DEF] THEN 
             BETA_TAC THEN
             FILTER_RULE_ASSUM_TAC [2] SYM THEN 
             ASM_REWRITE_TAC[] THEN
             FILTER_RULE_ASSUM_TAC [2] SYM THEN
             REWRITE_RULE_ASSUM_TAC [1] [2] THEN
             FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
             FILTER_RULE_ASSUM_TAC [2] SYM THEN
             REWRITE_RULE_ASSUM_TAC [1] [2] THEN
             ASM_REWRITE_TAC[]);; 

let w20 = "!x:*.~((PREV (INWOC x)) = (INWOC x))";;


let thm20 = prove(w20,  
            GEN_TAC THEN
            REWRITE_TAC[PREV;LET_DEF] THEN   
            BETA_TAC THEN
            CONV_TAC (RAND_CONV FUN_EQ_CONV) THEN
            REWRITE_TAC[GUNION] THEN
            BETA_TAC THEN
            STRIP_TAC THEN
            RULE_ASSUM_TAC (SPEC "x:*") THEN 
            RULE_ASSUM_TAC (REWRITE_RULE[thm19]) THEN
            FILTER_STRIP_ASSUM_TAC [1] THEN
            SUBGOAL_THEN "(\Y.(WOC Y) /\ (Y (x:*)))X" ASSUME_TAC THENL
            [BETA_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
            IMP_RES_TAC LB_THM THEN
            FILTER_RULE_ASSUM_TAC [7] (REWRITE_RULE[PSUBSET;INWOC]) THEN
            SUB_ASSUM_TAC[3;7] THEN
            FILTER_STRIP_ASSUM_TAC [2] THEN
            IMP_RES_TAC lemma10 THEN 
            RES_TAC);;   

let LB_INWOC = 
        let thm = SPEC "\Y.(WOC Y) /\ (Y (x:*))" LB_THM in
        let thm = BETA_RULE thm in
        let thm = REWRITE_RULE[(CONV_RULE (BINDER_CONV SYM_CONV)) INWOC] thm in
        GEN_ALL thm;;  

let GLB_INWOC =
        let thm = SPEC "\Y.(WOC Y) /\ (Y (x:*))" GLB_THM in
        let thm = BETA_RULE thm in
        let thm = REWRITE_RULE[(CONV_RULE (BINDER_CONV SYM_CONV)) INWOC] thm in
        GEN_ALL thm;;

let w21 = "!x:*.~((PREV (INWOC x)) x)";;  
        
let thm21 = prove(w21,
        GEN_TAC THEN
        STRIP_TAC THEN
        STRIP_ASSUME_TAC (SPEC "INWOC (x:*)" lemma11) THEN
        IMP_RES_TAC LB_INWOC THEN
        IMP_RES_TAC lemma10 THEN
        IMP_RES_TAC  thm20);;

let w22 = "!x:*.NEXT_x(PREV (INWOC x)) = x";;

let thm22 = prove(w22,
        GEN_TAC THEN
        ASSUME_TAC (SPEC "x:*" thm20) THEN
        STRIP_ASSUME_TAC (SPEC "x:*" thm19) THEN
        IMP_RES_TAC thm18 THENL
        [RES_TAC;ALL_TAC] THEN
        FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[NEXT]) THEN
        FILTER_RULE_ASSUM_TAC [1] (\thm.AP_THM thm "x:*") THEN
        FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[thm19;UNION]) THEN
        FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
        FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[thm21;SING]) THEN
        FILTER_RULE_ASSUM_TAC [1] ((CONV_RULE SYM_CONV) o BETA_RULE) THEN
        ASM_REWRITE_TAC[]);;

let w23 = "!x:*.x WLEQ x";;

let thm23 = prove(w23,
            REWRITE_TAC[WLEQ;SUBSET] THEN 
            REPEAT STRIP_TAC THEN 
            ASM_REWRITE_TAC[]);;  

let w24 = "!x y z:*.(x WLEQ y) /\ (y WLEQ z) ==> (x WLEQ z)";;

let thm24 = prove(w24,
            REWRITE_TAC[WLEQ] THEN 
            REPEAT STRIP_TAC THEN 
            IMP_RES_TAC lemma1);;  

let w25 = "!x y:*.((x WLEQ y) /\ (y WLEQ x)) ==> (x = y)";;

let thm25 = prove(w25,
            REWRITE_TAC[WLEQ] THEN
            REPEAT STRIP_TAC THEN 
            IMP_RES_TAC lemma10 THEN
            SUB_ASSUM_TAC [1] THEN
            CONV_TAC (LHS_CONV(REWRITE_CONV (SYM (SPEC "x:*" thm22)))) THEN
            CONV_TAC (RAND_CONV(REWRITE_CONV (SYM (SPEC "y:*" thm22)))) THEN
            ASM_REWRITE_TAC[]);;

let w26 = "!x y:*.(x WLEQ y) \/ (y WLEQ x)";;
  
let thm26 = prove(w26,
            REWRITE_TAC[WLEQ] THEN 
            REPEAT STRIP_TAC THEN
            STRIP_ASSUME_TAC (SPEC "x:*" thm19) THEN
            STRIP_ASSUME_TAC (SPEC "y:*" thm19) THEN 
            IMP_RES_TAC (REWRITE_RULE[LINEAR] thm17) THEN 
            ASM_REWRITE_TAC[]);;

let w27 = "!D:*->bool. ~(D = BOT) ==> (?z.(D z) /\ 
                                        ((LEAST_WOC_SET D) = (INWOC z)))";;


let thm27 = prove(w27,
            REWRITE_TAC[LEAST_WOC_SET] THEN
            GEN_TAC THEN
            DEFINE "SB = \Y:*->bool.?x. D x /\ (Y = INWOC x)" THEN
            RULE_ASSUM_TAC SYM THEN 
            ASM_REWRITE_TAC[] THEN
            STRIP_TAC THEN
            SUBGOAL_THEN "~(SB = (BOT:(*->bool)->bool))" ASSUME_TAC THENL
            [FILTER_RULE_ASSUM_TAC [2] SYM THEN 
             ASM_REWRITE_TAC[BOT] THEN
             CONV_TAC (RAND_CONV FUN_EQ_CONV) THEN
             CONV_TAC NOT_FORALL_CONV THEN 
             REWRITE_TAC[] THEN
             BETA_TAC THEN
             FILTER_RULE_ASSUM_TAC [1] (CONV_RULE (RAND_CONV FUN_EQ_CONV)) THEN
             FILTER_RULE_ASSUM_TAC [1] (CONV_RULE NOT_FORALL_CONV) THEN
             FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[BOT]) THEN
             FILTER_STRIP_ASSUM_TAC [1] THEN
             EXISTS_TAC "INWOC (x:*)" THEN 
             EXISTS_TAC "x:*" THEN 
             ASM_REWRITE_TAC[];ALL_TAC] THEN
            SUBGOAL_THEN "SB SUBSET (WOC:(*->bool)->bool)" ASSUME_TAC THENL
             [FILTER_RULE_ASSUM_TAC [3] SYM THEN 
              ASM_REWRITE_TAC[SUBSET] THEN 
              BETA_TAC THEN
              REPEAT STRIP_TAC THEN
              STRIP_ASSUME_TAC (SPEC "x:*" thm19) THEN
              ASM_REWRITE_TAC[];ALL_TAC] THEN
             IMP_RES_TAC thm15 THEN
             FILTER_RULE_ASSUM_TAC [6] SYM THEN 
             REWRITE_RULE_ASSUM_TAC [1] [6] THEN
             FILTER_RULE_ASSUM_TAC [6] SYM THEN 
             FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
             REWRITE_RULE_ASSUM_TAC [1] [6] THEN
             ASM_REWRITE_TAC[]);;

let LEAST_LB = 
     let thm = SPEC "\Y:*->bool.?x. D x /\ (Y = INWOC x)" LB_THM in
     let thm = BETA_RULE thm in
     let thm = REWRITE_RULE[(CONV_RULE (BINDER_CONV SYM_CONV)) LEAST_WOC_SET] 
                                                        thm in  
     let thm = (CONV_RULE (BINDER_CONV EXISTS_IMP_FORALL_CONV)) thm in
     let thm = SPEC_ALL thm in 
     let thm = GEN "X:*->bool" thm in
     let thm = SPEC "INWOC (x:*)" thm in
     let thm = REWRITE_RULE[] thm in
     GEN_ALL thm;;


let LEAST_GLB_lemma = 
     let thm = SPEC "\Y:*->bool.?x. D x /\ (Y = INWOC x)" GLB_THM in
     let thm = BETA_RULE thm in
     let thm = REWRITE_RULE[(CONV_RULE (BINDER_CONV SYM_CONV)) LEAST_WOC_SET] 
                                                        thm in
     let thm = (CONV_RULE (BINDER_CONV (LHS_CONV 
                           (BINDER_CONV EXISTS_IMP_FORALL_CONV)))) thm in
     GEN_ALL thm;; 

let w = "!D Y.(!x:*.(D x) ==> (Y SUBSET (INWOC x))) 
                                     ==> (Y SUBSET (LEAST_WOC_SET D))";;

let LEAST_GLB =  prove(w,
                 REPEAT STRIP_TAC THEN
                 MATCH_MP_TAC LEAST_GLB_lemma THEN
                 REPEAT STRIP_TAC THEN
                 RES_TAC THEN
                 ASM_REWRITE_TAC[]);;


let w28 = "!D:*->bool.~(D = BOT) ==> (D (LEAST D))";;

let thm28 = prove(w28,
            REPEAT STRIP_TAC THEN 
            IMP_RES_TAC thm27 THEN
            FILTER_STRIP_ASSUM_TAC [1] THEN
            ASSUME_TAC (SPEC "z:*" thm22) THEN
            REWRITE_TAC[LEAST] THEN
            ASM_REWRITE_TAC[]);;

let w29 = "!D.!x:*.(D x) ==> (LEAST D) WLEQ x";;

let thm29 = prove(w29,
            REWRITE_TAC[WLEQ;LEAST] THEN
            REPEAT STRIP_TAC THEN
            ASSUME_TAC (SPEC "D:*->bool" thm27) THEN
            FILTER_RULE_ASSUM_TAC [1] 
               (CONV_RULE (LHS_CONV(RAND_CONV FUN_EQ_CONV))) THEN
            FILTER_RULE_ASSUM_TAC [1] 
               (CONV_RULE (LHS_CONV NOT_FORALL_CONV)) THEN
            FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[BOT]) THEN
            FILTER_ASSUM_LIST [2] (MAP_EVERY
               (\thm.ASSUME_TAC (EXISTS ("?x:*.D x","x:*") thm ))) THEN
            RES_TAC THEN
            FILTER_STRIP_ASSUM_TAC [1] THEN
            ASM_REWRITE_TAC[thm22] THEN
            FILTER_RULE_ASSUM_TAC [1] SYM THEN 
            ASM_REWRITE_TAC[] THEN 
            MATCH_MP_TAC LEAST_LB THEN
            ASM_REWRITE_TAC[]);;  

let w30 = "!x y:*.INWOC x y = (y WLEQ x)";; 

let thm30 = prove(w30,
            REPEAT GEN_TAC THEN
            REWRITE_TAC[WLEQ] THEN
            EQ_TAC THEN
            STRIP_TAC THENL
            [MATCH_MP_TAC LB_INWOC THEN
             ASM_REWRITE_TAC[thm19];
             RULE_ASSUM_TAC (REWRITE_RULE[SUBSET]) THEN
             RULE_ASSUM_TAC ((REWRITE_RULE[thm19]) o (SPEC "y:*")) THEN
             ASM_REWRITE_TAC[]]);;

let PWO_WOC = save_thm(`PWO_WOC`, thm12);;  

let WOP_WOC = save_thm(`WOP_WOC`,thm15);;  

let LINEAR_WOC = save_thm(`LINEAR_WOC`,thm17);;  

let DENSE_WOC = save_thm(`DENSE_WOC`,thm18);;

let REFLEX_WLEQ = save_thm(`REFLEX_WLEQ`,thm23);;

let ANTI_SYM_WLEQ = save_thm(`ANTI_SYM_WLEQ`,thm25);; 

let TRANS_WLEQ = save_thm(`TRANS_WLEQ`,thm24);; 

let LINEAR_WLEQ = save_thm(`LINEAR_WLEQ`,thm26);;

let WOP_LEAST = save_thm(`WOP_LEAST`,(CONJ thm28 thm29));;

let INWOC_PROP = save_thm(`INWOC_PROP`, thm30);;
