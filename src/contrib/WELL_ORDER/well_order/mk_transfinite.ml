%<
FILE: mk_transfin_induct.ml

AUTHOR: Ton Kalker

DATE: 11-7-89

COMMENT: Proves transfinite induction theorem
         and transfinite recursion theorem.
         Follows the outline from "mk_prim_rec".
>% 

new_theory `transfinite`;;  

load_library `auxiliary`;; 

load_library `taut`;;

new_parent `well_order`;;

autoload_defs_and_thms `well_order`;;

autoload_defs_and_thms `fixpoints`;; 

let WLESS = new_infix_definition(`WLESS`,
           "WLESS x (y:*) = (x WLEQ y) /\ ~(x = y)");;
                                           
%<RESTRICT (x:*) (f:*->**):*->(*#**)>%

let RESTRICT = new_definition(`RESTRICT`,
          "RESTRICT (x:*) f = (x, (\y.((y WLESS x) => (f y)|(LEAST TOP:**))))");;

let PRE_REC_REL = new_definition(`PRE_REC_REL`,
          "PRE_REC_REL tau f (x:*) = !y:*.(y WLEQ x) ==>
                                      ((f y) = (tau (RESTRICT y f):**))");;

let PRE_REC_FUN = new_definition(`PRE_REC_FUN`,
          "PRE_REC_FUN tau (x:*) = @f:*->**.PRE_REC_REL tau f x");; 

let REC_REL = new_definition(`REC_REL`,
          "REC_REL tau f = !y:*.(f y:**) = tau (RESTRICT y f)");; 

let REC_FUN = new_definition(`REC_FUN`,
          "REC_FUN tau x = PRE_REC_FUN tau x (x:*):**");; 

%<First we prove some properties of WLESS>%

let w = "!x y z:*.(x WLEQ y) /\ (y WLESS z) ==> (x WLESS z)";;  

let LEMMA1 = prove(w,
             REWRITE_TAC[WLESS] THEN
             REPEAT STRIP_TAC THEN 
             IMP_RES_TAC TRANS_WLEQ THEN
             FILTER_FILTER_RULE_ASSUM_TAC [7] [4] REWRITE_RULE THEN
             IMP_RES_TAC ANTI_SYM_WLEQ THEN
             RES_TAC);; 

let w = "!x y z:*.(x WLESS y) /\ (y WLEQ z) ==> (x WLESS z)";;  

let LEMMA2 = prove(w,
             REWRITE_TAC[WLESS] THEN
             REPEAT STRIP_TAC THEN 
             IMP_RES_TAC TRANS_WLEQ THEN
             FILTER_FILTER_RULE_ASSUM_TAC [6;7] [4] REWRITE_RULE THEN
             IMP_RES_TAC ANTI_SYM_WLEQ THEN
             RES_TAC);;  

let w = "!x y z:*.(x WLESS y) /\ (y WLESS z) ==> (x WLESS z)";;

let LEMMA3 = prove(w,
             REPEAT STRIP_TAC THEN
             FILTER_ASSUM_LIST [1] (MAP_EVERY (STRIP_ASSUME_TAC o REWRITE_RULE[WLESS])) THEN
             IMP_RES_TAC LEMMA2);; 

let TRANSITIVITY_CLAUSES =
             save_thm(`TRANSITIVITY_CLAUSES`,
             LIST_CONJ [TRANS_WLEQ;
                        LEMMA1;
                        LEMMA2;
                        LEMMA3]);;  

let w = "!x:*.~(x WLESS x)";;

let IRREFLEX_WLESS = prove_thm(
              `IRREFLEX_WLESS`,
               w,
               REWRITE_TAC[WLESS]);;  

let w = "!x y:*.(x WLESS y) \/ (x = y) \/ (y WLESS x)";;

let WLESS_CASES = prove_thm(
              `WLESS_CASES`,
               w, 
               REWRITE_TAC[WLESS] THEN
               REPEAT GEN_TAC THEN
               ASSUME_TAC (SYM_CONV "y = x:*") THEN
               DISJ_CASES_TAC (SPEC_ALL LINEAR_WLEQ) THEN
               ASM_REWRITE_TAC[] THEN
               TAUT_TAC);;

%<Then we prove the induction theorem>%
                                      
let w = "!Q. (!x:*.(!y.(y WLESS x) ==> (Q y)) ==> (Q x)) ==> !x.Q x";;

let TRANSFIN_INDUCTION = prove(w,
         GEN_TAC THEN
         STRIP_TAC THEN
         ASM_CASES_TAC "!x:*.Q x" THEN 
         ASM_REWRITE_TAC[] THEN 
         DEFINE "D  =\x:*. ~(Q x)" THEN
         SUBGOAL_THEN "~(D = BOT:*->bool)" ASSUME_TAC THENL
           [CONV_TAC (RAND_CONV FUN_EQ_CONV) THEN 
            ASM_REWRITE_TAC[BOT] THEN 
            BETA_TAC THEN
            ASM_REWRITE_TAC[];ALL_TAC] THEN
         IMP_RES_TAC (CONJUNCT1 WOP_LEAST) THEN
         SUBGOAL_THEN "!y:*.(y WLESS (LEAST D)) ==> ~(D y)" ASSUME_TAC THENL
           [REWRITE_TAC[WLESS] THEN 
            REPEAT STRIP_TAC THEN
            SUB_ASSUM_TAC [1;2;3] THEN 
            IMP_RES_TAC (SPEC "D:*->bool" (CONJUNCT2 WOP_LEAST)) THEN
            IMP_RES_TAC ANTI_SYM_WLEQ THEN
            RES_TAC;ALL_TAC] THEN
          REWRITE_RULE_ASSUM_TAC [1;2] [4] THEN
          FILTER_RULE_ASSUM_TAC [1;2] BETA_RULE THEN
          FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[]) THEN
          FILTER_RULE_ASSUM_TAC [4] SYM THEN
          REWRITE_RULE_ASSUM_TAC [1;2] [4] THEN
          (2 TIMES RES_TAC));;   

let TRANSFIN_INDUCTION = save_thm(`TRANSFIN_INDUCTION`,TRANSFIN_INDUCTION);;

let TRANSFIN_INDUCT_TAC (A,t) = 
    (let th = TRANSFIN_INDUCTION in
     let th_tac = ASSUME_TAC in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in
     let tac = 
     (MATCH_MP_TAC thm THEN 
      GEN_TAC THEN
      CONV_TAC (RAND_CONV BETA_CONV) THEN
      CONV_TAC (LHS_CONV(BINDER_CONV(RAND_CONV BETA_CONV))) THEN
      REPEAT STRIP_TAC) in
      (tac (A,t))) ? failwith `TRANSFIN_INDUCT`;; 

%<Rewrite with definition of PRE_REC_FUN and PRE_REC_REL>%  

let w = "(?f:*->**.PRE_REC_REL tau f x) = PRE_REC_REL tau (PRE_REC_FUN tau x) x";;  

let LEMMA3 = prove(w,
             REWRITE_TAC[EXISTS_DEF] THEN
             BETA_TAC THEN
             REWRITE_TAC[SYM(SPEC_ALL PRE_REC_FUN)]);;

let w = "(?f:*->**.PRE_REC_REL tau f x) = (!y.(y WLEQ x) ==>
     ((PRE_REC_FUN tau x y) = tau (RESTRICT y (PRE_REC_FUN tau x))))";;

let LEMMA4 = prove(w,
             REWRITE_TAC[EXISTS_DEF] THEN
             BETA_TAC THEN
             REWRITE_TAC[SYM(SPEC_ALL PRE_REC_FUN)] THEN
             REWRITE_TAC[PRE_REC_REL]);;

%<Prove that PRE_REC_REL is downward closed>%  

let w = "!f:*->**.!tau.!x y.(x WLEQ y) /\ (PRE_REC_REL tau f y) ==>
                            (PRE_REC_REL tau f x)";;  

let LEMMA5 = prove(w,
             REWRITE_TAC[PRE_REC_REL] THEN
             REPEAT STRIP_TAC THEN
             IMP_RES_TAC TRANS_WLEQ THEN
             RES_TAC);;

let w = "!f g:*->**.(PRE_REC_REL tau f x) /\ (PRE_REC_REL tau g x) ==> (!y. (y WLEQ x) ==> ((f y) = (g y)))";;

let LEMMA6 = prove(w,
             (2 TIMES GEN_TAC) THEN
             STRIP_TAC THEN
             TRANSFIN_INDUCT_TAC THEN
             SUBGOAL_THEN "!y:*.(y WLESS x') ==> (f y = (g y:**))" ASSUME_TAC THENL
              [REPEAT STRIP_TAC THEN 
               RES_TAC THEN
               FILTER_RULE_ASSUM_TAC [2] (REWRITE_RULE[WLESS]) THEN
               FILTER_STRIP_ASSUM_TAC [2] THEN
               IMP_RES_TAC TRANS_WLEQ THEN 
               RES_TAC;ALL_TAC] THEN
             SUB_ASSUM_TAC [1;2;4;5] THEN
             SUBGOAL_THEN "RESTRICT x' f = (RESTRICT x' (g:*->**))" ASSUME_TAC THENL
              [REWRITE_TAC[RESTRICT;PAIR_EQ_THM] THEN
               CONV_TAC FUN_EQ_CONV THEN 
               BETA_TAC THEN
               GEN_TAC THEN 
               ASM_CASES_TAC "(x'':*) WLESS x'" THEN 
               ASM_REWRITE_TAC[] THEN
               RES_TAC THEN
               ASM_REWRITE_TAC[];ALL_TAC] THEN
             IMP_RES_TAC LEMMA5 THEN
             SUB_ASSUM_TAC [1;2;4] THEN
             FILTER_RULE_ASSUM_TAC [1;2]  (REWRITE_RULE[PRE_REC_REL]) THEN
             ASSUME_TAC (SPEC "x':*" REFLEX_WLEQ) THEN
             RES_TAC THEN
             ASM_REWRITE_TAC[]);;  

let w = "!f g:*->**.!x:*.(!y.(y WLESS x) ==> ((f y) = g y)) ==> ((RESTRICT x f) = (RESTRICT x g))";;

let LEMMA7 = prove(w,
             REPEAT STRIP_TAC THEN 
             REWRITE_TAC[RESTRICT;PAIR_EQ_THM] THEN
             CONV_TAC FUN_EQ_CONV THEN 
             BETA_TAC THEN 
             GEN_TAC THEN
             ASM_CASES_TAC "(x':*) WLESS x" THEN 
             ASM_REWRITE_TAC[] THEN
             RES_TAC THEN 
             ASM_REWRITE_TAC[]);; 

let w = "!f g:*->**.!x:*.(!y.(y WLESS x) ==> ((f y) = g y)) ==> 
                         (!z.(z WLEQ x) ==> ((RESTRICT z f) = (RESTRICT z g)))";;
                                      
let LEMMA8 = prove(w,
             REPEAT STRIP_TAC THEN
             SUBGOAL_THEN "!w:*.(w WLESS z) ==>((f w:**) = g w)" ASSUME_TAC THENL
              [REPEAT STRIP_TAC THEN
               IMP_RES_TAC (SPEC "x:*" (SPEC "y:*" (SPEC "w:*" LEMMA2))) THEN
               RES_TAC;ALL_TAC] THEN
             IMP_RES_TAC LEMMA7);;  



let w = "!x:*.?f:*->**.PRE_REC_REL tau f x";; 

let LEMMA9 = prove(w,
             TRANSFIN_INDUCT_TAC THEN
             DEFINE "F0:*->** = \x.PRE_REC_FUN tau x x" THEN
             SUBGOAL_THEN "!w1 w2 y:*.(w2 WLEQ w1) /\ (y WLEQ w2) /\ (w1 WLESS x)  ==> 
                                     ((PRE_REC_FUN tau w2 y:**) = (PRE_REC_FUN tau w1 y))" ASSUME_TAC THENL
              [REPEAT STRIP_TAC THEN
               SUBGOAL_THEN "(w2:*) WLESS x" ASSUME_TAC THENL
                [REWRITE_TAC[WLESS] THEN
                 FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[WLESS]) THEN
                 FILTER_STRIP_ASSUM_TAC [1] THEN
                 IMP_RES_TAC TRANS_WLEQ THEN
                 ASM_CASES_TAC "(w2:*) = x" THEN 
                 ASM_REWRITE_TAC[] THEN
                 FILTER_FILTER_RULE_ASSUM_TAC [10] [1] REWRITE_RULE THEN
                 IMP_RES_TAC ANTI_SYM_WLEQ THEN
                 RES_TAC;ALL_TAC] THEN
               RES_TAC THEN
               FILTER_RULE_ASSUM_TAC [1;2] (REWRITE_RULE[LEMMA3]) THEN
               SUB_ASSUM_TAC [1;2;3;4;5;6] THEN
               IMP_RES_TAC LEMMA5 THEN
               SUB_ASSUM_TAC [1;6;9;10] THEN
               IMP_RES_TAC LEMMA6;ALL_TAC] THEN
            SUBGOAL_THEN "!w y:*.(w WLESS x) /\ (y WLEQ w) ==> 
                                  ((F0 y:**) = (PRE_REC_FUN tau w y))" ASSUME_TAC THENL
             [REPEAT STRIP_TAC THEN
              ASM_REWRITE_TAC[] THEN
              BETA_TAC THEN
              ASSUME_TAC (SPEC "y:*" REFLEX_WLEQ) THEN
              RES_TAC;ALL_TAC] THEN
            SUBGOAL_THEN "!y:*.(y WLESS x) ==> (PRE_REC_REL tau (F0:*->**) y)" ASSUME_TAC THENL
             [REPEAT STRIP_TAC THEN
              REWRITE_TAC[PRE_REC_REL] THEN
              REPEAT STRIP_TAC THEN
              SUB_ASSUM_TAC [1;2;3;6] THEN
              FILTER_RULE_ASSUM_TAC [3] (SPEC "y:*") THEN
              FILTER_FILTER_RULE_ASSUM_TAC [3] [2] REWRITE_RULE THEN
              RES_TAC THEN
              FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[LEMMA4]) THEN
              RES_TAC THEN
              SUB_ASSUM_TAC [2;4;5;6;7] THEN
              SUBGOAL_THEN  "!y':*. y' WLESS y ==> ((F0 y':**) = PRE_REC_FUN tau y y')" ASSUME_TAC THENL
               [REWRITE_TAC[WLESS] THEN 
                REPEAT STRIP_TAC THEN 
                RES_TAC;ALL_TAC] THEN
              IMP_RES_TAC LEMMA8 THEN
              ASM_REWRITE_TAC[];ALL_TAC] THEN
            SUB_ASSUM_TAC [1] THEN
            DEFINE "G0 = \y:*.(y WLESS x) => (F0 y:**)|(tau (RESTRICT y F0))" THEN
            SUBGOAL_THEN "!z:*.(z WLEQ x) ==> ((RESTRICT z (F0:*->**)) = RESTRICT z G0)" ASSUME_TAC THENL
             [REPEAT STRIP_TAC THEN
              MATCH_MP_TAC LEMMA7 THEN
              REPEAT STRIP_TAC THEN
              IMP_RES_TAC (SPEC "x:*" (SPEC "z:*" (SPEC "y:*" LEMMA2))) THEN
              ASM_REWRITE_TAC[] THEN
              BETA_TAC THEN
              ASM_REWRITE_TAC[];ALL_TAC] THEN
            EXISTS_TAC "G0:*->**" THEN
            REWRITE_TAC[PRE_REC_REL] THEN
            REPEAT STRIP_TAC THEN
            RES_TAC THEN
            FILTER_RULE_ASSUM_TAC [1;4] SYM THEN
            ASM_REWRITE_TAC[] THEN
            FILTER_RULE_ASSUM_TAC [4] SYM THEN
            ASM_REWRITE_TAC[] THEN
            BETA_TAC THEN
            ASM_CASES_TAC "(y:*) WLESS x" THEN 
            ASM_REWRITE_TAC[] THEN
            RES_TAC THEN
            FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[PRE_REC_REL]) THEN
            ASSUME_TAC (SPEC "y:*" REFLEX_WLEQ) THEN
            RES_TAC);; 

let w = "!y w:*.(y WLEQ w) ==> ((REC_FUN tau y:**) = PRE_REC_FUN tau w y)";;   

let LEMMA10 = prove(w, 
              REWRITE_TAC[REC_FUN] THEN
              REPEAT STRIP_TAC THEN
              ASSUME_TAC (SPEC "y:*" LEMMA9) THEN
              ASSUME_TAC (SPEC "w:*" LEMMA9) THEN
              FILTER_RULE_ASSUM_TAC [1;2] (REWRITE_RULE[LEMMA3]) THEN
              IMP_RES_TAC LEMMA5 THEN
              SUB_ASSUM_TAC [1;4] THEN
              ASSUME_TAC (SPEC "y:*" REFLEX_WLEQ) THEN 
              IMP_RES_TAC LEMMA6);;

let w = "REC_REL (tau:(*#(*->**)) -> **) (REC_FUN tau)";;  

let LEMMA11 = prove(w,
              REWRITE_TAC[REC_REL;REC_FUN] THEN
              STRIP_TAC THEN
              SUBGOAL_THEN "!w:*.(w WLESS y) ==> ((REC_FUN tau w:**) = PRE_REC_FUN tau y w)" 
                                                                              ASSUME_TAC THENL
               [REWRITE_TAC[WLESS] THEN 
                REPEAT STRIP_TAC THEN 
                IMP_RES_TAC LEMMA10;ALL_TAC] THEN
              IMP_RES_TAC LEMMA7 THEN
              ASM_REWRITE_TAC[] THEN
              ASSUME_TAC (SPEC "y:*" LEMMA9) THEN
              FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[LEMMA4]) THEN
              ASSUME_TAC (SPEC "y:*" REFLEX_WLEQ) THEN
              RES_TAC);; 

let w = "(REC_REL tau (f:*->**)) /\  (REC_REL tau g) ==> (f = g)";;

let LEMMA12 = prove(w,
              REWRITE_TAC[REC_REL] THEN
              REPEAT STRIP_TAC THEN
              CONV_TAC FUN_EQ_CONV THEN 
              STRIP_TAC THEN
              SUBGOAL_THEN "PRE_REC_REL tau (f:*->**) x" ASSUME_TAC THENL
                [ASM_REWRITE_TAC[PRE_REC_REL];ALL_TAC] THEN
              SUBGOAL_THEN "PRE_REC_REL tau (g:*->**) x" ASSUME_TAC THENL
                [ASM_REWRITE_TAC[PRE_REC_REL];ALL_TAC] THEN
              ASSUME_TAC (SPEC "x:*" REFLEX_WLEQ) THEN
              IMP_RES_TAC LEMMA6);;  

let w = "!tau.?!f:*->**.REC_REL tau f";;

let wo_Axiom = save_thm(
   `wo_Axiom`,
    REWRITE_RULE[REC_REL]
   (prove(
    w, 
    EXP_UNIQUE_TAC THEN
    GEN_TAC THEN
    CONJ_TAC THEN
    REWRITE_TAC[LEMMA12] THEN
    EXISTS_TAC "REC_FUN (tau:(*#(*->**)) -> **)" THEN
    REWRITE_TAC[LEMMA11])));; 
