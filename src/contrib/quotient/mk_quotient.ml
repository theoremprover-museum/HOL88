new_theory `quotient`;; 

load_library `auxiliary`;;

let save_thm (name,th) = save_thm(name, GEN_ALL (DISCH_ALL th));;

let ONTO_DEF = definition `bool` `ONTO_DEF`;;

let REFLEX =
     new_definition
         (`REFLEX`,
          "REFLEX = \p. !x:*.p x x");;
               
let SYMMETRY =
     new_definition
         (`SYMMETRY`,
          "SYMMETRY = \p:*->*->bool.!x y:*.(p x y) = (p y x)");;

let TRANSITIVITY =
     new_definition
         (`TRANSITIVITY`,
           "TRANSITIVITY = \p.!x y z:*.(p x y) /\ (p y z) ==> p x z");;

let EQUIVALENCE =
     new_definition
         (`EQUIVALENCE`,
          "EQUIVALENCE = \p:*->*->bool.(REFLEX p) /\ (SYMMETRY p) /\ (TRANSITIVITY p)");;

let IS_CLASS =
    new_definition
        (`IS_CLASS`,
          "IS_CLASS = \p:*->*->bool.\dom:*->bool.(?x.dom x) /\
                             (!x y.dom x ==>( dom y = p x y))");;
                      
let MK_CLASS =
    new_definition
        (`MK_CLASS`,
         "MK_CLASS = \p:*->*->bool.\x:*.\y:*.p x y");;  

let P =
    new_infix_definition
        (`P`,
         "P = \f:*1->*2.\g:**1->**2.\x.((f (FST x)),(g (SND x)))");;

let IS_MK_CLASS = 
    save_thm
    (`IS_MK_CLASS`,
    TAC_PROOF(
    (["EQUIVALENCE (Q:*->*->bool)"],"!x:*.IS_CLASS Q (MK_CLASS Q x)"),
        FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN
        REWRITE_TAC [EQUIVALENCE;REFLEX;SYMMETRY;TRANSITIVITY;IS_CLASS;MK_CLASS] THEN
        BETA_TAC THEN  
        BETA_TAC THEN
        REPEAT STRIP_TAC THENL
             [EXISTS_TAC "x:*" THEN
              SUB_ASSUM_TAC [3] THEN
              ASM_REWRITE_TAC[];
              EQ_TAC THEN
              STRIP_TAC THENL
                  [ASSUM_LIST 
                                (\asl. FILTER_RULE_ASSUM_TAC [2] 
                                (ONCE_REWRITE_RULE  [el 4 asl])) THEN 
                   RES_TAC;
                   RES_TAC]
             ]));; 

let EXISTS_CLASS =
     save_thm
     (`EXISTS_CLASS`,
     TAC_PROOF(
          (["EQUIVALENCE (Q:*->*->bool)"],"?p:*->bool.IS_CLASS Q p"),
          EXISTS_TAC "MK_CLASS (Q:*->*->bool) p" THEN
          IMP_RES_THEN MATCH_ACCEPT_TAC IS_MK_CLASS));;
 
let SURJECTIVE_LEMMA =
    save_thm(
     `SURJECTIVE_LEMMA`,
      TAC_PROOF(
      (["EQUIVALENCE (Q:*->*->bool)"],"(IS_CLASS (Q:*->*->bool) p) ==>
                                          (?x:*.p = MK_CLASS Q x)"),
      FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN
      REWRITE_TAC [EQUIVALENCE;REFLEX;SYMMETRY;
                   TRANSITIVITY;IS_CLASS;MK_CLASS] THEN
      BETA_TAC THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC "x:*" THEN
      CONV_TAC FUN_EQ_CONV THEN 
      BETA_TAC THEN
      STRIP_TAC THEN
      FILTER_RULE_ASSUM_TAC [1] ((SPEC "x':*") o (SPEC "x:*")) THEN
      RES_TAC));;


let UNIVERSAL_LEMMA = 
     save_thm
     (`UNIVERSAL_LEMMA`,
     TAC_PROOF(
         (["EQUIVALENCE (Q:*->*->bool)"],"(MK_CLASS Q (x:*) = MK_CLASS Q y) = Q x y"),
          FILTER_ASSUM_TAC [1] UNDISCH_TAC THEN
          REWRITE_TAC [EQUIVALENCE;MK_CLASS;REFLEX;SYMMETRY;TRANSITIVITY] THEN
          CONV_TAC (REDEPTH_CONV FUN_EQ_CONV) THEN
          BETA_TAC THEN
          REPEAT STRIP_TAC THEN
          EQ_TAC THEN
          REPEAT STRIP_TAC THENL 
             [RULE_ASSUM_TAC (SPEC "x:*") THEN
              FILTER_RULE_ASSUM_TAC [2;3] (SPEC "y:*") THEN
              FILTER_RULE_ASSUM_TAC [1] SYM THEN
              ASM_REWRITE_TAC[];
              EQ_TAC THEN
              STRIP_TAC THENL
                   [ASSUM_LIST 
                                (\asl. FILTER_RULE_ASSUM_TAC [2] 
                                (ONCE_REWRITE_RULE  [el 4 asl])) THEN 
                    RES_TAC;
                    RES_TAC
                   ]
               ]));;

let FACTOR_THM =
      save_thm
      (`FACTOR_THM`,
      TAC_PROOF(
       ([],"!f:*->**.!g:*->***.((ONTO g) /\ (!x y.(g x = g y) ==> (f x = f y)))
                              ==>
                            ?!h.f = (h o g)"),
       REWRITE_TAC[ONTO_DEF;o_DEF] THEN
       CONV_TAC (REDEPTH_CONV FUN_EQ_CONV) THEN 
       BETA_TAC THEN
       REPEAT STRIP_TAC THEN   
       EXP_UNIQUE_TAC THEN
       REPEAT STRIP_TAC THENL
            [EXISTS_TAC "\x:***.(let y = (@z:*.g z = x) in (f y:**))"  THEN
             REWRITE_TAC[LET_DEF] THEN 
             BETA_TAC THEN
             STRIP_TAC THEN
             ASSUM_LIST (\asl.(MATCH_MP_TAC (hd asl))) THEN
             CONV_TAC SYM_CONV THEN
             REWRITE_TAC[(SYM o BETA_CONV) 
                        "(\z:*.g z = (g x:***))(@z.g z = (g x))"] THEN
             REWRITE_TAC[(BETA_RULE o 
                         (CONV_RULE FUN_EQ_CONV) o SYM) EXISTS_DEF] THEN
             EXISTS_TAC "x:*" THEN
             REFL_TAC;
             CONV_TAC FUN_EQ_CONV THEN 
             BETA_TAC THEN
             STRIP_TAC THEN
             RULE_ASSUM_TAC (REWRITE_RULE[EXISTS_DEF]) THEN
             RULE_ASSUM_TAC BETA_RULE THEN 
             ONCE_ASM_REWRITE_TAC[] THEN
             SUB_ASSUM_TAC [1;2;3] THEN
             FILTER_RULE_ASSUM_TAC [1;2] (GEN_ALL o SYM o SPEC_ALL) THEN
             ASM_REWRITE_TAC[]
            ]));;            

let ONTO_SURJ_THM =
         save_thm
         (`ONTO_SURJ_THM`,
         TAC_PROOF(
          ([],"!f:*1->*2.!g:**1->**2.(ONTO (f P g)) =           
                                     ((ONTO f) /\ (ONTO g)) "),
         REWRITE_TAC[ONTO_DEF;P] THEN
         BETA_TAC THEN
         REPEAT STRIP_TAC THEN
         EQ_TAC THEN
         REPEAT STRIP_TAC THENL
            [RULE_ASSUM_TAC (SPEC "y:*2,z:**2") THEN
             (POP_ASSUM_LIST o MAP_EVERY) STRIP_ASSUME_TAC THEN
             RULE_ASSUM_TAC (AP_TERM "FST:*2#**2->*2") THEN
             RULE_ASSUM_TAC (REWRITE_RULE[]) THEN
             EXISTS_TAC "FST (x:*1#**1)" THEN
             ASM_REWRITE_TAC[];
             RULE_ASSUM_TAC (SPEC "z:*2,y:**2") THEN
             (POP_ASSUM_LIST o MAP_EVERY) STRIP_ASSUME_TAC THEN
             RULE_ASSUM_TAC (AP_TERM "SND:*2#**2->**2") THEN
             RULE_ASSUM_TAC (REWRITE_RULE[]) THEN
             EXISTS_TAC "SND (x:*1#**1)" THEN
             ASM_REWRITE_TAC[];
             FILTER_RULE_ASSUM_TAC [1]  (SPEC "SND (y:*2#**2)") THEN
             FILTER_RULE_ASSUM_TAC [2]  (SPEC "FST (y:*2#**2)") THEN
             (POP_ASSUM_LIST o MAP_EVERY) STRIP_ASSUME_TAC  THEN
             EXISTS_TAC "x':*1,x:**1" THEN
             ONCE_REWRITE_TAC[(SYM o SPEC_ALL) PAIR] THEN
             PURE_ASM_REWRITE_TAC[] THEN
             ASM_REWRITE_TAC[]
            ]));;  


