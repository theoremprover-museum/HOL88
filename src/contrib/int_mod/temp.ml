% File temp.ml contains the composit tactic for proving INT_SBGP_CYCLIC %

let INT_SBGP_CYCLIC = prove_thm(`INT_SBGP_CYCLIC`,
"!H. SUBGROUP((\N.T),$plus)H ==> ? n.(H = int_mult_set (INT n))",
(GEN_TAC THEN DISCH_TAC THEN
 (FIRST_ASSUM
   \thm.(STRIP_ASSUME_TAC
     (PURE_ONCE_REWRITE_RULE[SUBGROUP_DEF] thm))) THEN
 (PURE_ONCE_REWRITE_TAC [INT_MULT_SET_DEF]) THEN
 (ASM_CASES_TAC "!m1. (H m1) ==> (m1 = (INT 0))") THENL
 [((EXISTS_TAC "0") THEN
   (EXT_TAC "m1:integer") THEN BETA_TAC THEN
   (REWRITE_TAC [TIMES_ZERO]) THEN
   GEN_TAC THEN EQ_TAC THENL
   [(FIRST_ASSUM (\thm.(ACCEPT_TAC (SPEC_ALL thm))));
    (DISCH_TAC THEN
     (ASM_REWRITE_TAC [(UNDISCH (SPEC_ALL INT_SBGP_ZERO))]))]);
  ((INT_MIN_TAC "\N. (POS N /\ H N)") THENL
   [((POP_ASSUM STRIP_ASSUME_TAC) THEN
     (SUPPOSE_TAC "?n. (INT n) = MIN") THENL
     [((POP_ASSUM STRIP_ASSUME_TAC) THEN
       (EXISTS_TAC "n:num") THEN
       (POP_ASSUM \thm. PURE_ONCE_REWRITE_TAC [thm]) THEN
       (EXT_TAC "m:integer") THEN BETA_TAC THEN
       GEN_TAC THEN EQ_TAC THENL
       [((SPEC_TAC ("m:integer","N:integer")) THEN
         SIMPLE_INT_CASES_TAC THENL
         [((REPEAT STRIP_TAC) THEN
           (INT_MAX_TAC "\X.~(NEG(N minus (X times MIN)))") THENL
           [((EXISTS_TAC "MAX:integer") THEN
             (MATCH_MP_IMP_TAC
               (SPEC "neg (MAX times MIN)" PLUS_RIGHT_CANCELLATION)) THEN
             (PURE_REWRITE_TAC
               [PLUS_INV_LEMMA;(SYM (SPEC_ALL MINUS_DEF))]) THEN
             (DISJ_CASES_TAC (CONJUNCT1
               (SPEC "N minus (MAX times MIN)" TRICHOTOMY))) THENL
             [((SUPPOSE_TAC "(N minus (MAX times MIN)) below MIN") THENL
               [((SUPPOSE_TAC "(H (N minus (MAX times MIN))):bool") THENL
                 [(RES_TAC THEN RES_TAC);
                  ((PURE_ONCE_REWRITE_TAC [MINUS_DEF]) THEN
                   (GROUP_TAC [INT_SBGP_neg;INT_SBGP_TIMES_CLOSED]))]);
                ((PURE_ONCE_REWRITE_TAC [BELOW_DEF]) THEN
                 (NEW_SUBST1_TAC 
                   (SYM (SPEC "MIN minus (N minus (MAX times MIN))"
                     PLUS_INV_INV_LEMMA))) THEN
                 (PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL(NEG_DEF)))]) THEN
                 (PURE_REWRITE_TAC
                    [MINUS_DEF;
                     (SYM (SPEC_ALL (PLUS_DIST_INV_LEMMA)));
                     PLUS_INV_INV_LEMMA]) THEN
                 (INT_RIGHT_ASSOC_TAC
                   "(N plus (neg (MAX times MIN))) plus (neg MIN)") THEN
                 (PURE_REWRITE_TAC
                    [(SYM neg_PLUS_DISTRIB);(SYM (SPEC_ALL MINUS_DEF))]) THEN
                 (PURE_ONCE_REWRITE_TAC
                   [(PURE_ONCE_REWRITE_RULE [TIMES_IDENTITY] (SYM
                     (SPECL ["MAX:integer";"INT 1";"MIN:integer"]
                       RIGHT_PLUS_DISTRIB)))]) THEN
                 (MATCH_MP_IMP_TAC (ONCE_REWRITE_RULE []
                   (ASSUME
                     "!N'.MAX below N' ==>
                       ~~NEG (N minus (N' times MIN))"))) THEN
                 (SUBST_MATCH_TAC
                   (PURE_ONCE_REWRITE_RULE [COMM_PLUS]
                     (SPECL ["A:integer";"B:integer";"neg MAX"]
                       PLUS_BELOW_TRANSL))) THEN
                 (PURE_REWRITE_TAC
                    [(SYM (SPEC_ALL PLUS_GROUP_ASSOC));
                     PLUS_INV_LEMMA;
                     (SYM (SPEC_ALL NUM_LESS_IS_INT_BELOW));
                     PLUS_ID_LEMMA]) THEN
                 (CONV_TAC (DEPTH_CONV num_CONV)) THEN
                 (ACCEPT_TAC (theorem `prim_rec` `LESS_0_0`)))]);
              ((POP_ASSUM DISJ_CASES_TAC) THENL
               [RES_TAC;(FIRST_ASSUM ACCEPT_TAC)])]);
            ((EXISTS_TAC "INT 0") THEN 
             (PURE_REWRITE_TAC
               [MINUS_DEF;TIMES_ZERO;PLUS_INV_ID_LEMMA;PLUS_ID_LEMMA]) THEN
             (ACCEPT_TAC (REWRITE_RULE [(ASSUME "POS N")]
               (CONJUNCT1 (CONJUNCT2 (SPEC "N:integer" TRICHOTOMY))))));
            ((EXISTS_TAC "N:integer") THEN
             (REWRITE_TAC
               [NEG_DEF;
                MINUS_DEF;
                (SYM (SPEC_ALL PLUS_DIST_INV_LEMMA));
                PLUS_INV_INV_LEMMA]) THEN
             (PURE_REWRITE_TAC[(SYM (SPEC_ALL MINUS_DEF));
                (SYM (SPEC_ALL BELOW_DEF))]) THEN
             (STRIP_ASSUME_TAC
               (PURE_ONCE_REWRITE_RULE [POS_DEF] (ASSUME "POS MIN"))) THEN
             (PURE_ONCE_ASM_REWRITE_TAC[]) THEN
             ((DISJ_CASES_TAC (SPEC "n:num" LESS_0_CASES)) THENL
              [(POP_ASSUM \thm. (ASM_REWRITE_TAC
                 [(SYM thm);(SYM (num_CONV "1"));TIMES_IDENTITY]));
               ALL_TAC]) THEN
             (REPEAT STRIP_TAC) THEN
             (MP_IMP_TAC
               (SPECL ["N:integer";"N':integer";"N' times (INT(SUC n))"]
                TRANSIT)) THEN
             (ASM_REWRITE_TAC []) THEN
             (PURE_REWRITE_TAC
               [ADD1; (SYM (SPEC_ALL NUM_ADD_IS_INT_ADD));
                LEFT_PLUS_DISTRIB; TIMES_IDENTITY]) THEN
             (NEW_SUBST1_TAC
               (SPECL ["N':integer";"(N' times (INT n)) plus N'";"neg N'"]
                 PLUS_BELOW_TRANSL)) THEN
             (PURE_REWRITE_TAC
               [PLUS_GROUP_ASSOC;PLUS_INV_LEMMA;PLUS_ID_LEMMA]) THEN
             (NEW_SUBST1_TAC 
              (SYM (CONJUNCT1 (SPEC "N':integer" TIMES_ZERO)))) THEN
             (NEW_SUBST1_TAC
               (SYM (UNDISCH (SPECL ["N':integer"; "INT 0"; "INT n"]
                 POS_MULT_PRES_BELOW)))) THENL
             [(ASM_REWRITE_TAC [(SYM (SPEC_ALL (NUM_LESS_IS_INT_BELOW)))]);
              ((PURE_ONCE_REWRITE_TAC [POS_IS_ZERO_BELOW]) THEN
               (MP_IMP_TAC
                 (SPECL ["INT 0";"N:integer";"N':integer"] TRANSIT)) THEN
               (ASM_REWRITE_TAC[(SYM (SPEC_ALL POS_IS_ZERO_BELOW))]))])]);
          ((PURE_ONCE_REWRITE_TAC [NEG_DEF]) THEN
           (REPEAT STRIP_TAC) THEN
           (NEW_SUBST1_TAC (SYM (SPEC "N:integer" PLUS_INV_INV_LEMMA))) THEN
           (STRIP_ASSUME_TAC (MP
             (UNDISCH (SPEC "neg N"
               (ASSUME "!N. POS N ==> H N ==> (?p. N = p times MIN)")))
             (UNDISCH (SPEC "N:integer" (UNDISCH
               (SPEC "H:integer -> bool" INT_SBGP_neg)))))) THEN
           (EXISTS_TAC "neg p") THEN (ASM_REWRITE_TAC [TIMES_neg]));
          (DISCH_TAC THEN (EXISTS_TAC "INT 0") THEN
           (REWRITE_TAC [TIMES_ZERO]))]);
        (STRIP_TAC THEN (ASM_REWRITE_TAC []) THEN
         (NEW_MATCH_ACCEPT_TAC
           (UNDISCH (SPEC_ALL (UNDISCH (SPEC_ALL INT_SBGP_TIMES_CLOSED))))))]);
      ((STRIP_ASSUME_TAC
         (PURE_ONCE_REWRITE_RULE [POS_DEF] (ASSUME "POS MIN"))) THEN
       (EXISTS_TAC "SUC n") THEN (ASM_REWRITE_TAC []))]);
    ((POP_ASSUM \thm. STRIP_ASSUME_TAC 
       (REWRITE_RULE [IMP_DISJ_THM;DE_MORGAN_THM]
         (CONV_RULE NOT_FORALL_CONV thm))) THEN
     ((DISJ_CASES_TAC
        (CONJUNCT1 (SPEC "m1:integer" TRICHOTOMY))) THENL
      [((EXISTS_TAC "m1:integer") THEN (ASM_REWRITE_TAC []));
       ((POP_ASSUM DISJ_CASES_TAC) THENL
        [ALL_TAC; RES_TAC])]) THEN
     (EXISTS_TAC "neg m1") THEN
     (ASM_REWRITE_TAC
       [(SYM (SPEC_ALL NEG_DEF));
        (UNDISCH (SPEC "m1:integer"
          (UNDISCH (SPEC_ALL INT_SBGP_neg))))]));
    ((EXISTS_TAC "INT 0") THEN
     (PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL NEG_IS_BELOW_ZERO))]) THEN
     GEN_TAC THEN DISCH_TAC THEN
     (REWRITE_TAC
       [(REWRITE_RULE[(ASSUME "NEG N")]
        (CONJUNCT1 (CONJUNCT2 (SPEC "N:integer" TRICHOTOMY))))]))])]));;
