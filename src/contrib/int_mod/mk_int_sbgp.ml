% --------------------------------------------------------------------- %
% FILE		: mk_int_sbgp.ml					%
% DESCRIPTION   : This file contains some of the facts about subgroups  %
%                 of the integers which are relavant to the development %
%                 of modular arithmetic.                                %
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.4.22						%
%									%
%-----------------------------------------------------------------------%

new_theory `int_sbgp`;;

load_library `integer`;;	    % This also loads the group library %


let INT_SBGP_NORMAL = prove_thm(`INT_SBGP_NORMAL`,
"!H.SUBGROUP((\N.T),$plus)H ==> NORMAL((\N.T),$plus)H",
(GEN_TAC THEN DISCH_TAC THEN (ASM_REWRITE_TAC[NORMAL_DEF]) THEN
 (REPEAT STRIP_TAC) THEN (PURE_ONCE_REWRITE_TAC[(SYM neg_DEF)]) THEN
 (NEW_SUBST1_TAC (SPECL ["n:integer";"x:integer"] COMM_PLUS)) THEN
 (PURE_ONCE_REWRITE_TAC[ASSOC_PLUS]) THEN
 (ASM_REWRITE_TAC[PLUS_INV_LEMMA; PLUS_ID_LEMMA])));;

%INT_SBGP_NORMAL = |- !H. SUBGROUP((\N. T),$plus)H ==> NORMAL((\N. T),$plus)H %


let INT_SBGP_ZERO = prove_thm (`INT_SBGP_ZERO`,
"!H.SUBGROUP((\N.T),$plus)H ==> H(INT 0)",
((REPEAT STRIP_TAC) THEN
 (PURE_ONCE_REWRITE_TAC [(SYM ID_EQ_0)]) THEN
 (SUBST_MATCH_TAC (SYM (UNDISCH SBGP_ID_GP_ID))) THEN
 GROUP_ELT_TAC THEN
 (POP_ASSUM \thm. (ACCEPT_TAC (CONJUNCT2 (CONJUNCT2
   (PURE_ONCE_REWRITE_RULE [SUBGROUP_DEF] thm)))))));;

%INT_SBGP_ZERO = |- !H. SUBGROUP((\N. T),$plus)H ==> H(INT 0)%


let INT_SBGP_neg = prove_thm(`INT_SBGP_neg`,
"!H.SUBGROUP((\N.T),$plus)H ==> !N. (H N ==> H (neg N))",
((REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (PURE_ONCE_REWRITE_RULE [SUBGROUP_DEF]
    (ASSUME "SUBGROUP((\N.T),$plus)H"))) THEN
 (PURE_ONCE_REWRITE_TAC [neg_DEF]) THEN
 (SUBST_MATCH_TAC
    (SYM (UNDISCH (SPEC_ALL (UNDISCH SBGP_INV_GP_INV))))) THEN
 GROUP_ELT_TAC));;

%INT_SBGP_neg = 
|- !H. SUBGROUP((\N. T),$plus)H ==> (!N. H N ==> H(neg N))%


let INT_MULT_SET_DEF = new_definition(`INT_MULT_SET_DEF`,
"int_mult_set n = \m. ?p. (m = p times n)");;

%INT_MULT_SET_DEF = |- !n. int_mult_set n = (\m. ?p. m = p times n) %


let INT_MULT_SET_NORMAL = prove_thm(`INT_MULT_SET_NORMAL`,
"!n. NORMAL((\N. T),$plus)(int_mult_set n)",
(GEN_TAC THEN (MATCH_MP_IMP_TAC INT_SBGP_NORMAL) THEN
 (REWRITE_TAC[SUBGROUP_LEMMA;INT_MULT_SET_DEF;integer_as_GROUP]) THEN
 BETA_TAC THEN (REPEAT STRIP_TAC) THENL
 [((EXISTS_TAC "INT 0") THEN (EXISTS_TAC "INT 0") THEN
  (REWRITE_TAC [TIMES_ZERO]));
  ((EXISTS_TAC "p plus p'") THEN
   (ASM_REWRITE_TAC [RIGHT_PLUS_DISTRIB]));
  ((PURE_ONCE_REWRITE_TAC[(SYM neg_DEF)]) THEN
   (EXISTS_TAC "neg p") THEN
   (ASM_REWRITE_TAC[TIMES_neg]))]));;

%INT_MULT_SET_NORMAL = |- !n. NORMAL((\N. T),$plus)(int_mult_set n) %


let INT_SBGP_TIMES_CLOSED = prove_thm(`INT_SBGP_TIMES_CLOSED`,
"SUBGROUP((\N.T),$plus)H ==> !m p. H p ==> H (m times p)",
(DISCH_TAC THEN
 (FIRST_ASSUM
   \thm.(STRIP_ASSUME_TAC (PURE_ONCE_REWRITE_RULE[SUBGROUP_DEF] thm))) THEN
 INT_CASES_TAC THENL
 [(INDUCT_TAC THENL
   [((PURE_REWRITE_TAC[TIMES_ZERO;(SYM ID_EQ_0)]) THEN
     (NEW_SUBST1_TAC (SYM (MATCH_MP SBGP_ID_GP_ID
       (ASSUME "SUBGROUP((\N. T),$plus)H")))) THEN
     GROUP_ELT_TAC);
    (GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
     (PURE_REWRITE_TAC[ADD1;(SYM (SPEC_ALL NUM_ADD_IS_INT_ADD))]) THEN
     (PURE_REWRITE_TAC[RIGHT_PLUS_DISTRIB;TIMES_IDENTITY]) THEN
     GROUP_ELT_TAC)]);
  ((REPEAT STRIP_TAC) THEN
   (PURE_ONCE_REWRITE_TAC[neg_IS_TIMES_neg1]) THEN
   (PURE_ONCE_REWRITE_TAC [(SYM (SPEC_ALL ASSOC_TIMES))]) THEN
   (PURE_ONCE_REWRITE_TAC 
    [(PURE_ONCE_REWRITE_RULE[COMM_TIMES]
       (SYM(SPEC_ALL neg_IS_TIMES_neg1)))]) THEN
   (MP_IMP_TAC (SPECL ["n2:num";"neg p"]
     (ASSUME "!n1 p. H p ==> H((INT n1) times p)"))) THEN
   (PURE_ONCE_REWRITE_TAC[neg_DEF]) THEN
   (NEW_SUBST1_TAC (SYM (UNDISCH (SPEC "p:integer"
     (MATCH_MP SBGP_INV_GP_INV (ASSUME "SUBGROUP((\N. T),$plus)H")))))) THEN
   GROUP_ELT_TAC)]));;

%INT_SBGP_TIMES_CLOSED = 
|- SUBGROUP((\N. T),$plus)H ==> (!M p. H p ==> H(M times p))%


let INT_SBGP_CYCLIC = prove_thm(`INT_SBGP_CYCLIC`,
"SUBGROUP((\N.T),$plus)H ==> ? n.(H = int_mult_set (INT n))",
(DISCH_TAC THEN
 (ASSUME_TAC (CONJUNCT2 (REWRITE_RULE [SUBGROUP_DEF]
  (ASSUME "SUBGROUP((\N. T),$plus)H")))) THEN
 (PURE_ONCE_REWRITE_TAC [INT_MULT_SET_DEF]) THEN
 (ASM_CASES_TAC "!m1. (H m1) ==> (m1 = (INT 0))") THENL
 [(EXISTS_TAC "0" THEN
   (EXT_TAC "m1:integer") THEN BETA_TAC THEN
   (REWRITE_TAC [TIMES_ZERO]) THEN
   GEN_TAC THEN EQ_TAC THENL
   [(FIRST_ASSUM (NEW_MATCH_ACCEPT_TAC));
    (DISCH_TAC THEN ASM_REWRITE_TAC[(SYM ID_EQ_0)] THEN
     (SUBST_MATCH_TAC (SYM (UNDISCH SBGP_ID_GP_ID))) THEN
     GROUP_ELT_TAC)]);
  ((POP_ASSUM \thm. STRIP_ASSUME_TAC
    ((CONV_RULE NOT_FORALL_CONV thm) and_then
     (REWRITE_RULE [IMP_DISJ_THM;DE_MORGAN_THM]))) THEN
   ((REV_SUPPOSE_TAC "!m. H m ==> H(neg m)") THENL
     [((REPEAT STRIP_TAC) THEN
       (PURE_ONCE_REWRITE_TAC [neg_DEF]) THEN
      (SUBST_MATCH_TAC (SYM (UNDISCH
        (SPEC_ALL (UNDISCH SBGP_INV_GP_INV))))) THEN
       GROUP_ELT_TAC);
      ALL_TAC]) THEN
   (SUPPOSE_TAC "?k.(POS k)/\ H k") THENL
   [((POP_ASSUM \thm. (STRIP_ASSUME_TAC (CONJUNCT1 (MP (BETA_RULE
       (SPEC "\x.POS x /\ H x" DISCRETE)) thm)))) THEN
     (SUPPOSE_TAC "?K1. !N. N below K1 ==> ~(POS N /\ H N)") THENL
    [((POP_ASSUM \thm1.
         (POP_ASSUM \thm2. (STRIP_ASSUME_TAC (MP thm2 thm1)))) THEN
       (STRIP_ASSUME_TAC
         (PURE_ONCE_REWRITE_RULE[POS_DEF] (ASSUME "POS M1"))) THEN
       (POP_ASSUM \thm.POP_ASSUM_LIST \thl.
         (MAP_EVERY STRIP_ASSUME_TAC (map (REWRITE_RULE [thm]) thl))) THEN
       (EXISTS_TAC "SUC n") THEN
       (EXT_TAC "m:integer") THEN BETA_TAC THEN GEN_TAC THEN
       EQ_TAC THENL
       [((SPEC_TAC ("m:integer","m:integer")) THEN INT_CASES_TAC THENL
         [(GEN_TAC THEN DISCH_TAC THEN
           (DISJ_CASES_TAC (SPEC "n1:num" num_CASES)) THENL
           [((EXISTS_TAC "INT 0") THEN
             (ASM_REWRITE_TAC [TIMES_ZERO]));
            (let S1 = "~(NEG((INT n1) plus (neg(x times (INT(SUC n))))))" in
             ((REV_SUPPOSE_TAC "?x:integer.^S1") THENL
               [((EXISTS_TAC "INT 0") THEN
                 (PURE_ONCE_REWRITE_TAC[neg_IS_TIMES_neg1]) THEN
                 (REWRITE_TAC
                    [TIMES_ZERO;PLUS_ID_LEMMA;NON_NEG_INT_IS_NUM]) THEN
                 (EXISTS_TAC "n1:num") THEN REFL_TAC);
                ALL_TAC]) THEN
             (REV_SUPPOSE_TAC "?y. !x. (y below x) ==> ~(^S1)") THENL
             [((EXISTS_TAC "INT n1") THEN
               (REWRITE_TAC [BELOW_DEF;MINUS_DEF]) THEN
               (PURE_ONCE_REWRITE_TAC[POS_DEF]) THEN
               (REPEAT STRIP_TAC) THEN
               (POP_ASSUM \thm. (STRIP_ASSUME_TAC 
                ((AP_TERM "\z. z plus (INT n1)" thm) and_then
                 BETA_RULE and_then 
                 (REWRITE_RULE
                   [PLUS_GROUP_ASSOC;PLUS_INV_LEMMA;PLUS_ID_LEMMA]) and_then
                 (PURE_ONCE_REWRITE_RULE [COMM_PLUS])))) THEN
               (ASM_REWRITE_TAC
                  [RIGHT_PLUS_DISTRIB;neg_PLUS_DISTRIB;ASSOC_PLUS]) THEN
               (NEW_SUBST1_TAC
                  (PURE_ONCE_REWRITE_RULE [ADD_SYM] (SPEC "n:num" ADD1))) THEN
               (PURE_REWRITE_TAC
                 [(SYM (SPEC_ALL NUM_ADD_IS_INT_ADD));
                  LEFT_PLUS_DISTRIB; TIMES_IDENTITY; 
                  neg_PLUS_DISTRIB; ASSOC_PLUS;
                  PLUS_INV_LEMMA; PLUS_ID_LEMMA]) THEN
               (REWRITE_TAC
                 [PLUS_DIST_INV_LEMMA;NUM_ADD_IS_INT_ADD;NUM_MULT_IS_INT_MULT;
                  ADD_CLAUSES;NEG_DEF;PLUS_INV_INV_LEMMA;POS_DEF]) THEN
               (\ (asl,gl).(EXISTS_TAC
                   (rand (rand (lhs (snd (dest_exists gl))))) (asl,gl))) THEN
               REFL_TAC);
              ((POP_ASSUM \thm1. POP_ASSUM \thm2. STRIP_ASSUME_TAC
                 (ONCE_REWRITE_RULE [] (MP (CONJUNCT2 (MP (BETA_RULE 
                  (SPEC "\x:integer.^S1" DISCRETE)) thm2)) thm1))) THEN
               (EXISTS_TAC "M1:integer") THEN
               (MATCH_MP_IMP_TAC
                 (SPEC_ALL (SPEC "neg(M1 times (INT(SUC n)))"
                   PLUS_RIGHT_CANCELLATION))) THEN
               (PURE_ONCE_REWRITE_TAC[PLUS_INV_LEMMA]) THEN
               (DISJ_CASES_THENL
                 [ASSUME_TAC;(\thm.(ASSUME_TAC thm) THEN RES_TAC); ACCEPT_TAC]
                 (CONJUNCT1 (SPEC "(INT n1) plus (neg(M1 times (INT(SUC n))))"
                    TRICHOTOMY))) THEN
               (use_thm (UNDISCH (REWRITE_RULE
                 [(ASSUME "POS((INT n1) plus (neg(M1 times (INT(SUC n)))))")]
                 (CONTRAPOS (SPEC "(INT n1) plus (neg(M1 times (INT(SUC n))))"
                   (ASSUME "!N1. N1 below (INT(SUC n)) ==>
                     ~(POS N1 /\ H N1)")))))
                 ASSUME_TAC) THENL
               [((POP_ASSUM \thm. STRIP_ASSUME_TAC
                   ((REWRITE_RULE
                     [BELOW_DEF;MINUS_DEF;neg_PLUS_DISTRIB;PLUS_INV_INV_LEMMA;
                      (SPECL["neg(INT n1)";"M1 times (INT(SUC n))"] COMM_PLUS);
                      ASSOC_PLUS] thm) and_then
                    (SUBS_OCCS [([1],(SYM(CONJUNCT2(SPEC "INT (SUC n)"
                       TIMES_IDENTITY))))]) and_then
                    (REWRITE_RULE
                      [(SYM (SPEC_ALL RIGHT_PLUS_DISTRIB))]) and_then
                   (SUBS
                     [(SYM (SPEC
                       "(((INT 1)plus M1) times (INT(SUC n)))plus(neg(INT n1))"
                        PLUS_INV_INV_LEMMA))]) and_then
                   (REWRITE_RULE [(SYM (SPEC_ALL NEG_DEF));
                                  (SYM (SPEC_ALL PLUS_DIST_INV_LEMMA));
                                  PLUS_INV_INV_LEMMA]))) THEN
                 (IMP_RES_TAC (CONTRAPOS (SPEC "(INT 1) plus M1" (ASSUME
                   "!N1. M1 below N1 ==>
                      NEG((INT n1) plus (neg(N1 times (INT(SUC n)))))")))) THEN
                 ((SUPPOSE_TAC "M1 below ((INT 1) plus M1)") THENL
                    [RES_TAC; ALL_TAC]) THEN
                 (REWRITE_TAC [BELOW_DEF; MINUS_DEF; POS_DEF]) THEN
                 (REWRITE_TAC
                    [PLUS_GROUP_ASSOC;PLUS_INV_LEMMA;PLUS_ID_LEMMA;ADD1]) THEN
                 (EXISTS_TAC "0") THEN
                 (REWRITE_TAC [ADD_CLAUSES]));
                (GROUP_TAC[(UNDISCH INT_SBGP_TIMES_CLOSED);
                   (ASSUME "!m. H m ==> H(neg m)")])])])]);
          ((REPEAT STRIP_TAC) THEN
           (IMP_RES_TAC (ASSUME "!m. H m ==> H(neg m)")) THEN
           (STRIP_ASSUME_TAC (REWRITE_RULE [PLUS_INV_INV_LEMMA]
             (ASSUME "H(neg(neg(INT n2))):bool"))) THEN
           (STRIP_ASSUME_TAC (MP (SPEC "n2:num"
            (ASSUME "!n1. H(INT n1) ==> (?p. INT n1 = p times (INT(SUC n)))"))
            (ASSUME "H(INT n2):bool"))) THEN
           (EXISTS_TAC "neg p") THEN
           (ASM_REWRITE_TAC [TIMES_neg]))]);
        ((REPEAT STRIP_TAC) THEN (ASM_REWRITE_TAC []) THEN
         (MATCH_MP_IMP_TAC (SPEC_ALL (UNDISCH INT_SBGP_TIMES_CLOSED))) THEN
         (FIRST_ASSUM ACCEPT_TAC))]);
      ((EXISTS_TAC "INT 0") THEN
       (REWRITE_TAC [BELOW_DEF;MINUS_DEF;PLUS_ID_LEMMA;
         (SYM (SPEC_ALL NEG_DEF))]) THEN
       (REPEAT STRIP_TAC) THEN
       (STRIP_ASSUME_TAC
         (CONJUNCT1 (CONJUNCT2 (SPEC "N:integer" TRICHOTOMY)))) THEN
       RES_TAC)]);
   (DISJ_CASES_THENL 
       [\thm.((EXISTS_TAC "m1:integer") THEN (ASM_REWRITE_TAC [thm]));
        \thm.((EXISTS_TAC "neg m1") THEN RES_TAC THEN
          (ASM_REWRITE_TAC [thm;(SYM (SPEC_ALL NEG_DEF))]));
        \thm.((ASSUME_TAC thm) THEN RES_TAC)]
        (CONJUNCT1 (SPEC "m1:integer" TRICHOTOMY)))])]));;

%INT_SBGP_CYCLIC = 
 |- SUBGROUP((\N. T),$plus)H ==> (?n. H = int_mult_set(INT n)) %


close_theory ();;		% arg is void [TFM 90.06.12] %

quit();;
