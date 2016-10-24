
%----------------------------------------------------------------------------
|                                                                           |
| FILE: lnum.ml                                                             |
|                                                                           |
| AUTHOR: G TREDOUX                                                         |
|                                                                           |
| DESCRIPTION:                                                              |
| Defines numbers to represent lengths of exseqs, with an                   |
| appropriate ordering. This allows a uniform implementation                |
| of exseqs.                                                                |
----------------------------------------------------------------------------%

new_theory `lnum`;;

load_library `more_arithmetic`;;
load_library `taut`;;
load_library `reduce`;;

loadf `mytactics`;;
loadf `l_arith_hack`;;
loadf `l_cpo`;;

let lnum = define_type `lnum` `lnum = WHOLE num | FRAG num | OO`;;

%
| lnum_cases =
| |- !l. (?n. l = WHOLE n) \/ (?n. l = FRAG n) \/ (l = OO)
| : thm
|
| lnum_const_dist =
| |- (!n n'. ~(WHOLE n = FRAG n')) /\
|    (!n. ~(WHOLE n = OO)) /\
|    (!n. ~(FRAG n = OO))
| : thm
%

let lnum_cases = prove_cases_thm (prove_induction_thm lnum);;

let lnum_const_dist = prove_constructors_distinct lnum;;
let lnum_const_one_one = prove_constructors_one_one lnum;;

save_thm (`lnum_cases`,lnum_cases);;
save_thm (`lnum_const_dist`,lnum_const_dist);;
save_thm (`lnum_const_one_one`,lnum_const_one_one);;

letrec lnum_cases_TAC l =
        if null l then ALL_TAC else
        REPEAT GEN_TAC
        THEN STRUCT_CASES_TAC (SPEC (hd l) lnum_cases)
        THEN lnum_cases_TAC (tl l);;

let is_WHOLE =
        new_recursive_definition false lnum `is_WHOLE`
        "(is_WHOLE (WHOLE n) = T) /\
         (is_WHOLE (FRAG n) = F) /\
         (is_WHOLE OO = F)";;

let is_OO =
        new_recursive_definition false lnum `is_OO`
        "(is_OO (WHOLE n) = F) /\
         (is_OO (FRAG n) = F) /\
         (is_OO OO = T)";;

let is_FRAG =
        new_recursive_definition false lnum `is_FRAG`
        "(is_FRAG (WHOLE n) = F) /\
         (is_FRAG (FRAG n) = T) /\
         (is_FRAG OO = F)";;

let lnum_cases2 = prove_thm (
        `lnum_cases2`,
        "!l. is_WHOLE l \/ is_FRAG l \/ is_OO l",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;is_FRAG;is_OO]
);;

let lnum_cases4 = prove_thm (
        `lnum_cases4`,
        "!l. (~ is_WHOLE l) = (is_FRAG l \/ is_OO l)",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;is_FRAG;is_OO]
);;

let WHOLE_dest =
        new_recursive_definition false lnum `WHOLE_dest`
        "WHOLE_dest (WHOLE n) = n";;

let FRAG_dest =
        new_recursive_definition false lnum `FRAG_dest`
        "FRAG_dest (FRAG n) = n";;

new_special_symbol `<+`;;
new_special_symbol `<-+`;;

%
| Define the extension orderings <+ and <-+
%

let lnum_less_eq = new_infix_definition (
  `lnum_less_eq`,
  "!l m:lnum. <-+ l m =
        (is_WHOLE l /\ is_WHOLE m /\ (WHOLE_dest l <= WHOLE_dest m))
        \/ (is_WHOLE l /\ is_FRAG m /\ (WHOLE_dest l < FRAG_dest m))
        \/ (is_WHOLE l /\ is_OO m)
        \/ (l = m)"
);;

let lnum_less = new_infix_definition
 (
  `lnum_less`,
  "!l m:lnum. <+ l m = (l <-+ m) /\ ~(l=m)"
 );;


let lnum_less_reduce = prove_thm (
        `lnum_less_reduce`,
        "!n m.
         (WHOLE n <+ WHOLE m = n < m) /\
         (WHOLE n <+ FRAG m = n < m) /\
         (WHOLE n <+ OO = T)",
         REWRITE_TAC
                [lnum_less_eq
                ;lnum_less
                ;is_WHOLE
                ;lnum_const_dist
                ;lnum_const_one_one
                ;SYM_th lnum_const_dist
                ;is_FRAG
                ;WHOLE_dest
                ;FRAG_dest
                ;is_OO
                ]
        THEN REWRITE_TAC [LESS_AS_LESS_EQ;RIGHT_AND_OVER_OR]
        THEN REPEAT GEN_TAC
        THEN TAUT_TAC
);;

let lnum_less_eq_reduce = prove_thm (
        `lnum_less_eq_reduce`,
        "!n m.
         (WHOLE n <-+ WHOLE m = n <= m) /\
         (WHOLE n <-+ FRAG m = n < m) /\
         (WHOLE n <-+ OO = T) /\
         (OO <-+ OO = T) /\
         ((FRAG m <-+ FRAG n) = (m = n))",
         REWRITE_TAC
                [lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;WHOLE_dest
                ;FRAG_dest
                ;is_OO
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;lnum_const_one_one
                ]
        THEN REPEAT GEN_TAC
        THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[LESS_OR_EQ]
);;

let lnum_not_less_eq = prove_thm (
        `lnum_not_less_eq`,
        "!m n.
         (FRAG m <-+ WHOLE n = F) /\
         (OO <-+ FRAG m = F) /\
         (OO <-+ WHOLE m = F) /\
         (FRAG m <-+ OO = F)",
        REWRITE_TAC
                [lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;WHOLE_dest
                ;FRAG_dest
                ;is_OO
                ;lnum_const_one_one
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ]
);;

let lnum_not_less = prove_thm (
        `lnum_not_less`,
        "!l m n.
         (FRAG m <+ WHOLE n = F) /\
         (FRAG m <+ FRAG n = F) /\
         (OO <+ FRAG m = F) /\
         (OO <+ WHOLE m = F) /\
         (FRAG m <+ OO = F) /\
         (l <+ l = F)",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [lnum_less
                ;lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;WHOLE_dest
                ;FRAG_dest
                ;is_OO
                ;lnum_const_one_one
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;DE_MORGAN_THM
                ]
        THEN ONCE_REWRITE_TAC [DISJ_SYM]
        THEN REWRITE_TAC [EXCLUDED_MIDDLE]
);;

let lnum_less_eq_top = prove_thm(
        `lnum_less_eq_top`,
        "!l. is_WHOLE l ==> (l <-+ OO)",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;lnum_less_eq_reduce
                ]
);;

let lnum_less_imp_less_eq = prove_thm (
        `lnum_less_imp_less_eq`,
        "!l1 l2. l1 <+ l2 ==> l1 <-+ l2",
        REWRITE_TAC [lnum_less]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
);;

let lnum_less_plus = prove_thm
(       `lnum_less_plus`,
        "!l.
         is_WHOLE l ==>
         WHOLE 1 <+ l ==> WHOLE 2 <-+ l",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;lnum_less_reduce
                ;lnum_less_eq_reduce
                ]
        THEN DISCH_TAC
        THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
        THEN IMP_RES_TAC LESS_EQ
);;


%
| Prove that <-+ is a partial order and that <+ is transitive
%

let lnum_less_trans = prove_thm (
        `lnum_less_trans`,
        "trans $<+",
        REWRITE_TAC [trans]
        THEN lnum_cases_TAC ["d1:lnum";"d2:lnum";"d3:lnum"]
        THEN REWRITE_TAC
                [lnum_less_reduce
                ;lnum_not_less
                ;LESS_TRANS
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;lnum_const_one_one
                ;lnum_less
                ;lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;is_OO
                ]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
);;

let lnum_less_trans_alt = save_thm
        (`lnum_less_trans_alt`
        ,REWRITE_RULE [trans] lnum_less_trans
        );;

let lnum_less_eq_refl = prove_thm (
        `lnum_less_eq_refl`,
        "refl $<-+",
        REWRITE_TAC [refl]
        THEN lnum_cases_TAC ["d:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq_reduce
                ;lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;is_OO
                ;LESS_EQ_REFL
                ]
);;

let lnum_less_eq_antisym = prove_thm (
        `lnum_less_eq_antisym`,
        "antisym $<-+",
        REWRITE_TAC [antisym]
        THEN lnum_cases_TAC ["d1:lnum";"d2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq_reduce
                ;lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;is_OO
                ;lnum_const_one_one
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;LESS_EQUAL_ANTISYM
                ]
        THEN REPEAT STRIP_TAC
        THEN ASSUM_REDUCE_TAC
);;


let lnum_less_eq_trans = prove_thm (
        `lnum_less_eq_trans`,
        "trans $<-+",
        REWRITE_TAC [trans]
        THEN lnum_cases_TAC ["d1:lnum";"d2:lnum";"d3:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq
                ;is_WHOLE
                ;is_FRAG
                ;is_OO
                ;lnum_less_eq_reduce
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;lnum_const_one_one
                ]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THENL   [IMP_RES_TAC LESS_EQ_TRANS
                ;IMP_RES_TAC LESS_EQ_LESS_TRANS
                ;FIRST_ASSUM SUBST_ALL_TAC
                 THEN ASSUM_REDUCE_TAC
                ]
);;

let lnum_less_eq_partial_order = prove_thm (
        `lnum_less_eq_partial_order`,
        "partial_order $<-+",
        REWRITE_TAC
                [partial_order
                ;lnum_less_eq_trans
                ;lnum_less_eq_antisym
                ;lnum_less_eq_refl
                ]
);;

let lnum_less_eq_po = save_thm (
        `lnum_less_eq_po`,
         REWRITE_RULE
                [partial_order
                ;trans
                ;antisym
                ;refl
                ]
                lnum_less_eq_partial_order
);;

let lnum_less_eq_as_less = prove_thm (
        `lnum_less_eq_as_less`,
        "!l1 l2. l1 <-+ l2 = l1 <+ l2 \/ (l1=l2)",
        REPEAT GEN_TAC
        THEN REWRITE_TAC
                [lnum_less
                ;RIGHT_OR_OVER_AND
                ;ONCE_REWRITE_RULE [DISJ_SYM] EXCLUDED_MIDDLE
                ]
        THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[lnum_less_eq_po]
);;

let lnum_less_less_eq_trans = prove_thm (
        `lnum_less_less_eq_trans`,
        "!l1 l2 l3. l1 <+ l2 ==> l2 <-+ l3 ==> l1 <+ l3",
        REWRITE_TAC [lnum_less_eq_as_less]
        THEN REPEAT STRIP_TAC
        THENL   [IMP_RES_TAC lnum_less_trans_alt
                ;FIRST_ASSUM SUBST_ALL_TAC
                 THEN ASSUM_REDUCE_TAC
                ]
);;

let lnum_less_eq_less_trans = prove_thm
(       `lnum_less_eq_less_trans`,
        "!l1 l2 l3. l1 <-+ l2 ==> l2 <+ l3 ==> l1 <+ l3",
        REWRITE_TAC [lnum_less_eq_as_less]
        THEN REPEAT STRIP_TAC
        THENL   [IMP_RES_TAC lnum_less_trans_alt
                ;FIRST_ASSUM SUBST_ALL_TAC
                 THEN ASSUM_REDUCE_TAC
                ]
);;

%
| Prove that lnum is a cpo, ie. chains have lubs
%

let lemma = PROVE (
        "!l m. (is_FRAG l \/ is_OO l) ==> (l <-+ m) ==> (l=m)",
        lnum_cases_TAC ["l:lnum";"m:lnum"]
        THEN REWRITE_TAC
                [is_FRAG
                ;lnum_less_eq
                ;lnum_less_eq_reduce
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;lnum_const_one_one
                ;is_WHOLE
                ;is_OO
                ]
);;

let lemma2 = PROVE (
        "!C. chain $<-+ C ==> (?n. ~is_WHOLE (C n)) ==> stunt_chain $<-+ C",
        REWRITE_TAC [stunt_chain;is_ub;lnum_cases4]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
        THEN EXISTS_TAC "n:num"
        THEN GEN_TAC
        THEN ASSUME_TAC (MATCH_MP chain_less_eq lnum_less_eq_partial_order)
        THEN FIRST_ASSUM SUBST_ALL_TAC
        THEN DISJ_CASES_SPLIT "n <= n'"
        THENL   [RES_TAC
                 THEN IMP_RES_TAC lemma
                 THEN ASM_REWRITE_TAC[REWRITE_RULE [refl] lnum_less_eq_refl]
                ;IMP_RES_TAC LESS_EQ_SYM
                 THEN RES_TAC
                ;RES_TAC
                 THEN IMP_RES_TAC lemma
                 THEN ASM_REWRITE_TAC[REWRITE_RULE [refl] lnum_less_eq_refl]
                ;IMP_RES_TAC LESS_EQ_SYM
                 THEN RES_TAC
                ]
);;

let lemma3 = PROVE (
         "!C. chain $<-+ C ==> ~stunt_chain $<-+ C ==> (!n. is_WHOLE (C n))",
        GEN_TAC
        THEN DISCH_TAC
        THEN CONTRAPOS_TAC
        THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
        THEN IMP_RES_TAC lemma2
        THEN DISCH_THEN CHOOSE_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
);;

let lemma4 = PROVE (
        "!C:num->lnum.
         chain $<-+ C ==>
         ~stunt_chain  $<-+C ==>
         (!l. is_WHOLE l ==> ?n. l <-+ C n /\ ~(C n = l))",
         GEN_TAC
         THEN REPEAT DISCH_TAC
         THEN ASSUME_TAC lnum_less_eq_partial_order
         THEN lnum_cases_TAC ["l:lnum"]
         THEN REWRITE_TAC [is_WHOLE]
         THEN SPEC_TAC ("n:num","n:num")
         THEN IMP_RES_TAC not_stunt_chain
         THEN IMP_RES_TAC lemma3
         THEN INDUCT_TAC
         THENL  [DISJ_CASES_SPLIT "C 0 = WHOLE 0"
                 THENL  [FIRST_ASSUM (CHOOSE_TAC o (SPEC "0"))
                         THEN EXISTS_TAC "m:num"
                         THEN FIRST_ASSUM SUBST_ALL_TAC
                         THEN FIRST_ASSUM (ASSUME_TAC o SPEC_ALL)
                         THEN ASSUM_LIST (REWRITE_TAC o SYML_th)
                        ;EXISTS_TAC "0"
                                                 THEN ASM_REWRITE_TAC[]
                         THEN APPLY_TO "!n:num. is_WHOLE(C n)"
                                (MP_TAC o (SPEC "0"))
                         THEN lnum_cases_TAC ["(C:num->lnum) 0"]
                         THEN REWRITE_TAC [is_WHOLE]
                         THEN REWRITE_TAC[lnum_less_eq_reduce;ZERO_LESS_EQ]
                        ]
                ;FIRST_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
                 THEN FIRST_ASSUM ((CHOOSE_THEN STRIP_ASSUME_TAC) o (SPEC "n':num"))
                 THEN EXISTS_TAC "m:num"
                 THEN APPLY_TO "!n:num. is_WHOLE(C n)"
                        (FORK (MP_TAC o (SPEC "m:num")) (MP_TAC o (SPEC "n':num")))
                 THEN UNDISCH_ALL_TAC
                 THEN lnum_cases_TAC ["(C:num->lnum) m"]
                 THEN lnum_cases_TAC ["(C:num->lnum) n'"]
                 THEN REWRITE_TAC
                        [is_WHOLE
                        ;lnum_less_eq_reduce
                        ;lnum_const_one_one
                        ;LESS_OR_EQ]
                 THEN REPEAT STRIP_TAC
                 THEN RES_TAC
                 THENL  [IMP_RES_TAC LESS_OR
                         THEN IMP_RES_TAC LESS_EQ_LESS_TRANS
                         THEN ASM_REWRITE_TAC[]
                        ;FIRST_ASSUM SUBST_ALL_TAC
                         THEN IMP_RES_TAC LESS_SUC_NOT
                        ;FIRST_ASSUM SUBST_ALL_TAC
                         THEN RES_TAC
                        ;FIRST_ASSUM SUBST_ALL_TAC
                         THEN REPLACE_ASSUM
                                "n=n''':num"
                                SYM_th
                         THEN RES_TAC
                        ]
                ]
);;

let not_stunt_chain_lub_OO = prove_thm (
        `not_stunt_chain_lub_OO`,
        "!C:num->lnum.
         chain $<-+ C ==>
         ~stunt_chain  $<-+ C ==>
         is_lub $<-+ OO C",
        REWRITE_TAC [is_lub;is_ub]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC lemma3
        THENL   [FIRST_ASSUM (MP_TAC o SPEC_ALL)
                 THEN lnum_cases_TAC ["(C:num->lnum) n"]
                 THEN REWRITE_TAC [is_WHOLE;lnum_less_eq_reduce]
                ;IMP_RES_TAC lemma4
                 THEN UNDISCH_ALL_TAC
                 THEN lnum_cases_TAC ["k:lnum"]
                 THEN REWRITE_TAC
                        [REWRITE_RULE [refl] lnum_less_eq_refl
                        ;lnum_const_dist
                        ;SYM_th lnum_const_dist
                        ]
                 THEN REPEAT DISCH_TAC
                 THEN FIRST_ASSUM (MP_TAC o (SPEC "WHOLE n"))
                 THEN REWRITE_TAC [is_WHOLE]
                 THEN DISCH_THEN STRIP_ASSUME_TAC
                 THEN MAPFILTER_ASSUM (MP_TAC o (SPEC "n':num"))
                 THEN UNDISCH_ALL_TAC
                 THEN lnum_cases_TAC ["(C:num->lnum) n'"]
                 THEN REWRITE_TAC
                        [is_WHOLE
                        ;lnum_less_eq_reduce
                        ;lnum_const_one_one
                        ;lnum_const_dist
                        ;SYM_th lnum_const_dist
                        ;lnum_not_less_eq
                        ]
                 THEN REPEAT DISCH_TAC
                 THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
                 THEN RES_TAC
                 THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
                 THEN RES_TAC
                 THEN RES_TAC
                ]
);;

let lnum_cpo = prove_thm (
        `lnum_cpo`,
        "cpo $<-+",
        REWRITE_TAC [cpo;lnum_less_eq_partial_order;lub]
        THEN CONV_TAC (DEPTH_CONV SELECT_CONV)
        THEN REPEAT STRIP_TAC
        THEN DISJ_CASES_SPLIT "stunt_chain $<-+ (C:num->lnum)"
        THENL   [IMP_RES_TAC stunt_chain_lub
                 THEN EXISTS_TAC "(C:num->lnum) n"
                 THEN ASM_REWRITE_TAC[]
                ;EXISTS_TAC "OO"
                 THEN IMP_RES_TAC not_stunt_chain_lub_OO
                ]
);;

let stunted_lub = prove_thm (
        `stunted_lub`,
        "!C. chain $<-+ C ==> !i. ~is_WHOLE(C i) ==> (lub $<-+ C = C i)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC (REWRITE_RULE[cpo;is_ub;is_lub] lnum_cpo)
        THEN REWRITE_ASM [lnum_cases4]
        THEN FIRST_ASSUM (ASSUME_TAC o (SPEC "i:num"))
        THEN FIRST_ASSUM DISJ_CASES_TAC
        THEN IMP_RES_TAC lemma
        THEN ASM_REWRITE_TAC[]
);;

let cpo_lemma = REWRITE_RULE [cpo;is_lub;is_ub] lnum_cpo;;

let lemma5 = PROVE
(       "!Ch l.
         chain $<-+ Ch ==>
         l <+ (lub $<-+ Ch) ==> ~!i. Ch i <-+ l",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC cpo_lemma
        THEN IMP_RES_TAC lnum_less_less_eq_trans
        THEN IMP_RES_TAC lnum_not_less
);;

let lemma6 = PROVE
(       "!l n. is_WHOLE l ==> ~ l <-+ WHOLE n ==> WHOLE n <+ l",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;lnum_less_reduce
                ;lnum_less_eq_reduce
                ;SYM_th NOT_LESS
                ]
);;

let converge_lub = prove_thm
(       `converge_lub`,
        "!Ch n. chain $<-+ Ch ==>
          WHOLE n <+ (lub $<-+ Ch) ==>
                ?i. WHOLE n <+ (Ch i)",
        REPEAT GEN_TAC
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC lemma5
        THEN UNDISCH_ALL_TAC
        THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
        THEN REPEAT STRIP_TAC
        THEN DISJ_CASES_SPLIT "lub $<-+ Ch = Ch i"
        THENL   [EXISTS_TAC "i:num"
                 THEN ASSUM_LIST (REWRITE_TAC o SYML_th)
                ;IMP_RES_TAC cpo_lemma
                 THEN IMP_RES_TAC stunted_lub
                 THEN FIRST_ASSUM
                        (ASSUME_TAC
                        o (CONV_RULE CONTRAPOS_CONV)
                        o (SPEC "i:num")
                        )
                 THEN RES_TAC
                 THEN REWRITE_ASM[]
                 THEN IMP_RES_TAC lemma6
                 THEN EXISTS_TAC "i:num"
                 THEN ASM_REWRITE_TAC[]
                ]
);;

let whole_lub = prove_thm
(       `whole_lub`,
        "!C.
         chain $<-+ C ==>
         is_WHOLE (lub $<-+ C) ==>
         stunt_chain $<-+ C",
        GEN_TAC
        THEN DISCH_TAC
        THEN CONTRAPOS_TAC
        THEN DISCH_TAC
        THEN IMP_RES_TAC not_stunt_chain_lub_OO
        THEN STRIP_ASSUME_TAC
                (REWRITE_RULE[cpo] lnum_cpo)
        THEN FIRST_ASSUM (ASSUME_TAC o SPEC_ALL)
        THEN RES_TAC
        THEN IMP_RES_TAC lub_unique
        THEN POP_IT "OO=OO"
        THEN ONCE_ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[is_WHOLE]
);;

let is_FRAG_choose = prove_thm
(       `is_FRAG_choose`,
        "!l. is_FRAG l ==> ?n. l = FRAG n",
        GEN_TAC
        THEN lnum_cases_TAC["l:lnum"]
        THEN REWRITE_TAC[is_FRAG]
        THEN EXISTS_TAC "n:num"
        THEN REFL_TAC
);;

let is_WHOLE_choose = prove_thm
(       `is_WHOLE_choose`,
        "!l. is_WHOLE l = ?n. l = WHOLE n",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN CONV_TAC(TRY_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC [lnum_const_dist;SYM_th lnum_const_dist]
        THEN EXISTS_TAC "n:num"
        THEN REFL_TAC
);;

let is_OO_choose = prove_thm
(       `is_OO_choose`,
        "!l. is_OO l = (l = OO)",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_OO;lnum_const_dist;SYM_th lnum_const_dist]
);;

let frag_lub = prove_thm
(       `frag_lub`,
        "!C.
         chain $<-+ C ==>
         (!n:num. ~is_FRAG(C n)) ==>
         ~is_FRAG(lub $<-+ C)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC is_FRAG_choose
        THEN ASM_CASES_TAC "!n:num. is_WHOLE (C n)"
        THENL   [ASM_CASES_TAC "stunt_chain $<-+ C"
                 THENL  [RULE_ASSUM_TAC
                                (REWRITE_RULE[stunt_chain])
                         THEN EVERY_ASSUM STRIP_ASSUME_TAC
                         THEN IMP_RES_TAC
                                (REWRITE_RULE[cpo;is_lub]lnum_cpo)
                         THEN IMP_RES_TAC lemma
                         THEN FIRST_ASSUM(ASSUME_TAC o (SPEC "n':num"))
                         THEN IMP_RES_TAC is_WHOLE_choose
                         THEN UNDISCH_TAC  "lub $<-+ C = C n'"
                         THEN POP_IT  "lub $<-+ C = lub $<-+ C"
                         THEN ASM_REWRITE_TAC[SYM_th lnum_const_dist]
                        ;IMP_RES_TAC not_stunt_chain_lub_OO
                         THEN ASSUME_TAC lnum_less_eq_partial_order
                         THEN IMP_RES_TAC lub_eq
                         THEN REWRITE_ASM[SYM_th lnum_const_dist]
                         THEN ASM_REWRITE_TAC[]
                        ]
                ;RULE_ASSUM_TAC(CONV_RULE (TRY_CONV NOT_FORALL_CONV))
                 THEN EVERY_ASSUM STRIP_ASSUME_TAC
                 THEN FIRST_ASSUM(ASSUME_TAC o (SPEC "n':num"))
                 THEN IMP_RES_TAC lnum_cases4
                 THEN RES_TAC
                 THEN IMP_RES_TAC(REWRITE_RULE[cpo;is_lub;is_ub]lnum_cpo)
                 THEN MAPFILTER_ASSUM(ASSUME_TAC o (SPEC "n':num"))
                 THEN IMP_RES_TAC lemma
                 THEN UNDISCH_TAC  "C n' = lub $<-+ C"
                 THEN POP_IT  "lub $<-+ C = lub $<-+ C"
                 THEN IMP_RES_TAC is_OO_choose
                 THEN ASM_REWRITE_TAC[SYM_th lnum_const_dist]
                ]
);;

%
| Define addition of lengths. Lengths can only be added where this is sensible,
| that is when one of them is WHOLE.
|
| This has to be defined in steps to get around
| the limitations of HOL's recursive defn facilities
%

let WHOLE_plus = new_recursive_definition true lnum `WHOLE_plus`
        "(!n m:num. WHOLE_plus m (WHOLE n) = WHOLE (m+n)) /\
         (!n m:num. WHOLE_plus m (FRAG n) = FRAG (m+n)) /\
         (!n m:num. WHOLE_plus m OO = OO)";;

let FRAG_plus = new_recursive_definition true lnum `FRAG_plus`
        "(!n m:num. FRAG_plus m (WHOLE n) = FRAG (m+n)) /\
         (!n m:num. FRAG_plus m (FRAG n) = FRAG (m+n)) /\
         (!n m:num. FRAG_plus m OO = OO)";;

let OO_plus = new_recursive_definition false lnum `OO_plus`
        "(!n:num. OO_plus (WHOLE n) = OO) /\
         (!n:num. OO_plus (FRAG n) = OO) /\
         (OO_plus OO = OO)";;

new_special_symbol `++`;;

let lnum_plus_parts = new_recursive_definition true lnum `lnum_plus_parts`
        "(!l.!n:num. ++ (WHOLE m) l = m WHOLE_plus l) /\
         (!l.!m:num. ++ (FRAG m) l = m FRAG_plus l) /\
         (!l. ++ OO l = OO_plus l)";;

let lnum_plus = prove_thm (
        `lnum_plus`,
        "!m n:num.
         ((WHOLE m) ++ (WHOLE n) = (WHOLE (m+n))) /\
         ((WHOLE m) ++ (FRAG n) = (FRAG (m+n))) /\
         ((WHOLE m) ++ OO = OO) /\
         ((FRAG m) ++ (FRAG n) = FRAG (m+n)) /\
         ((FRAG m) ++ (WHOLE n) = FRAG (m+n)) /\
         ((FRAG m) ++ OO = OO) /\
         (OO ++ (WHOLE n) = OO) /\
         (OO ++ (FRAG n) = OO) /\
         (OO ++ OO = OO)",
        REWRITE_TAC
                [lnum_plus_parts
                ;WHOLE_plus
                ;FRAG_plus
                ;OO_plus
                ]
);;

%
| Define subtraction partially, leaving some cases unspecified
%

let WHOLE_sub = new_recursive_definition true lnum `WHOLE_sub`
        "(!n m:num. WHOLE_sub m (WHOLE n) = WHOLE (m-n))";;

let FRAG_sub = new_recursive_definition true lnum `FRAG_sub`
        "(!n m:num. FRAG_sub m (WHOLE n) = FRAG (m-n))";;

let OO_sub = new_recursive_definition false lnum `OO_sub`
        "(!n:num. OO_sub (WHOLE n) = OO)";;

new_special_symbol `--`;;

let lnum_sub_parts = new_recursive_definition true lnum `lnum_sub_parts`
        "(!l.!n:num. -- (WHOLE m) l = m WHOLE_sub l) /\
         (!l.!m:num. -- (FRAG m) l = m FRAG_sub l) /\
         (!l.!m:num. -- OO l = OO_sub l)";;

let lnum_sub = prove_thm (
        `lnum_sub`,
        "!m n:num.
         ((WHOLE m) -- (WHOLE n) = (WHOLE (m-n))) /\
         ((FRAG m) -- (WHOLE n) = (FRAG (m-n))) /\
         (OO -- (WHOLE m) = OO)",
        REWRITE_TAC
                [lnum_sub_parts
                ;WHOLE_sub
                ;FRAG_sub
                ;OO_sub
                ]
);;

%
| A useful special case is subtraction by (WHOLE 1)
%

let PR_fn = new_definition(
        `PR_fn`,
        "!l. PR l = l -- (WHOLE 1)"
);;

let PR = prove_thm (
        `PR`,
        "(!n. PR(WHOLE n) = (WHOLE (n-1))) /\
         (!n. PR(FRAG n) = (FRAG (n-1))) /\
         (PR OO = OO)",
        REWRITE_TAC [PR_fn;lnum_sub]
);;

%
| A useful special case is addition by (WHOLE 1)
%

let SC_fn = new_definition(
        `SC_fn`,
        "!l. SC l = l ++ (WHOLE 1)"
);;

let SC = prove_thm (
        `SC`,
        "(!n. SC(WHOLE n) = (WHOLE (n+1))) /\
         (!n. SC(FRAG n) = (FRAG (n+1))) /\
         (SC OO = OO)",
        REWRITE_TAC [SC_fn;lnum_plus]
);;

let fin_dest = new_recursive_definition false lnum `fin_dest`
        "(!m. fin_dest (WHOLE m) = m) /\
         (!m. fin_dest (FRAG m) = m)";;


%
| Prove some useful theorems about simple arithmetic
%


let lnum_plus_id = prove_thm (
        `lnum_plus_id`,
        "!l.
         (l ++ (WHOLE 0) = l) /\ ((WHOLE 0) ++ l = l)",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [lnum_plus;ADD_0]
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN REWRITE_TAC [ADD_0]
);;

let lnum_plus_com = prove_thm (
        `lnum_plus_com`,
        "!l1 l2.
         l1 ++ l2 = l2 ++ l1",
        lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC [lnum_plus]
        THEN ONCE_RIGHT_SUBST_TAC ADD_SYM
        THEN REWRITE_TAC []
);;

let lnum_plus_sym = prove_thm (
        `lnum_plus_sym`,
        "!l m.
         l ++ (WHOLE m) = (WHOLE m) ++ l",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [lnum_plus]
        THEN ONCE_RIGHT_SUBST_TAC ADD_SYM
        THEN REWRITE_TAC []
);;

let lnum_plus_sym1 = prove_thm (
        `lnum_plus_sym1`,
        "!l m. is_WHOLE l ==> (l ++ m = m ++ l)",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;lnum_plus_sym]
);;

%
let lnum_plus_assoc = prove_thm (
        `lnum_plus_assoc`,
        "!l m n.
         (((WHOLE n) ++ ((WHOLE m) ++ l)) = (((WHOLE n) ++ (WHOLE m)) ++ l)) /\
         ((l ++ ((WHOLE n) ++ (WHOLE m))) = ((l ++ (WHOLE n)) ++ (WHOLE m))) ",
        lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [lnum_plus;ADD_ASSOC]
);;
%

let lnum_plus_assoc = prove_thm (
        `lnum_plus_assoc`,
        "!l1 l2 l3.
          l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3",
        lnum_cases_TAC ["l1:lnum";"l2:lnum";"l3:lnum"]
        THEN REWRITE_TAC [lnum_plus;ADD_ASSOC]
);;

% ++ is monotonic in one argument %

let lnum_plus_mono = prove_thm (
        `lnum_plus_mono`,
        "!l l1 l2.
        is_WHOLE l ==>
                l1 <-+ l2 ==> (l1 ++ l) <-+ (l2 ++ l)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq_reduce
                ;lnum_not_less_eq
                ;lnum_plus
                ;LESS_EQ_MONO_ADD_EQ
                ;LESS_MONO_ADD
                ]
        THEN DISCH_THEN (\th.REWRITE_TAC[th])
);;

let lnum_plus_mono_alt = prove_thm (
        `lnum_plus_mono_alt`,
        "!n l1 l2.
         l1 <-+ l2 ==> (l1 ++ (WHOLE n)) <-+ (l2 ++ (WHOLE n))",
        GEN_TAC
        THEN MP_TAC (SPEC "WHOLE n" lnum_plus_mono)
        THEN REWRITE_TAC [is_WHOLE]
);;

let lnum_strict_plus_mono = prove_thm (
        `lnum_strict_plus_mono`,
        "!l l1 l2.
        is_WHOLE l ==>
                l1 <+ l2 ==> (l1 ++ l) <+ (l2 ++ l)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_reduce
                ;lnum_not_less
                ;lnum_plus
                ;LESS_MONO_ADD
                ]
        THEN DISCH_THEN (\th.REWRITE_TAC[th])
);;

let lnum_strict_plus_mono_alt = prove_thm (
        `lnum_strict_plus_mono_alt`,
        "!n l1 l2.
         l1 <+ l2 ==> (l1 ++ (WHOLE n)) <+ (l2 ++ (WHOLE n))",
        GEN_TAC
        THEN MP_TAC (SPEC "WHOLE n" lnum_strict_plus_mono)
        THEN REWRITE_TAC [is_WHOLE]
);;

% ++ is monotonic in both arguments %

let lnum_plus_mono2 = prove_thm (
        `lnum_plus_mono2`,
        "!l1 l2 l3 l4.
         is_WHOLE l2 ==>
         is_WHOLE l3 ==>
                 l1 <-+ l2 /\ l3 <-+ l4 ==> (l1 ++ l3) <-+ (l2 ++ l4)",
        REPEAT STRIP_TAC
        THEN ASSUME_TAC (SPECL ["l3:lnum";"l1:lnum";"l2:lnum"] lnum_plus_mono)
        THEN RES_TAC
        THEN ASSUME_TAC (SPECL ["l2:lnum";"l3:lnum";"l4:lnum"] lnum_plus_mono)
        THEN RES_TAC
        THEN UNDISCH_TAC "(l1 ++ l3) <-+ (l2 ++ l3)"
        THEN IMP_RES_TAC lnum_plus_sym1
        THEN APPLY_TO  "!m. l2 ++ m = m ++ l2"
                 (ONCE_REWRITE_TERM "l2 ++ l3")
        THEN DISCH_TAC
        THEN IMP_RES_TAC lnum_less_eq_po
);;

let lnum_plus_mono2_alt = prove_thm (
        `lnum_plus_mono2_alt`,
        "!n m l1 l4.
         l1 <-+ (WHOLE n) /\ (WHOLE m) <-+ l4 ==>
                (l1 ++ (WHOLE m)) <-+ ((WHOLE n) ++ l4)",
        GEN_TAC
        THEN GEN_TAC
        THEN GEN_TAC
        THEN MP_TAC (SPECL ["l1:lnum";"WHOLE n";"WHOLE m"] lnum_plus_mono2)
        THEN REWRITE_TAC [is_WHOLE]
);;

let lnum_strict_plus_mono2 = prove_thm (
        `lnum_strict_plus_mono2`,
        "!l1 l2 l3 l4.
         is_WHOLE l2 ==>
         is_WHOLE l3 ==>
                 l1 <+ l2 /\ l3 <+ l4 ==> (l1 ++ l3) <+ (l2 ++ l4)",
        REPEAT STRIP_TAC
        THEN ASSUME_TAC
                (SPECL ["l3:lnum";"l1:lnum";"l2:lnum"]
                 lnum_strict_plus_mono
                )
        THEN RES_TAC
        THEN ASSUME_TAC
                (SPECL ["l2:lnum";"l3:lnum";"l4:lnum"]
                 lnum_strict_plus_mono
                )
        THEN RES_TAC
        THEN UNDISCH_TAC "(l1 ++ l3) <+ (l2 ++ l3)"
        THEN IMP_RES_TAC lnum_plus_sym1
        THEN APPLY_TO  "!m. l2 ++ m = m ++ l2"
                 (ONCE_REWRITE_TERM "l2 ++ l3")
        THEN DISCH_TAC
        THEN IMP_RES_TAC lnum_less_trans_alt
);;

let lnum_strict_plus_mono2_alt = prove_thm (
        `lnum_strict_plus_mono2_alt`,
        "!n m l1 l4.
         l1 <+ (WHOLE n) /\ (WHOLE m) <+ l4 ==>
                (l1 ++ (WHOLE m)) <+ ((WHOLE n) ++ l4)",
        GEN_TAC
        THEN GEN_TAC
        THEN GEN_TAC
        THEN MP_TAC (SPECL ["l1:lnum";"WHOLE n";"WHOLE m"]
                        lnum_strict_plus_mono2)
        THEN REWRITE_TAC [is_WHOLE]
);;

let lnum_less_plus_cancel = prove_thm
(       `lnum_less_plus_cancel`,
        "!l l1 l2.
         is_WHOLE l ==>
         ((l++l1) <+ (l++l2) = l1 <+ l2)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_plus
                ;lnum_less_reduce
                ;lnum_not_less
                ]
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN REWRITE_TAC[LESS_MONO_ADD_EQ]
);;

% -- is monotonic in one argument %


let lnum_sub_mono = prove_thm (
        `lnum_sub_mono`,
        "!l l1 l2.
         is_WHOLE l ==>
         l <-+ l1 ==>
         l1 <-+ l2 ==>
                (l1 -- l) <-+ (l2 -- l)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq_reduce
                ;lnum_not_less_eq
                ;lnum_sub
                ;LESS_EQ_MONO_ADD_EQ
                ;SUB_MONO
                ;LESS_SUB_MONO
                ]
        THEN REPEAT DISCH_TAC
        THEN ASM_REWRITE_TAC[]
);;

let lnum_sub_mono_alt = prove_thm (
        `lnum_sub_mono_alt`,
        "!n l1 l2.
         (WHOLE n) <-+ l1 ==>
         l1 <-+ l2 ==>
                (l1 -- (WHOLE n)) <-+ (l2 -- (WHOLE n))",
        GEN_TAC
        THEN MP_TAC (SPEC "WHOLE n" lnum_sub_mono)
        THEN REWRITE_TAC [is_WHOLE]
);;

let lnum_strict_sub_mono = prove_thm (
        `lnum_strict_sub_mono`,
        "!l l1 l2.
         is_WHOLE l ==>
         l <-+ l1 ==>
         l1 <+ l2 ==>
                (l1 -- l) <+ (l2 -- l)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_reduce
                ;lnum_less_eq_reduce
                ;lnum_not_less
                ;lnum_sub
                ;LESS_MONO_ADD
                ;SUB_MONO
                ;LESS_SUB_MONO
                ]
);;

let lnum_strict_sub_mono_alt = prove_thm (
        `lnum_strict_sub_mono_alt`,
        "!n l1 l2.
         (WHOLE n) <-+ l1 ==>
         l1 <+ l2 ==>
                (l1 -- (WHOLE n)) <+ (l2 -- (WHOLE n))",
        GEN_TAC
        THEN MP_TAC (SPEC "WHOLE n" lnum_strict_sub_mono)
        THEN REWRITE_TAC [is_WHOLE]
);;

let lnum_PR_mono = prove_thm (
        `lnum_PR_mono`,
        "!l1 l2.
         (WHOLE 1) <-+ l1 ==>
         l1 <-+ l2 ==> (PR l1) <-+ (PR l2)",
        REWRITE_TAC [PR_fn;lnum_sub_mono_alt]
);;

let lnum_PR_mono_strict = prove_thm (
        `lnum_PR_mono_strict`,
        "!l1 l2.
         (WHOLE 1) <-+ l1 ==>
         l1 <+ l2 ==> (PR l1) <+ (PR l2)",
        REWRITE_TAC [PR_fn;lnum_strict_sub_mono_alt]
);;

let lnum_PR_mono_strict_alt = prove_thm (
        `lnum_PR_mono_strict_alt`,
        "!l1 l2.
         (WHOLE 0) <+ l1 ==>
         ((PR l1) <+ (PR l2) = l1 <+ l2)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_reduce
                ;PR
                ;lnum_not_less
                ;SYM_th PRE_SUB1
                ;INV_PRE_LESS_SHARP
                ]
);;

let join_length_lemma = prove_thm (
        `join_length_lemma`,
        "is_WHOLE l1 ==>
         WHOLE 1 <+ l1 ==>
         WHOLE 1 <+ l2 ==>
         WHOLE 1 <+ l1 ++ (PR l2)",
        REWRITE_TAC [PR_fn]
        THEN REPEAT STRIP_TAC
        THEN MP_TAC
                (SPECL ["1";"WHOLE 1";"l2:lnum"]
                 lnum_strict_sub_mono_alt)
        THEN REWRITE_TAC [lnum_less_eq_po;lnum_sub]
        THEN REDUCE_TAC
        THEN DISCH_THEN IMP_RES_TAC
        THEN MP_TAC
                (SPECL  ["WHOLE 1"
                        ;"l1:lnum"
                        ;"WHOLE 0"
                        ;"l2 -- (WHOLE 1)"
                        ]
                 lnum_strict_plus_mono2
                )
         THEN ASM_REWRITE_TAC [lnum_sub;lnum_plus;is_WHOLE;ADD_0]
);;

let lnum_plus_inc_strict = prove_thm (
        `lnum_plus_inc_strict`,
        "!l1 l2.
         is_WHOLE l1 ==>
         WHOLE 0 <+ l2 ==>
         l1 <+ l1 ++ l2",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq_reduce
                ;lnum_less_reduce
                ;lnum_not_less_eq
                ;lnum_not_less
                ;lnum_plus
                ]
        THEN DISCH_TAC
        THEN ONCE_LEFT_SUBST_TAC (SYM_th ADD_0)
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN ASM_REWRITE_TAC [LESS_MONO_ADD_EQ]
);;

let is_WHOLE_plus = prove_thm (
        `is_WHOLE_plus`,
        "!l1 l2. is_WHOLE l1 ==> is_WHOLE l2 ==> is_WHOLE (l1 ++ l2)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l2:lnum"]
        THEN REWRITE_TAC [is_WHOLE;lnum_plus]
);;

let is_WHOLE_sub = prove_thm (
        `is_WHOLE_sub`,
        "!l1 l2. is_WHOLE l1 ==> is_WHOLE l2 ==> is_WHOLE (l1 -- l2)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l2:lnum"]
        THEN REWRITE_TAC [is_WHOLE;lnum_sub]
);;

let is_WHOLE_PR = prove_thm (
        `is_WHOLE_PR`,
        "!l. is_WHOLE l ==> is_WHOLE (PR l)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;PR]
);;

let lnum_less_eq_imp_not_less = prove_thm (
        `lnum_less_eq_imp_not_less`,
        "!l1 l2. l1 <-+ l2 ==> ~l2 <+ l1",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_less_eq_reduce
                ;lnum_less_reduce
                ;lnum_not_less
                ;lnum_not_less_eq
                ]
        THEN REWRITE_TAC [NOT_LESS]
);;

let lnum_PR_less = prove_thm (
        `lnum_PR_less`,
        "!l.
         is_WHOLE l ==>
         WHOLE 0 <+ l ==> (PR l) <+ l",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;lnum_less_reduce;PR]
        THEN DISCH_TAC
        THEN REWRITE_TAC [LESS_EQ;ADD1]
        THEN REWRITE_ASM
                [LESS_EQ; ADD1
                ;ONCE_REWRITE_RULE[ADD_SYM] ADD_0
                ]
        THEN IMP_RES_TAC SUB_ADD
        THEN ASM_REWRITE_TAC [LESS_OR_EQ]
);;

let lnum_zero_less_one = prove_thm
(       `lnum_zero_less_one`,
        "WHOLE 0 <+ WHOLE 1",
        REWRITE_TAC [lnum_less_reduce]
        THEN REDUCE_TAC
);;

let PR_WHOLE = prove_thm
(       `PR_WHOLE`,
        "!l. is_WHOLE l ==> is_WHOLE(PR l)",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;PR]
);;

let lnum_less_WHOLE = prove_thm
(       `lnum_less_WHOLE`,
        "!l m. l <+ m ==> is_WHOLE l",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum";"m:lnum"]
        THEN REWRITE_TAC [is_WHOLE;lnum_less_reduce;lnum_not_less]
);;

let lnum_less_eq_PR = prove_thm
(       `lnum_less_eq_PR`,
        "!l. is_WHOLE l ==> PR(l) <-+ l",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE;PR;lnum_less_eq_reduce]
        THEN ONCE_REWRITE_TAC [SYM_th PRE_SUB1]
        THEN REWRITE_TAC [PRE_LESS_EQ]
);;

let lnum_less_eq_PR_alt = prove_thm
(       `lnum_less_eq_PR_alt`,
        "!n. PR(WHOLE n) <-+ (WHOLE n)",
        GEN_TAC
        THEN SUPPOSE_TAC "is_WHOLE(WHOLE n)"
        THENL   [IMP_RES_TAC lnum_less_eq_PR
                ;REWRITE_TAC [is_WHOLE]
                ]
);;

let lnum_PR_plus = prove_thm
(       `lnum_PR_plus`,
        "!l.
         is_WHOLE l ==>
         WHOLE 1 <-+ l ==> (l -- (PR l) = WHOLE 1)",
        GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;lnum_sub
                ;lnum_less_eq_reduce
                ;PR
                ;lnum_const_one_one
                ;LESS_OR_EQ
                ]
        THEN DISCH_THEN DISJ_CASES_TAC
        THENL   [IMP_RES_TAC SUB_SUB_ID
                ;ASSUM_LIST (REWRITE_TAC o SYML_th)
                 THEN REDUCE_TAC
                ]
);;


let lnum_less_contrapos = prove_thm
(       `lnum_less_contrapos`,
        "!m n. ~(WHOLE m <+ WHOLE n) ==> WHOLE n <-+ WHOLE m",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [lnum_less_reduce;lnum_less_eq_reduce;NOT_LESS]
);;

let lnum_less_contrapos_alt = prove_thm
(       `lnum_less_contrapos_alt`,
        "!l1 l2.
         is_WHOLE l1 ==>
         is_WHOLE l2 ==>
         ~(l1 <+ l2) ==> l2 <-+ l1",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC["l1:lnum";"l2:lnum"]
        THEN REWRITE_TAC [is_WHOLE;lnum_less_contrapos]
);;


let lnum_less_eq_add_sub = prove_thm
(       `lnum_less_eq_add_sub`,
        "!l m.
         is_WHOLE l ==>
         is_WHOLE m ==>
         l <-+ m ==>
         (!k. m <-+ k ==> (k -- (m -- l) = (k -- m) ++ l))",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum";"m:lnum"]
        THEN REWRITE_TAC[is_WHOLE;lnum_less_eq_reduce]
        THEN DISCH_TAC
        THEN GEN_TAC
        THEN lnum_cases_TAC ["k:lnum"]
        THEN REWRITE_TAC
                [lnum_sub
                ;lnum_plus
                ;lnum_const_one_one
                ;lnum_less_eq_reduce
                ]
        THEN DISCH_TAC
        THEN IMP_RES_TAC SUB_SUB
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN ONCE_RIGHT_SUBST_TAC ADD_SYM
        THEN IMP_RES_TAC LESS_EQ_ADD_SUB
        THEN EVERY_ASSUM (RIGHT_SUBST_TAC o SYM_th)
        THEN ONCE_LEFT_SUBST_TAC ADD_SYM
        THEN REFL_TAC
);;

let lnum_add_sub = prove_thm
(       `lnum_add_sub`,
        "!l m.
         is_WHOLE m ==>
         ((l ++ m) -- m = l)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["m:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [lnum_plus
                ;lnum_sub
                ;lnum_const_one_one
                ;ADD_SUB
                ]
);;

let lnum_sub_add = prove_thm
(       `lnum_sub_add`,
        "!l m.
         is_WHOLE l ==>
         l <-+ m ==> (l ++ (m -- l) = m)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["m:lnum"]
        THEN REWRITE_TAC
                [lnum_plus
                ;lnum_sub
                ;lnum_less_eq_reduce
                ;lnum_const_one_one
                ]
        THEN DISCH_TAC
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN IMP_RES_TAC SUB_ADD
);;


let lnum_plus_cancel = prove_thm
(       `lnum_plus_cancel`,
        "!l.
         is_WHOLE l ==> !m n. (l ++ m = l ++ n) = (m = n)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN REPEAT GEN_TAC
        THEN lnum_cases_TAC ["m:lnum";"n':lnum"]
        THEN REWRITE_TAC
                [lnum_plus
                ;lnum_const_one_one
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ]
        THEN REWRITE_TAC
                [ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ]
);;

let PR_one_one = prove_thm
(       `PR_one_one`,
        "!l m.
         WHOLE 0 <+ l ==>
         WHOLE 0 <+ m ==>
         ((PR l = PR m) = (l = m))",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum";"m:lnum"]
        THEN REWRITE_TAC
                [PR
                ;lnum_const_one_one
                ;lnum_const_dist
                ;SYM_th lnum_const_dist
                ;lnum_less_reduce
                ;lnum_not_less
                ;SYM_th PRE_SUB1
                ]
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC INV_PRE_EQ
);;



let lnum_plus1_choose = prove_thm
(       `lnum_plus1_choose`,
        "!l. WHOLE 0 <+ l ==> ?l1. l= l1 ++ WHOLE 1",
        REPEAT STRIP_TAC
        THEN EXISTS_TAC "PR l"
        THEN UNDISCH_ALL_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC
                [PR
                ;lnum_plus
                ;lnum_less_reduce
                ;lnum_not_less
                ;lnum_const_one_one
                ]
        THEN DISCH_TAC
        THEN IMP_RES_THEN
                (ASSUME_TAC o (REWRITE_RULE[SYM_th SUC_0]))
                LESS_OR
        THEN IMP_RES_TAC SUB_ADD
        THEN ASM_REWRITE_TAC[]
);;


let lnum_strict_plus_sub_move = prove_thm
(       `lnum_strict_plus_sub_move`,
        "!l l1 l2.
         is_WHOLE l1 ==>
         (l1 <-+ l) ==>
         ((l -- l1) <+ l2 = l <+ (l2 ++ l1))",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["l:lnum";"l2:lnum"]
        THEN REWRITE_TAC
                [lnum_sub
                ;lnum_not_less
                ;lnum_less_reduce
                ;lnum_less_eq_reduce
                ;lnum_not_less_eq
                ;lnum_plus
                ;SUB_LESS_TO_LESS_ADDR
                ]
);;


let lnum_PR_shift = prove_thm
(       `lnum_PR_shift`,
        "!l l1.
         is_WHOLE l1 ==>
         WHOLE 1 <-+ l ==>
         WHOLE 1 <-+ l1 ==> ((PR l) ++ l1 = l ++ (PR l1))",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l1:lnum";"l:lnum"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;lnum_plus
                ;PR
                ;lnum_less_eq_reduce
                ;lnum_const_one_one
                ]
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN IMP_RES_TAC LESS_EQ_SUB_ADD
        THEN ASSUME_TAC (SPEC "1" LESS_EQ_REFL)
        THEN IMP_RES_TAC LESS_EQ_ADD_SUB1
        THEN ASM_REWRITE_TAC[]
);;

let lnum_WHOLE_less_PR_less = prove_thm
(       `lnum_WHOLE_less_PR_less`,
        "!n l. WHOLE n <+ (PR l) ==> WHOLE n <+ l",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC["l:lnum"]
        THEN REWRITE_TAC
                [PR;lnum_less_reduce;SYM_th PRE_SUB1
                ;SYM_th SUC_LESS_PRE_SHARP
                ]
        THEN DISCH_TAC
        THEN ASSUME_TAC(SPEC "n:num" LESS_SUC_REFL)
        THEN IMP_RES_TAC LESS_TRANS
);;

%
| Rule to lift any appropriate arithmetic thm to one about WHOLE lnums
%

let WHOLE_rewrite_thm = prove_thm
(       `WHOLE_rewrite_thm`,
        "!n m.
          ((n = m) = (WHOLE n = WHOLE m)) /\
          (n <= m = WHOLE n <-+ WHOLE m) /\
          (n < m = WHOLE n <+ WHOLE m) /\
          (WHOLE(n+m) = (WHOLE n) ++ (WHOLE m)) /\
          (WHOLE(n-m) = (WHOLE n) -- (WHOLE m)) /\
          (WHOLE(SUC n) = SC(WHOLE n)) /\
          (WHOLE(PRE n) = PR(WHOLE n))",
        REWRITE_TAC
                [lnum_const_one_one
                ;lnum_plus
                ;lnum_sub
                ;SC
                ;PR
                ;ADD1
                ;PRE_SUB1
                ;lnum_less_reduce
                ;lnum_less_eq_reduce
                ]
);;

let LNUM_LIFT = REWRITE_RULE[WHOLE_rewrite_thm];;



close_theory();;
