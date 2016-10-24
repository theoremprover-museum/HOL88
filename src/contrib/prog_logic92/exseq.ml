%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        |
|                                                              |
| exseq.ml                                                     |
|                                                              |
| DESCRIPTION:                                                 |
|                                                              |
| Defines a theory of execution sequences                      |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

%
| The following construction of "execution sequences" will be the
| basis of the semantics of a simple programming language.
%

new_theory `exseq`;;

loadf `mytactics`;;

load_library `reduce`;;
load_library `taut`;;
load_library `more_arithmetic`;;
load_library `string`;;

loadf `l_arith_hack`;;
loadf `l_cpo`;;
loadf `l_lnum`;;

%
| Define the subset predicate for exseqs
%

new_type_abbrev(`state`,":string->num");;

let IS_exseq_REP = new_definition (
        `IS_exseq_REP`,
        "IS_exseq_REP r =
         ?f:num->state.?l:lnum.
         (r = ((\m.(WHOLE m) <+ l => f m | @x:state.T), l))
                /\  ((WHOLE 1) <+ l)"
);;

%
| Prove that there is at least one exseq
%

let EXISTS_exseq_REP = prove_thm
(       `EXISTS_exseq_REP`,
        "?e. IS_exseq_REP e",
        EXISTS_TAC
                "((\m.(WHOLE m) <+ (WHOLE 2)
                         => (\n:num.@x:state.T) m
                          |  @x:state.T
                  ),
                  (WHOLE 2)
                 )"
        THEN PURE_REWRITE_TAC [IS_exseq_REP]
        THEN MAP_EVERY EXISTS_TAC ["\n:num.@x:state.T";"WHOLE 2"]
        THEN REWRITE_TAC[lnum_less_reduce]
        THEN CONV_TAC LT_CONV
);;

%
| Define the new type
%

let exseq_TY_DEF =
    new_type_definition
     (`exseq`, "IS_exseq_REP:((num->state) # lnum) -> bool", EXISTS_exseq_REP);;

save_thm(`exseq_TY_DEF_alt`,REWRITE_RULE[TYPE_DEFINITION]exseq_TY_DEF);;

%
| Define a representation function, REP_exseq, from the type exseq to
| the representing type and the inverse abstraction function ABS_exseq,
| and prove some trivial lemmas about them.
%

let exseq_ISO_DEF =
    define_new_type_bijections
        `exseq_ISO_DEF` `ABS_exseq` `REP_exseq` exseq_TY_DEF;;

let R_ONTO = prove_rep_fn_onto exseq_ISO_DEF     and
    R_11   = prove_rep_fn_one_one exseq_ISO_DEF  and
    A_ONTO = prove_abs_fn_onto exseq_ISO_DEF     and
    A_11   = prove_abs_fn_one_one exseq_ISO_DEF  and
    A_R = CONJUNCT1 exseq_ISO_DEF                and
    R_A = CONJUNCT2 exseq_ISO_DEF;;

let REP_lemma1 = TAC_PROOF
 (
  ([], "!e:exseq. IS_exseq_REP (REP_exseq e)"),
  GEN_TAC
  THEN REWRITE_TAC [R_ONTO]
  THEN EXISTS_TAC "e:exseq"
  THEN REWRITE_TAC []
 );;

let REP_lemma = REWRITE_RULE [IS_exseq_REP] REP_lemma1;;

let ABS_11_lemma = TAC_PROOF
 (
  ([],"!x y:exseq.
        (ABS_exseq (REP_exseq x) = ABS_exseq (REP_exseq y)) =
                (REP_exseq x = REP_exseq y)"),
  REPEAT GEN_TAC
  THEN ASSUME_TAC (SPEC "x:exseq" REP_lemma1)
  THEN ASSUME_TAC (SPEC "y:exseq" REP_lemma1)
  THEN IMP_RES_TAC (SPEC "REP_exseq (x:exseq)"
                        (SPEC "REP_exseq (y:exseq)" A_11))
 );;

%
| Replaces (REP_exseq e) by (f,l) for appropriately chosen f,l
| t is the term "e:state". Adds IS_REP_exseq t to the assumptions.
%

let REP_inst t = CHOOSE_THEN
                        (CHOOSE_THEN \th.REWRITE_TAC[th]
                         THEN (ASSUME_TAC (CONJUNCT2 th))) (SPEC t REP_lemma);;

%
| Define a function that will return the function component of
| a exseq
%

let exseq_fn_dest = new_definition (
        `exseq_fn_dest`,
        "!e:exseq. exseq_fn_dest e = FST (REP_exseq e)"
);;

%
| Define a function that will return the length of a exseq
| and prove that every exseq has length of at least 1
%

let length = new_definition
 (
  `length`,
  "!e:exseq. length e = SND (REP_exseq e)"
 );;

let length_min = prove_thm (
        `length_min`,
        "!e:exseq. (WHOLE 1) <+ length e",
        GEN_TAC
        THEN REWRITE_TAC[length]
        THEN REP_inst "e:exseq"
);;

let zero_less_length = prove_thm
(       `zero_less_length`,
        "!e. (WHOLE 0) <+ length e",
        GEN_TAC
        THEN ASSUME_TAC (SPEC "e:exseq" length_min)
        THEN SUPPOSE_TAC "WHOLE 0 <+ WHOLE 1"
        THEN REWRITE_TAC[lnum_less_reduce]
        THEN REDUCE_TAC
        THEN IMP_RES_TAC lnum_less_trans_alt
);;

%
| Define functions to test the `type' of an exseq
%

let TERM = new_definition (
        `TERM`,
        "!e. TERM e = is_WHOLE(length e)"
);;

let ABORT = new_definition (
        `ABORT`,
        "!e. ABORT e = is_FRAG(length e)"
);;

let INF = new_definition (
        `INF`,
        "!e. INF e = is_OO(length e)"
);;

let TERM_not_ABORT = prove_thm
(       `TERM_not_ABORT`,
        "!e. TERM e ==> ~ABORT e",
        GEN_TAC
        THEN REWRITE_TAC[TERM;ABORT]
        THEN lnum_cases_TAC["length e"]
        THEN REWRITE_TAC[is_WHOLE;is_FRAG]
);;

%
| Define a function that will return the elts of a exseq fs
| NOTE: elts are numbered from 0
%

let elt = new_recursive_definition false lnum `elt`
        "(elt (WHOLE n) e = exseq_fn_dest e n) /\
         (elt (FRAG n) e = exseq_fn_dest e n)";;

save_thm(`elt_alt`,REWRITE_RULE[exseq_fn_dest]elt);;

let last = new_definition
 (
  `last`,
  "!e:exseq. last e =
        elt (PR(length e)) e"
 );;

let first = new_definition
 (
  `first`,
  "!e:exseq. first e =
        elt (WHOLE 0) e"
 );;


%
| General procedure for explicitly defining an exseq
| and proofs of characterizing theorems.
%

let mk_exseq_rp = new_definition
(       `mk_exseq_rp`,
         "!f:num->state.!l:lnum.
         mk_exseq_rp (f,l) =
                ((\n. (WHOLE n <+ l) => f n | (@y:state.T))
                ,l
                )"
);;

let mk_exseq = new_definition
(       `mk_exseq`,
        "!f:num->state.!l:lnum.
         mk_exseq (f,l) = ABS_exseq (mk_exseq_rp(f,l))"
);;

let mk_exseq_REP = prove_thm
(       `mk_exseq_REP`,
        "!f l. WHOLE 1 <+ l ==> IS_exseq_REP (mk_exseq_rp(f,l))",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC [mk_exseq_rp;IS_exseq_REP]
        THEN EXISTS_TAC "f:num->state"
        THEN EXISTS_TAC "l:lnum"
        THEN ASM_REWRITE_TAC[]
);;

let mk_exseq_thm = prove_thm
(       `mk_exseq_thm`,
        "!f l.
         WHOLE 1 <+ l ==>
                (length(mk_exseq(f,l)) = l) /\
                (!n. elt (WHOLE n) (mk_exseq(f,l)) =
                        ((WHOLE n <+ l) => f n | (@x:state.T))
                )",
        REPEAT GEN_TAC
        THEN DISCH_TAC
        THEN IMP_RES_TAC mk_exseq_REP
        THEN REWRITE_TAC [mk_exseq]
        THEN REWRITE_TAC [length;elt;exseq_fn_dest]
        THEN FIRST_ASSUM (ASSUME_TAC o SPEC_ALL)
        THEN IMP_RES_TAC R_A
        THEN ASM_REWRITE_TAC[mk_exseq_rp]
        THEN CONV_TAC (DEPTH_CONV BETA_CONV)
        THEN REWRITE_TAC[]
);;

%-

creates an exseq and returns a theorem specifying its
length and elements, completely determining it. requires
a theorem stating that the supplied length is greater than one

eg:

let lemma = PROVE
        ("WHOLE 1 <+ WHOLE 2",
         REWRITE_TAC[lnum_less_reduce]
         THEN REDUCE_TAC
        );;


new_exseq `zoo5` "(zoo5 (s:state) (t:state)):exseq"
                "\n.(n=0)=>(s:state)|(t:state)" "WHOLE 2" lemma;;

|- !s t.
    (length(zoo5 s t) = WHOLE 2) /\
    (!n.
      elt(WHOLE n)(zoo5 s t) =
      ((WHOLE n) <+ (WHOLE 2) => ((n = 0) => s | t) | (@x. T)))

-%

let new_exseq name const_term fn len len_thm =
        let mk_exseq_fn name const_name fn len = new_definition
         (name^`_mk_exseq`,
          "^const_term = mk_exseq (^fn,^len)"
          ) in
        let thm = mk_exseq_fn name const_term fn len in
        let thm2 = MATCH_MP (SPEC fn mk_exseq_thm) len_thm in
        let thm3 = GEN_ALL (BETA_RULE((REWRITE_RULE [SYM_th thm] thm2))) in
        save_thm(name,thm3);;


%
| The following function will be used later in the definition
| of a "join" function for exseqs
%

let splice = new_definition (
        `splice`,
        "!x y:exseq. splice x y =
                (\n. (WHOLE n) <+ (length x)
                        => elt (WHOLE n) x
                         | elt ((WHOLE n)--(PR(length x))) y
                )"
);;

let this_lemma = PROVE
(       "!x y. WHOLE 1 <+ (length x) ++ (PR(length y))",
        REPEAT GEN_TAC
        THEN MP_TAC (SPEC "x:exseq" length_min)
        THEN lnum_cases_TAC ["length x";"length y"]
        THEN REWRITE_TAC[lnum_plus;PR;lnum_less_reduce;ADDR_GREATER]
);;

let join_f = new_exseq
                `join_f`
                "join_f (x:exseq) (y:exseq):exseq"
                "splice x y"
                "(length x) ++ (PR(length y))"
                (SPEC_ALL this_lemma);;

%-
let join_f = new_infix_definition (
        `join_f`,
        "!x y:exseq.
         join_f x y = mk_exseq(splice x y,(length x) ++ (PR(length y)))"
);;
-%

let join_lemma = PROVE (
        "?f:exseq->exseq->exseq.!x y.
        TERM x ==>
        (first y = last x) ==>
                (f x y = join_f x y)",
        EXISTS_TAC "join_f"
        THEN REWRITE_TAC[]
 );;

new_special_symbol `<*>`;;

let join =
    new_specification `join` [`infix`,`<*>`] join_lemma;;


%
| A useful little tactic that will attempt
| to rewrite <*> provided it is defined
%

let REWRITE_JOIN =
        IMP_RES_TAC join
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t="x <*> y = join_f x y")
                [join_f]
        THEN POP_IT "x <*> y = join_f x y";;

%
| Prove the defining characteristic of the exseq_join, in terms of elts and
| length
%

%-
let this_lemma = PROVE
(       "!x y. TERM x ==> WHOLE 1 <+ (length x) ++ (PR(length y))",
        REWRITE_TAC[TERM]
        THEN REPEAT STRIP_TAC
        THEN HALF_REWRITE_TAC[de_imp join_length_lemma]
        THEN ASM_REWRITE_TAC[length_min]
);;
-%

let join_length = prove_thm (
        `join_length`,
        "!x y:exseq.
         TERM x ==>
         (first y = last x) ==>
         (length (x <*> y) =
                (length x) ++ (PR(length y)))",
        REPEAT STRIP_TAC
        THEN REWRITE_JOIN
);;

let lemma = PROVE (
        "!n x y.
         TERM x ==>
         WHOLE n <+ length x ==>
                WHOLE n <+ (length x ++ (PR(length y)))",
        REPEAT GEN_TAC
        THEN ASSUME_TAC (SPEC "y:exseq" length_min)
        THEN MP_TAC (SPEC "WHOLE 1" lnum_PR_mono_strict)
        THEN REWRITE_TAC [lnum_less_eq_reduce;PR;TERM]
        THEN REDUCE_TAC
        THEN DISCH_THEN IMP_RES_TAC
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC lnum_plus_inc_strict
        THEN IMP_RES_TAC lnum_less_trans_alt
);;

let join_elts = prove_thm (
        `join_elts`,
        "!x y:exseq.
         TERM x ==>
         (first y = last x) ==>
         !n. elt (WHOLE n) (x <*> y) =
                (((WHOLE n) <+ (length x))
                        => elt (WHOLE n) x
                         |
                 ((WHOLE n) <+ (length (x<*>y)))
                        => elt ((WHOLE n)--(PR(length x))) y
                         | @q:state.T
                )",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_JOIN
        THEN REWRITE_TAC [splice]
        THEN CONV_TAC (DEPTH_CONV BETA_CONV)
        THEN COND_CASES_TAC
        THEN COND_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC lemma
        THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "y:exseq"))
        THEN RES_TAC
);;

let join_elts_alt = prove_thm (
        `join_elts_alt`,
        "!l:lnum.
         !x y:exseq.
         is_WHOLE l ==>
         TERM x ==>
         (first y = last x) ==>
         (elt l (x <*> y) =
                ((l <+ (length x))
                        => elt l x
                         |
                 (l <+ (length (x<*>y)))
                        => elt (l -- (PR(length x))) y
                         | @q:state.T
                ))",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC ["l:lnum"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC join_elts
        THEN ASM_REWRITE_TAC[]
);;


let join_TERM = prove_thm (
        `join_TERM`,
        "!x y.
        (first y = last x) ==>
        TERM x ==>
        (TERM y = TERM(x<*>y))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN UNDISCH_TAC "TERM x"
        THEN ASM_REWRITE_TAC [TERM]
        THEN lnum_cases_TAC ["length x"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["length y"]
        THEN REWRITE_TAC [is_WHOLE;lnum_plus;PR]
);;

let join_ABORT = prove_thm (
        `join_ABORT`,
        "!x y.
        (first y = last x) ==>
        TERM x ==>
        (ABORT y = ABORT(x<*>y))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN UNDISCH_TAC "TERM x"
        THEN ASM_REWRITE_TAC [TERM;ABORT]
        THEN lnum_cases_TAC ["length x"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["length y"]
        THEN REWRITE_TAC [is_WHOLE;is_FRAG;lnum_plus;PR]
);;

let join_first = prove_thm (
        `join_first`,
        "!x y. (TERM x) ==> (first y = last x) ==> (first(x<*>y) = first x)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_elts
        THEN ASM_REWRITE_TAC[first]
        THEN SUPPOSE_TAC "WHOLE 0 <+ WHOLE 1"
        THENL   [ASSUME_TAC (SPEC "x:exseq" length_min)
                 THEN IMP_RES_TAC lnum_less_trans_alt
                 THEN ASM_REWRITE_TAC[]
                ;REWRITE_TAC [lnum_less_reduce]
                 THEN CONV_TAC LT_CONV
                ]
);;

let lemma = PROVE (
        "!x y.
         (first y = last x) ==>
         (TERM x) ==>
         (TERM y) ==>
         is_WHOLE (PR(length(x<*>y)))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_ASM [TERM]
        THEN IMP_RES_TAC is_WHOLE_PR
        THEN ASSUME_TAC (SPEC "length x" is_WHOLE_plus)
        THEN RES_TAC
        THEN IMP_RES_TAC is_WHOLE_PR
);;

let lemma2 = PROVE (
        "!x y.
        (first y = last x) ==>
        TERM x ==>
        TERM y ==>
         (length x) <-+ (PR(length(x<*>y)))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN MP_TAC (SPEC "x:exseq" length_min)
        THEN MP_TAC (SPEC "y:exseq" length_min)
        THEN UNDISCH_TAC "TERM x"
        THEN UNDISCH_TAC "TERM y"
        THEN ASM_REWRITE_TAC [TERM]
        THEN lnum_cases_TAC ["length x"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["length y"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;PR
                ;lnum_less_reduce
                ;lnum_less_eq_reduce
                ;lnum_plus
                ]
        THEN POP_ASSUM_LIST \thl.REPEAT DISCH_TAC
        THEN IMP_RES_TAC SUB_LESS_OR
        THEN IMP_RES_TAC LESS_EQ_ADD_SUB
        THEN ASM_REWRITE_TAC[LESS_EQ_ADD]
);;

let lemma3 = PROVE (
        "!x y.
         (first y = last x) ==>
         TERM x ==>
         TERM y ==>
         ~(PR(length(x<*>y))) <+ (length x)" ,
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC lemma2
        THEN IMP_RES_TAC lnum_less_eq_imp_not_less
);;

let lemma4 = PROVE (
        "!x.
         (first y = last x) ==>
         TERM x ==>
         TERM y ==>
         PR(length (x<*>y)) <+ (length (x<*>y))",
        REPEAT STRIP_TAC
        THEN ASSUME_TAC (SPEC "x<*>y" length_min)
        THEN IMP_RES_TAC join_TERM
        THEN REWRITE_ASM [TERM]
        THEN SUPPOSE_TAC "WHOLE 0 <+ WHOLE 1"
        THENL   [IMP_RES_TAC lnum_less_trans_alt
                 THEN IMP_RES_TAC lnum_PR_less
                ;REWRITE_TAC[lnum_less_reduce]
                 THEN CONV_TAC LT_CONV
                ]
);;

let lemma5 = PROVE (
        "!x.
         (first y = last x) ==>
         TERM x ==>
         TERM y ==>
         ((PR(length(x <*> y))) -- (PR(length x)) = (PR(length y)))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN UNDISCH_TAC "TERM x"
        THEN UNDISCH_TAC "TERM y"
        THEN ASM_REWRITE_TAC [TERM]
        THEN MP_TAC (SPEC "x:exseq" length_min)
        THEN lnum_cases_TAC ["length x"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["length y"]
        THEN REWRITE_TAC
                [is_WHOLE;PR;lnum_sub
                ;lnum_plus;lnum_less_reduce
                ]
        THEN DISCH_TAC
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN IMP_RES_TAC LESS_EQ_ADD_SUB
        THEN ASM_REWRITE_TAC[ADD_SUB]
);;

let join_last = prove_thm (
        `join_last`,
        "!x y.
         (first y = last x) ==>
         (TERM x) ==>
         (TERM y) ==>
         (last(x<*>y) = last y)",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC [last]
        THEN EVERY
                (mapfilter IMP_RES_TAC
                        [lemma
                        ;join_elts_alt
                        ]
                )
        THEN IMP_RES_TAC lemma3
        THEN IMP_RES_TAC lemma4
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC lemma5
        THEN ASM_REWRITE_TAC[]
);;

%
| Test if two exseqs are of the same sub-type
%

let sametype = new_infix_definition (
        `sametype`,
        "!x y. sametype x y =
                (TERM x /\ TERM y) \/
                (ABORT x /\ ABORT y) \/
                (INF x /\ INF y)"
);;

%
| Prove that if two exseqs have the same length and the same
| elts then they are equal.
%

let exseq_eq = prove_thm (
        `exseq_eq`,
        "!x y:exseq.
        ((length x = length y) /\
         (!n. ((WHOLE n) <+ length x) ==>
                (elt (WHOLE n) x = elt (WHOLE n) y))
        ) = (x = y)",
 REPEAT GEN_TAC
 THEN EQ_TAC
 THENL  [REWRITE_TAC [length;elt;exseq_fn_dest]
         THEN CHOOSE_THEN CHOOSE_TAC (SPEC "x:exseq" REP_lemma)
         THEN CHOOSE_THEN CHOOSE_TAC (SPEC "y:exseq" REP_lemma)
         THEN ASM_REWRITE_TAC[]
         THEN ONCE_REWRITE_TAC
                [SYM (SPEC "x:exseq" A_R)
                ;SYM (SPEC "y:exseq" A_R)
                ]
         THEN REWRITE_TAC [ABS_11_lemma]
         THEN POP_ASSUM_LIST REWRITE_TAC
         THEN CONV_TAC ANTE_CONJ_CONV
         THEN DISCH_THEN (\th.REWRITE_TAC[th])
         THEN CONV_TAC (DEPTH_CONV BETA_CONV)
         THEN DISCH_TAC
         THEN PAIR_EQ_TAC
         THENL  [CONV_TAC (FUN_EQ_CONV THENC (DEPTH_CONV BETA_CONV))
                 THEN GEN_TAC
                 THEN COND_CASES_TAC
                 THEN REWRITE_TAC[]
                 THEN RES_TAC
                 THEN REWRITE_ASM []
                 THEN ASM_REWRITE_TAC[]
                ;REFL_TAC
                ]
        ;DISCH_THEN (\th.REWRITE_TAC[th])
        ]
);;

%
| Define a function that will create an exseq from a pair
%


let this_lemma = PROVE
(       "WHOLE 1 <+ WHOLE 2",
        REWRITE_TAC[lnum_less_reduce]
        THEN REDUCE_TAC
);;

let pair = new_exseq
                `pair`
                "pair(x:state,y:state):exseq"
                "\n.(n=0) => (x:state) | (y:state)"
                "WHOLE 2"
                this_lemma;;

let pair_length = prove_thm (
        `pair_length`,
        "!x y:state. length (pair (x,y)) = WHOLE 2",
        REWRITE_TAC [pair]
);;

let pair_TERM = prove_thm
(       `pair_TERM`,
        "!x y. TERM (pair(x,y))",
        REWRITE_TAC[TERM;pair_length;is_WHOLE]
);;

let pair_first = prove_thm (
        `pair_first`,
        "!x y:state. first (pair(x,y)) = x",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [
                pair;
                first;
                lnum_less_reduce
        ]
        THEN REDUCE_TAC
        THEN BETA_TAC
        THEN REWRITE_TAC[]
);;

let pair_last = prove_thm (
        `pair_last`,
        "!x y:state. last (pair (x,y)) = y",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [
                pair;
                last;
                PR;
                pair_length
        ]
        THEN REDUCE_TAC
        THEN BETA_TAC
        THEN REWRITE_TAC[this_lemma]
        THEN REDUCE_TAC
        THEN REFL_TAC
);;


%
| Create an aborted sequence containing two states
%

let this_lemma = PROVE
(       "WHOLE 1 <+ FRAG 2",
        REWRITE_TAC[lnum_less_reduce]
        THEN REDUCE_TAC
);;

let abort_pair = new_exseq
                `abort_pair`
                "abort_pair(x:state,y:state):exseq"
                "\n.(n=0) => (x:state) | (y:state)"
                "FRAG 2"
                this_lemma;;

let abort_pair_length = prove_thm (
        `abort_pair_length`,
        "!x y:state. length(abort_pair(x,y)) = FRAG 2",
        REWRITE_TAC [abort_pair]
);;


let abort_pair_ABORT = prove_thm
(       `abort_pair_ABORT`,
        "!x y. ABORT (abort_pair(x,y))",
        REWRITE_TAC[ABORT;abort_pair_length;is_FRAG]
);;

let abort_pair_first = prove_thm (
        `abort_pair_first`,
        "!x y:state. first (abort_pair (x,y)) = x",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [
                abort_pair;
                first;
                lnum_less_reduce
        ]
        THEN REDUCE_TAC
        THEN BETA_TAC
        THEN REWRITE_TAC[]
);;

%
| Partial order on exseqs
%

new_special_symbol `<=|`;;

let exseq_subseq = new_infix_definition (
        `exseq_subseq`,
        "!e d.
         <=| (e: exseq) (d:exseq) =
                (length e) <-+ (length d) /\
                !n.(WHOLE n) <+ (length e) ==>
                        (elt (WHOLE n) e = elt (WHOLE n) d)"
);;

%
| Prove that <=| is a partial order
%

let exseq_subseq_refl = prove_thm (
        `exseq_subseq_refl`,
        "!e. e <=| e",
        REWRITE_TAC [exseq_subseq;lnum_less_eq_po]
);;

let exseq_subseq_antisym = prove_thm (
        `exseq_subseq_antisym`,
        "!d e. (d <=| e /\ e <=| d) = (d = e)",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [exseq_subseq]
        THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[lnum_less_eq_po]
        THEN IMP_RES_TAC lnum_less_eq_po
        THEN IMP_RES_TAC exseq_eq
);;

let exseq_subseq_trans = prove_thm (
        `exseq_subseq_trans`,
        "!d e f. d <=| e /\ e <=| f ==> d <=| f",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [exseq_subseq]
        THEN REPEAT STRIP_TAC
        THENL   [IMP_RES_TAC lnum_less_eq_po
                ;IMP_RES_TAC lnum_less_less_eq_trans
                 THEN RES_TAC
                 THEN ASM_REWRITE_TAC[]
                ]
);;

let exseq_po = prove_thm
(       `exseq_po`,
        "partial_order $<=|",
        REWRITE_TAC
                [partial_order
                ;refl;antisym;trans
                ;exseq_subseq_trans
                ;exseq_subseq_antisym
                ;exseq_subseq_refl
                ]
);;

%
| Prove that exseqs form a CPO
%

let lengths = new_definition
(       `lengths`,
        "!C:num->exseq. lengths C = \n. length (C n)"
);;

let exseq_subseq_length = prove_thm
(       `exseq_subseq_length`,
        "!e d. e <=| d ==> (length e) <-+ (length d)",
        REPEAT GEN_TAC
        THEN REWRITE_TAC[exseq_subseq]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]

);;

let exseq_subseq_elts = prove_thm
(       `exseq_subseq_elts`,
        "!e d. e <=| d ==>
                (!n. WHOLE n <+ length e ==>
                        (elt (WHOLE n) e = elt (WHOLE n) d)
                )",
        REPEAT GEN_TAC
        THEN REWRITE_TAC[exseq_subseq]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
);;

let length_chain = prove_thm
(       `length_chain`,
        "!C:num->exseq. chain $<=| C ==> chain $<-+ (lengths C)",
        GEN_TAC
        THEN REWRITE_TAC[chain]
        THEN REPEAT STRIP_TAC
        THEN FIRST_ASSUM (ASSUME_TAC o (SPEC "i:num"))
        THEN IMP_RES_TAC exseq_subseq_length
        THEN REWRITE_TAC[lengths]
        THEN CONV_TAC (DEPTH_CONV BETA_CONV)
        THEN ASM_REWRITE_TAC[]
);;

let lub_fn = new_definition
(       `lub_fn`,
        "!C:num->exseq.!n.
         lub_fn C n = @x:state.?j.
                (x = elt (WHOLE n) (C j))
                /\ (WHOLE n <+ length (C j))"

);;

let lub_exseq = new_definition
(       `lub_exseq`,
        "!C. lub_exseq C = mk_exseq (lub_fn C, lub $<-+ (lengths C))"
);;

let length_lemma = PROVE
(       "!C. chain $<=| C ==>
                ((WHOLE 1) <+ (lub $<-+ (lengths C))) /\
                (!n. length (C n) <-+ (lub $<-+ (lengths C)))",
        GEN_TAC
        THEN DISCH_TAC
        THEN IMP_RES_TAC length_chain
        THEN SUPPOSE_TAC "!i. WHOLE 1 <+ (lengths C)i"
        THEN IMP_RES_TAC
                (REWRITE_RULE[cpo;is_lub;is_ub] lnum_cpo)
        THENL   [MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "i:num"))
                 THEN IMP_RES_TAC lnum_less_less_eq_trans
                 THEN ASM_REWRITE_TAC[]
                 THEN GEN_TAC
                 THEN MAPFILTER_ASSUM (MP_TAC o (SPEC "n:num"))
                 THEN REWRITE_TERM "lengths C n" lengths
                 THEN BETA_TAC
                 THEN REPEAT DISCH_TAC
                 THEN ASM_REWRITE_TAC[]
                ;REWRITE_TAC [lengths]
                 THEN BETA_TAC
                 THEN REWRITE_TAC [length_min]
                ]
);;

let lub_fn_lemma = PROVE
(       "!C n.
         chain $<=| C ==>
         WHOLE n <+ lub $<-+ (lengths C) ==>
         ?j.
         (lub_fn C n = elt (WHOLE n)(C j))
         /\ (WHOLE n <+ length(C j))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC length_chain
        THEN IMP_RES_TAC converge_lub
        THEN REWRITE_TAC [lub_fn]
        THEN CONV_TAC (DEPTH_CONV SELECT_CONV)
        THEN EXISTS_TAC "elt (WHOLE n) (C (i:num))"
        THEN EXISTS_TAC "i:num"
        THEN REWRITE_ASM [lengths]
        THEN CONV_ASM (DEPTH_CONV BETA_CONV)
        THEN ASM_REWRITE_TAC[]
);;

let lub_exseq_thm = prove_thm
(       `lub_exseq_thm`,
        "!C. chain $<=| C ==>
                (length (lub_exseq C) = lub $<-+ (lengths C)) /\
                (!n. elt(WHOLE n)(lub_exseq C) =
                        WHOLE n <+ length(lub_exseq C)
                                => lub_fn C n
                                 | (@x:state.T)
                )",
        GEN_TAC
        THEN DISCH_TAC
        THEN IMP_RES_TAC length_lemma
        THEN REWRITE_TAC [lub_exseq]
        THEN IMP_RES_TAC mk_exseq_thm
        THEN ASM_REWRITE_TAC[]
);;


let exseq_cpo = prove_thm
(       `exseq_cpo`,
        "cpo $<=|",
        REWRITE_TAC
                [cpo
                ;exseq_po
                ;lub
                ]
        THEN CONV_TAC (DEPTH_CONV SELECT_CONV)
        THEN REWRITE_TAC [is_lub;is_ub]
        THEN GEN_TAC
        THEN DISCH_TAC
        THEN IMP_RES_TAC lub_exseq_thm
        THEN EXISTS_TAC "lub_exseq C"
        THEN IMP_RES_TAC length_chain
        THEN IMP_RES_TAC length_lemma
        THEN ASM_REWRITE_TAC [exseq_subseq;lub_exseq]
        THEN REPEAT STRIP_TAC
        THENL   [MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "n:num"))
                 THEN IMP_RES_TAC lnum_less_less_eq_trans
                 THEN IMP_RES_TAC lub_fn_lemma
                 THEN ASM_REWRITE_TAC[]
                 THEN DISJ_CASES_SPLIT "n<=j"
                 THENL  [ALL_TAC
                        ;IMP_RES_TAC LESS_EQ_SYM
                        ]
                 THEN IMP_RES_TAC
                        (MATCH_MP chain_less_eq
                         exseq_po
                        )
                 THEN IMP_RES_THEN
                        (IMP_RES_TAC o (SPEC "n':num"))
                        exseq_subseq_elts
                 THEN ASM_REWRITE_TAC[]
                ;IMP_RES_THEN
                        ( ASSUME_TAC
                        o (CONV_RULE (DEPTH_CONV BETA_CONV))
                        o (REWRITE_RULE [lengths])
                        )
                        (REWRITE_RULE[cpo;is_lub;is_ub]
                         lnum_cpo
                        )
                 THEN FIRST_ASSUM
                        ( ASSUME_TAC
                        o (CONV_RULE (DEPTH_CONV BETA_CONV))
                        o (REWRITE_RULE[lengths])
                        o CONJUNCT1
                        o (CONV_RULE FORALL_AND_CONV)
                        )
                 THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "k:num"))
                 THEN RES_TAC
                 THEN ASM_REWRITE_TAC[lengths]
                ;IMP_RES_TAC lub_fn_lemma
                 THEN ASM_REWRITE_TAC[]
                 THEN RES_TAC
                ]
);;


let exseq_subseq_as_length = prove_thm
(       `exseq_subseq_as_length`,
        "!C.
         chain $<=| C ==>
         !i j. length (C i) <-+ length (C j) = (C i) <=| (C j)",
        REPEAT STRIP_TAC
        THEN EQ_TAC
        THENL   [DISCH_TAC
                 THEN DISJ_CASES_SPLIT "i<=j"
                 THEN IMP_RES_TAC (MATCH_MP chain_less_eq exseq_po)
                 THEN IMP_RES_TAC LESS_EQ_SYM
                 THEN RES_THEN MP_TAC
                 THEN ASM_REWRITE_TAC[exseq_subseq]
                 THEN REPEAT STRIP_TAC
                 THEN IMP_RES_TAC (lnum_less_less_eq_trans)
                 THEN RES_TAC
                 THEN ASM_REWRITE_TAC[]
                ;REPEAT STRIP_TAC
                 THEN IMP_RES_TAC exseq_subseq_length
                ]
);;

let lub_exseq_is_lub = prove_thm
(       `lub_exseq_is_lub`,
        "!Ch. chain $<=| Ch ==> is_lub $<=| (lub_exseq Ch) Ch",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC[is_lub;is_ub]
        THEN IMP_RES_TAC lub_exseq_thm
        THEN IMP_RES_TAC length_chain
        THEN IMP_RES_TAC length_lemma
        THEN ASM_REWRITE_TAC [exseq_subseq;lub_exseq]
        THEN REPEAT STRIP_TAC
        THENL   [MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "n:num"))
                 THEN IMP_RES_TAC lnum_less_less_eq_trans
                 THEN IMP_RES_TAC lub_fn_lemma
                 THEN ASM_REWRITE_TAC[]
                 THEN DISJ_CASES_SPLIT "n<=j"
                 THENL  [ALL_TAC
                        ;IMP_RES_TAC LESS_EQ_SYM
                        ]
                 THEN IMP_RES_TAC
                        (MATCH_MP chain_less_eq
                         exseq_po
                        )
                 THEN IMP_RES_THEN
                        (IMP_RES_TAC o (SPEC "n':num"))
                        exseq_subseq_elts
                 THEN ASM_REWRITE_TAC[]
                ;IMP_RES_THEN
                        ( ASSUME_TAC
                        o (CONV_RULE (DEPTH_CONV BETA_CONV))
                        o (REWRITE_RULE [lengths])
                        )
                        (REWRITE_RULE[cpo;is_lub;is_ub]
                         lnum_cpo
                        )
                 THEN FIRST_ASSUM
                        ( ASSUME_TAC
                        o (CONV_RULE (DEPTH_CONV BETA_CONV))
                        o (REWRITE_RULE[lengths])
                        o CONJUNCT1
                        o (CONV_RULE FORALL_AND_CONV)
                        )
                 THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "k:num"))
                 THEN RES_TAC
                 THEN ASM_REWRITE_TAC[lengths]
                ;IMP_RES_TAC lub_fn_lemma
                 THEN ASM_REWRITE_TAC[]
                 THEN RES_TAC
                ]
);;

let lub_lub_exseq = prove_thm
(       `lub_lub_exseq`,
        "!Ch. chain $<=| Ch ==> (lub $<=| Ch = lub_exseq Ch)",
        REPEAT STRIP_TAC
        THEN ASSUME_TAC exseq_po
        THEN MAP_EVERY IMP_RES_TAC[lub_exseq_is_lub;lub_eq]
        THEN ASM_REWRITE_TAC[]
);;

let exseq_lub_length = prove_thm
(       `exseq_lub_length`,
        "!Ch. chain $<=| Ch ==>
         (length(lub $<=| Ch) = lub $<-+(lengths Ch))",
        REPEAT STRIP_TAC
        THEN MAP_EVERY IMP_RES_TAC[lub_lub_exseq;lub_exseq_thm]
        THEN ASM_REWRITE_TAC[]
);;

let exseq_lub_elts = prove_thm
(       `exseq_lub_elts`,
        "!Ch. chain $<=| Ch ==>
         !n.elt(WHOLE n)(lub $<=| Ch) =
                ((WHOLE n) <+ (length(lub $<=| Ch)) => lub_fn Ch n | (@x. T))",
        REPEAT STRIP_TAC
        THEN MAP_EVERY IMP_RES_TAC[lub_lub_exseq;lub_exseq_thm]
        THEN ASM_REWRITE_TAC[]
);;

let lub_fn_elt_n_SUC_n = prove_thm
(       `lub_fn_elt_n_SUC_n`,
        "!C n.
         chain $<=| C ==>
         WHOLE (SUC n) <+ lub $<-+ (lengths C) ==>
         ?j.
         (lub_fn C (SUC n) = elt (WHOLE(SUC n))(C j))
         /\ (lub_fn C n = elt (WHOLE n)(C j))
         /\ (WHOLE(SUC n) <+ length(C j))",
        REPEAT STRIP_TAC
        THEN SUPPOSE_TAC "WHOLE n <+ WHOLE(SUC n)"
        THEN REWRITE_TAC[lnum_less_reduce;LESS_SUC_REFL]
        THEN IMP_RES_TAC lnum_less_trans_alt
        THEN IMP_RES_TAC lub_fn_lemma
        THEN ASM_CASES_TAC "j<=j'"
        THENL   [ALL_TAC;IMP_RES_TAC LESS_EQ_SYM]
        THEN ASSUME_TAC exseq_po
        THEN IMP_RES_TAC chain_less_eq
        THENL   [EXISTS_TAC "j':num";EXISTS_TAC "j:num"]
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC exseq_subseq_elts
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC exseq_subseq_length
        THEN IMP_RES_TAC lnum_less_less_eq_trans
);;

new_special_symbol `<|`;;

let exseq_subseq_strict = new_infix_definition
(       `exseq_subseq_strict`,
        "!e d.
         <| e d = e <=| d /\ ~(e=d)"
);;

let exseq_strict_imp_subseq = prove_thm
(       `exseq_strict_imp_subseq`,
        "!e d. e <| d ==> e <=| d",
        REWRITE_TAC [exseq_subseq_strict]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
);;

let exseq_subseq_strict_subseq_trans = prove_thm
(       `exseq_subseq_strict_subseq_trans`,
        "!e d f.
         (e <| d ==> d <=| f ==> e <| f) /\
         (e <=| d ==> d <| f ==> e <| f)",
        REWRITE_TAC [exseq_subseq_strict]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC exseq_subseq_trans
        THEN FIRST_ASSUM SUBST_ALL_TAC
        THEN IMP_RES_TAC exseq_subseq_antisym
        THEN RES_TAC
);;

let exseq_subseq_strict_alt = prove_thm
(       `exseq_subseq_strict_alt`,
        "!e d.
         e <| d =
                (length e) <+ (length d) /\
                !n.(WHOLE n) <+ (length e) ==>
                        (elt (WHOLE n) e = elt (WHOLE n) d)",
        REPEAT GEN_TAC
        THEN REWRITE_TAC [exseq_subseq_strict;exseq_subseq]
        THEN EQ_TAC
        THEN DISCH_THEN STRIP_ASSUME_TAC
        THEN ASM_REWRITE_TAC[]
        THENL   [REWRITE_TAC [lnum_less]
                 THEN ASM_REWRITE_TAC[]
                 THEN UNDISCH_TAC "~((e:exseq) = d)"
                 THEN CONTRAPOS_TAC
                 THEN REWRITE_TAC[]
                 THEN DISCH_TAC
                 THEN IMP_RES_TAC exseq_eq
                ;DISJ_CASES_SPLIT "(e:exseq)=d"
                 THEN ASM_REWRITE_TAC[]
                 THENL  [FIRST_ASSUM SUBST_ALL_TAC
                         THEN IMP_RES_TAC lnum_not_less
                        ;ASM_REWRITE_TAC [lnum_less_eq_as_less]
                        ]
                ]
);;

let exseq_subseq_as_strict = prove_thm
(       `exseq_subseq_as_strict`,
        "!e d. e <=| d = e <| d \/ (e=d)",
        REWRITE_TAC [exseq_subseq_strict]
        THEN REPEAT GEN_TAC
        THEN EQ_TAC
        THEN DISCH_THEN STRIP_ASSUME_TAC
        THEN ASM_REWRITE_TAC [exseq_subseq_refl]
        THEN ONCE_REWRITE_TAC [DISJ_SYM]
        THEN REWRITE_TAC [EXCLUDED_MIDDLE]
);;

let exseq_subseq_strict_not_swop = prove_thm
(       `exseq_subseq_strict_not_swop`,
        "!e d. e <| d ==> ~d <=| e",
        REPEAT STRIP_TAC
        THEN MAP_EVERY IMP_RES_TAC
                [exseq_strict_imp_subseq
                ;exseq_subseq_antisym
                ;exseq_subseq_strict
                ]
);;

let exseq_subseq_strict_length = prove_thm
(       `exseq_subseq_strict_length`,
        "!e d. e <| d ==> (length e) <+ (length d)",
        REWRITE_TAC [exseq_subseq_strict]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC exseq_subseq_length
        THEN REWRITE_ASM [exseq_subseq;lnum_less_eq_as_less]
        THEN FIRST_ASSUM DISJ_CASES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC exseq_eq
        THEN RES_TAC
);;

let exseq_subseq_strict_elts = prove_thm
(       `exseq_subseq_strict_elts`,
        "!e d. e <| d ==>
                (!n. WHOLE n <+ length e ==>
                        (elt (WHOLE n) e = elt (WHOLE n) d)
                )",
        REPEAT GEN_TAC
        THEN REWRITE_TAC[exseq_subseq_strict;exseq_subseq]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
);;

let lemma1 = PROVE
(       "!e d. e <| d ==> TERM e",
        REWRITE_TAC[TERM]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC exseq_subseq_strict_length
        THEN IMP_RES_TAC lnum_less_WHOLE
);;

let lemma2 = PROVE
(       "!e d.
         e <| d ==>
         WHOLE 1 <+ (length d -- PR(length e))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC exseq_subseq_strict_length
        THEN IMP_RES_THEN (ASSUME_TAC o (REWRITE_RULE[TERM])) lemma1
        THEN IMP_RES_TAC lnum_less_eq_PR
        THEN IMP_RES_TAC PR_WHOLE
        THEN IMP_RES_TAC lnum_strict_sub_mono
        THEN SUPPOSE_TAC "WHOLE 1 <-+ (length e -- (PR(length e)))"
        THENL   [IMP_RES_TAC lnum_less_eq_less_trans
                ;ASSUME_TAC (SPEC "e:exseq" length_min)
                 THEN IMP_RES_TAC lnum_less_imp_less_eq
                 THEN IMP_RES_TAC lnum_PR_plus
                 THEN ASM_REWRITE_TAC [lnum_less_eq_po]
                ]
);;

new_special_symbol `//`;;

let exseq_subtract = new_infix_definition
(       `exseq_subtract`,
        "!e d:exseq. // d e = mk_exseq
                        ((\n. elt((WHOLE n) ++ PR(length e)) d),
                         (length d -- PR(length e))
                        )"
);;

let exseq_subtract_thm = prove_thm
(       `exseq_subtract_thm`,
        "!e d.
         e <| d ==>
                (length (d // e) = length d -- PR(length e)) /\
                (!n. elt(WHOLE n)(d // e) =
                        ((WHOLE n <+ (length d -- PR(length e)))
                                => (elt((WHOLE n) ++ PR(length e)) d)
                                | (@x:state.T)
                        )
                )",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC [exseq_subtract]
        THEN IMP_RES_TAC lemma2
        THEN IMP_RES_TAC mk_exseq_thm
        THEN ASM_REWRITE_TAC[]
        THEN BETA_TAC
        THEN REWRITE_TAC[]
);;

let lemma3 = PROVE
(       "!e d. e <| d ==> (first(d // e) = last e)",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC [last;first]
        THEN IMP_RES_TAC exseq_subtract_thm
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC lemma2
        THEN SUPPOSE_TAC "WHOLE 0 <+ WHOLE 1"
        THENL   [IMP_RES_TAC lnum_less_trans_alt
                 THEN ASM_REWRITE_TAC[lnum_plus_id]
                 THEN ASSUME_TAC (SPEC "e:exseq" length_min)
                 THEN IMP_RES_TAC lnum_less_trans_alt
                 THEN IMP_RES_TAC lemma1
                 THEN REWRITE_ASM
                        [TERM
                        ;exseq_subseq_strict
                        ;exseq_subseq
                        ]
                 THEN IMP_RES_TAC lnum_PR_less
                 THEN UNDISCH_ALL_TAC
                 THEN lnum_cases_TAC ["length e"]
                 THEN REWRITE_TAC [is_WHOLE;PR]
                 THEN REPEAT DISCH_TAC
                 THEN RES_TAC
                 THEN ASM_REWRITE_TAC[]
                ;REWRITE_TAC[lnum_less_reduce]
                 THEN REDUCE_TAC
                ]
);;


let lemma4 = PROVE
(       "!e d. e <| d ==> (length(e <*> (d // e)) = length d)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC exseq_subseq_strict_length
        THEN IMP_RES_TAC exseq_subtract_thm
        THEN IMP_RES_TAC lemma3
        THEN IMP_RES_TAC lemma1
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[PR_fn]
        THEN REWRITE_ASM [TERM]
        THEN ASSUME_TAC (SPEC "e:exseq" length_min)
        THEN IMP_RES_TAC lnum_less_imp_less_eq
        THEN SUPPOSE_TAC "is_WHOLE(WHOLE 1)"
        THEN REWRITE_TAC [is_WHOLE]
        THEN IMP_RES_TAC lnum_less_eq_add_sub
        THEN IMP_RES_TAC lnum_add_sub
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC lnum_sub_add
);;

let exseq_subtract_join = prove_thm
(       `exseq_subtract_join`,
        "!e d. e <| d ==> (e <*> (d // e) = d)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC lemma3
        THEN IMP_RES_TAC lemma1
        THEN IMP_RES_TAC lemma4
        THEN ONCE_REWRITE_TAC [SYM_th exseq_eq]
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_elts
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC exseq_subseq_strict_elts
        THEN IMP_RES_TAC exseq_subtract_thm
        THEN UNDISCH_ALL_TAC
        THEN REWRITE_TAC [TERM]
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC [PR;lnum_sub;is_WHOLE]
        THEN REPEAT DISCH_TAC
        THEN COND_CASES_TAC
        THENL   [RES_TAC
                ;IMP_RES_TAC lnum_less_contrapos
                 THEN ASM_REWRITE_TAC[lnum_plus]
                 THEN ONCE_REWRITE_TAC [SYM_th lnum_plus]
                 THEN REWRITE_TERM "WHOLE(n - (n' - 1))"
                        (SYM_th lnum_sub)
                 THEN ASSUME_TAC (SPEC "n':num" lnum_less_eq_PR_alt)
                 THEN IMP_RES_TAC
                        (REWRITE_RULE [trans] lnum_less_eq_trans)
                 THEN REWRITE_ASM [PR]
                 THEN IMP_RES_TAC lnum_strict_sub_mono_alt
                 THEN ASM_REWRITE_TAC[]
                 THEN ONCE_REWRITE_TAC [lnum_plus_sym]
                 THEN SUPPOSE_TAC "is_WHOLE(WHOLE(n'-1))"
                 THEN REWRITE_TAC [is_WHOLE]
                 THEN IMP_RES_TAC lnum_sub_add
                 THEN ASM_REWRITE_TAC[]
                ]
);;

let lemma6 = PROVE
(       "!Ch.
         chain $<=| Ch ==>
         !i j. first (Ch i) = first (Ch j)",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC [first]
        THEN SUPPOSE_TAC "WHOLE 0 <+ WHOLE 1"
        THENL   [DISJ_CASES_SPLIT "i<=j"
                 THEN IMP_RES_TAC LESS_EQ_SYM
                 THEN IMP_RES_TAC (MATCH_MP chain_less_eq exseq_po)
                 THENL  [ASSUME_TAC (SPEC "(Ch:num->exseq) i" length_min)
                        ;ASSUME_TAC (SPEC "(Ch:num->exseq) j" length_min)
                        ]
                 THEN IMP_RES_TAC (REWRITE_RULE[trans] lnum_less_trans)
                 THEN IMP_RES_TAC exseq_subseq_elts
                 THEN ASM_REWRITE_TAC[]
                ;REWRITE_TAC [lnum_less_reduce]
                 THEN CONV_TAC LT_CONV
                ]
);;


let join_inc = prove_thm
(       `join_inc`,
        "!e d.
         TERM e ==>
         (first d = last e) ==>
         e <| (e <*> d)",
        REPEAT STRIP_TAC
        THEN REWRITE_TAC [exseq_subseq_strict_alt]
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[]
        THEN ASSUME_TAC (SPEC "d:exseq" length_min)
        THEN SUPPOSE_TAC "WHOLE 1 <-+ WHOLE 1"
        THEN REWRITE_TAC [lnum_less_eq_po]
        THEN IMP_RES_TAC lnum_PR_mono_strict
        THEN REWRITE_ASM [PR;TERM]
        THEN UNDISCH_ALL_TAC
        THEN REDUCE_TAC
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC lnum_plus_inc_strict
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_ASM [SYM_th TERM]
        THEN IMP_RES_TAC join_elts
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN ASM_REWRITE_TAC[]
);;


let lemma8 = PROVE
(       "!n n'. 0 < n ==> ~((n + (n'-1)) < n')",
        REWRITE_TAC [NOT_LESS]
        THEN REPEAT STRIP_TAC
        THEN DISJ_CASES_SPLIT "0<n'"
        THENL   [IMP_RES_TAC ADD1_CHOOSE
                 THEN FILTER_ASM_REWRITE_TAC
                        (\t.t="n = m' + 1")[SYM_th ADD_ASSOC]
                 THEN ONCE_REWRITE_TERM "1+(n'-1)" ADD_SYM
                 THEN IMP_RES_THEN (ASSUME_TAC o REDUCE_RULE) LESS_EQ
                 THEN IMP_RES_TAC SUB_ADD
                 THEN FILTER_ASM_REWRITE_TAC
                        (\t.t="(n'-1)+1=n'") []
                 THEN ONCE_REWRITE_TAC [ADD_SYM]
                 THEN REWRITE_TAC [LESS_EQ_ADD]
                ;IMP_RES_TAC NOT_LESS
                 THEN ASSUME_TAC (SPEC "n':num" ZERO_LESS_EQ)
                 THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
                 THEN ONCE_ASM_REWRITE_TAC[]
                 THEN REDUCE_TAC
                 THEN REWRITE_TAC [ADD_0;ZERO_LESS_EQ]
                ]
);;

let join_length_parts = prove_thm
(       `join_length_parts`,
        "!e d.
         TERM e ==>
         (first d = last e) ==>
         ((length e <+ length(e<*>d) /\
          (TERM d ==> length d <-+ length(e<*>d))))",
        REPEAT GEN_TAC
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[TERM]
        THEN ASSUME_TAC (SPEC "d:exseq" length_min)
        THEN SUPPOSE_TAC "WHOLE 1 <-+ WHOLE 1"
        THEN REWRITE_TAC [lnum_less_eq_reduce]
        THEN REDUCE_TAC
        THEN IMP_RES_THEN
                (IMP_RES_THEN
                 (ASSUME_TAC
                 o REDUCE_RULE
                 o (REWRITE_RULE[PR])
                 )
                )
                lnum_PR_mono_strict
        THEN REWRITE_ASM [TERM]
        THEN IMP_RES_TAC lnum_plus_inc_strict
        THEN ASM_REWRITE_TAC[PR_fn]
        THEN ASSUME_TAC lnum_zero_less_one
        THEN ASSUME_TAC (SPEC "e:exseq" length_min)
        THEN ASSUME_TAC
                (SPECL ["WHOLE 0";"WHOLE 1";"length e"]
                 lnum_less_trans_alt
                )
        THEN RES_TAC
        THEN UNDISCH_ALL_TAC
        THEN lnum_cases_TAC ["length d";"length e"]
        THEN REWRITE_TAC
                [is_WHOLE
                ;TERM
                ;lnum_less_reduce
                ;lnum_less_eq_reduce
                ;lnum_plus
                ;lnum_sub
                ;PR
                ]
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC ADD1_CHOOSE
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t="n' = m + 1") []
        THEN ONCE_REWRITE_TAC [SYM_th ADD_ASSOC]
        THEN ONCE_REWRITE_TERM "1+(n-1)" ADD_SYM
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN IMP_RES_TAC SUB_ADD
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t="(n-1)+1 = n") []
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN REWRITE_TAC [LESS_EQ_ADD]
);;

let lemma9 = PROVE
(       "!n f e.
         WHOLE n <+ length f ==>
         is_WHOLE (length e) ==>
         WHOLE n <+ length e ++ PR(length f)",
        REPEAT GEN_TAC
        THEN MP_TAC (SPEC "e:exseq" length_min)
        THEN MP_TAC (SPEC "f:exseq" length_min)
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["length f"]
        THEN REWRITE_TAC [PR;lnum_plus;lnum_less_reduce]
        THEN REPEAT DISCH_TAC
        THEN SUPPOSE_TAC "0 < 1"
        THEN REDUCE_TAC
        THEN IMP_RES_TAC LESS_TRANS
        THEN IMP_RES_TAC ADD1_CHOOSE
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t="n'=m'+1") []
        THEN ONCE_REWRITE_TAC [SYM_th ADD_ASSOC]
        THEN ONCE_REWRITE_TERM
                "1+(n''-1)" ADD_SYM
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN IMP_RES_TAC SUB_ADD
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t="(n'' - 1) + 1 = n''") []
        THEN ONCE_REWRITE_TAC [ADD_SYM]
        THEN ASSUME_TAC (SPECL["n'':num";"m':num"] LESS_EQ_ADD)
        THEN IMP_RES_TAC LESS_LESS_EQ_TRANS
);;

let lemma10 = PROVE
(       "!e f n.
         is_WHOLE(length e) ==>
         WHOLE n <+ length f ==>
         (WHOLE n ++ PR(length e)) <+ (length e ++ PR(length f))",
        REPEAT GEN_TAC
        THEN MP_TAC (SPEC "e:exseq" length_min)
        THEN MP_TAC (SPEC "f:exseq" length_min)
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN lnum_cases_TAC ["length f"]
        THEN REWRITE_TAC [PR;lnum_plus;lnum_less_reduce]
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
        THEN IMP_RES_TAC (LESS_EQ_ADD_SUB)
        THEN APPLY_TO "!a. (a + n'') - 1 = a + (n'' - 1)"
                (\th.REWRITE_TAC[SYM_th th])
        THEN ONCE_REWRITE_TERM "(n'+n'')-1" ADD_SYM
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC (SYM_th LESS_MONO_ADD_EQ)
        THEN ASM_REWRITE_TAC[]
);;

let join_cancel = prove_thm
(       `join_cancel`,
        "!e d f.
         TERM e ==>
         (first d = last e) ==>
         (first f = last e) ==>
         ((e<*>d = e<*>f) = (d = f))",
        REPEAT STRIP_TAC
        THEN EQ_TAC
        THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC join_elts
        THEN IMP_RES_TAC join_length
        THEN ONCE_REWRITE_TAC [SYM_th exseq_eq]
        THEN SUPPOSE_TAC "length d = length f"
        THEN ASM_REWRITE_TAC[]
        THENL   [REPEAT STRIP_TAC
                 THEN REWRITE_ASSUM [TERM] "TERM e"
                 THEN IMP_RES_TAC lemma10
                 THEN REWRITE_ASM[]
                 THEN UNDISCH_ALL_TAC
                 THEN lnum_cases_TAC ["length e"]
                 THEN REWRITE_TAC
                        [is_WHOLE
                        ;PR
                        ;lnum_plus
                        ;lnum_less_reduce
                        ;lnum_sub
                        ]
                 THEN REPEAT DISCH_TAC
                 THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "n+(n'-1)"))
                 THEN UNDISCH_TAC
                        "((n + (n' - 1)) < n' =>
                        elt(WHOLE(n + (n' - 1)))e |
                           ((WHOLE(n + (n' - 1))) <+
                                ((WHOLE n') ++ (PR(length f))) =>
                            elt(WHOLE((n + (n' - 1)) - (n' - 1)))f |
                             (@q. T))) =
                              ((n + (n' - 1)) < n' =>
                               elt(WHOLE(n + (n' - 1)))e |
                               ((WHOLE(n + (n' - 1))) <+
                                        ((WHOLE n') ++ (PR(length f))) =>
                                elt(WHOLE((n + (n' - 1)) - (n' - 1)))d |
                              (@q. T)))"
                 THEN FILTER_ASM_REWRITE_TAC
                        (\t.t= "(WHOLE(n + (n' - 1))) <+
                                        ((WHOLE n') ++ (PR(length f)))")
                        []
                 THEN DISJ_CASES_SPLIT "0<n"
                 THENL  [IMP_RES_TAC lemma8
                         THEN FILTER_ASM_REWRITE_TAC
                                (\t.t="!n'. ~(n + (n' - 1)) < n'") [ADD_SUB]
                         THEN DISCH_THEN SUBST1_TAC
                         THEN REFL_TAC
                        ;IMP_RES_TAC NOT_LESS
                         THEN ASSUME_TAC (SPEC "n:num" ZERO_LESS_EQ)
                         THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
                         THEN APPLY_TO "n=0" SUBST_ALL_TAC
                         THEN REWRITE_TAC
                                [ONCE_REWRITE_RULE[ADD_SYM]ADD_0
                                ;SUB_EQUAL_0
                                ;SYM_th first
                                ]
                         THEN FILTER_ASM_REWRITE_TAC
                                (\t.t="first f = last e") []
                         THEN FILTER_ASM_REWRITE_TAC
                                (\t.t="first d = last e")[]
                        ]
                ;UNDISCH_TAC
                        "length(e <*> d) = (length e) ++ (PR(length d))"
                 THEN ASM_REWRITE_TAC[]
                 THEN UNDISCH_TAC "TERM e"
                 THEN REWRITE_TAC [TERM]
                 THEN REPEAT DISCH_TAC
                 THEN ASSUME_TAC (SPEC "length e" lnum_plus_cancel)
                 THEN RES_TAC
                 THEN ASSUME_TAC (SPEC "f:exseq" length_min)
                 THEN ASSUME_TAC (SPEC "d:exseq" length_min)
                 THEN SUPPOSE_TAC "WHOLE 0 <+ WHOLE 1"
                 THEN REWRITE_TAC [lnum_less_reduce]
                 THEN REDUCE_TAC
                 THEN IMP_RES_TAC lnum_less_trans_alt
                 THEN IMP_RES_TAC  PR_one_one
                 THEN FILTER_ASM_REWRITE_TAC
                        (\t.t="length f = length d") []

                ]
);;


let lemma11 = PROVE
(       "!e d f.
         TERM e ==>
         (first d = last e) ==>
         (first f = last e) ==>
         (length(e<*>d) <+ length(e<*>f) =
                length d <+ length f)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[]
        THEN REWRITE_ASM[TERM]
        THEN IMP_RES_TAC lnum_less_plus_cancel
        THEN ASM_REWRITE_TAC[]
        THEN ASSUME_TAC (SPEC "d:exseq" length_min)
        THEN ASSUME_TAC lnum_zero_less_one
        THEN IMP_RES_TAC lnum_less_trans_alt
        THEN IMP_RES_TAC lnum_PR_mono_strict_alt
        THEN ASM_REWRITE_TAC[]
);;



let lemma12 = PROVE
(       "!e n.
         TERM e ==>
         ?n'. WHOLE n' = (WHOLE n) ++ (PR(length e))",
        REWRITE_TAC [TERM]
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC [is_WHOLE;PR;lnum_plus]
        THEN EXISTS_TAC "n+(n'-1)"
        THEN REWRITE_TAC[]
);;

let lemma13 = PROVE
(       "!n e.
         ~(n=0) ==> ~((WHOLE n) ++ (PR(length e))) <+ (length e)",
        REPEAT GEN_TAC
        THEN lnum_cases_TAC["length e"]
        THEN REWRITE_TAC
                [PR
                ;lnum_less_reduce
                ;lnum_not_less
                ;lnum_plus
                ]
        THEN DISCH_THEN (ASSUME_TAC o SYM_th)
        THEN DISJ_CASES_TAC (SPEC "n:num" LESS_0_CASES)
        THEN RES_TAC
        THEN IMP_RES_TAC lemma8
        THEN ASM_REWRITE_TAC[]
);;


let exseq_subseq_strict_join_cancel = prove_thm
(       `exseq_subseq_strict_join_cancel`,
        "!e d f.
         TERM e ==>
         (first d = last e) ==>
         (first f = last e) ==>
         ((e<*>d) <| (e<*>f) = d <| f)",
        REWRITE_TAC [exseq_subseq_strict_alt]
        THEN REPEAT STRIP_TAC
        THEN ASSUME_TAC (SPEC_ALL lemma11)
        THEN EQ_TAC
        THEN DISCH_THEN STRIP_ASSUME_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_TAC join_elts
        THEN IMP_RES_TAC join_length
        THENL   [ASSUME_TAC (SPECL["e:exseq";"d:exseq";"n:num"] lemma10)

                 THEN IMP_RES_THEN (CHOOSE_TAC o SPEC_ALL) lemma12
                 THEN REWRITE_ASSUM [TERM] "TERM e"
                 THEN ASSUME_TAC
                        (SPECL["WHOLE n";"length d";"length f"]
                         lnum_less_trans_alt
                        )
                 THEN RES_TAC
                 THEN IMP_RES_TAC lemma10
                 THEN UNDISCH_TAC
                        "!n.
                       (WHOLE n) <+ (length(e <*> d)) ==>
                       (elt(WHOLE n)(e <*> d) = elt(WHOLE n)(e <*> f))"
                 THEN ASM_REWRITE_TAC[]
                 THEN DISCH_THEN (MP_TAC o (SPEC "n':num"))
                 THEN IMP_RES_TAC PR_WHOLE
                 THEN IMP_RES_TAC lnum_add_sub
                 THEN ASM_REWRITE_TAC[]
                 THEN DISJ_CASES_SPLIT "n=0"
                 THENL  [ASM_REWRITE_TAC [SYM_th first]
                        ;IMP_RES_TAC lemma13
                         THEN ASM_REWRITE_TAC[]
                        ]
                ;IMP_RES_TAC lnum_less_trans_alt
                 THEN ASSUME_TAC (SPEC "e:exseq" length_min)
                 THEN ASSUME_TAC (SPEC "d:exseq" length_min)
                 THEN ASM_REWRITE_TAC[]
                 THEN COND_CASES_TAC
                 THEN REWRITE_TAC[]
                 THEN REWRITE_ASSUM [TERM] "TERM e"
                 THEN UNDISCH_TAC "~(WHOLE n) <+ (length e)"
                 THEN IMP_RES_TAC is_WHOLE_choose
                 THEN ASM_REWRITE_TAC[]
                 THEN DISCH_TAC
                 THEN IMP_RES_TAC lnum_less_contrapos
                 THEN APPLY_TO "length e = WHOLE n'" SUBST_ALL_TAC
                 THEN IMP_RES_TAC lnum_less_eq_PR
                 THEN IMP_RES_TAC lnum_less_eq_po
                 THEN IMP_RES_TAC PR_WHOLE
                 THEN IMP_RES_TAC lnum_strict_plus_sub_move
                 THEN UNDISCH_TAC  "(WHOLE n) <+ (length(e <*> d))"
                 THEN FILTER_ASM_REWRITE_TAC
                        (\t.t= "length(e <*> d) = WHOLE n' ++ (PR(length d))"  ) []
                                 THEN ONCE_REWRITE_TAC [SYM_th lnum_plus_sym]
                 THEN ONCE_REWRITE_TAC [SYM_th lnum_plus_sym]
                 THEN IMP_RES_TAC lnum_less_imp_less_eq
                 THEN IMP_RES_TAC lnum_PR_shift
                 THEN FILTER_ASM_REWRITE_TAC
                        (\t.t="(PR(length d)) ++ (WHOLE n') = (length d) ++ (PR(WHOLE n'))")[]
                 THEN DISCH_TAC
                 THEN RES_TAC
                 THEN UNDISCH_TAC
                         "((WHOLE n) -- (PR(WHOLE n'))) <+ (length d)"
                 THEN REWRITE_TAC [lnum_sub;PR]
                 THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "n+(n'-1)"))
                 THEN DISCH_TAC
                 THEN RES_TAC
                ]
);;

let exseq_subseq_join_cancel = prove_thm
(       `exseq_subseq_join_cancel`,
        "!e d f.
         TERM e ==>
         (first d = last e) ==>
         (first f = last e) ==>
         ((e<*>d) <=| (e<*>f) = d <=| f)",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC exseq_subseq_strict_join_cancel
        THEN IMP_RES_TAC join_cancel
        THEN ASM_REWRITE_TAC[exseq_subseq_as_strict]
);;



let exseq_subseq_first = prove_thm
(       `exseq_subseq_first`,
        "!e d. e <=| d ==> (first e = first d)",
        REWRITE_TAC [exseq_subseq;first]
        THEN REPEAT STRIP_TAC
        THEN ASSUME_TAC (SPEC "e:exseq" length_min)
        THEN ASSUME_TAC lnum_zero_less_one
        THEN IMP_RES_TAC lnum_less_trans_alt
        THEN RES_TAC
);;

let exseq_subseq_join_subtract = prove_thm
(       `exseq_subseq_join_subtract`,
        "!e d k.
         TERM e ==>
         (first d = last e) ==>
         e <| k ==>
         ((e <*> d) <=| k = d <=| (k // e))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC lemma3
        THEN IMP_RES_TAC exseq_subseq_join_cancel
        THEN IMP_RES_TAC exseq_subtract_join
        THEN ASSUM_LIST (ONCE_REWRITE_TAC o SYML_th)
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t ="e <*> (k // e) = k") []
);;

let join_distrib_lub = prove_thm
(       `join_distrib_lub`,
        "!e Ch.
         chain $<=| Ch ==>
         TERM e ==>
         (first (Ch 0) = last e) ==>
         (e <*> (lub $<=| Ch) = lub $<=| (\i. e<*>(Ch i)))",
        REPEAT STRIP_TAC
        THEN SUPPOSE_TAC "is_lub $<=| (e<*>(lub $<=| Ch)) (\i.e<*>(Ch i))"
        THENL   [ASSUME_TAC exseq_po
                 THEN IMP_RES_TAC lub_eq
                ;IMP_RES_THEN (MP_TAC o (SPEC "0")) lemma6
                 THEN ASM_REWRITE_TAC[is_lub]
                 THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
                 THEN DISCH_TAC
                 THEN CONJ_TAC
                 THEN REWRITE_TAC [is_ub]
                 THEN GEN_TAC
                 THEN BETA_TAC
                 THENL  [IMP_RES_TAC
                                (REWRITE_RULE[cpo;is_lub;is_ub] exseq_cpo)
                         THEN MAPFILTER_ASSUM (ASSUME_TAC o (SPEC "n:num"))
                         THEN IMP_RES_TAC exseq_subseq_first
                         THEN POP_IT "first(lub $<=| Ch) = first(lub $<=| Ch)"
                         THEN APPLY_TO "first(Ch (n:num)) = last e" MP_TAC
                         THEN FILTER_ASM_REWRITE_TAC
                                (\t.t="first(Ch n) = first(lub $<=| Ch)")[]
                         THEN DISCH_TAC
                         THEN IMP_RES_TAC exseq_subseq_join_cancel
                        ;DISCH_THEN (FORK (ASSUME_TAC o (SPEC "0")) MP_TAC)
                         THEN IMP_RES_TAC join_inc
                         THEN IMP_RES_TAC
                                exseq_subseq_strict_subseq_trans
                         THEN SUPPOSE_TAC
                                "(!n:num. (e <*> (Ch n)) <=| k) =
                                 (!n. Ch n <=| (k//e))"
                         THENL  [ASM_REWRITE_TAC[]
                                 THEN DISCH_TAC
                                 THEN IMP_RES_TAC
                                        (REWRITE_RULE[cpo;is_lub;is_ub]
                                         exseq_cpo
                                        )
                                 THEN IMP_RES_TAC exseq_subseq_join_subtract
                                 THEN MAPFILTER_ASSUM
                                        (ASSUME_TAC o (SPEC "0:num"))
                                 THEN IMP_RES_TAC exseq_subseq_first
                                 THEN UNDISCH_TAC "first(Ch 0) = last e"
                                 THEN FILTER_ASM_REWRITE_TAC
                                        (\t.t= "first(Ch 0) =
                                                first(lub $<=| Ch)")[]
                                 THEN DISCH_TAC
                                 THEN IMP_RES_TAC exseq_subseq_join_subtract
                                ;AP_TERM_TAC
                                 THEN CONV_TAC FUN_EQ_CONV
                                 THEN BETA_TAC
                                 THEN GEN_TAC
                                 THEN MAPFILTER_ASSUM
                                        (ASSUME_TAC o (SPEC "n:num"))
                                 THEN IMP_RES_TAC exseq_subseq_join_subtract
                                ]
                        ]
                ]
);;

let lub_first = prove_thm
(       `lub_first`,
        "!Ch.
         chain $<=| Ch ==> (first(lub $<=| Ch) = first(Ch 0))",
        REPEAT STRIP_TAC
        THEN IMP_RES_TAC(REWRITE_RULE[cpo;is_lub;is_ub] exseq_cpo)
        THEN FIRST_ASSUM
                (STRIP_ASSUME_TAC
                o (REWRITE_RULE[exseq_subseq])
                o (SPEC "0")
                )
        THEN ASSUME_TAC (SPEC "(Ch:num->exseq) 0" length_min)
        THEN ASSUME_TAC lnum_zero_less_one
        THEN IMP_RES_TAC lnum_less_trans_alt
        THEN RES_TAC
        THEN ASM_REWRITE_TAC [first]
);;

let lemma14 = PROVE
(       "!e.
         TERM e ==>
         !n.?n'. WHOLE n' = (WHOLE n -- (PR(length e)))",
        REWRITE_TAC [TERM]
        THEN GEN_TAC
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC
                [lnum_sub;PR;is_WHOLE]
        THEN GEN_TAC
        THEN EXISTS_TAC "n''-(n-1)"
        THEN REFL_TAC
);;

let lemma15 = PROVE
(       "!e.
         TERM e ==> (?n. length e = WHOLE n)",
        GEN_TAC
        THEN REWRITE_TAC[TERM]
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC [is_WHOLE]
        THEN EXISTS_TAC "n:num"
        THEN REFL_TAC
);;

let lemma16 = PROVE
(       "!e d n.
         TERM e ==>
         (first d = last e) ==>
         (~WHOLE n <+ length e) ==>
         ((WHOLE n) <+ (length(e<*>d)) =
         ((WHOLE n) -- (PR(length e))) <+ (length d))",
        REPEAT GEN_TAC
        THEN DISCH_TAC THEN DISCH_TAC
        THEN IMP_RES_TAC join_length
        THEN ASM_REWRITE_TAC[]
        THEN SUPPOSE_TAC "is_WHOLE(WHOLE n)"
        THEN REWRITE_TAC[is_WHOLE]
        THEN REWRITE_ASM[TERM]
        THEN DISCH_TAC
        THEN IMP_RES_TAC lnum_less_contrapos_alt
        THEN ASSUME_TAC (SPEC "e:exseq" length_min)
        THEN ASSUME_TAC (SPEC "d:exseq" length_min)
        THEN IMP_RES_TAC lnum_less_imp_less_eq
        THEN IMP_RES_TAC lnum_PR_shift
        THEN IMP_RES_TAC lnum_plus_sym1
        THEN ONCE_ASM_REWRITE_TAC[]
        THEN APPLY_TO
                "(PR(length d)) ++ (length e) = (length d) ++ (PR(length e))"
                SUBST1_TAC
        THEN IMP_RES_TAC PR_WHOLE
        THEN IMP_RES_TAC lnum_less_eq_PR
        THEN IMP_RES_TAC lnum_less_eq_po
        THEN IMP_RES_TAC lnum_strict_plus_sub_move
        THEN FILTER_ASM_REWRITE_TAC
                (\t.t= "!l2.
                 ((WHOLE n) -- (PR(length e))) <+ l2 =
                 (WHOLE n) <+ (l2 ++ (PR(length e)))") []
);;


let lemma17 = PROVE
(       "!e. TERM e ==> is_WHOLE((WHOLE n)--(PR(length e)))",
         GEN_TAC
         THEN REWRITE_TAC[TERM]
         THEN lnum_cases_TAC ["length e"]
         THEN REWRITE_TAC
                [is_WHOLE
                ;PR
                ;lnum_sub
                ]
);;

let join_assoc = prove_thm
(       `join_assoc`,
        "!e d f.
         TERM e ==>
         TERM d ==>
         (first d = last e) ==>
         (first f = last d) ==>
         (e <*> (d <*> f) = (e <*> d) <*> f)",
        REPEAT STRIP_TAC
        THEN ONCE_REWRITE_TAC [SYM_th exseq_eq]
        THEN IMP_RES_TAC join_inc
        THEN IMP_RES_TAC exseq_strict_imp_subseq
        THEN IMP_RES_TAC exseq_subseq_first
        THEN IMP_RES_TAC join_TERM
        THEN IMP_RES_TAC join_last
        THEN APPLY_TO  "first d = last e" MP_TAC
        THEN APPLY_TO "first f = last d" MP_TAC
        THEN FILTER_ASM_REWRITE_TAC (\t.t="first d = first(d <*> f)")[]
        THEN APPLY_TO  "last(e <*> d) = last d" (SUBST1_TAC o SYM_th)
        THEN REPEAT DISCH_TAC
        THEN IMP_RES_TAC join_length
        THEN REV_SUPPOSE_TAC
                "length(e <*> (d <*> f)) = length((e <*> d) <*> f)"
        THENL   [ASM_REWRITE_TAC[PR_fn]
                 THEN ASSUME_TAC (SPEC "d:exseq" length_min)
                 THEN ASSUME_TAC (SPEC "f:exseq" length_min)
                 THEN UNDISCH_ALL_TAC
                 THEN REWRITE_TAC [TERM]
                 THEN lnum_cases_TAC ["length e";"length d"]
                 THEN REWRITE_TAC [is_WHOLE]
                 THEN lnum_cases_TAC ["length f"]
                 THEN REWRITE_TAC
                        [lnum_plus
                        ;lnum_sub
                        ;lnum_less_reduce
                        ;lnum_const_one_one
                        ]
                 THEN REPEAT DISCH_TAC
                 THEN ONCE_REWRITE_TERM "(n' + (n'' - 1))-1" ADD_SYM
                 THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
                 THEN IMP_RES_TAC LESS_EQ_ADD_SUB
                 THEN ASM_REWRITE_TAC []
                 THEN ONCE_REWRITE_TERM "(n'' - 1) + (n' - 1)" ADD_SYM
                 THEN REWRITE_TAC [ADD_ASSOC]
                ;ASSUM_REDUCE_TAC
                 THEN IMP_RES_TAC join_elts
                 THEN REPEAT STRIP_TAC
                 THEN MAPFILTER_ASSUM
                        ((\th.REWRITE_TAC[th]) o (SPEC "n:num"))
                 THEN ASSUM_LIST
                        ((REWRITE_TERML "length((e<*>d)<*>f)") o SYML_th)
                 THEN ASSUM_REDUCE_TAC
                 THEN COND_CASES_TAC
                 THENL  [IMP_RES_TAC exseq_subseq_length
                         THEN IMP_RES_TAC lnum_less_less_eq_trans
                         THEN ASSUM_REDUCE_TAC
                         THEN ONCE_ASM_REWRITE_TAC[]
                         THEN ASSUM_REDUCE_TAC
                        ;COND_CASES_TAC
                         THENL  [IMP_RES_TAC lemma16
                                 THEN ASSUME_TAC(SPEC "e:exseq" lemma17)
                                 THEN RES_TAC
                                 THEN IMP_RES_TAC is_WHOLE_choose
                                 THEN ASM_REWRITE_TAC[]
                                 THEN ASSUM_LIST
                                        ((REWRITE_TERML "WHOLE n'") o SYML_th)
                                 THEN ASSUM_REDUCE_TAC
                                ;ASSUME_TAC(SPEC "e:exseq" lemma17)
                                 THEN RES_TAC
                                 THEN IMP_RES_TAC is_WHOLE_choose
                                 THEN ASM_REWRITE_TAC[]
                                 THEN APPLY_TO
                                        "(WHOLE n) -- (PR(length e)) =
                                          WHOLE n'"
                                        (SUBST1_TAC o SYM_th)
                                 THEN ASSUME_TAC
                                        (SPECL["e:exseq";"d:exseq";"n:num"]
                                         lemma16)
                                 THEN RES_TAC
                                 THEN MAPFILTER_ASSUM (ASSUME_TAC o CONTRAPOS)
                                 THEN RES_TAC
                                 THEN FILTER_ASM_REWRITE_TAC
                                        (\t.t= "~((WHOLE n) -- (PR(length e)))
                                                 <+ (length d)"  )[]
                                 THEN ASSUME_TAC
                                        (SPECL["e:exseq";"d<*>f";"n:num"]
                                         lemma16)
                                 THEN RES_TAC
                                 THEN APPLY_TO
                                         "length(d <*> f) =
                                          (length d) ++ (PR(length f))"
                                          (SUBST1_TAC o SYM_th)
                                 THEN ASSUM_REDUCE_TAC
                                 THEN IMP_RES_TAC lemma15
                                 THEN MP_TAC (SPEC "e:exseq" length_min)
                                 THEN MP_TAC (SPEC "d:exseq" length_min)
                                 THEN APPLY_TO "length d = WHOLE n'''"
                                        SUBST1_TAC
                                 THEN APPLY_TO  "length e = WHOLE n''''"
                                        SUBST1_TAC
                                 THEN REWRITE_TAC
                                         [PR
                                         ;lnum_sub
                                         ;lnum_plus
                                         ;lnum_less_reduce
                                         ]
                                 THEN REPEAT DISCH_TAC
                                 THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
                                 THEN ONCE_REWRITE_TAC[ADD_SYM]
                                 THEN IMP_RES_TAC LESS_EQ_ADD_SUB
                                 THEN APPLY_TO
                                        "!a. (a + n'''') - 1 = a + (n'''' - 1)"
                                        (\th.REWRITE_TAC[th])
                                 THEN ONCE_REWRITE_TAC[ADD_SYM]
                                 THEN REWRITE_TAC[SUB_PLUS]
                                ]

                        ]
                ]
);;

let exseq_length_SUC_PR_shift =  prove_thm
(       `exseq_length_SUC_PR_shift`,
        "!e.
         WHOLE(SUC n) <+ length e = WHOLE n <+ PR(length e)",
        GEN_TAC
        THEN lnum_cases_TAC ["length e"]
        THEN REWRITE_TAC[lnum_less_reduce;PR]
        THEN REWRITE_TAC [SYM_th PRE_SUB1;SUC_LESS_PRE_SHARP]
);;

let length_less_suc_less_eq = prove_thm
(       `length_less_suc_less_eq`,
        "!e. ~ABORT e ==> WHOLE n <+ length e ==> WHOLE(SUC n) <-+ length e",
        GEN_TAC
        THEN REWRITE_TAC[ABORT]
        THEN lnum_cases_TAC["length e"]
        THEN REWRITE_TAC[is_FRAG;lnum_less_reduce;lnum_less_eq_reduce;LESS_OR]
);;

let length_less_suc_swop = prove_thm
(       `length_less_suc_swop`,
        "!e. (WHOLE(SUC n) = length e) = (WHOLE n = PR(length e))",
        GEN_TAC
        THEN MP_TAC(SPEC "e:exseq" length_min)
        THEN lnum_cases_TAC["length e"]
        THEN REWRITE_TAC
                [PR;lnum_const_dist
                ;lnum_const_one_one;lnum_less_reduce
                ]
        THEN DISCH_TAC
        THEN IMP_RES_TAC ONE_LESS_NOUGHT_LESS
        THEN IMP_RES_TAC PRE_SUC_EQ
        THEN ASM_REWRITE_TAC[SYM_th PRE_SUB1]
);;

let length_PR_less = prove_thm
(       `length_PR_less`,
        "!e. TERM e ==> PR(length e) <+ length e",
        GEN_TAC
        THEN REWRITE_TAC[TERM]
        THEN MP_TAC(SPEC "e:exseq" length_min)
        THEN lnum_cases_TAC["length e"]
        THEN REWRITE_TAC[is_WHOLE;PR;lnum_less_reduce;SYM_th PRE_SUB1]
        THEN DISCH_TAC
        THEN IMP_RES_TAC ONE_LESS_NOUGHT_LESS
        THEN IMP_RES_TAC PRE_K_K
);;

let length_PR_as_SUC = prove_thm
(       `length_PR_as_SUC`,
        "!e. TERM e ==> ?n. PR(length e) = WHOLE(SUC n)",
        GEN_TAC
        THEN REWRITE_TAC[TERM]
        THEN MP_TAC(SPEC "e:exseq" length_min)
        THEN lnum_cases_TAC["length e"]
        THEN REWRITE_TAC[is_WHOLE;PR;lnum_const_one_one;lnum_less_reduce]
        THEN DISCH_TAC
        THEN EXISTS_TAC "(n-1)-1"
        THEN REWRITE_TAC[ADD1]
        THEN HALF_REWRITE_TAC[SYM_th (SPECL["n-1";"1"]SUB_ADD)]
        THEN SUPPOSE_TAC "0<1"
        THEN REDUCE_TAC
        THEN IMP_RES_TAC(SYM_th INV_PRE_LESS_SHARP)
        THEN RULE_ASSUM_TAC REDUCE_RULE
        THEN IMP_RES_TAC LESS_EQ
        THEN RULE_ASSUM_TAC REDUCE_RULE
        THEN REWRITE_TAC[SYM_th PRE_SUB1]
        THEN ASSUM_REDUCE_TAC
);;

close_theory();;
