% Some laws proved about the process PAR.                               %
%                                                                       %
% FILE            : par_laws.ml                                         %
%                                                                       %
% READS FILES     : process.th, rules_and_tacs.ml                       %
% LOADS LIBRARIES : sets, string, taut                                  %
% WRITES FILES    : par_laws.th                                         %
%                                                                       %
% AUTHOR          : Albert J Camilleri                                  %
% AFFILIATION     : Hewlett-Packard Laboratories, Bristol               %
% DATE            : 89.03.15                                            %
% REVISED         : 91.10.01                                            %

load_library `sets`;;
load_library `string`;;
load_library `taut`;;
loadf `rules_and_tacs`;;

new_theory `par_laws`;;

new_parent `process`;;

load_theorems `list_lib1`;;

load_definition `restrict` `RESTRICT`;;
map (load_theorem `restrict`) [`STRICT_REST`; `DISTRIB_REST`; `REP_RESTR`];;

load_definition `star` `STAR`;;
map (load_theorem `star`) [`NIL_IN_STAR`; `CONS_STAR`];;

map (load_theorem `process_ty`)
    [`NIL_IN_TRACES`; `TRACES_IN_STAR`; `ID_PROCESS`;
     `ALPHA_FST`; `PROCESS_EQ_SPLIT`];;

load_definitions `stop`;;
load_theorems    `stop`;;

load_definitions `run`;;
load_theorems    `run`;;

load_definitions `prefix`;;
load_theorems    `prefix`;;

load_definitions `parallel`;;
load_theorems    `parallel`;;

let INTER_UNION_IMP =
    prove_thm
       (`INTER_UNION_IMP`,
        "! x (A B:(*)set). x IN (A INTER B) ==> x IN (A UNION B)",
        REWRITE_TAC [IN_INTER; IN_UNION] THEN
        REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC []);;

let PAR_SYM =
    prove_thm
       (`PAR_SYM`,
        "! P Q: process. P PAR Q = Q PAR P",
        REPEAT STRIP_TAC THEN
        REWRITE_TAC [PROCESS_EQ_SPLIT; PAR] THEN
        SUBST_TAC
         [SPECL ["ALPHA Q"; "ALPHA P"]
                (INST_TYPE [":event",":*"] UNION_COMM)] THEN
        REWRITE_TAC
         [CONJ_DISCH
           "s IN (STAR((ALPHA P) UNION (ALPHA Q)))"
           (ADD_ASSUM
            "s IN (STAR((ALPHA P) UNION (ALPHA Q)))"
            (SPECL ["(RESTRICT s (ALPHA Q)) IN (TRACES Q)";
                    "(RESTRICT s (ALPHA P)) IN (TRACES P)"] CONJ_SYM))]);;

let INT_UNI_LEMMA =
    TAC_PROOF (([], "! A B:(*)set. (A UNION B) INTER A = A"),
               REWRITE_TAC [EXTENSION; IN_UNION; IN_INTER] THEN
               REPEAT GEN_TAC THEN
               BOOL_CASES_TAC "(x:*) IN A" THEN
               REWRITE_TAC []);;

let INT_UNI_LEMMA' =
    GEN_ALL (SUBS [SPECL ["A:(*)set"; "B:(*)set"] UNION_COMM]
                  (SPEC_ALL INT_UNI_LEMMA));;

let PAR_ASSOC =
    prove_thm
       (`PAR_ASSOC`,
        "! P Q R: process. (P PAR (Q PAR R)) = ((P PAR Q) PAR R)",
        REPEAT STRIP_TAC THEN
        REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
        SUBST_TAC (CONJUNCTS (SPECL ["P:process"; "Q PAR R"] PAR)) THEN
        SUBST_TAC (CONJUNCTS (SPECL ["P PAR Q"; "R:process"] PAR)) THEN
        REWRITE_TAC [ALPHA_PAR; TRACES_PAR; UNION_ASSOC; STAR] THEN
        SET_SPEC_TAC THEN
        REWRITE_TAC [REP_RESTR; INTER_IDEMPOT; INT_UNI_LEMMA;
                     INT_UNI_LEMMA'; CONJ_ASSOC]);;

let CONS_RESTR =
    TAC_PROOF
       (([],
         "!(a:*) s A. RESTRICT (CONS a s) A = RESTRICT (APPEND [a] s) A"),
        REWRITE_TAC [APPEND]);;

let PAR_STOP_TRACES =
    TAC_PROOF
       (([],
         "s IN (STAR (ALPHA P)) /\
          (RESTRICT s (ALPHA P)) IN (TRACES P) /\
          (RESTRICT s (ALPHA P) = []) = (s = [])"),
        EQ_TAC THENL
        [SPEC_TAC ("s:trace", "s:trace") THEN
         LIST_INDUCT_TAC THENL
         [REWRITE_TAC [NIL_IN_STAR; STRICT_REST; NIL_IN_TRACES];
          REWRITE_TAC [CONS_STAR] THEN
          REPEAT STRIP_TAC THEN
          UNDISCH_TAC "RESTRICT(CONS h s)(ALPHA P) = []" THEN
          ASM_REWRITE_TAC [RESTRICT; NOT_CONS_NIL]];
         STRIP_TAC THEN
         ASM_REWRITE_TAC [NIL_IN_STAR; STRICT_REST; NIL_IN_TRACES]]);;

let PAR_STOP =
    prove_thm
       (`PAR_STOP`,
        "! P:process. P PAR (STOP (ALPHA P)) = (STOP (ALPHA P))",
        REWRITE_TAC [PROCESS_EQ_SPLIT; PAR; ALPHA_STOP; TRACES_STOP;
                     STOP; UNION_IDEMPOT; EXTENSION; IN_SING] THEN
        SET_SPEC_TAC THEN
        REWRITE_TAC [PAR_STOP_TRACES]);;

let PAR_RUN_TRACES =
    TAC_PROOF
       (([],
         "{s | s IN (STAR (ALPHA P)) /\
               (RESTRICT s (ALPHA P)) IN (TRACES P) /\
               (RESTRICT s (ALPHA P)) IN (STAR (ALPHA P))} =
          (TRACES P)"),
        REWRITE_TAC [EXTENSION] THEN
        SET_SPEC_TAC THEN
        GEN_TAC THEN
        EQ_TAC THENL
        [SUBST_TAC
         [SET_SPEC_RULE
          (SPEC "x:trace"
                (REWRITE_RULE
                 [EXTENSION]
                 (SPEC "ALPHA P" (INST_TYPE [":event", ":*"] STAR))))] THEN
         STRIP_TAC THEN
         UNDISCH_TAC "(RESTRICT x(ALPHA P)) IN (TRACES P)" THEN
         ASM_REWRITE_TAC [];
         STRIP_TAC THEN
         IMP_RES_TAC
          (SET_SPEC_RULE (REWRITE_RULE [STAR; SUBSET_DEF] TRACES_IN_STAR)) THEN
         IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] TRACES_IN_STAR) THEN
         ASM_REWRITE_TAC []]);;

let PAR_RUN =
    prove_thm
       (`PAR_RUN`,
        "! P:process. P PAR (RUN (ALPHA P)) = P",
        REWRITE_TAC
         [PROCESS_EQ_SPLIT; PAR; ALPHA_RUN; TRACES_RUN;
          UNION_IDEMPOT; PAR_RUN_TRACES; ID_PROCESS]);;

let PREFIX_PAR_1 =
    prove_thm
       (`PREFIX_PAR_1`,
        "!c P Q. (c IN ((ALPHA P) INTER (ALPHA Q))) ==>
                 ((c --> P) PAR (c --> Q) = (c --> (P PAR Q)))",
        REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC
          (REWRITE_RULE
            [SYM (SPEC_ALL ALPHA_PAR)]
            (SPECL ["c:string"; "ALPHA P"; "ALPHA Q"]
                   (INST_TYPE [":event", ":*"] INTER_UNION_IMP))) THEN
        UNDISCH_TAC "c IN ((ALPHA P) INTER (ALPHA Q))" THEN
        REWRITE_TAC [IN_INTER] THEN
        STRIP_TAC THEN
        IMP_RES_TAC ALPHA_PREFIX THEN
        IMP_RES_TAC TRACES_PREFIX THEN
        ASM_REWRITE_TAC
         [ALPHA_PAR; TRACES_PAR; EXTENSION; IN_UNION; IN_SING] THEN
        SET_SPEC_TAC THEN
        GEN_TAC THEN
        EQ_TAC THENL
        [DISJ_CASES_TAC (SPEC "x:trace = []" EXCLUDED_MIDDLE) THEN
         ASM_REWRITE_TAC [] THEN
         IMP_RES_TAC (REWRITE_RULE [SYM (SPEC_ALL NULL_EQ_NIL)] CONS) THEN
         POP_ASSUM ((\x. ONCE_ASM_REWRITE_TAC [x]) o SYM) THEN
         ASM_REWRITE_TAC [RESTRICT; CONS_STAR; IN_UNION; blemma] THEN
         DISCH_THEN STRIP_ASSUME_TAC THENL
         [ALL_TAC ; ONCE_REWRITE_TAC [blemma']] THEN
         ASM_REWRITE_TAC [NOT_CONS_NIL; CONS_11] THEN
         DISCH_TAC THEN
         DISCH_THEN STRIP_ASSUME_TAC THEN
         ASM_REWRITE_TAC [NOT_CONS_NIL; CONS_11] THEN
         REPEAT STRIP_TAC THEN
         EXISTS_TAC "TL (x:trace)" THEN
         ASM_REWRITE_TAC [];
         REPEAT STRIP_TAC THEN
         ASM_REWRITE_TAC [NIL_IN_STAR; RESTRICT; CONS_STAR; IN_UNION] THEN
         DISJ2_TAC THENL
         [EXISTS_TAC "RESTRICT t (ALPHA P)";
          EXISTS_TAC "RESTRICT t (ALPHA Q)"] THEN
         ASM_REWRITE_TAC [RESTRICT]])
    where blemma  = TAUT_RULE "!a b c. ((a /\ b) ==> c) = (a ==> (b ==>c))"
    and   blemma' =
          TAUT_RULE
          "!a b c d. (a ==> (b ==> (c ==> d))) = (a ==> (c ==> (b ==> d)))";;

let Sets_Lemma =
    let th =
        REWRITE_RULE [SUBSET_DEF; IN_INSERT; NOT_IN_EMPTY]
                     (ASSUME "{c,d:event} SUBSET A") in
    let   th1 = REWRITE_RULE [] (SPEC "c:event" th)
    and   th2 = REWRITE_RULE [] (SPEC "d:event" th) in
    DISCH_ALL (CONJ th1 th2);;

let PREFIX_PAR_2_LEMMA =
    TAC_PROOF
       ((["~(c:event = d)"; "c IN (ALPHA P)"; "c IN (ALPHA Q)";
                            "d IN (ALPHA P)"; "d IN (ALPHA Q)"],
         "!x:trace.
          (x IN (STAR((ALPHA P) UNION (ALPHA Q))) /\
           ((RESTRICT x(ALPHA P) = []) \/
            (?t. (RESTRICT x(ALPHA P) = CONS c t) /\ t IN (TRACES P))) /\
           ((RESTRICT x(ALPHA Q) = []) \/
            (?t. (RESTRICT x(ALPHA Q) = CONS d t) /\ t IN (TRACES Q)))) =
          (x = [])"),
        LIST_INDUCT_TAC THENL
        [REWRITE_TAC [NIL_IN_STAR; RESTRICT];
         GEN_TAC THEN
         REWRITE_TAC [CONS_STAR] THEN
         DISJ_CASES_TAC
          (SPEC "h IN ((ALPHA P) UNION (ALPHA Q))" EXCLUDED_MIDDLE) THENL
         [UNDISCH_TAC "h IN ((ALPHA P) UNION (ALPHA Q))" THEN
          REWRITE_TAC [IN_UNION] THEN
          REPEAT STRIP_TAC THENL
          [DISJ_CASES_TAC (SPEC "h = c:event" EXCLUDED_MIDDLE);
           DISJ_CASES_TAC (SPEC "h = d:event" EXCLUDED_MIDDLE)] THEN
          IMP_RES_TAC lemma1 THEN
          ASM_REWRITE_TAC [RESTRICT; NOT_CONS_NIL; CONS_11] THEN
          SUBST_TAC
           [SPECL ["d:event"; "c:event"]
                  (INST_TYPE [":event",":*"] EQ_SYM_EQ)] THEN
          ASM_REWRITE_TAC [];
          ASM_REWRITE_TAC [NOT_CONS_NIL]]])
    where lemma1 =
          TAC_PROOF
           (([], "! (h c:event) A. ((c IN A) /\ (h = c)) ==> (h IN A)"),
            REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let PREFIX_PAR_2 =
    prove_thm
       (`PREFIX_PAR_2`,
        "!c d P Q.
          ({c,d} SUBSET ((ALPHA P) INTER (ALPHA Q)) /\ ~(c = d)) ==>
          ((c --> P) PAR (d --> Q) = (STOP ((ALPHA P) UNION (ALPHA Q))))",
        REWRITE_TAC [PROCESS_EQ_SPLIT] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC Sets_Lemma THEN
        IMP_RES_TAC
          (REWRITE_RULE
            [SYM (SPEC_ALL ALPHA_PAR)]
            (SPECL ["c:string"; "ALPHA P"; "ALPHA Q"]
                   (INST_TYPE [":event", ":*"] INTER_UNION_IMP))) THEN
        UNDISCH_TAC "c IN ((ALPHA P) INTER (ALPHA Q))" THEN
        UNDISCH_TAC "d IN ((ALPHA P) INTER (ALPHA Q))" THEN
        REWRITE_TAC [IN_INTER] THEN
        REPEAT STRIP_TAC THEN
        IMP_RES_TAC ALPHA_PREFIX THEN
        IMP_RES_TAC TRACES_PREFIX THEN
        ASM_REWRITE_TAC [ALPHA_PAR; TRACES_PAR; ALPHA_STOP; TRACES_STOP;
                         EXTENSION; IN_UNION; IN_SING] THEN
        SET_SPEC_TAC THEN
        ACCEPT_TAC PREFIX_PAR_2_LEMMA);;

close_theory ();;
