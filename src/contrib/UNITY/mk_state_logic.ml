% -*- Emacs Mode: fundamental -*- %

%-----------------------------------------------------------------------------%
%
   File:         mk_state_logic.ml

   Description:  This file defines the state abstracted logical operators used
                 in unity and some theorems valid for the combination of these
                 operators.

   Author:       (c) Copyright by Flemming Andersen
   Date:         October 23, 1989
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;
%

system `/bin/rm state_logic.th`;;

new_theory`state_logic`;;

let FALSE_DEF = new_definition
  (`FALSE_DEF`,
   "(FALSE:*->bool) = \s:*.F");;

let TRUE_DEF = new_definition
  (`TRUE_DEF`,
   "(TRUE:*->bool) = \s:*.T");;

let ~* = new_definition
  (`~*`,
   "~* (p:*->bool) = \s. ~p s");;

let /\* = new_infix_definition
  (`/\\*`, "/\* (p:*->bool) (q:*->bool) = \s. (p s) /\ (q s)");;

let \/* = new_infix_definition
  (`\\/*`, "\/* (p:*->bool) (q:*->bool) = \s. (p s) \/ (q s)");;

% State dependent universal quantification %
let !* = new_binder_definition
  (`!*`, "$!* (P:**->(*->bool)) = (\s. (!x. ((P x)s)))");;

% State dependent existential quantification %
let ?* = new_binder_definition
  (`?*`, "$?* (P:**->(*->bool)) = (\s. (?x. ((P x)s)))");;

let ==>* = new_infix_definition
  (`==>*`, "==>* (p:*->bool) (q:*->bool) = \s. (p s) ==> (q s)");;

let <* = new_infix_definition
  (`<*`, "<* (p:*->num) (q:*->num) = \s. (p s) < (q s)");;

let >* = new_infix_definition
  (`>*`, ">* (p:*->num) (q:*->num) = \s. (p s) > (q s)");;

let <=* = new_infix_definition
  (`<=*`, "<=* (p:*->num) (q:*->num) = \s. (p s) <= (q s)");;

let >=* = new_infix_definition
  (`>=*`, ">=* (p:*->num) (q:*->num) = \s. (p s) >= (q s)");;

let =* = new_infix_definition
  (`=*`, "=* (p:*->**) (q:*->**) = \s. (p s) = (q s)");;

% State dependent conditional %
let =>* = new_infix_definition
  (`=>*`, "=>* (p:*->bool) (r1:*->**) (r2:*->**) = \s. (p s) => r1 s | r2 s");;

let +* = new_infix_definition
  (`+*`, "+* (p:*->num) (q:*->num) = \s. (p s) + (q s)");;

let -* = new_infix_definition
  (`-*`, "-* (p:*->num) (q:*->num) = \s. (p s) - (q s)");;

let ** = new_infix_definition
  (`**`, "** (p:*->num) (q:*->num) = \s. (p s) * (q s)");;

let SucX = new_definition
  (`SucX`, "SucX (p:*->num) = \s. SUC (p s)");;

let PreX = new_definition
  (`PreX`, "PreX (p:*->num) = \s. PRE (p s)");;

let ModX = new_infix_definition
  (`ModX`, "ModX (p:*->num) (q:*->num) = \s. (p s) MOD (q s)");;

let DivX = new_infix_definition
  (`DivX`, "DivX (p:*->num) (q:*->num) = \s. (p s) DIV (q s)");;

let ExpX = new_infix_definition
  (`ExpX`, "ExpX (p:*->num) (q:*->num) = \s. (p s) EXP (q s)");;

% State dependent index %
let IndX = new_infix_definition
  (`IndX`, "IndX (a:*->(*1->*2)) (i:*->*1) = \s. (a s) (i s)");;

% More State dependent operators to be defined ??? %

%
  Be aware that (!i :: i <= m. P i) = (!i. i <= m ==> P i)
%
let !<=* = new_definition
  (`!<=*`, "!<=* (P:num->(*->bool)) m = (\s:*. (!i. i <= m ==> ((P i)s)))");;

%
  Be aware that ?i :: i <= m. P i == ?i. i <= m /\ P i
%
let ?<=* = new_definition
  (`?<=*`, "?<=* (P:num->(*->bool)) m = (\s:*. (?i. i <= m /\ ((P i)s)))");;

let ?<* = new_definition
  (`?<*`, "?<* (P:num->(*->bool)) m = (\s:*. (?i. i < m /\ ((P i)s)))");;

let /<=\* = new_prim_rec_definition
  (`/<=\\*`,
   "(!(P:num->(*->bool)). /<=\* P 0        = (P 0)) /\
    (!P.                  /<=\* P (SUC i) = ((/<=\* P i) /\* (P (SUC i))))");;

let \<=/* = new_prim_rec_definition
  (`\\<=/*`,
   "(!(P:num->(*->bool)). \<=/* P 0        = (P 0)) /\
    (!P.                  \<=/* P (SUC i) = ((\<=/* P i) \/* (P (SUC i))))");;

let /<\* = new_prim_rec_definition
  (`/<\\*`,
   "(!(P:num->(*->bool)). /<\* P 0        = FALSE) /\
    (!P.                  /<\* P (SUC i) = ((/<\* P i) /\* (P i)))");;

let \</* = new_prim_rec_definition
  (`\\</*`,
   "(!(P:num->(*->bool)). \</* P 0        = FALSE) /\
    (!P.                  \</* P (SUC i) = ((\</* P i) \/* (P i)))");;

%-----------------------------------------------------------------------------%
% Theorems valid in this theory                                               %
%-----------------------------------------------------------------------------%

let IMPLY_WEAK_lemma1 = prove_thm
   (`IMPLY_WEAK_lemma1`,
    "!(p:*->bool) q p' q'.
         !s:*. (((p /\* q') \/* (p' /\* q)) \/* (q /\* q'))s ==> (q \/* q')s",
    REPEAT(GEN_TAC) THEN
    REWRITE_TAC [/\*;\/*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC))] THEN
    REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma2 = prove_thm
   (`IMPLY_WEAK_lemma2`,
    "!(p:*->bool) q p' q'.
         !s:*. ((((~* p) /\* q') \/* ((~* p') /\* q)) \/* (q /\* q'))s ==>
                   (q \/* q')s",
    REPEAT GEN_TAC THEN
    REWRITE_TAC [~*;/\*;\/*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                 (SYM (SPEC_ALL DISJ_ASSOC));NOT_CLAUSES;DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma3 = prove_thm
   (`IMPLY_WEAK_lemma3`,
    "!(p:*->bool) q r.
         !s:*. ((((~* p) /\* r) \/* ((~* q) /\* q)) \/* (q /\* r))s ==> r s",
    REPEAT GEN_TAC THEN
    REWRITE_TAC [~*;/\*;\/*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC))] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC);;

let IMPLY_WEAK_lemma4 = prove_thm
  (`IMPLY_WEAK_lemma4`,
   "!(p:*->bool) q p' q' r r' s.
      ((((~*(p \/* p')) /\* (p \/* r')) \/* ((~*(q \/* q')) /\* (q \/* r))) \/*
         ((q \/* r) /\* (p \/* r')))s ==> ((p /\* q) \/* r \/* r')s",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*;~*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC));
                GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC));
                NOT_CLAUSES;DE_MORGAN_THM] THEN
   REPEAT STRIP_TAC THENL
     [RES_TAC;ASM_REWRITE_TAC [];RES_TAC;ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma5 = prove_thm
  (`IMPLY_WEAK_lemma5`,
   "!(p:*->bool) q r s.
     ((p /\* r) \/* (((p \/* q) /\* (q \/* r)) \/* r)) s ==> (q \/* r) s",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma6 = prove_thm
  (`IMPLY_WEAK_lemma6`,
   "!(p:*->bool) q b r s.
        ((r /\* q) \/* (p /\* b) \/* (b /\* q)) s ==> ((q /\* r) \/* b) s",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma7 = prove_thm
  (`IMPLY_WEAK_lemma7`,
   "!(p:*->bool) q b r s.
     (((r /\* q) \/* ((r /\* p) /\* b)) \/* (b /\* q)) s ==>
           ((q /\* r) \/* b) s",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_COMM_DISJ_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. (r s /\ q s) \/ p s ==> (q s /\ r s) \/ p s"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_COMM_DISJ_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. (q s /\ r s) \/ p s ==> (r s /\ q s) \/ p s"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_COMM_DISJ_lemma = TAC_PROOF
  (([], "!(p:*->bool) q r s. (r s /\ q s) \/ p s = (q s /\ r s) \/ p s"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_COMM_DISJ_lemma_a)
                    (SPEC_ALL CONJ_COMM_DISJ_lemma_b)));;

let AND_COMM_OR_lemma = prove_thm
  (`AND_COMM_OR_lemma`,
   "!(p:*->bool) q r. (r /\* q) \/* p = (q /\* r) \/* p",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                CONJ_COMM_DISJ_lemma)));;

let CONJ_DISJ_COMM_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. (p s /\ (r s \/ q s)) ==> (p s /\ (q s \/ r s))"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_DISJ_COMM_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. (p s /\ (q s \/ r s)) ==> (p s /\ (r s \/ q s))"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_DISJ_COMM_lemma = TAC_PROOF
  (([], "!(p:*->bool) q r s. (p s /\ (r s \/ q s)) = (p s /\ (q s \/ r s))"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_DISJ_COMM_lemma_a)
                    (SPEC_ALL CONJ_DISJ_COMM_lemma_b)));;

let AND_OR_COMM_lemma = prove_thm
  (`AND_OR_COMM_lemma`,
   "!(p:*->bool) q r. p /\* (r \/* q) = p /\* (q \/* r)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                CONJ_DISJ_COMM_lemma)));;

let DISJ_COMM_CONJ_lemma_a = TAC_PROOF
  (([],    "!(p:*->bool) q r s. (r s \/ q s) /\ p s ==> (q s \/ r s) /\ p s"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_COMM_CONJ_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. (q s \/ r s) /\ p s ==> (r s \/ q s) /\ p s"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_COMM_CONJ_lemma = TAC_PROOF
  (([],    "!(p:*->bool) q r s. (r s \/ q s) /\ p s = (q s \/ r s) /\ p s"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_COMM_CONJ_lemma_a)
                    (SPEC_ALL DISJ_COMM_CONJ_lemma_b)));;

let OR_COMM_AND_lemma = prove_thm
  (`OR_COMM_AND_lemma`,
   "!(p:*->bool) q r. (r \/* q) /\* p = (q \/* r) /\* p",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                DISJ_COMM_CONJ_lemma)));;

let DISJ_COMM_DISJ_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. (r s \/ q s) \/ p s ==> (q s \/ r s) \/ p s"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_COMM_DISJ_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. (q s \/ r s) \/ p s ==> (r s \/ q s) \/ p s"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_COMM_DISJ_lemma = TAC_PROOF
  (([],    "!(p:*->bool) q r s. (r s \/ q s) \/ p s = (q s \/ r s) \/ p s"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_COMM_DISJ_lemma_a)
                    (SPEC_ALL DISJ_COMM_DISJ_lemma_b)));;

let OR_COMM_OR_lemma = prove_thm
  (`OR_COMM_OR_lemma`,
   "!(p:*->bool) q r. (r \/* q) \/* p = (q \/* r) \/* p",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                DISJ_COMM_DISJ_lemma)));;

let DISJ_DISJ_COMM_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s \/ (r s \/ q s) ==> p s \/ (q s \/ r s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_DISJ_COMM_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s \/ (q s \/ r s) ==> p s \/ (r s \/ q s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_DISJ_COMM_lemma = TAC_PROOF
  (([],    "!(p:*->bool) q r s. p s \/ (r s \/ q s)  = p s \/ (q s \/ r s) "),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_DISJ_COMM_lemma_a)
                    (SPEC_ALL DISJ_DISJ_COMM_lemma_b)));;

let OR_OR_COMM_lemma = prove_thm
  (`OR_OR_COMM_lemma`,
   "!(p:*->bool) q r. p \/* (r \/* q) = p \/* (q \/* r)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                DISJ_DISJ_COMM_lemma)));;

let CONJ_COMM_CONJ_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. (r s /\ q s) /\ p s ==> (q s /\ r s) /\ p s"),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_COMM_CONJ_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. (q s /\ r s) /\ p s ==> (r s /\ q s) /\ p s"),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_COMM_CONJ_lemma = TAC_PROOF
  (([],    "!(p:*->bool) q r s. (r s /\ q s) /\ p s = (q s /\ r s) /\ p s"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_COMM_CONJ_lemma_a)
                    (SPEC_ALL CONJ_COMM_CONJ_lemma_b)));;

let AND_COMM_AND_lemma = prove_thm
  (`AND_COMM_AND_lemma`,
   "!(p:*->bool) q r. (r /\* q) /\* p = (q /\* r) /\* p",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                CONJ_COMM_CONJ_lemma)));;

let CONJ_CONJ_COMM_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s /\ (r s /\ q s) ==> p s /\ (q s /\ r s)"),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_CONJ_COMM_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s /\ (q s /\ r s) ==> p s /\ (r s /\ q s)"),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_CONJ_COMM_lemma = TAC_PROOF
  (([],    "!(p:*->bool) q r s. p s /\ (r s /\ q s)  = p s /\ (q s /\ r s) "),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_CONJ_COMM_lemma_a)
                    (SPEC_ALL CONJ_CONJ_COMM_lemma_b)));;

let AND_AND_COMM_lemma = prove_thm
  (`AND_AND_COMM_lemma`,
   "!(p:*->bool) q r. p /\* (r /\* q) = p /\* (q /\* r)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                CONJ_CONJ_COMM_lemma)));;

let DISJ_CONJ_COMM_lemma_a = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s \/ (r s /\ q s) ==> p s \/ (q s /\ r s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_CONJ_COMM_lemma_b = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s \/ (q s /\ r s) ==> p s \/ (r s /\ q s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_CONJ_COMM_lemma = TAC_PROOF
  (([], "!(p:*->bool) q r s. p s \/ (r s /\ q s) = p s \/ (q s /\ r s)"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_CONJ_COMM_lemma_a)
                    (SPEC_ALL DISJ_CONJ_COMM_lemma_b)));;

let OR_AND_COMM_lemma = prove_thm
  (`OR_AND_COMM_lemma`,
   "!(p:*->bool) q r. p \/* (r /\* q) = p \/* (q /\* r)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                                DISJ_CONJ_COMM_lemma)));;

let NOT_NOT_lemma = prove_thm
   (`NOT_NOT_lemma`,
     "!(p:*->bool). (~* (~* p)) = p",
    REWRITE_TAC [~*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [NOT_CLAUSES;ETA_AX]);;

let DISJ_COMM_lemma = TAC_PROOF
   (([], "!(p:*->bool) q s. p s \/ q s = q s \/ p s"),
    REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC (SPECL ["(p:*->bool)s";"(q:*->bool)s"] DISJ_SYM));;

let OR_COMM_lemma = prove_thm
   (`OR_COMM_lemma`,
    "!(p:*->bool) q. (p \/* q) = (q \/* p)",
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [\/*] THEN
    ASSUME_TAC DISJ_COMM_lemma THEN
    STRIP_ASSUME_TAC
        (MK_ABS (SPECL ["p:*->bool";"q:*->bool"]
                (ASSUME "!(p:*->bool) q s. p s \/ q s = q s \/ p s"))));;

let OR_OR_lemma = prove_thm
   (`OR_OR_lemma`,
    "!p:*->bool. p \/* p = p",
    GEN_TAC THEN REWRITE_TAC [\/*;ETA_AX]);;

let DISJ_ASSOC_lemma = TAC_PROOF
   (([], "!(p:*->bool) q  r s. ((p s \/ q s) \/ r s) = (p s \/ (q s \/ r s))"),
    REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC))]);;

let OR_ASSOC_lemma = prove_thm
   (`OR_ASSOC_lemma`,
    "!(p:*->bool) q r. (p \/* q) \/* r = p \/* (q \/* r)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [\/*]  THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ASSUME_TAC DISJ_ASSOC_lemma THEN
    STRIP_ASSUME_TAC
   (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
      (ASSUME "!(p:*->bool) q  r s.
                 ((p s \/ q s) \/ r s) = (p s \/ (q s \/ r s))"))));;

let CONJ_WEAK_lemma = TAC_PROOF
  (([], "!(p:*->bool) q. (!s. p s /\ q s ==> q s)"),
    REPEAT STRIP_TAC THEN RES_TAC);;

let AND_IMPLY_WEAK_lemma = prove_thm
  (`AND_IMPLY_WEAK_lemma`,
    "!(p:*->bool) q. (!s. (p /\* q) s ==> q s)",
    REWRITE_TAC [/\*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [CONJ_WEAK_lemma]);;

let SYM_CONJ_WEAK_lemma = TAC_PROOF
  (([], "!(p:*->bool) q. (!s. p s /\ q s ==> p s)"),
    REPEAT STRIP_TAC THEN RES_TAC);;

let SYM_AND_IMPLY_WEAK_lemma = prove_thm
  (`SYM_AND_IMPLY_WEAK_lemma`,
    "!(p:*->bool) q. (!s. (p /\* q) s ==> p s)",
    REWRITE_TAC [/\*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [SYM_CONJ_WEAK_lemma]);;

let OR_IMPLY_WEAK_lemma = prove_thm
  (`OR_IMPLY_WEAK_lemma`,
   "!(p:*->bool) q. (!s. p s ==> (p \/* q) s)",
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let SYM_OR_IMPLY_WEAK_lemma = prove_thm
  (`SYM_OR_IMPLY_WEAK_lemma`,
   "!(p:*->bool) q. (!s. p s ==> (q \/* p) s)",
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let IMPLY_WEAK_AND_lemma = prove_thm
  (`IMPLY_WEAK_AND_lemma`,
   "!(p:*->bool) q r. (!s. p s ==> q s) ==> (!s. (p /\* r) s ==> (q /\* r) s)",
   REWRITE_TAC [/\*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [RES_TAC;
      RES_TAC THEN
      ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_OR_lemma = prove_thm
  (`IMPLY_WEAK_OR_lemma`,
   "!(p:*->bool) q r. (!s. p s ==> q s) ==> (!s. (p \/* r) s ==> (q \/* r) s)",
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [RES_TAC THEN
      ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []]);;

let AND_AND_lemma = prove_thm
  (`AND_AND_lemma`,
   "!p:*->bool. p /\* p = p",
   REWRITE_TAC [/\*;ETA_AX]);;

let CONJ_COMM_lemma = TAC_PROOF
  (([], "!(p:*->bool) q s. (p s /\ q s) = (q s /\ p s)"),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (SPECL ["(p:*->bool)s";"(q:*->bool)s"] CONJ_SYM));;

let AND_COMM_lemma = prove_thm
   (`AND_COMM_lemma`,
   "!(p:*->bool) q. (p /\* q) = (q /\* p)",
   REWRITE_TAC [/\*] THEN
   REPEAT GEN_TAC THEN
   ASSUME_TAC CONJ_COMM_lemma THEN
   STRIP_ASSUME_TAC
        (MK_ABS (SPECL ["p:*->bool";"q:*->bool"]
                (ASSUME "!(p:*->bool) q s. p s /\ q s = q s /\ p s"))));;

let CONJ_ASSOC_lemma = TAC_PROOF
  (([], "!(p:*->bool) q  r s. ((p s /\ q s) /\ r s) = (p s /\ (q s /\ r s))"),
    REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC))]);;

let AND_ASSOC_lemma = prove_thm
   (`AND_ASSOC_lemma`,
    "!(p:*->bool) q r. (p /\* q) /\* r = p /\* (q /\* r)",
   REPEAT GEN_TAC THEN REWRITE_TAC [/\*]  THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   ASSUME_TAC CONJ_ASSOC_lemma THEN
   STRIP_ASSUME_TAC
   (MK_ABS (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
      (ASSUME "!(p:*->bool) q  r s.
                 ((p s /\ q s) /\ r s) = (p s /\ (q s /\ r s))"))));;

let AND_TRUE_lemma = prove_thm
   (`AND_TRUE_lemma`,
    "!p:*->bool. p /\* TRUE = p",
   REWRITE_TAC [/\*;TRUE_DEF;ETA_AX]);;

let OR_TRUE_lemma = prove_thm
   (`OR_TRUE_lemma`,
    "!p:*->bool. p \/* TRUE = TRUE",
   REWRITE_TAC [\/*;TRUE_DEF;ETA_AX]);;

let AND_FALSE_lemma = prove_thm
   (`AND_FALSE_lemma`,
    "!p:*->bool. p /\* FALSE = FALSE",
   REWRITE_TAC [/\*;FALSE_DEF;ETA_AX]);;

let OR_FALSE_lemma = prove_thm
   (`OR_FALSE_lemma`,
    "!p:*->bool. p \/* FALSE = p",
   REWRITE_TAC [\/*;FALSE_DEF;ETA_AX]);;

let P_OR_NOT_P_lemma = prove_thm
   (`P_OR_NOT_P_lemma`,
    "!p:*->bool. p \/* (~* p) = TRUE",
   REWRITE_TAC [\/*;~*;TRUE_DEF] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [EXCLUDED_MIDDLE;OR_CLAUSES;NOT_CLAUSES;ETA_AX]);;

let P_AND_NOT_P_lemma = prove_thm
   (`P_AND_NOT_P_lemma`,
    "!p:*->bool. p /\* (~* p) = FALSE",
   REWRITE_TAC [/\*;~*;FALSE_DEF] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [NOT_AND;AND_CLAUSES;NOT_CLAUSES;ETA_AX]);;

let CONJ_COMPL_DISJ_lemma1 = TAC_PROOF
  (([], "!p q. p /\ ~q \/ p /\ q ==> p"),
   REPEAT STRIP_TAC);;

let CONJ_COMPL_DISJ_lemma2 = TAC_PROOF
  (([], "!p q. p ==> p /\ ~q \/ p /\ q"),
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
   REWRITE_TAC [EXCLUDED_MIDDLE]);;

let CONJ_COMPL_DISJ_lemma = TAC_PROOF
  (([], "!p q. p /\ ~q \/ p /\ q = p"),
   REWRITE_TAC [IMP_ANTISYM_RULE
                  (SPEC_ALL CONJ_COMPL_DISJ_lemma1)
                  (SPEC_ALL CONJ_COMPL_DISJ_lemma2)]);;

let AND_COMPL_OR_lemma = prove_thm
   (`AND_COMPL_OR_lemma`,
    "!(p:*->bool) q. ((p /\* (~* q)) \/* (p /\* q)) = p",
   REWRITE_TAC [/\*;~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [CONJ_COMPL_DISJ_lemma;ETA_AX]);;

let DISJ_NOT_CONJ_lemma1 = TAC_PROOF
  (([],"!p q. (p \/ q) /\ ~q ==> p /\ ~q"),
    REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [];RES_TAC;RES_TAC;RES_TAC]);;

let DISJ_NOT_CONJ_lemma2 = TAC_PROOF
  (([],"!p q. p /\ ~q ==> (p \/ q) /\ ~q"),
    REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [];RES_TAC]);;

let DISJ_NOT_CONJ_lemma = TAC_PROOF
  (([], "!p q. (p \/ q) /\ ~q = p /\ ~q"),
   REWRITE_TAC [IMP_ANTISYM_RULE
                  (SPEC_ALL DISJ_NOT_CONJ_lemma1)
                  (SPEC_ALL DISJ_NOT_CONJ_lemma2)]);;

let OR_NOT_AND_lemma = prove_thm
  (`OR_NOT_AND_lemma`,
   "!(p:*->bool) q. ((p \/* q) /\* (~* q)) = p /\* (~* q)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [\/*;/\*;~*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [DISJ_NOT_CONJ_lemma]);;

let P_CONJ_Q_DISJ_Q_lemma1 = TAC_PROOF
  (([], "!(p:*->bool) q s. (p s /\ q s) \/ q s ==> q s"),
   REPEAT STRIP_TAC);;

let P_CONJ_Q_DISJ_Q_lemma2 = TAC_PROOF
  (([], "!(p:*->bool) q s. q s ==> (p s /\ q s) \/ q s"),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let P_CONJ_Q_DISJ_Q_lemma = TAC_PROOF
  (([], "!(p:*->bool) q s. (p s /\ q s) \/ q s = q s"),
   ASM_REWRITE_TAC [IMP_ANTISYM_RULE
                         (SPEC_ALL P_CONJ_Q_DISJ_Q_lemma1)
                         (SPEC_ALL P_CONJ_Q_DISJ_Q_lemma2)]);;

let P_AND_Q_OR_Q_lemma = prove_thm
  (`P_AND_Q_OR_Q_lemma`,
   "!(p:*->bool) q. (p /\* q) \/* q = q",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [GEN_ALL (MK_ABS (SPECL
         ["p:*->bool";"q:*->bool"] P_CONJ_Q_DISJ_Q_lemma));ETA_AX]);;

let P_DISJ_Q_CONJ_Q_lemma1 = TAC_PROOF
  (([], "!(p:*->bool) q s. (p s \/ q s) /\ q s ==> q s"),
   REPEAT STRIP_TAC);;

let P_DISJ_Q_CONJ_Q_lemma2 = TAC_PROOF
  (([], "!(p:*->bool) q s. q s ==> (p s \/ q s) /\ q s"),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let P_DISJ_Q_CONJ_Q_lemma = TAC_PROOF
  (([], "!(p:*->bool) q s. (p s \/ q s) /\ q s = q s"),
   ASM_REWRITE_TAC [IMP_ANTISYM_RULE
                         (SPEC_ALL P_DISJ_Q_CONJ_Q_lemma1)
                         (SPEC_ALL P_DISJ_Q_CONJ_Q_lemma2)]);;

let P_OR_Q_AND_Q_lemma = prove_thm
  (`P_OR_Q_AND_Q_lemma`,
   "!(p:*->bool) q. (p \/* q) /\* q = q",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [GEN_ALL (MK_ABS (SPECL
         ["p:*->bool";"q:*->bool"] P_DISJ_Q_CONJ_Q_lemma));ETA_AX]);;

let NOT_OR_AND_NOT_lemma = prove_thm
  (`NOT_OR_AND_NOT_lemma`,
   "!(p:*->bool) q. ~* (p \/* q) = (~* p) /\* (~* q)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [~*;\/*;/\*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [NOT_CLAUSES;DE_MORGAN_THM]);;

let NOT_AND_OR_NOT_lemma = prove_thm
  (`NOT_AND_OR_NOT_lemma`,
   "!(p:*->bool) q. ~* (p /\* q) = (~* p) \/* (~* q)",
      REPEAT GEN_TAC THEN
   REWRITE_TAC [~*;\/*;/\*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [NOT_CLAUSES;DE_MORGAN_THM]);;

let NOT_IMPLY_OR_lemma = prove_thm
  (`NOT_IMPLY_OR_lemma`,
   "!(p:*->bool) q. (!s. (~* p)s ==> q s) = (!s. (p \/* q)s)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM]);;

let IMPLY_OR_lemma = prove_thm
  (`IMPLY_OR_lemma`,
   "!(p:*->bool) q. (!s. p s ==> q s) = (!s. ((~* p) \/* q)s)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM]);;

let OR_IMPLY_lemma = prove_thm
  (`OR_IMPLY_lemma`,
   "!(p:*->bool) q. (!s. (p \/* q)s) = (!s. (~* p)s ==> q s)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM;NOT_CLAUSES]);;

let NOT_OR_IMPLY_lemma = prove_thm
  (`NOT_OR_IMPLY_lemma`,
   "!(p:*->bool) q. (!s. ((~* p) \/* q)s) = (!s. p s ==> q s)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM;NOT_CLAUSES]);;

let DISJ_CONJ_lemma1 = TAC_PROOF
  (([], "!(p:*->bool) q r s.
           (p s \/ q s /\ r s) ==> ((p s \/ q s) /\ (p s \/ r s))"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_CONJ_lemma2 = TAC_PROOF
  (([], "!(p:*->bool) q r s.
    ((p s \/ q s) /\ (p s \/ r s)) ==> (p s \/ q s /\ r s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let DISJ_CONJ_lemma = TAC_PROOF
  (([], "!(p:*->bool) q r s.
    (p s \/ q s /\ r s) = ((p s \/ q s) /\ (p s \/ r s))"),
   REWRITE_TAC [IMP_ANTISYM_RULE
                      (SPEC_ALL DISJ_CONJ_lemma1)
                      (SPEC_ALL DISJ_CONJ_lemma2)]);;

let OR_AND_DISTR_lemma = prove_thm
  (`OR_AND_DISTR_lemma`,
   "!(p:*->bool) q r. p \/* (q /\* r) = (p \/* q) /\* (p \/* r)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL
          ["p:*->bool";"q:*->bool";"r:*->bool"] DISJ_CONJ_lemma)));;

let CONJ_DISJ_lemma1 = TAC_PROOF
  (([], "!(p:*->bool) q r s.
      (p s /\ (q s \/ r s)) ==> (p s /\ q s \/ p s /\ r s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_DISJ_lemma2 = TAC_PROOF
  (([], "!(p:*->bool) q r s.
      (p s /\ q s \/ p s /\ r s) ==> (p s /\ (q s \/ r s))"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_DISJ_lemma = TAC_PROOF
  (([], "!(p:*->bool) q r s.
      (p s /\ (q s \/ r s)) = (p s /\ q s \/ p s /\ r s)"),
   REWRITE_TAC [IMP_ANTISYM_RULE
                      (SPEC_ALL CONJ_DISJ_lemma1)
                      (SPEC_ALL CONJ_DISJ_lemma2)]);;

let AND_OR_DISTR_lemma = prove_thm
  (`AND_OR_DISTR_lemma`,
   "!(p:*->bool) q r. p /\* (q \/* r) = (p /\* q) \/* (p /\* r)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL
          ["p:*->bool";"q:*->bool";"r:*->bool"] CONJ_DISJ_lemma)));;

let NOT_IMPLIES_FALSE_lemma = prove_thm
  (`NOT_IMPLIES_FALSE_lemma`,
   "!(p:*->bool). (!s. (~* p)s) ==> (!s. p s = FALSE s)",
   REWRITE_TAC [FALSE_DEF;~*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC []);;

let NOT_P_IMPLIES_P_EQ_FALSE_lemma = prove_thm
  (`NOT_P_IMPLIES_P_EQ_FALSE_lemma`,
   "!(p:*->bool). (!s. (~* p)s) ==> (p = FALSE)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (MK_ABS (UNDISCH_ALL (SPEC_ALL NOT_IMPLIES_FALSE_lemma))) THEN
   UNDISCH_TAC "(\s:*. p s) = (\s. FALSE s)" THEN
   REWRITE_TAC [ETA_AX]);;

let NOT_AND_IMPLIES_lemma = prove_thm
  (`NOT_AND_IMPLIES_lemma`,
   "!(p:*->bool) q. (!s. (~* (p /\* q))s) = (!s. p s ==> ~* q s)",
   REWRITE_TAC [/\*;~*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [DE_MORGAN_THM;NOT_CLAUSES;IMP_DISJ_THM]);;

let NOT_AND_IMPLIES_lemma1 = prove_thm
  (`NOT_AND_IMPLIES_lemma1`,
   "!(p:*->bool) q. (!s. (~* (p /\* q))s) ==> (!s. p s ==> ~* q s)",
   REWRITE_TAC [NOT_AND_IMPLIES_lemma]);;

let NOT_AND_IMPLIES_lemma2 = prove_thm
  (`NOT_AND_IMPLIES_lemma2`,
   "!(p:*->bool) q. (!s. (~* (p /\* q))s) ==> (!s. q s ==> ~* p s)",
   REWRITE_TAC [NOT_AND_IMPLIES_lemma;~*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let CONJ_DISJ_IMPLY_lemma1 = TAC_PROOF
   (([], "!(p:*->bool) q s. p s /\ (p s \/ q s) ==> p s"),
   REPEAT STRIP_TAC);;

let CONJ_DISJ_IMPLY_lemma2 = TAC_PROOF
   (([], "!(p:*->bool) q s. p s ==> p s /\ (p s \/ q s)"),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC [];ASM_REWRITE_TAC []]);;

let CONJ_DISJ_IMPLY_lemma = TAC_PROOF
  (([], "!(p:*->bool) q s. p s /\ (p s \/ q s) = p s"),
   REWRITE_TAC [IMP_ANTISYM_RULE
                  (SPEC_ALL CONJ_DISJ_IMPLY_lemma1)
                  (SPEC_ALL CONJ_DISJ_IMPLY_lemma2)]);;

let CONJ_DISJ_ABS_IMPLY_lemma = TAC_PROOF
  (([], "!(p:*->bool) q.  (\s. p s /\ (p s \/ q s)) = p"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [CONJ_DISJ_IMPLY_lemma;ETA_AX]);;

let AND_OR_EQ_lemma = prove_thm
  (`AND_OR_EQ_lemma`,
   "!(p:*->bool) q. p /\* (p \/* q) = p",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/\*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [CONJ_DISJ_ABS_IMPLY_lemma]);;

let AND_OR_EQ_AND_COMM_OR_lemma = prove_thm
  (`AND_OR_EQ_AND_COMM_OR_lemma`,
   "!(p:*->bool) q. p /\* (q \/* p) = p /\* (p \/* q)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [AND_OR_EQ_lemma]);;

let IMPLY_WEAK_lemma = prove_thm
  (`IMPLY_WEAK_lemma`,
   "!(p:*->bool) q. (!s. p s) ==> (!s. (p \/* q) s)",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   ASM_REWRITE_TAC []);;

let IMPLY_WEAK_lemma_b = prove_thm
  (`IMPLY_WEAK_lemma_b`,
   "!(p:*->bool) q s. p s ==> (p \/* q) s",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   ASM_REWRITE_TAC []);;

let ALL_AND_lemma1 = TAC_PROOF
  (([],
   "!(P:num->(*->bool)) i s. (!i. P i s) = (P i s /\ (!i. P i s))"),
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ];
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC []]);;

%----------------------------------------------------------------------------%
% Proof changed for new STRIP_TAC [JRH 92.11.07]; old proof:                 %
%                                                                            %
% let ALL_OR_lemma1 = TAC_PROOF                                              %
%   (([],                                                                    %
%    "!(P:num->(*->bool)) i s. (?i. P i s) = (P i s \/ (?i. P i s))"),       %
%    REPEAT GEN_TAC THEN                                                     %
%    EQ_TAC THENL                                                            %
%      [REPEAT STRIP_TAC THEN                                                %
%       DISJ2_TAC THEN                                                       %
%       EXISTS_TAC "i':num" THEN                                             %
%       ASM_REWRITE_TAC [];                                                  %
%       REPEAT STRIP_TAC THENL                                               %
%         [EXISTS_TAC "i:num" THEN                                           %
%          ASM_REWRITE_TAC [];                                               %
%          EXISTS_TAC "i:num" THEN                                           %
%          ASM_REWRITE_TAC []]]);;                                           %
%----------------------------------------------------------------------------%

let ALL_OR_lemma1 = PROVE
 ("!(P:num->(*->bool)) i s. (?i. P i s) = (P i s \/ (?i. P i s))",
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN($THEN DISJ2_TAC o ACCEPT_TAC);
    DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC "i:num" THEN POP_ASSUM ACCEPT_TAC]);;

let ALL_OR_lemma = prove_thm
  (`ALL_OR_lemma`,
   "!(P:num->(*->bool)) i. (($?* P) = ((P i) \/* ($?* P)))",
   GEN_TAC THEN GEN_TAC THEN
   REWRITE_TAC [?*;\/*] THEN
   BETA_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL ["P:num->(*->bool)";"i:num"]
      ALL_OR_lemma1)));;

let ALL_i_OR_lemma1 = TAC_PROOF
  (([],
   "!(P:num->(*->bool)) s. (?i. \<=/* P i s) = (?i. P i s)"),
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      STRIP_TAC THEN
      UNDISCH_TAC "\<=/* (P:num->(*->bool)) i s" THEN
      SPEC_TAC ("i:num","i:num") THEN
      INDUCT_TAC THENL
        [
         REWRITE_TAC [\<=/* ] THEN
         DISCH_TAC THEN
         EXISTS_TAC "0" THEN
         ASM_REWRITE_TAC []
        ;
         REWRITE_TAC [\<=/*;\/*] THEN
         BETA_TAC THEN
         REPEAT STRIP_TAC THENL
           [
            RES_TAC THEN
            EXISTS_TAC "i':num" THEN
            ASM_REWRITE_TAC []
           ;
            EXISTS_TAC "SUC i" THEN
            ASM_REWRITE_TAC []
           ]
        ];
      STRIP_TAC THEN
      UNDISCH_TAC "(P:num->(*->bool)) i s" THEN
      SPEC_TAC ("i:num","i:num") THEN
      INDUCT_TAC THENL
        [
         DISCH_TAC THEN
         EXISTS_TAC "0" THEN
         ASM_REWRITE_TAC [\<=/* ]
        ;
         DISCH_TAC THEN
         EXISTS_TAC "SUC i" THEN
         REWRITE_TAC [\<=/*;\/*] THEN
         BETA_TAC THEN
         ASM_REWRITE_TAC []
        ]
     ]);;

let ALL_i_OR_lemma = prove_thm
  (`ALL_i_OR_lemma`,
   "!(P:num->(*->bool)). ((\s. ?i. \<=/* P i s) = ($?* P))",
   REWRITE_TAC [?*] THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPEC "P:num->(*->bool)"
      ALL_i_OR_lemma1)));;

close_theory();;
