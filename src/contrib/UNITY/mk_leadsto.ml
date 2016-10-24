% -*- Emacs Mode: fundamental -*- %


%-----------------------------------------------------------------------------%
%
   File:         mk_leadsto.ml

   Description:  This file defines LEADSTO and the theorems and corrollaries
                 described in [CM88].

   Authors:      (c) Copyright by Flemming Andersen
   Date:         July 24. 1990
   Updated:      November 11, 1991 (including LUB)
   Last update:  October 3, 1992 (including state space restriction)
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
autoload_defs_and_thms `gen_induct`;;
%

set_flag(`print_all_subgoals`, false);;

system `/bin/rm leadsto.th`;;

new_theory`leadsto`;;

%
 We want to define a function LeadstoRel, which satisfies the three 
 properties of the given axiomatic definition of LEADSTO:

                  p ensures q in Pr
                 ------------------- (1)
                  p leadsto q in Pr

         p leadsto q in Pr,  q leadsto r in Pr
        -------------------------------------- (2)
                  p leadsto r in Pr

                 !i. (p i) leadsto q in Pr
               ------------------------- (3)
                (?i. p i) leadsto q in Pr
%
let LUB = new_definition
  (`LUB`,
   "LUB (P:(*->bool)->bool) = \s:*. ?p. (P p) /\ p s");;

let In = new_infix_definition
  (`In`,
   "In (p:*->bool) (P:(*->bool)->bool) = P p");;

let LeadstoRel = new_definition
  (`LeadstoRel`,
   "LeadstoRel R Pr =
      !(p:*->bool) q.
        ((p ENSURES q)Pr                                 ==> R p q Pr) /\
        (!r. (R p r Pr /\ R r q Pr)                      ==> R p q Pr) /\
        (!P.  (p = LUB P) /\ (!p. (p In P) ==> R p q Pr) ==> R p q Pr)");;

%
   Now we may define LEADSTO:
%
let LEADSTO = new_infix_definition
  (`LEADSTO`,
   "LEADSTO (p:*->bool) q Pr = (!R. (LeadstoRel R Pr) ==> (R p q Pr))");;

%
 ******************************************************************************
	Prove that the given axioms 1, 2, 3 are really theorems for the family
 ******************************************************************************
%

% Prove:
   !P Q Pr. (P ENSURES Q)Pr ==> (P LEADSTO Q)Pr
%
let LEADSTO_thm0 = prove_thm
  (`LEADSTO_thm0`,
   "!(p:*->bool) q Pr. (p ENSURES q) Pr ==> (p LEADSTO q)Pr",
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

% Prove:
   !P Q R Pr.
    (P LEADSTO Q)Pr /\ (Q LEADSTO R)Pr ==> (P LEADSTO R)Pr
%
let LEADSTO_thm1 = prove_thm
  (`LEADSTO_thm1`,
   "!(p:*->bool) r q Pr.
        (p LEADSTO r)Pr /\ (r LEADSTO q)Pr ==> (p LEADSTO q) Pr",
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;

% Prove:
   !P Q R Pr.
    (P ENSURES Q)Pr /\ (Q LEADSTO R)Pr ==> (P LEADSTO R)Pr
%
let LEADSTO_thm2 = prove_thm
  (`LEADSTO_thm2`,
   "!(p:*->bool) r q Pr.
        (p ENSURES r)Pr /\ (r LEADSTO q)Pr ==> (p LEADSTO q) Pr",
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;

% Prove:
   !P Q R Pr.
    (P ENSURES Q)Pr /\ (Q ENSURES R)Pr ==> (P LEADSTO R)Pr
%
let LEADSTO_thm2a = prove_thm
  (`LEADSTO_thm2a`,
   "!(p:*->bool) r q Pr.
        (p ENSURES r)Pr /\ (r ENSURES q)Pr ==> (p LEADSTO q) Pr",
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;

% Prove:
   !P q Pr. (!i. (P i) LEADSTO q)Pr ==> (($?* P) LEADSTO q)Pr
%
let LEADSTO_thm3_lemma01 = TAC_PROOF
  (([],
   "(!p:*->bool.
        p In P ==>
        (!R.
          (!p q.
            ((p ENSURES q)Pr ==> R p q Pr) /\
            (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
            (!P.
              (p = LUB P) /\ (!p'. p' In P ==> R p' q Pr) ==> R p q Pr)) ==>
          R p q Pr))
        ==>
       (!p:*->bool.
        p In P ==>
        ((!p q.
            ((p ENSURES q)Pr ==> R p q Pr) /\
            (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
            (!P.
              (p = LUB P) /\ (!p'. p' In P ==> R p' q Pr) ==> R p q Pr)) ==>
          R p q Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm3 = prove_thm
  (`LEADSTO_thm3`,
   "!p (P:(*->bool)->bool) q Pr.
      ((p = LUB P) /\ (!p. (p In P) ==> (p LEADSTO q)Pr)) ==> (p LEADSTO q)Pr",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (GEN_ALL (REWRITE_RULE[ASSUME
     "!(p:*->bool) q.
        ((p ENSURES q)Pr ==> R p q Pr) /\
        (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
        (!P. (p = LUB P) /\ (!p'. p' In P ==> R p' q Pr) ==> R p q Pr)"]
           (SPEC_ALL (UNDISCH (SPEC_ALL LEADSTO_thm3_lemma01))))) THEN
   RES_TAC);;

let LEADSTO_thm3a = prove_thm
  (`LEADSTO_thm3a`,
   "!(P:(*->bool)->bool) q Pr.
       (!p. (p In P) ==> (p LEADSTO q)Pr) ==> ((LUB P) LEADSTO q)Pr",
   REPEAT GEN_TAC THEN
   ACCEPT_TAC (SPEC_ALL
    (REWRITE_RULE [] (SPECL
      ["LUB (P:(*->bool)->bool)";"P:(*->bool)->bool"] LEADSTO_thm3))));;

let LEADSTO_thm3c_lemma01 = TAC_PROOF
  (([],
   "!p:*->bool. p In (\p. ?i. p = P (i:num)) = (?i. p = P i)"),
   REWRITE_TAC [In] THEN
   BETA_TAC THEN
   REWRITE_TAC []);;

let LEADSTO_thm3c_lemma02 = TAC_PROOF
  (([],
   "!(P:num->*->bool) q i.
       ((?i'. P i = P i') ==> q) = (!i'. (P i = P i') ==> q)"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ASM_CASES_TAC "?i'. (P:num->*->bool) i = P i'" THEN 
     RES_TAC
    ;
     ACCEPT_TAC (REWRITE_RULE [SYM (ASSUME "(P:num->*->bool) i = P i'")]
      (SPEC_ALL (ASSUME "!i'. ((P:num->*->bool) i = P i') ==> q")))
    ]);;

let LEADSTO_thm3c_lemma03 = TAC_PROOF
  (([],
   "(!p:*->bool. (?i. p = P i) ==> (p LEADSTO q)Pr) =
    (!i:num. ((P i) LEADSTO q)Pr)"),
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ACCEPT_TAC (REWRITE_RULE [] (SPEC "i:num" (REWRITE_RULE
      [LEADSTO_thm3c_lemma02] (SPEC "(P:num->*->bool)i" (ASSUME
       "!p:*->bool. (?i:num. p = P i) ==> (p LEADSTO q)Pr")))))
    ;
     ASM_REWRITE_TAC []
    ]);;

let LEADSTO_thm3c_lemma04 = TAC_PROOF
  (([],
   "!s. ($?* (P:num->*->bool))s = (LUB(\p. ?i. p = P i))s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [?*;LUB] THEN
   BETA_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     EXISTS_TAC "(P:num->*->bool)x" THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC "x:num" THEN
     REFL_TAC
    ;
     EXISTS_TAC "i:num" THEN
     ACCEPT_TAC (ONCE_REWRITE_RULE [ASSUME "p = (P:num->*->bool)i"]
      (ASSUME "(p:*->bool) s"))
    ]);;

let LEADSTO_thm3c = prove_thm
  (`LEADSTO_thm3c`,
   "!(P:num->*->bool) q Pr.
        (!i. ((P i) LEADSTO q)Pr) ==> (($?* P) LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm3c_lemma03]
    (REWRITE_RULE [LEADSTO_thm3c_lemma01] (ISPEC
       "\p. ?i. (p = (P:num->*->bool)i)" LEADSTO_thm3a))) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [REWRITE_RULE [ETA_AX] (MK_ABS LEADSTO_thm3c_lemma04)]);;

% Prove:
   !p1 p2 q Pr.
     (p1 LEADSTO q)Pr /\ (p2 LEADSTO q)Pr ==> ((p1 \/* p2) LEADSTO q)Pr
%

%
  To prove this we need some general lemmas about expressing two known
  relations as one relation:
%

%
  |- !p1 p2 s. (p1 \/* p2)s = LUB(\p. (p = p1) \/ (p = p2))s
%
let LEADSTO_thm4_lemma1a = TAC_PROOF
  (([],
   "!(p1:*->bool) p2 s. (p1 \/* p2) s = (LUB (\p. (p = p1) \/ (p = p2))) s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LUB;\/*] THEN
   BETA_TAC THEN
   EQ_TAC THENL
     [
      STRIP_TAC THENL
       [
        EXISTS_TAC "p1:*->bool" THEN
        ASM_REWRITE_TAC []
       ;
        EXISTS_TAC "p2:*->bool" THEN
        ASM_REWRITE_TAC []
       ]
     ;
      STRIP_TAC THENL
       [
        REWRITE_TAC [REWRITE_RULE [ASSUME "(p:*->bool) = p1"] (ASSUME
         "(p:*->bool) s")]
       ;
        REWRITE_TAC [REWRITE_RULE [ASSUME "(p:*->bool) = p2"] (ASSUME
         "(p:*->bool) s")]
       ]
     ]);;

%
  |- !p1 p2. p1 \/* p2 = LUB(\p. (p = p1) \/ (p = p2))
%
let LEADSTO_thm4_lemma1 = (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:*"
  (SPEC_ALL LEADSTO_thm4_lemma1a)))));;

%
  |- !R p1 p2 q Pr.
    R p1 q Pr ==> R p2 q Pr ==> (!p. (\p. (p = p1) \/ (p = p2))p ==> R p q Pr)
%
let LEADSTO_thm4_lemma2 = TAC_PROOF
  (([],
   "!R (p1:*->bool) p2 (q:*->bool) (Pr:(*->*)list).
      R p1 q Pr ==> R p2 q Pr ==> 
       (!p. (\p. (p = p1) \/ (p = p2))p ==> R p q Pr)"),
   BETA_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ASM_REWRITE_TAC []
    ;
     ASM_REWRITE_TAC []
    ]);;

%
  |- !R p1 p2 q Pr. R p1 q Pr ==> R p2 q Pr ==>
      (!p q P. (p = LUB P) /\ (!p. P p ==> R p q Pr) ==> R p q Pr)
           ==> R(p1 \/* p2) q Pr
%
let LEADSTO_thm4_lemma3 = TAC_PROOF
  (([],
   "!R (p1:*->bool) p2 (q:*->bool) (Pr:(*->*)list).
     R p1 q Pr ==> R p2 q Pr ==> 
       (!p q P. (p = LUB P) /\ (!p. P p ==> R p q Pr) ==> R p q Pr) ==>
          R (p1 \/* p2) q Pr"),
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [SYM (SPEC_ALL LEADSTO_thm4_lemma1);
     UNDISCH_ALL (SPEC_ALL LEADSTO_thm4_lemma2)]
      (SPECL
        ["(p1:*->bool) \/* p2";"q:*->bool";"\p:*->bool. (p = p1) \/ (p = p2)"]
           (ASSUME "!p (q:*->bool) (P:(*->bool)->bool). (p = LUB P) /\
                       (!p. P p ==> R p q Pr) ==> R p q (Pr:(*->*)list)"))));;
%
  Now Prove that the finite disjunction is satisfied
%

%
|- !p1 p2 q Pr.
      (p1 LEADSTO q)Pr /\ (p2 LEADSTO q)Pr ==> ((p1 \/* p2) LEADSTO q)Pr
%
let LEADSTO_thm4 = prove_thm
  (`LEADSTO_thm4`,
   "!(p1:*->bool) p2 q Pr.
        (p1 LEADSTO q)Pr /\ (p2 LEADSTO q)Pr ==> ((p1 \/* p2) LEADSTO q)Pr",
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASSUME_TAC (REWRITE_RULE [In] (GEN_ALL (CONJUNCT2 (CONJUNCT2 (SPEC_ALL
    (ASSUME
      "!(p:*->bool) q.
        ((p ENSURES q)Pr ==> R p q Pr) /\
        (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
     (!P. (p = LUB P) /\ (!p'. p' In P ==> R p' q Pr) ==> R p q Pr)")))))) THEN
   ACCEPT_TAC (UNDISCH_ALL (SPEC_ALL LEADSTO_thm4_lemma3)));;

%
   Prove:
      ((p ENSURES q)Pr \/
       (?r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr) \/
       (?P. (p = ($?* P)) /\ (!i. ((P i) LEADSTO q)Pr))) =
          (p LEADSTO q)Pr
%
let LEADSTO_thm5_lemma1 = TAC_PROOF
  (([],
   "!(p:*->bool) s. (p s = (\s. ?p'. ((p = p') => T | F) /\ p' s)s)"),
   REPEAT GEN_TAC THEN
   BETA_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL
    [
     EXISTS_TAC "p:*->bool" THEN
     ASM_REWRITE_TAC []
    ;
     UNDISCH_TAC "(((p:*->bool) = p') => T | F)" THEN
     REPEAT COND_CASES_TAC THEN
     ASM_REWRITE_TAC []
    ]);;

%
   |- !p. p = (\s. ?p'. ((p = p') => T | F) /\ p' s)
%
let LEADSTO_thm5_lemma2 = (GEN_ALL
     (REWRITE_RULE [ETA_AX] (MK_ABS (SPEC "p:*->bool" LEADSTO_thm5_lemma1))));;

let LEADSTO_thm5_lemma3 = TAC_PROOF
  (([],
   "!(p:*->bool) p'. ((p = p') => T | F) = (p = p')"),
   REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC []);;


%
  |- !p q Pr.
       (p ENSURES q)Pr \/
       (?r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr) \/
       (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))
      =
       (p LEADSTO q)Pr
%
let LEADSTO_thm5 = prove_thm
  (`LEADSTO_thm5`,
   "!(p:*->bool) q Pr.
      ((p ENSURES q) Pr \/
      (?r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr) \/
      (?P:(*->bool)->bool. (p = LUB P) /\ (!p. (p In P) ==> (p LEADSTO q)Pr)))
     =
      (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (UNDISCH (SPEC_ALL LEADSTO_thm0))
        ;
         IMP_RES_TAC LEADSTO_thm1
        ;
         IMP_RES_TAC LEADSTO_thm3
        ]
     ;
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        GEN_TAC THEN
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        DISCH_TAC THEN
        ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
       ]
     ]);;

%
   Prove:
      ((p ENSURES q)Pr \/
       (?r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) \/
       (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))
      =
       (p LEADSTO q)Pr
%
let LEADSTO_thm6 = prove_thm
  (`LEADSTO_thm6`,
   "!(p:*->bool) q Pr.
       ((p ENSURES q) Pr \/
        (?r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) \/
        (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr)))
      =
        (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (UNDISCH (SPEC_ALL LEADSTO_thm0))
        ;
         IMP_RES_TAC LEADSTO_thm2
        ;
         IMP_RES_TAC LEADSTO_thm3
        ]
     ;
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        GEN_TAC THEN
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        DISCH_TAC THEN
        ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
       ]
     ]);;

%
   Prove:
      ((p ENSURES q)Pr \/
       (?r. (p ENSURES r)Pr /\ (r ENSURES q)Pr) \/
       (?P. (p = ($?* P)) /\ (!i. ((P i) LEADSTO q)Pr))) =
          (p LEADSTO q)Pr
%
let LEADSTO_thm7 = prove_thm
  (`LEADSTO_thm7`,
   "!(p:*->bool) q Pr.
       ((p ENSURES q) Pr \/
        (?r. (p ENSURES r)Pr /\ (r ENSURES q)Pr) \/
        (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))) =
           (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (UNDISCH (SPEC_ALL LEADSTO_thm0))
        ;
         IMP_RES_TAC LEADSTO_thm2a
        ;
         IMP_RES_TAC LEADSTO_thm3
        ]
     ;
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        GEN_TAC THEN
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        DISCH_TAC THEN
        ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
       ]
     ]);;

%
   Prove:
      ((p ENSURES q)Pr \/
      (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr)) =
          (p LEADSTO q)Pr
%
let LEADSTO_thm8 = prove_thm
  (`LEADSTO_thm8`,
   "!(p:*->bool) q Pr.
       ((p ENSURES q) Pr \/
        (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr)))
      =
        (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (UNDISCH (SPEC_ALL LEADSTO_thm0))
        ;
         IMP_RES_TAC LEADSTO_thm3 THEN
         ASM_REWRITE_TAC []
        ]
     ;
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        GEN_TAC THEN
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        DISCH_TAC THEN
        ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
       ]
     ]);;

%
   Prove:
     (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr)) = (p LEADSTO q)Pr
%
let LEADSTO_thm9 = prove_thm
  (`LEADSTO_thm9`,
   "!(p:*->bool) q Pr.
      (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr)) = (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THEN
      IMP_RES_TAC LEADSTO_thm3 THEN
      ASM_REWRITE_TAC []
     ;
      REPEAT STRIP_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        GEN_TAC THEN
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        DISCH_TAC THEN
        ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
       ]
     ]);;

% Prove:

  !P Q Pr. (P LEADSTO Q) [] = false

%

%
   Theorem LEADSTO_thm10 does not hold for the generalised disjunctive
   rule, since:

     (!P. (p = LUB P) /\ (!p'. p' In P ==> F) ==> F))

   is only satisfied when P is non-empty

let LEADSTO_thm10 = prove_thm
  (`LEADSTO_thm10`,
   "!(p:*->bool) q. (p LEADSTO q) [] = F",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC "\(p:*->bool) (q:*->bool) (Pr:(*->*)list). F" THEN
   BETA_TAC THEN
   REWRITE_TAC [ENSURES_thm0] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [DE_MORGAN_THM] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL IMP_DISJ_THM))] THEN
   REWRITE_TAC [In;LUB] THEN
   STRIP_TAC THEN
   CONV_TAC NOT_FORALL_CONV THEN
   REWRITE_TAC [] THEN

   ...

%

%
   Prove:
       (?r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) = (p LEADSTO q)Pr
%
let LEADSTO_thm11 = prove_thm
  (`LEADSTO_thm11`,
   "!(p:*->bool) q st Pr.
        (?r. (p ENSURES r)(CONS st Pr) /\ (r LEADSTO q)(CONS st Pr)) =
            (p LEADSTO q)(CONS st Pr)",
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     IMP_RES_TAC LEADSTO_thm2
    ;
     EXISTS_TAC "p:*->bool" THEN
     ASM_REWRITE_TAC [ENSURES_thm1]
    ]);;


% Prove:

  !P Pr. (P LEADSTO P) (CONS st Pr)

%
let LEADSTO_thm12 = prove_thm
  (`LEADSTO_thm12`,
   "!(p:*->bool) st Pr. (p LEADSTO p) (CONS st Pr)",
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [SYM (SPEC_ALL LEADSTO_thm5)] THEN
   DISJ1_TAC THEN
   REWRITE_TAC [ENSURES_thm1]);;

%
   Prove:
       (?r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr) = (p LEADSTO q)Pr
%
let LEADSTO_thm13 = prove_thm
  (`LEADSTO_thm13`,
   "!(p:*->bool) q st Pr.
        (?r. (p LEADSTO r)(CONS st Pr) /\ (r LEADSTO q)(CONS st Pr))
      = (p LEADSTO q)(CONS st Pr)",
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     IMP_RES_TAC LEADSTO_thm1
    ;
     EXISTS_TAC "p:*->bool" THEN
     ASM_REWRITE_TAC [LEADSTO_thm12]
    ]);;

%
   Prove:
       (?r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr) =
       (?r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr)
%
let LEADSTO_thm14 = prove_thm
  (`LEADSTO_thm14`,
   "!(p:*->bool) q st Pr.
        (?r. (p LEADSTO r)(CONS st Pr) /\ (r LEADSTO q)(CONS st Pr))
      =
        (?r. (p ENSURES r)(CONS st Pr) /\ (r LEADSTO q)(CONS st Pr))",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LEADSTO_thm11;LEADSTO_thm13]);;

%
   Prove:
    |- !p q Pr.
        (p ENSURES q)Pr \/
        (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) \/
        (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))
      =
        (p LEADSTO q)Pr
%
let LEADSTO_thm15 = prove_thm
  (`LEADSTO_thm15`,
   "!(p:*->bool) q Pr.
       ((p ENSURES q) Pr \/
        (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) \/
        (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))) =
           (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     IMP_RES_TAC LEADSTO_thm0
    ;
     ACCEPT_TAC (MP (SPEC_ALL LEADSTO_thm2) (SPEC_ALL
      (ASSUME "!r:*->bool. (p ENSURES r)Pr /\ (r LEADSTO q)Pr")))
    ;
     IMP_RES_TAC LEADSTO_thm3
    ;
     DISJ2_TAC THEN
     DISJ2_TAC THEN
     EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
     REWRITE_TAC [LUB;In] THEN
     BETA_TAC THEN
     CONJ_TAC THENL
      [
       ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
      ;
       GEN_TAC THEN
       REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
       DISCH_TAC THEN
       ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
      ]
    ]);;

%
   Prove:

    |- !p q Pr.
        (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) \/
        (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))
       =
        (p LEADSTO q)Pr
%
let LEADSTO_thm16 = prove_thm
  (`LEADSTO_thm16`,
   "!(p:*->bool) q Pr.
       ((!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr) \/
       (?P. (p = LUB P) /\ (!p. p In P ==> (p LEADSTO q)Pr))) =
           (p LEADSTO q)Pr",
   REPEAT STRIP_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ACCEPT_TAC (MP (SPEC_ALL LEADSTO_thm2) (SPEC_ALL
      (ASSUME "!r:*->bool. (p ENSURES r)Pr /\ (r LEADSTO q)Pr")))
    ;
     IMP_RES_TAC LEADSTO_thm3
    ;
     DISJ2_TAC THEN
     EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
     REWRITE_TAC [LUB;In] THEN
     BETA_TAC THEN
     CONJ_TAC THENL
      [
       ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
      ;
       GEN_TAC THEN
       REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
       DISCH_TAC THEN
       ACCEPT_TAC (REWRITE_RULE [ASSUME "(p:*->bool) = p'"]
         (ASSUME "((p:*->bool) LEADSTO q)Pr"))
      ]
    ]);;


%
  Finally prove one of the used LEADSTO induction principles in CM88:

|- !X p q Pr.

    (!p q.

      ((p ENSURES q)Pr ==> X p q Pr)

     /\

      (!r.
        (p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr) /\
        (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)

           ==> (p LEADSTO q)Pr ==> X p q Pr)

     /\

      (!P.
        (!p. p In P ==> (p LEADSTO q)Pr) /\
        (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)

           ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))

    ==> (p LEADSTO q)Pr ==> X p q Pr

%
let STRUCT_lemma0 = TAC_PROOF
  (([],
   "(!p:*->bool. p In P ==> (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr))
    =
    ((!p. p In P ==> (p LEADSTO q)Pr) /\
     (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr))"),
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;


let STRUCT_lemma00 = TAC_PROOF
  (([],
   "!X Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r.
          (p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr) /\
          (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
             ==> (p LEADSTO q)Pr ==> X p q Pr) /\
        (!P.
          (!p. p In P ==> (p LEADSTO q)Pr) /\
          (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
             ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))
     =
      (!p q.
         ((p ENSURES q)Pr ==>
          (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)) /\
         (!r.
           ((p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr)) /\
           (r LEADSTO q)Pr /\
           ((r LEADSTO q)Pr ==> X r q Pr) ==>
           (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)) /\
         (!P.
           (p = LUB P) /\
           (!p'.
             p' In P ==> (p' LEADSTO q)Pr /\ ((p' LEADSTO q)Pr ==> X p' q Pr))
                ==> (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     IMP_RES_TAC LEADSTO_thm0
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm1
    ;
     RES_TAC
    ;
     IMP_RES_TAC STRUCT_lemma0 THEN
     IMP_RES_TAC LEADSTO_thm3a THEN
     RES_TAC THEN
     ASM_REWRITE_TAC []
    ;
     IMP_RES_TAC STRUCT_lemma0 THEN
     IMP_RES_TAC LEADSTO_thm3a THEN
     RES_TAC THEN
     ASM_REWRITE_TAC []
    ;
     RES_TAC
    ;
     RES_TAC
    ;
     ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL STRUCT_lemma0)] (CONJ 
      (ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr")
      (ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr ==> X p q Pr"))) THEN
     ACCEPT_TAC (REWRITE_RULE [ASSUME "((LUB P) LEADSTO (q:*->bool))Pr"]
      (SPEC "LUB (P:(*->bool)->bool)" (GEN_ALL (REWRITE_RULE
        [ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr /\
                                     ((p LEADSTO q)Pr ==> X p q Pr)"]
          (SPEC_ALL (CONJUNCT2 (CONJUNCT2 (SPEC_ALL (ASSUME
            "!(p:*->bool) q.
               ((p ENSURES q)Pr ==>
               (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)) /\
               (!r.
                 ((p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr)) /\
                  (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr) ==>
                     (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)) /\
               (!P. (p = LUB P) /\
                  (!p'. p' In P ==>
                     (p' LEADSTO q)Pr /\ ((p' LEADSTO q)Pr ==> X p' q Pr)) ==>
              (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr))")))))))))
    ]);;

%
  The induction theorem:
%
let LEADSTO_thm17 = prove_thm
  (`LEADSTO_thm17`,
   "!X (p:*->bool) q Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr) /\
             (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
            ==> ((p LEADSTO q)Pr ==> X p q Pr)) /\
        (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\
             (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
            ==> (((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr)))
     ==> ((p LEADSTO q)Pr ==> X p q Pr)",
   REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL STRUCT_lemma00)] (BETA_RULE (SPEC
     "\(p:*->bool) q Pr. (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)"
       (REWRITE_RULE [LEADSTO;LeadstoRel]
          (ASSUME "((p:*->bool) LEADSTO q)Pr"))))) THEN
   RES_TAC);;

%
  A derived theorem for an induction tactic
%
let LEADSTO_thm18 = prove_thm
  (`LEADSTO_thm18`,
   "!X.
      ((!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr) /\
        (!p r q Pr. (p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr) /\
                 (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
            ==> ((p LEADSTO q)Pr ==> X p q Pr)) /\
        (!p P q Pr. (!p. p In P ==> (p LEADSTO q)Pr) /\
                  (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
            ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))
     ==> (!p q Pr. (p LEADSTO q)Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL STRUCT_lemma00)]
    (BETA_RULE (SPEC
     "\(p:*->bool) q Pr. (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)"
       (REWRITE_RULE [LEADSTO;LeadstoRel]
          (ASSUME "((p:*->bool) LEADSTO q)Pr"))))) THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) r q Pr.
        (p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr) /\
        (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
            ==> (p LEADSTO q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) P q Pr.
        (!p. p In P ==> (p LEADSTO q)Pr) /\
        (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
            ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr";
     ASSUME "((p:*->bool) LEADSTO q)Pr"] (ASSUME
      "(!(p:*->bool) q.
         ((p ENSURES q)Pr ==> X p q Pr) /\
         (!r.
           (p LEADSTO r)Pr /\ ((p LEADSTO r)Pr ==> X p r Pr) /\
           (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
             ==> (p LEADSTO q)Pr ==> X p q Pr) /\
         (!P.
           (!p'. p' In P ==> (p' LEADSTO q)Pr) /\
           (!p'. p' In P ==> (p' LEADSTO q)Pr ==> X p' q Pr)
             ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))
         ==> (p LEADSTO q)Pr /\ ((p LEADSTO q)Pr ==> X p q Pr)")));;


%
  Now prove another LEADSTO induction principle:

%
let STRUCT_lemma1 = TAC_PROOF
  (([],
   "(!p:*->bool. p In P ==> (p LEADSTO q)Pr /\ X p q Pr)
    =
    ((!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr))"),
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let STRUCT_lemma01 = TAC_PROOF
  (([],
   "!X Pr.
      (!(p:*->bool) q.
         ((p ENSURES q)Pr ==> (p LEADSTO q)Pr /\ X p q Pr) /\
         (!r. ((p LEADSTO r)Pr /\ X p r Pr) /\ (r LEADSTO q)Pr /\ X r q Pr
              ==> (p LEADSTO q)Pr /\ X p q Pr) /\
         (!P. (p = LUB P) /\ (!p'. p' In P ==> (p' LEADSTO q)Pr /\ X p' q Pr)
              ==> (p LEADSTO q)Pr /\ X p q Pr))
     =
      (!p q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p LEADSTO r)Pr /\ X p r Pr /\ (r LEADSTO q)Pr /\ X r q Pr
              ==> (p LEADSTO q)Pr ==> X p q Pr) /\
        (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
               ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))"),
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
    [
     RES_TAC
    ;
     RES_TAC
    ;
     ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL STRUCT_lemma1)] (CONJ 
      (ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr")
      (ASSUME "!p. p In P
         ==> (X:(*->bool)->(*->bool)->(*->*)list->bool) p q Pr"))) THEN
     RES_TAC THEN
     ACCEPT_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME 
      "!p. (p = LUB P) ==> (X:(*->bool)->(*->bool)->(*->*)list->bool)p q Pr")))
    ;
     IMP_RES_TAC LEADSTO_thm0
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm1
    ;
     IMP_RES_TAC LEADSTO_thm1 THEN
     RES_TAC
    ;
     IMP_RES_TAC STRUCT_lemma1 THEN
     IMP_RES_TAC LEADSTO_thm3
    ;
     IMP_RES_TAC STRUCT_lemma1 THEN
     IMP_RES_TAC LEADSTO_thm3a THEN
     RES_TAC THEN
     ASM_REWRITE_TAC []
    ]);;
       
%
  The induction theorem:
%
let LEADSTO_thm19 = prove_thm
  (`LEADSTO_thm19`,
   "!X (p:*->bool) q Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p LEADSTO r)Pr /\ (X p r Pr) /\ (r LEADSTO q)Pr /\ (X r q Pr)
            ==> ((p LEADSTO q)Pr ==> X p q Pr)) /\
        (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
            ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))
     ==> ((p LEADSTO q)Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [STRUCT_lemma01] (BETA_RULE
    (SPEC "\(p:*->bool) q Pr. (p LEADSTO q)Pr /\ (X p q Pr)"
      (REWRITE_RULE [LEADSTO;LeadstoRel]
        (ASSUME "((p:*->bool) LEADSTO q)Pr"))))) THEN
   RES_TAC);;

%
  The derived theorem for the induction tactic
%
let LEADSTO_thm20 = prove_thm
  (`LEADSTO_thm20`,
   "!X.
     ((!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr) /\
      (!p r q Pr. (p LEADSTO r)Pr /\ X p r Pr /\ (r LEADSTO q)Pr /\ X r q Pr
            ==> ((p LEADSTO q)Pr ==> X p q Pr)) /\
      (!p P q Pr. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
            ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))
     ==> (!p q Pr. (p LEADSTO q)Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) r q Pr.
                (p LEADSTO r)Pr /\ X p r Pr /\ (r LEADSTO q)Pr /\ X r q Pr ==>
                   (p LEADSTO q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) P q Pr.
        (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr) ==>
                   ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr";
     ASSUME "((p:*->bool) LEADSTO q)Pr"]
      (REWRITE_RULE [STRUCT_lemma01](BETA_RULE (SPEC
        "\(p:*->bool) q Pr. (p LEADSTO q)Pr /\ (X p q Pr)"
          (REWRITE_RULE [LEADSTO;LeadstoRel]
             (ASSUME "((p:*->bool) LEADSTO q)Pr")))))));;

%
  Now prove a third LEADSTO induction principle:

|- !X p q Pr.

    (!p q.

       ((p ENSURES q)Pr ==> X p q Pr)
     /\
       (!r. (X p r Pr) /\ (X r q Pr) ==> X p q Pr)
     /\
       (!P. (!i. X(P i)q Pr) ==> X($?* P)q Pr))

     ==> (p LEADSTO q)Pr ==> X p q Pr

%
let LEADSTO_thm21 = prove_thm
  (`LEADSTO_thm21`,
   "!X (p:*->bool) q Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (X p r Pr) /\ (X r q Pr) ==> X p q Pr) /\
        (!P. (p = LUB P) /\ (!p. p In P ==> X p q Pr) ==> X p q Pr))
     ==> ((p LEADSTO q)Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (BETA_RULE (SPEC
     "\(p:*->bool) (q:*->bool) (Pr:(*->*)list). X p q Pr:bool"
      (REWRITE_RULE [LEADSTO;LeadstoRel]
        (ASSUME "((p:*->bool) LEADSTO q)Pr")))) THEN
   RES_TAC);;

%
  The theorem derived for an induction tactic
%
let LEADSTO_thm22 = prove_thm
  (`LEADSTO_thm22`,
   "!X.
      ((!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr) /\
       (!p r q Pr. (X p r Pr) /\ (X r q Pr) ==> (X p q Pr)) /\
       (!p P q Pr. (p = LUB P) /\ (!p. p In P ==> X p q Pr) ==> X p q Pr))
     ==> (!p q Pr. (p LEADSTO q)Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) (r:*->bool) q (Pr:(*->*)list).
                X p r Pr /\ X r q Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) P (q:*->bool) (Pr:(*->*)list).
               (p = LUB P) /\ (!p. p In P ==> X p q Pr) ==> X p q Pr";
     ASSUME "((p:*->bool) LEADSTO q)Pr"]
     (REWRITE_RULE [SYM (SPEC_ALL CONJ_ASSOC)] (BETA_RULE (SPEC
       "\(p:*->bool) (q:*->bool) (Pr:(*->*)list). X p q Pr:bool"
         (REWRITE_RULE [LEADSTO;LeadstoRel]
           (ASSUME "((p:*->bool) LEADSTO q)Pr")))))));;

%
  yet another LEADSTO induction principle:
%
let LEADSTO_thm23_lemma00 = TAC_PROOF
  (([],
   "!X Pr.
      ((!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)) =
       (!p:*->bool. p In P ==> (p LEADSTO q)Pr /\ X p q Pr)"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm23_lemma01 = TAC_PROOF
  (([],
   "!X Pr.
      (!(p:*->bool) q.
         ((p ENSURES q)Pr ==> (p LEADSTO q)Pr /\ X p q Pr) /\
         (!r.
           ((p LEADSTO r)Pr /\ X p r Pr) /\ (r LEADSTO q)Pr /\ X r q Pr
                          ==> (p LEADSTO q)Pr /\ X p q Pr) /\
         (!P. (p = LUB P) /\
              (!p'. p' In P ==> (p' LEADSTO q)Pr /\ X p' q Pr)
                          ==> (p LEADSTO q)Pr /\ X p q Pr))
      =
       (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r.
          (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
                         ==> X p q Pr) /\
        (!P. (p = LUB P) /\
             (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                         ==> X p q Pr))"),
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
    [
     RES_TAC
    ;
     RES_TAC
    ;
     ASSUME_TAC (REWRITE_RULE [LEADSTO_thm23_lemma00] (CONJ
      (ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr")
      (ASSUME "!p. p In P
                 ==> (X:(*->bool)->(*->bool)->(*->*)list->bool) p q Pr"))) THEN
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm0
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm1
    ;
     RES_TAC
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL LEADSTO_thm23_lemma00)]
      (ASSUME "!p':*->bool. p' In P ==> (p' LEADSTO q)Pr /\ X p' q Pr")) THEN
     IMP_RES_TAC LEADSTO_thm3a THEN
     ASM_REWRITE_TAC []
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL LEADSTO_thm23_lemma00)]
      (ASSUME "!p':*->bool. p' In P ==> (p' LEADSTO q)Pr /\ X p' q Pr")) THEN
     RES_TAC
    ]);;

let LEADSTO_thm23 = prove_thm
  (`LEADSTO_thm23`,
   "!X Pr.
      (!(p:*->bool) q.
       ((p ENSURES q)Pr ==> X p q Pr) /\
       (!r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
                        ==> X p q Pr) /\
       (!P. (p = LUB P) /\
            (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                        ==> X p q Pr))
     ==> (!p q. (p LEADSTO q) Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm23_lemma01] (BETA_RULE (SPEC
     "\(p:*->bool) q Pr. (p LEADSTO q)Pr /\ (X p q Pr)" 
       (REWRITE_RULE [LEADSTO;LeadstoRel]
         (ASSUME "((p:*->bool) LEADSTO q) Pr"))))) THEN
   RES_TAC);;

let LEADSTO_thm24_lemma01 = TAC_PROOF
  (([],
   "!X Pr.
     (!(p:*->bool) q.
       ((p ENSURES q)Pr ==> X p q Pr) /\
       (!r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
                        ==> X p q Pr) /\
       (!P. (p = LUB P) /\
            (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                        ==> X p q Pr))
     =
     (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r.
          (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr ==>
          X p q Pr) /\
        (!P.
          (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr) ==>
          X(LUB P)q Pr))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THENL
    [
     ACCEPT_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
     "!p. (p = LUB P) ==> (X:(*->bool)->(*->bool)->(*->*)list->bool) p q Pr")))
    ;
     ASM_REWRITE_TAC []
    ]);;

let LEADSTO_thm24 = prove_thm
  (`LEADSTO_thm24`,
   "!X Pr.
      (!(p:*->bool) q.
       ((p ENSURES q)Pr ==> X p q Pr) /\
       (!r. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
                        ==> X p q Pr) /\
       (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                        ==> X (LUB P) q Pr))
     ==> (!p q. (p LEADSTO q) Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (UNDISCH (SPEC_ALL (UNDISCH (REWRITE_RULE [LEADSTO_thm24_lemma01]
    (SPEC_ALL LEADSTO_thm23))))));;

% Prove:

  !P Q st Pr. (!s. P s ==> Q s) ==> (P LEADSTO Q) (CONS st Pr)

%
let LEADSTO_thm25 = prove_thm
  (`LEADSTO_thm25`,
   "!(p:*->bool) q st Pr. (!s. p s ==> q s) ==> (p LEADSTO q) (CONS st Pr)",
   REPEAT STRIP_TAC THEN
   STRIP_ASSUME_TAC
     (MP (SPECL ["p:*->bool";"q:*->bool";"CONS (st:*->*) Pr"] LEADSTO_thm0)
         (MP (SPECL ["p:*->bool";"q:*->bool";"st:*->*";"Pr:(*->*)list"]
                     ENSURES_cor1) (ASSUME "!s:*. p s ==> q s"))));;


% Prove:

  |- !p q q' st Pr.
         (p LEADSTO q)(CONS st Pr) ==> (p LEADSTO (q \/* q'))(CONS st Pr)
%
let LEADSTO_thm26 = prove_thm
  (`LEADSTO_thm26`,
   "!(p:*->bool) q q' st Pr.
       (p LEADSTO q)(CONS st Pr) ==> (p LEADSTO (q \/* q'))(CONS st Pr)",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL ["q:*->bool";"q':*->bool"] IMPLY_WEAK_lemma_b) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["q:*->bool";"(q:*->bool) \/* q'";"st:*->*";"Pr:(*->*)list"]
      LEADSTO_thm25)) THEN
   IMP_RES_TAC (SPECL
     ["p:*->bool";"q:*->bool";"(q:*->bool) \/* q'";"CONS (st:*->*) Pr"]
     LEADSTO_thm1));;


% Prove:

   |- !p q p' q' st Pr.
        (p LEADSTO q)(CONS st Pr) /\ (p' LEADSTO q')(CONS st Pr) ==>
           ((p \/* p') LEADSTO (q \/* q'))(CONS st Pr)
%
let LEADSTO_thm27 = prove_thm
  (`LEADSTO_thm27`,
   "!(p:*->bool) q p' q' st Pr.
      (p LEADSTO q)(CONS st Pr) /\ (p' LEADSTO q')(CONS st Pr)
          ==> ((p \/* p') LEADSTO (q \/* q'))(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL LEADSTO_thm26)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["p':*->bool";"q':*->bool";"q:*->bool";"st:*->*";"Pr:(*->*)list"]
     LEADSTO_thm26)) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [OR_COMM_lemma]
    (ASSUME "((p':*->bool) LEADSTO (q' \/* q))(CONS st Pr)")) THEN
   IMP_RES_TAC (SPECL
    ["p:*->bool";"p':*->bool";"(q:*->bool) \/* q'";"CONS (st:*->*) Pr"]
     LEADSTO_thm4));;


% Prove:

   |- !p q b r st Pr.
      (p LEADSTO (q \/* b))(CONS st Pr) /\ (b LEADSTO r)(CONS st Pr) ==>
         (p LEADSTO (q \/* r))(CONS st Pr)
%
let LEADSTO_thm28 = prove_thm
  (`LEADSTO_thm28`,
   "!(p:*->bool) q b r st Pr.
       (p LEADSTO (q \/* b))(CONS st Pr) /\ (b LEADSTO r)(CONS st Pr)
           ==> (p LEADSTO (q \/* r))(CONS st Pr)",
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (SPEC "q:*->bool" LEADSTO_thm12)) THEN
   ASSUME_TAC (MP (SPECL
    ["b:*->bool";"r:*->bool";"q:*->bool";"q:*->bool";
     "st:*->*";"Pr:(*->*)list"] LEADSTO_thm27) (CONJ
       (ASSUME "((b:*->bool) LEADSTO r)(CONS st Pr)")
         (ASSUME "((q:*->bool) LEADSTO q)(CONS st Pr)"))) THEN
   ACCEPT_TAC (MP (SPECL ["p:*->bool";"(q:*->bool) \/* b";
    "(q:*->bool) \/* r";"CONS (st:*->*) Pr"] LEADSTO_thm1)
       (CONJ (ASSUME "((p:*->bool) LEADSTO (q \/* b))(CONS st Pr)")
         (ONCE_REWRITE_RULE [OR_COMM_lemma]
           (ASSUME "(((b:*->bool) \/* q) LEADSTO (r \/* q))(CONS st Pr)")))));;

% Prove:

   !p q r b Pr.
      (p LEADSTO q)Pr /\ (r UNLESS b)Pr
          ==> ((p /\* r) LEADSTO ((q /\* r) \/* b))Pr

%
let LEADSTO_thm29_lemma00 =
  (SPEC "CONS (st:*->*) Pr" (GEN "Pr:(*->*)list" (BETA_RULE (SPEC_ALL (SPEC
   "\(p:*->bool) q Pr.
        (r UNLESS b) Pr ==> ((p /\* r) LEADSTO ((q /\* r) \/* b)) Pr"
   LEADSTO_thm17)))));;

let LEADSTO_thm29_lemma05_1 = TAC_PROOF
  (([],
   "(!p'':*->bool. p'' In P ==> (p'' LEADSTO q')(CONS st Pr)) ==>
       (!p''. p'' In P ==>
        (p'' LEADSTO q')(CONS st Pr) ==> (r UNLESS b)(CONS st Pr) ==>
        ((p'' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)) ==>
       (!p''. p'' In P ==> (r UNLESS b)(CONS st Pr) ==>
        ((p'' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;

let LEADSTO_thm29_lemma05_2 = TAC_PROOF
  (([],
   "!(P:(*->bool)->bool) r q st Pr.
    (!p. p In P ==> ((p /\* r) LEADSTO q)(CONS st Pr)) ==>
    (!p. p In P ==> (p LEADSTO q)(CONS st Pr)) ==>
    (((LUB P) /\* r) LEADSTO q)(CONS st Pr)"),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm3a THEN
   ASSUME_TAC (SPECL
    ["LUB (P:(*->bool)->bool)";"r:*->bool"] SYM_AND_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL (SPECL
    ["(LUB P) /\* (r:*->bool)";"(LUB P):*->bool"] ENSURES_cor1))) THEN
   IMP_RES_TAC LEADSTO_thm0 THEN
   IMP_RES_TAC LEADSTO_thm1);;

let LEADSTO_thm29_lemma05_3 = TAC_PROOF
  (([],
   "!(p:*->bool) P r.
      p In (\p''. ?p'. p' In P /\ (p'' = p' /\* r))
     =
      (?p'. p' In P /\ (p = p' /\* r))"),
   REWRITE_TAC [In] THEN
   BETA_TAC THEN
   REWRITE_TAC []);;

let LEADSTO_thm29_lemma05_4 = TAC_PROOF
  (([],
   "!s:*.
      ((LUB P) /\* r)s =
      (LUB(\p. ?p'. p' In P /\ (p = p' /\* r)))s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LUB;/\*] THEN
   BETA_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     EXISTS_TAC "\s:*. p s /\ r s" THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC "p:*->bool" THEN
     ASM_REWRITE_TAC [In]
    ;
     EXISTS_TAC "p':*->bool" THEN
     REWRITE_TAC [REWRITE_RULE [In] (ASSUME "(p':*->bool) In P")] THEN
     STRIP_ASSUME_TAC (BETA_RULE (SUBS [ASSUME "p = (\s:*. p' s /\ r s)"]
                                       (ASSUME "(p:*->bool) s")))
    ;
     STRIP_ASSUME_TAC (BETA_RULE (SUBS [ASSUME "p = (\s:*. p' s /\ r s)"]
                                       (ASSUME "(p:*->bool) s")))
    ]);;

let LEADSTO_thm29_lemma05_5 = TAC_PROOF
  (([],
   "!(P:(*->bool)->bool) r q' b st Pr.
    (!p''. p'' In P ==> ((p'' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr))
      ==>
        (!p. (?p'. p' In P /\ (p = p' /\* r)) ==>
                 (p LEADSTO ((q' /\* r) \/* b))(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []);;

let LEADSTO_thm29_lemma05_6 = TAC_PROOF
  (([],
   "!(P:(*->bool)->bool) r q' b st Pr.
       (!p''.
        p'' In P ==>
        ((p'' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr))
           ==> ((((LUB P) /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm29_lemma05_3] (SPECL
     ["\p:*->bool. ?p'. p' In P /\ (p = (p' /\* r))";
      "(q' /\* r) \/* (b:*->bool)";"CONS (st:*->*) Pr"]
     LEADSTO_thm3a)) THEN
   ASSUME_TAC (REWRITE_RULE [UNDISCH (SPEC_ALL LEADSTO_thm29_lemma05_5)]
    (ASSUME "(!p:*->bool. (?p'. p' In P /\ (p = p' /\* r)) ==>
       (p LEADSTO ((q' /\* r) \/* b))(CONS st Pr)) ==>
       ((LUB(\p. ?p'. p' In P /\ (p = p' /\* r))) LEADSTO ((q' /\* r) \/* b))
        (CONS st Pr)")) THEN
   ASM_REWRITE_TAC [REWRITE_RULE [ETA_AX] (MK_ABS LEADSTO_thm29_lemma05_4)]);;


let LEADSTO_thm29_lemma05 = TAC_PROOF
  (([],
   "!(p':*->bool) q' r b st Pr.
     ((p' ENSURES q')(CONS st Pr) ==>
      (r UNLESS b)(CONS st Pr) ==>
      ((p' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)) /\
     (!r'.
       (p' LEADSTO r')(CONS st Pr) /\
       ((p' LEADSTO r')(CONS st Pr) ==>
        (r UNLESS b)(CONS st Pr) ==>
        ((p' /\* r) LEADSTO ((r' /\* r) \/* b))(CONS st Pr)) /\
       (r' LEADSTO q')(CONS st Pr) /\
       ((r' LEADSTO q')(CONS st Pr) ==>
        (r UNLESS b)(CONS st Pr) ==>
        ((r' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)) ==>
       (p' LEADSTO q')(CONS st Pr) ==>
       (r UNLESS b)(CONS st Pr) ==>
       ((p' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)) /\
     (!P.
       (!p''. p'' In P ==> (p'' LEADSTO q')(CONS st Pr)) /\
       (!p''.
         p'' In P ==>
         (p'' LEADSTO q')(CONS st Pr) ==>
         (r UNLESS b)(CONS st Pr) ==>
         ((p'' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)) ==>
       ((LUB P) LEADSTO q')(CONS st Pr) ==>
       (r UNLESS b)(CONS st Pr) ==>
       (((LUB P) /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr))"),
   REPEAT GEN_TAC THEN
   REPEAT CONJ_TAC THENL
     [
      REPEAT STRIP_TAC THEN
      IMP_RES_TAC ENSURES_thm4 THEN
      ASSUME_TAC (SPECL
        ["p':*->bool";"q':*->bool";"b:*->bool";"r:*->bool"]
         IMPLY_WEAK_lemma6) THEN
      ASSUME_TAC (MP (SPECL
        ["(r:*->bool) /\* p'";
         "((r:*->bool) /\* q') \/* ((p' /\* b) \/* (b /\* q'))";
         "((q':*->bool) /\* r) \/* b";"(CONS st Pr):(*->*)list"] ENSURES_thm2)
          (CONJ (REWRITE_RULE [OR_ASSOC_lemma]
            (ASSUME "(((r:*->bool) /\* p') ENSURES
                  (((r /\* q') \/* (p' /\* b)) \/* (b /\* q')))(CONS st Pr)"))
            (ASSUME "!s:*. ((r /\* q') \/* ((p' /\* b) \/* (b /\* q')))s ==>
                          ((q' /\* r) \/* b)s"))) THEN
      ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
      ONCE_REWRITE_TAC [AND_COMM_OR_lemma] THEN
      IMP_RES_TAC (SPECL ["(r:*->bool) /\* p'";"((q':*->bool) /\* r) \/* b";
                          "(CONS st Pr):(*->*)list"] LEADSTO_thm0)
     ;
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (MP (MP (ASSUME "((p':*->bool) LEADSTO r')(CONS st Pr) ==>
         (r UNLESS b)(CONS st Pr)
             ==> ((p' /\* r) LEADSTO ((r' /\* r) \/* b))(CONS st Pr)")
       (ASSUME "((p':*->bool) LEADSTO r')(CONS st Pr)"))
       (ASSUME "((r:*->bool) UNLESS b)(CONS st Pr)")) THEN
      ASSUME_TAC (MP (MP (ASSUME "((r':*->bool) LEADSTO q')(CONS st Pr) ==>
         (r UNLESS b)(CONS st Pr)
             ==> ((r' /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)")
       (ASSUME "((r':*->bool) LEADSTO q')(CONS st Pr)"))
       (ASSUME "((r:*->bool) UNLESS b)(CONS st Pr)")) THEN
      ACCEPT_TAC (REWRITE_RULE [OR_ASSOC_lemma;OR_OR_lemma]
       (ONCE_REWRITE_RULE [OR_COMM_lemma] (MP (SPECL
        ["(p':*->bool) /\* r";"b:*->bool";"(r':*->bool) /\* r";
         "((q':*->bool) /\* r) \/* b";"st:*->*";"Pr:(*->*)list"] LEADSTO_thm28)
         (CONJ (ONCE_REWRITE_RULE [OR_COMM_lemma]
          (ASSUME
             "(((p':*->bool) /\* r) LEADSTO ((r' /\* r) \/* b))(CONS st Pr)"))
          (ASSUME
           "(((r':*->bool) /\* r) LEADSTO ((q' /\* r) \/* b))(CONS st Pr)")))))
     ;
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (REWRITE_RULE [ASSUME "((r:*->bool) UNLESS b)(CONS st Pr)"]
       (UNDISCH_ALL LEADSTO_thm29_lemma05_1)) THEN
      IMP_RES_TAC LEADSTO_thm29_lemma05_6
     ]);;

let LEADSTO_thm29_lemma06 =
   GEN_ALL (MP (SPEC_ALL LEADSTO_thm29_lemma00)
      (GEN "p':*->bool" (GEN "q':*->bool" (SPEC_ALL LEADSTO_thm29_lemma05))));;

let LEADSTO_thm29 = prove_thm
  (`LEADSTO_thm29`,
   "!(p:*->bool) q r b st Pr.
    (p LEADSTO q)(CONS st Pr) /\ (r UNLESS b)(CONS st Pr)
      ==> ((p /\* r) LEADSTO ((q /\* r) \/* b))(CONS st Pr)",
   REPEAT STRIP_TAC THEN 
   REWRITE_TAC [UNDISCH_ALL (SPEC_ALL LEADSTO_thm29_lemma06)]);;

% Prove:

      !p st Pr. (p LEADSTO FALSE)(CONS st Pr) ==> (!s. ~* p s)

%
let LEADSTO_thm30_lemma00 = BETA_RULE
  (SPEC "CONS (st:*->*) Pr" (GEN "Pr:(*->*)list" (BETA_RULE (SPEC_ALL (SPEC
   "\(p:*->bool) (q:*->bool) (Pr:(*->*)list). (q = FALSE) ==> (!s. ~* p s)"
   LEADSTO_thm21)))));;

let LEADSTO_thm30_lemma01 = TAC_PROOF
  (([],
   "!(r:*->bool). (!s. ~* r s) ==> (!s. r s = FALSE s)"),
   REWRITE_TAC [~*;FALSE_DEF] THEN
   BETA_TAC THEN
   REWRITE_TAC []);;

%
  |- (!s. ~* r s) ==> (r = FALSE)
%
let LEADSTO_thm30_lemma02 = (DISCH_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (UNDISCH
     (SPEC_ALL LEADSTO_thm30_lemma01)))));;

let LEADSTO_thm30_lemma03 = TAC_PROOF
  (([],
  "!p:*->bool. (p' = (\s. ?p. P p /\ p s)) ==> (!s. p' s = ?p. P p /\ p s)"),
  GEN_TAC THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  ONCE_ASM_REWRITE_TAC [] THEN
  BETA_TAC THEN
  REFL_TAC);;

let LEADSTO_thm30_lemma04 = TAC_PROOF
  (([],
   "!(p':*->bool) (q':*->bool).
     ((p' ENSURES q')(CONS st Pr) ==> (q' = FALSE) ==> (!s. ~* p' s)) /\
     (!r:*->bool.
       ((r = FALSE) ==> (!s. ~* p' s)) /\
       ((q' = FALSE) ==> (!s. ~* r s)) ==>
       (q' = FALSE) ==> (!s. ~* p' s)) /\
     (!P:(*->bool)->bool.
       (p' = LUB P) /\
       (!p''. p'' In P ==> (q' = FALSE) ==> (!s. ~* p'' s)) ==>
       (q' = FALSE) ==> (!s. ~* p' s))"),
   REPEAT GEN_TAC THEN
   REPEAT CONJ_TAC THENL
     [
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (REWRITE_RULE [ASSUME "(q':*->bool) = FALSE"]
       (ASSUME "((p':*->bool) ENSURES q')(CONS st Pr)")) THEN
      IMP_RES_TAC ENSURES_thm3 THEN
      ASM_REWRITE_TAC []
     ;
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      IMP_RES_TAC LEADSTO_thm30_lemma02 THEN
      RES_TAC THEN
      ASM_REWRITE_TAC []
     ;
      REPEAT GEN_TAC THEN
      REWRITE_TAC [LUB;In;~*;FALSE_DEF] THEN
      BETA_TAC THEN
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (REWRITE_RULE [ASSUME "(q':*->bool) = \s. F"] (ASSUME 
       "!p'':*->bool. P p''
            ==> ((q':*->bool) = \s. F) ==> (!s. ~p'' s)")) THEN
      IMP_RES_TAC LEADSTO_thm30_lemma03 THEN
      RES_TAC
     ]);;

%
  |- !p q st Pr. (p LEADSTO q)(CONS st Pr) ==> (q = FALSE) ==> (!s. ~* p s)
%
let LEADSTO_thm30_lemma05 =
   GEN_ALL (MP (SPEC_ALL LEADSTO_thm30_lemma00) LEADSTO_thm30_lemma04);;

let LEADSTO_thm30_lemma06 = TAC_PROOF
  (([],
   "!(p:*->bool) st Pr.
       (p LEADSTO FALSE)(CONS st Pr)
          ==> (?q. (q = FALSE) /\ (p LEADSTO q)(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   EXISTS_TAC "FALSE:*->bool" THEN
   ASM_REWRITE_TAC []);;

% Now Prove:

   |- !p st Pr. (p LEADSTO FALSE)(CONS st Pr) ==> (!s. ~* p s)
%
let LEADSTO_thm30 = prove_thm
  (`LEADSTO_thm30`,
   "!(p:*->bool) st Pr. (p LEADSTO FALSE)(CONS st Pr) ==> (!s. ~* p s)",
   REPEAT STRIP_TAC THEN 
   IMP_RES_TAC LEADSTO_thm30_lemma06 THEN
   REWRITE_TAC [UNDISCH_ALL (SPEC_ALL LEADSTO_thm30_lemma05)]);;


% Prove:

  |- !p b q Pr.
    ((p /\* b) LEADSTO q)Pr /\ ((p /\* (~* b)) LEADSTO q)Pr ==> (p LEADSTO q)Pr
%
let LEADSTO_cor1 = prove_thm
  (`LEADSTO_cor1`,
   "!(p:*->bool) b q Pr.
       ((p /\* b) LEADSTO q) Pr /\ ((p /\* (~* b)) LEADSTO q) Pr
           ==> (p LEADSTO q) Pr",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC (SPECL ["(p:*->bool) /\* b";"(p:*->bool) /\* (~* b)";
                       "q:*->bool";"Pr:(*->*)list"] LEADSTO_thm4) THEN
   ACCEPT_TAC (REWRITE_RULE [SYM (SPEC_ALL AND_OR_DISTR_lemma);
                               P_OR_NOT_P_lemma;AND_TRUE_lemma]
    (ASSUME "((((p:*->bool) /\* b) \/* (p /\* (~* b))) LEADSTO q)Pr")));;


% Prove:

  |- !p q r st Pr.
       (p LEADSTO q)(CONS st Pr) /\ r STABLE (CONS st Pr) ==>
           ((p /\* r) LEADSTO (q /\* r))(CONS st Pr)
%
let LEADSTO_cor2 = prove_thm
  (`LEADSTO_cor2`,
   "!(p:*->bool) q r st Pr.
       (p LEADSTO q)(CONS st Pr) /\ r STABLE (CONS st Pr)
            ==> ((p /\* r) LEADSTO (q /\* r))(CONS st Pr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm29 THEN
   ACCEPT_TAC (REWRITE_RULE [OR_FALSE_lemma] (ASSUME
     "(((p:*->bool) /\* r) LEADSTO ((q /\* r) \/* FALSE))(CONS st Pr)")));;


% Prove:

   |- !p q st Pr.
           (p LEADSTO q)(CONS st Pr) = ((p /\* (~* q)) LEADSTO q)(CONS st Pr)
%
let LEADSTO_cor3 = prove_thm
  (`LEADSTO_cor3`,
   "!(p:*->bool) q st Pr.
        (p LEADSTO q)(CONS st  Pr) = ((p /\* (~* q)) LEADSTO q)(CONS st  Pr)",
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ASSUME_TAC (REWRITE_RULE [NOT_NOT_lemma]
      (SPECL ["~* (q:*->bool)";"CONS (st:*->*) Pr"] UNLESS_thm2)) THEN
     IMP_RES_TAC LEADSTO_thm29 THEN
     ASSUME_TAC (REWRITE_RULE [P_AND_NOT_P_lemma]
      (ASSUME "(((p:*->bool) /\* (~* q)) LEADSTO
                 ((q /\* (~* q)) \/* q))(CONS st Pr)")) THEN
     ACCEPT_TAC (REWRITE_RULE [OR_FALSE_lemma]
      (ONCE_REWRITE_RULE [OR_COMM_lemma] (ASSUME
        "(((p:*->bool) /\* (~* q)) LEADSTO (FALSE \/* q))(CONS st Pr)")))
    ;
     ASSUME_TAC (MP
      (SPECL ["(p:*->bool) /\* q";"q:*->bool";"st:*->*";"Pr:(*->*)list"]
              LEADSTO_thm25)
      (SPECL ["p:*->bool";"q:*->bool"] AND_IMPLY_WEAK_lemma)) THEN
     IMP_RES_TAC LEADSTO_cor1
    ]);;


% Prove:

   |- !p b q st Pr.
       ((p /\* b) LEADSTO q)(CONS st Pr) /\
       ((p /\* (~* b)) LEADSTO ((p /\* b) \/* q))(CONS st Pr) ==>
           (p LEADSTO q)(CONS st Pr)
%
let LEADSTO_cor4 = prove_thm
  (`LEADSTO_cor4`,
   "!(p:*->bool) b q st Pr.
     ((p /\* b) LEADSTO q)(CONS st Pr) /\
     ((p /\* (~* b)) LEADSTO ((p /\* b) \/* q))(CONS st Pr)
          ==> (p LEADSTO q)(CONS st Pr)",
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm28 THEN
   ASSUME_TAC (REWRITE_RULE [OR_OR_lemma] (ASSUME
    "(((p:*->bool) /\* (~* b)) LEADSTO (q \/* q))(CONS st Pr)")) THEN
   IMP_RES_TAC LEADSTO_cor1);;


% Prove:

  |- !p q r st Pr.
   ((p /\* q) LEADSTO r)(CONS st Pr) ==> (p LEADSTO ((~* q) \/* r))(CONS st Pr)
%
let LEADSTO_cor5 = prove_thm
  (`LEADSTO_cor5`,
   "!(p:*->bool) q r st Pr.
          ((p /\* q) LEADSTO r)(CONS st Pr)
               ==> (p LEADSTO ((~* q) \/* r))(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [LEADSTO_cor3] THEN
   REWRITE_TAC [NOT_OR_AND_NOT_lemma;NOT_NOT_lemma] THEN
   ASSUME_TAC (REWRITE_RULE [NOT_NOT_lemma]
    (SPECL ["~*(r:*->bool)";"CONS (st:*->*) Pr"] UNLESS_thm2)) THEN
   IMP_RES_TAC LEADSTO_thm29 THEN
   ASSUME_TAC (REWRITE_RULE [AND_ASSOC_lemma;P_AND_NOT_P_lemma] (ASSUME
    "((((p:*->bool) /\* q) /\* (~* r)) LEADSTO ((r /\* (~* r)) \/* r))
                                               (CONS st Pr)")) THEN
   ASSUME_TAC (REWRITE_RULE [OR_FALSE_lemma] (ONCE_REWRITE_RULE
    [OR_COMM_lemma] (ASSUME "(((p:*->bool) /\* (q /\* (~* r))) LEADSTO
                             (FALSE \/* r))(CONS st Pr)"))) THEN
   ASSUME_TAC (MP
    (SPEC_ALL (SPECL ["r:*->bool";"(~* (q:*->bool)) \/* r"] LEADSTO_thm25))
    (SPECL ["r:*->bool";"~* (q:*->bool)"] SYM_OR_IMPLY_WEAK_lemma)) THEN
   IMP_RES_TAC LEADSTO_thm1);;


% Prove:

   |- !p q r st Pr.
       (p LEADSTO q)(CONS st Pr) /\ (r UNLESS (q /\* r))(CONS st Pr) ==>
           ((p /\* r) LEADSTO (q /\* r))(CONS st Pr)
%
let LEADSTO_cor6 = prove_thm
  (`LEADSTO_cor6`,
   "!(p:*->bool) q r st Pr.
       (p LEADSTO q)(CONS st Pr) /\ (r UNLESS (q /\* r))(CONS st Pr)
            ==> ((p /\* r) LEADSTO (q /\* r))(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm29 THEN
   ACCEPT_TAC (REWRITE_RULE [OR_OR_lemma] (ASSUME
    "(((p:*->bool) /\* r) LEADSTO ((q /\* r) \/* (q /\* r)))(CONS st Pr)")));;


% Prove:

   |- !p q r st Pr.
       (p LEADSTO q)(CONS st Pr) /\ (r /\* (~* q)) STABLE (CONS st Pr) ==>
           (!s. (p /\* r)s ==> q s)
%
let LEADSTO_cor7 = prove_thm
  (`LEADSTO_cor7`,
   "!(p:*->bool) q r st Pr.
     (p LEADSTO q)(CONS st Pr) /\ (r /\* (~* q)) STABLE (CONS st Pr)
          ==> (!s. (p /\* r)s ==> q s)",
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_cor2 THEN
   ASSUME_TAC (REWRITE_RULE
     [(SYM (SPEC_ALL AND_ASSOC_lemma));P_AND_NOT_P_lemma]
      (ONCE_REWRITE_RULE [AND_AND_COMM_lemma] (ASSUME
        "(((p:*->bool) /\* (r /\* (~* q))) LEADSTO
           (q /\* (r /\* (~* q))))(CONS st Pr)"))) THEN
   ASSUME_TAC (REWRITE_RULE [AND_FALSE_lemma] 
    (ONCE_REWRITE_RULE [AND_COMM_lemma] (ASSUME
      "((((p:*->bool) /\* (~* q)) /\* r) LEADSTO (FALSE /\* r))
                                            (CONS st Pr)"))) THEN
   IMP_RES_TAC LEADSTO_thm30 THEN
   GEN_TAC THEN
   MP_TAC (SPEC_ALL (ASSUME "!s:*. ~*(r /\* (p /\* (~* q)))s")) THEN
   REWRITE_TAC [~*;/\*] THEN
   BETA_TAC THEN
   REWRITE_TAC [DE_MORGAN_THM] THEN
   REPEAT STRIP_TAC THENL
    [
     RES_TAC
    ;
     RES_TAC
    ;
     ASM_REWRITE_TAC []
    ]);;


%
  Prove:

   |- !p r q st Pr.
            (p LEADSTO r)(CONS st Pr) ==> ((p /\* q) LEADSTO r)(CONS st Pr)
%
let LEADSTO_cor8 = prove_thm
  (`LEADSTO_cor8`,
   "!(p:*->bool) r q st Pr. (p LEADSTO r)(CONS st Pr)
                   ==> ((p /\* q) LEADSTO r)(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL ["p:*->bool";"q:*->bool"] SYM_AND_IMPLY_WEAK_lemma) THEN
   IMP_RES_TAC LEADSTO_thm25 THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
    "!st Pr. (((p:*->bool) /\* q) LEADSTO p)(CONS st Pr)")) THEN
   IMP_RES_TAC LEADSTO_thm1);;


%
  Prove:

   |- !p q r st Pr.
       (p LEADSTO q)(CONS st Pr) /\ (!s. q s ==> r s) ==>
           (p LEADSTO r)(CONS st Pr)
%
let LEADSTO_cor9 = prove_thm
  (`LEADSTO_cor9`,
   "!(p:*->bool) q r st Pr.
        (p LEADSTO q)(CONS st Pr) /\ (!s. q s ==> r s)
              ==> (p LEADSTO r)(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm25 THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
    "!st Pr. ((q:*->bool) LEADSTO r)(CONS st Pr)")) THEN
   IMP_RES_TAC LEADSTO_thm1);;


% Prove:

   |- !P q Pr. (!i. ((P i) LEADSTO q)Pr) ==> (!i. ((\<=/* P i) LEADSTO q)Pr)
%
let LEADSTO_cor10 = prove_thm
  (`LEADSTO_cor10`,
   "!(P:num->*->bool) q Pr.
      (!i. ((P i) LEADSTO q)Pr) ==> (!i. ((\<=/* P i) LEADSTO q)Pr)",
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   INDUCT_TAC THENL
     [
      ASM_REWRITE_TAC [\<=/*]
     ;
      REWRITE_TAC [\<=/*] THEN
      ACCEPT_TAC (MP
       (SPECL ["\<=/* (P:num->*->bool) i";"(P:num->*->bool) (SUC i)";
               "q:*->bool";"Pr:(*->*)list"] LEADSTO_thm4) (CONJ
         (ASSUME "((\<=/* (P:num->*->bool) i) LEADSTO q)Pr")
         (SPEC "SUC i" (ASSUME "!i. (((P:num->*->bool) i) LEADSTO q)Pr"))))
     ]);;


% Prove:

   !p st Pr. (FALSE LEADSTO p) (CONS st Pr)

%
let LEADSTO_cor11 = prove_thm
  (`LEADSTO_cor11`,
   "!(p:*->bool) st Pr. (FALSE LEADSTO p) (CONS st Pr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LEADSTO;LeadstoRel] THEN
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE [ENSURES_cor6] (CONJUNCT1
    (SPECL ["FALSE:*->bool";"p:*->bool"]
      (ASSUME "!(p:*->bool) q.
        ((p ENSURES q)(CONS st Pr) ==> R p q(CONS st Pr)) /\
        (!r. R p r(CONS st Pr) /\ R r q(CONS st Pr) ==> R p q(CONS st Pr)) /\
        (!P. (p = LUB P) /\ (!p'. p' In P ==> R p' q(CONS st Pr)) ==>
                           R p q(CONS st Pr))")))));;


% Prove:

   |- !P q st Pr. (!i. ((P i) LEADSTO q)(CONS st Pr)) ==>
                  (!i. ((\</* P i) LEADSTO q)(CONS st Pr))
%
let LEADSTO_cor12 = prove_thm
  (`LEADSTO_cor12`,
   "!(P:num->*->bool) q st Pr.
      (!i. ((P i) LEADSTO q)(CONS st Pr))
             ==> (!i. ((\</* P i) LEADSTO q)(CONS st Pr))",
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   INDUCT_TAC THENL
    [
     REWRITE_TAC [\</*;LEADSTO_cor11]
    ;
     REWRITE_TAC [\</*] THEN
     ACCEPT_TAC (MP
      (SPECL ["\</* (P:num->*->bool) i";"(P:num->*->bool) i";
              "q:*->bool";"CONS (st:*->*) Pr"] LEADSTO_thm4) (CONJ
         (ASSUME "((\</* (P:num->*->bool) i) LEADSTO q)(CONS st Pr)")
         (SPEC "i:num"
           (ASSUME "!i. (((P:num->*->bool) i) LEADSTO q)(CONS st Pr)"))))
    ]);;


%
  We now want to introduce some tactics for allowing structural induction
  of leadsto relations, but we have problems with the induction principle
  for the completion theorem:

   !P Q R P' Q' Pr.
     (P LEADSTO Q)Pr /\ (P' LEADSTO Q')Pr /\ (Q UNLESS R)Pr /\ (Q' UNLESS R)Pr
       ==> ((P /\* P') LEADSTO ((Q /\* Q') \/* R))Pr

  since this theorems demands another induction principle not directly
  derivable from the given definition of leadsto.

  We circumvent the problem by proving that leadsto may be defined by another
  functional.

  This time we use the results of Tarski directly.
%

% ************************************************************************** %

%
  Suppose we wanted to change the transitive inductitive axiom into

                   p ensures r, r leadsto q
                 --------------------------- (2)
                        p leadsto q

  instead of the previous given.

  Let us investigate the following definition a litte:

  Now the functional becomes

%

%
  |- !R Pr.
    LEADSTO2Fn R Pr =
    (\p q.
      (p ENSURES q) Pr \/
      (?r. (p ENSURES r) Pr /\ R r q Pr) \/
      (?P. (p = LUB P) /\ (!p'. p' In P ==> R p' q Pr)))
%
let LEADSTO2Fn = new_definition
  (`LEADSTO2Fn`,
   "LEADSTO2Fn R = \(p:*->bool) q Pr.
     (p ENSURES q) Pr \/
     (?r. (p ENSURES r) Pr /\ R r q Pr) \/
     (?P. (p = LUB P) /\ (!p. p In P ==> R p q Pr))");;

%
  |- !p q Pr.
      LEADSTO2 p q Pr =
        (!R Pr. (!p' q'. LEADSTO2Fn R p' q' Pr ==> R p' q' Pr) ==> R p q Pr)
%
let LEADSTO2 = new_definition
  (`LEADSTO2`,
   "LEADSTO2 (p:*->bool) q Pr =
      !R. (!p q. LEADSTO2Fn R p q Pr ==> R p q Pr) ==> R p q Pr");;
%
  |- !R p q Pr.
    (!p q. LEADSTO2Fn R p q Pr ==> R p q Pr) ==>
    (!p q.
      (\p q Pr. !R.
           (!p q. LEADSTO2Fn R p q Pr ==> R p q Pr) ==> R p q Pr) p q Pr
    ==>
      R p q Pr)
%
let LEADSTO2Imply_1 = TAC_PROOF
  (([],
   "!R (p:*->bool) q Pr.
       (!p q. LEADSTO2Fn R p q Pr ==> R p q Pr) ==>
          (!p q. (\p q Pr. !R. (!p q. LEADSTO2Fn R p q Pr ==> R p q Pr)
                           ==> R p q Pr) p q Pr
                   ==> R p q Pr)"),
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
  |- !R1 R2 Pr.
    (!p q. R1 p q Pr ==> R2 p q Pr) ==>
    (!p q. LEADSTO2Fn R1 p q Pr ==> LEADSTO2Fn R2 p q Pr)
%
let IsMonoLEADSTO2 = TAC_PROOF
  (([],
   "!R1 R2 (Pr:(*->*)list).
      (!p q. R1 p q Pr ==> R2 p q Pr)
            ==> (!p q. LEADSTO2Fn R1 p q Pr ==> LEADSTO2Fn R2 p q Pr)"),
   REWRITE_TAC [LEADSTO2Fn] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ASM_REWRITE_TAC []
    ;
     RES_TAC THEN
     DISJ2_TAC THEN
     DISJ1_TAC THEN
     EXISTS_TAC "r:*->bool" THEN
     ASM_REWRITE_TAC []
    ;
     DISJ2_TAC THEN
     DISJ2_TAC THEN
     EXISTS_TAC "P:(*->bool)->bool" THEN
     ASM_REWRITE_TAC [] THEN
     REPEAT STRIP_TAC THEN
     RES_TAC THEN
     RES_TAC
    ]);;

%
LEADSTO2th = 
  |- LEADSTO2 =
   (\p q Pr.
     !R. (!p' q'. LEADSTO2Fn R p' q' Pr ==> R p' q' Pr) ==> R p q Pr)
%
let LEADSTO2th = (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "p:*->bool"  (MK_ABS
  (GEN "q:*->bool" (MK_ABS (GEN "Pr:(*->*)list" (SPEC_ALL LEADSTO2))))))));;

%
  |- !p q Pr. LEADSTO2Fn LEADSTO2 p q Pr ==> LEADSTO2 p q Pr
%
let LEADSTO2Imply1 = TAC_PROOF
  (([],
   "!(p:*->bool) q Pr.
       LEADSTO2Fn LEADSTO2 p q Pr ==> LEADSTO2 p q Pr"),
   REPEAT GEN_TAC THEN
   ASSUME_TAC (GENL
    ["R1:(*->bool)->(*->bool)->((*->*)list)->bool";
     "R2:(*->bool)->(*->bool)->((*->*)list)->bool"]
     (SPEC_ALL IsMonoLEADSTO2)) THEN
   REWRITE_TAC [LEADSTO2th] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (MP (SPEC_ALL (MP (BETA_RULE (SPEC_ALL (SPECL
      ["\(p:*->bool) q Pr. !R. (!p' q'. LEADSTO2Fn R p' q' Pr ==> R p' q' Pr)
            ==> R p q Pr";
       "R:(*->bool)->(*->bool)->((*->*)list)->bool"] IsMonoLEADSTO2)))
     (BETA_RULE (MP (SPEC_ALL LEADSTO2Imply_1)
          (ASSUME "!(p':*->bool) q'. LEADSTO2Fn R p' q' Pr ==> R p' q' Pr")))))
      (ASSUME "LEADSTO2Fn (\(p:*->bool) q Pr.
        !R. (!p' q'. LEADSTO2Fn R p' q' Pr ==> R p' q' Pr)
                ==> R p q Pr) p q Pr")) THEN
   RES_TAC);;

%
  |- !p q Pr. LEADSTO2 p q Pr ==> LEADSTO2Fn LEADSTO2 p q Pr
%
let LEADSTO2Imply2 = TAC_PROOF
  (([],
   "!(p:*->bool) q Pr. LEADSTO2 p q Pr ==> LEADSTO2Fn LEADSTO2 p q Pr"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [ETA_AX] (MP (BETA_RULE (SPECL
    ["\p q Pr. LEADSTO2Fn LEADSTO2 (p:*->bool) q Pr";
     "LEADSTO2:(*->bool)->(*->bool)->((*->*)list)->bool";
     "Pr:(*->*)list"] IsMonoLEADSTO2))
       (GENL ["p:*->bool";"q:*->bool"] (SPEC_ALL LEADSTO2Imply1)))) THEN
   ACCEPT_TAC (UNDISCH (GEN_ALL (SPEC
    "LEADSTO2Fn (LEADSTO2:(*->bool)->(*->bool)->((*->*)list)->bool)" (BETA_RULE
      (REWRITE_RULE [LEADSTO2] (ASSUME "LEADSTO2 (p:*->bool) q Pr")))))));;

%
  |- !p q Pr. LEADSTO2 p q Pr = LEADSTO2Fn LEADSTO2 p q Pr
%
let LEADSTO2EQs = TAC_PROOF
  (([],
   "!(p:*->bool) q Pr. LEADSTO2 p q Pr = LEADSTO2Fn LEADSTO2 p q Pr"),
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
    [
     ACCEPT_TAC (SPEC_ALL LEADSTO2Imply2)
    ;
     ACCEPT_TAC (SPEC_ALL LEADSTO2Imply1)
    ]);;

%
  |- LEADSTO2 = LEADSTO2Fn LEADSTO2
%
let LEADSTO2EQ = 
  (REWRITE_RULE [ETA_AX]
    (MK_ABS (GEN "p:*->bool"
      (MK_ABS (GEN "q:*->bool" (MK_ABS (GEN "Pr:(*->*)list"
         (SPEC_ALL LEADSTO2EQs))))))));;
%
  |- !R. (R = LEADSTO2Fn R) ==> (!p q Pr. LEADSTO2Fn R p q Pr ==> R p q Pr)
%
let LEADSTO2Thm1_1 = TAC_PROOF
  (([],
   "!R. (R = LEADSTO2Fn R)
           ==> (!(p:*->bool) q Pr. LEADSTO2Fn R p q Pr ==> R p q Pr)"),
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC
    [ASSUME
      "R = LEADSTO2Fn (R:(*->bool)->(*->bool)->((*->*)list)->bool)"] THEN
   REWRITE_TAC [ASSUME "LEADSTO2Fn R (p:*->bool) q Pr"]);;

%
  |- !R. (R = LEADSTO2Fn R) ==> (!p q Pr. LEADSTO2 p q Pr ==> R p q Pr)
%
let LEADSTO2MinFixThm = TAC_PROOF
  (([],
   "!R. (R = LEADSTO2Fn R)
           ==> (!(p:*->bool) q Pr. LEADSTO2 p q Pr ==> R p q Pr)"),
   REWRITE_TAC [LEADSTO2] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
     "!R. (!(p':*->bool) q'. LEADSTO2Fn R p' q' Pr ==> R p' q' Pr)
              ==> R p q Pr")) THEN
   ASSUME_TAC (GENL ["p:*->bool";"q:*->bool"] (SPEC_ALL
     (UNDISCH (SPEC_ALL LEADSTO2Thm1_1)))) THEN
   RES_TAC);;

%
  |- !R.
    (!p q Pr. LEADSTO2Fn R p q Pr ==> R p q Pr) ==>
    (!p q Pr. LEADSTO2 p q Pr ==> R p q Pr)
%
let LEADSTO2InductThm = TAC_PROOF
  (([],
   "!R. (!(p:*->bool) q Pr. LEADSTO2Fn R p q Pr ==> R p q Pr)
             ==> (!p q Pr. LEADSTO2 p q Pr ==> R p q Pr)"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LEADSTO2] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (GENL ["p:*->bool";"q:*->bool"] (SPEC_ALL (ASSUME
    "!(p:*->bool) q Pr. LEADSTO2Fn R p q Pr ==> R p q Pr"))) THEN
   RES_TAC);;

%
  |- !R Pr.
    LEADSTO2Fam R Pr =
    (!p q.
      ((p ENSURES q)Pr ==> R p q Pr) /\
      (!r. (p ENSURES r)Pr /\ R r q Pr ==> R p q Pr) /\
      (!P. (!p. p In P ==> R p q Pr)    ==> R (LUB P) q Pr)
%
let LEADSTO2Fam = new_definition
  (`LEADSTO2Fam`,
   "LEADSTO2Fam R Pr =
     !(p:*->bool) (q:*->bool).
         ((p ENSURES q) Pr                 ==> R p q Pr) /\
         (!r. (p ENSURES r) Pr /\ R r q Pr ==> R p q Pr) /\
         (!P. (!p. p In P ==> R p q Pr)    ==> R (LUB P) q Pr)");;

%
  |- !R Pr. (!p q. LEADSTO2Fn R p q Pr ==> R p q Pr) = LEADSTO2Fam R Pr
%
let LEADSTO2Fn_EQ_LEADSTO2Fam = TAC_PROOF
  (([],
   "!R Pr.
      (!(p:*->bool) q. LEADSTO2Fn R p q Pr ==> R p q Pr) = LEADSTO2Fam R Pr"),
   REWRITE_TAC [LEADSTO2Fam;LEADSTO2Fn] THEN
   BETA_TAC THEN
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THENL
    [
     REWRITE_TAC [REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
        "!p. (p = LUB (P:(*->bool)->bool)) ==>
             (R:(*->bool)->(*->bool)->((*->*)list)->bool) p q Pr"))]
    ;
     ASM_REWRITE_TAC []
    ]);;


%
 ******************************************************************************
	Prove that the wanted axioms 1, 2, 3 are really theorems for the found
	fixed point
 ******************************************************************************
%

%
  |- !p q Pr. (p ENSURES q)Pr ==> LEADSTO2 p q Pr
%
let LEADSTO2_thm0 = prove_thm
  (`LEADSTO2_thm0`,
   "!(p:*->bool) q Pr. (p ENSURES q) Pr ==> LEADSTO2 p q Pr",
   REWRITE_TAC [LEADSTO2;LEADSTO2Fn] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;
   
%
  |- !p r q Pr. (p ENSURES r)Pr /\ LEADSTO2 r q Pr ==> LEADSTO2 p q Pr
%
let LEADSTO2_thm1 = prove_thm
  (`LEADSTO2_thm1`,
   "!(p:*->bool) r q Pr.
        (p ENSURES r) Pr /\ (LEADSTO2 r q Pr) ==> (LEADSTO2 p q Pr)",
   REWRITE_TAC [LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;


% Prove:

   |- !P q Pr. (!p. p In P ==> LEADSTO2 p q Pr) ==> LEADSTO2(LUB P)q Pr
%
let LEADSTO2_thm3_lemma1 = TAC_PROOF
  (([],
   "(!p:*->bool. p In P ==>
     (!R.
       (!p q.
         ((p ENSURES q)Pr ==> R p q Pr) /\
         (!r. (p ENSURES r)Pr /\ R r q Pr ==> R p q Pr) /\
         (!P. (!p'. p' In P ==> R p' q Pr) ==> R (LUB P) q Pr)) ==>
       R p q Pr)) ==>
   (!p. p In P ==>
     (!p q.
       ((p ENSURES q)Pr ==> R p q Pr) /\
       (!r. (p ENSURES r)Pr /\ R r q Pr ==> R p q Pr) /\
       (!P. (!p'. p' In P ==> R p' q Pr) ==> R (LUB P) q Pr)) ==>
     R p q Pr)"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO2_thm3 = prove_thm
  (`LEADSTO2_thm3`,
   "!(P:(*->bool)->bool) q Pr.
       (!p. p In P ==> LEADSTO2 p q Pr) ==> LEADSTO2 (LUB P) q Pr",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (GEN_ALL (REWRITE_RULE[ASSUME
     "!(p:*->bool) q.
        ((p ENSURES q)Pr ==> R p q Pr) /\
        (!r. (p ENSURES r)Pr /\ R r q Pr ==> R p q Pr) /\
        (!P. (!p'. p' In P ==> R p' q Pr) ==> R (LUB P) q Pr)"]
           (SPEC_ALL (UNDISCH (SPEC_ALL LEADSTO2_thm3_lemma1))))) THEN
   RES_TAC);;

let LEADSTO2_thm3a = prove_thm
  (`LEADSTO2_thm3a`,
   "!(P:(*->bool)->bool) q Pr.
       (p = LUB P) /\ (!p. p In P ==> LEADSTO2 p q Pr)
             ==> LEADSTO2 p q Pr",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO2_thm3 THEN
   ASM_REWRITE_TAC []);;

%
   !p1 p2 q Pr. (LEADSTO2 p1 q Pr) /\ (LEADSTO2 p2 q Pr)
                     ==> (LEADSTO2 (p1 \/* p2) q Pr)
%

%
  To prove this we need some general lemmas about expressing two known
  relations as one relation:
%

%
  |- !p1 p2 s. (p1 \/* p2)s = LUB(\p. (p = p1) \/ (p = p2))s
%
let LEADSTO2_thm4_lemma1a = TAC_PROOF
  (([],
   "!(p1:*->bool) p2 s. (p1 \/* p2) s = (LUB (\p. (p = p1) \/ (p = p2))) s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LUB;\/*] THEN
   BETA_TAC THEN
   EQ_TAC THENL
     [
      STRIP_TAC THENL
       [
        EXISTS_TAC "p1:*->bool" THEN
        ASM_REWRITE_TAC []
       ;
        EXISTS_TAC "p2:*->bool" THEN
        ASM_REWRITE_TAC []
       ]
     ;
      STRIP_TAC THENL
       [
        REWRITE_TAC [REWRITE_RULE [ASSUME "(p:*->bool) = p1"] (ASSUME
         "(p:*->bool) s")]
       ;
        REWRITE_TAC [REWRITE_RULE [ASSUME "(p:*->bool) = p2"] (ASSUME
         "(p:*->bool) s")]
       ]
     ]);;

%
  |- !p1 p2. p1 \/* p2 = LUB(\p. (p = p1) \/ (p = p2))
%
let LEADSTO2_thm4_lemma1 =  (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:*"
  (SPEC_ALL LEADSTO2_thm4_lemma1a)))));;

%
  |- !R Pr.
    (!p' q'.
      (p' ENSURES q')Pr \/
      (?r. (p' ENSURES r)Pr /\ R r q' Pr) \/
      (?P. (p' = LUB P) /\ (!p. p In P ==> R p q' Pr)) ==>
      R p' q' Pr) ==>
    (!p q P. (p = LUB P) /\ (!p. p In P ==> R p q Pr) ==> R p q Pr)

%
let LEADSTO2_thm4_lemma2 = TAC_PROOF
  (([],
   "!(R:(*->bool)->(*->bool)->((*->*)list)->bool) Pr.
     (!p' q'.
        (p' ENSURES q') Pr \/ (?r. (p' ENSURES r) Pr /\ R r q' Pr) \/
        (?P. (p' = LUB P) /\ (!p. p In P ==> R p q' Pr)) ==> R p' q' Pr)
      ==> (!p q P. ((p = LUB P) /\ (!p. p In P ==> R p q Pr)) ==> R p q Pr)"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
  |- !R p1 p2 q Pr Pr. R p1 q Pr ==> R p2 q Pr ==>
                          (!p. (\p. (p = p1) \/ (p = p2))p ==> R p q Pr)
%
let LEADSTO2_thm4_lemma3 = TAC_PROOF
  (([],
   "!R (p1:*->bool) p2 (q:*->bool) (Pr:(*->*)list) (Pr:(*->*)list).
      R p1 q Pr ==> R p2 q Pr ==> 
       (!p. (\p. (p = p1) \/ (p = p2))p ==> R p q Pr)"),
   BETA_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     ASM_REWRITE_TAC []
    ;
     ASM_REWRITE_TAC []
    ]);;

%
  |- !R p1 p2 q Pr. R p1 q Pr ==> R p2 q Pr ==>
       (!p q P. (p = LUB P) /\ (!p. p In P ==> R p q Pr) ==> R p q Pr) ==>
                 R(p1 \/* p2)q Pr

%
let LEADSTO2_thm4_lemma4 = TAC_PROOF
  (([],
   "!R (p1:*->bool) (p2:*->bool) (q:*->bool)  (Pr:(*->*)list).
      R p1 q Pr ==> R p2 q Pr ==> 
       (!p q P. (p = LUB P) /\ (!p. p In P ==> R p q Pr) ==> R p q Pr) ==>
          R (p1 \/* p2) q Pr"),
   REWRITE_TAC [In] THEN
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [SYM (SPEC_ALL LEADSTO2_thm4_lemma1);
     UNDISCH_ALL (SPEC_ALL LEADSTO2_thm4_lemma3)]
      (SPECL
        ["(p1:*->bool) \/* p2";"q:*->bool";"\p:*->bool. (p = p1) \/ (p = p2)"]
           (ASSUME "!p (q:*->bool) (P:(*->bool)->bool). (p = LUB P) /\
                     (!p. P p ==> R p q Pr) ==> R p q (Pr:(*->*)list)"))));;
%
  Now Prove that the finite disjunction is satisfied
%

%
  |- !p1 p2 q Pr.
       LEADSTO2 p1 q Pr /\ LEADSTO2 p2 q Pr ==> LEADSTO2(p1 \/* p2)q Pr
%
let LEADSTO2_thm4 = prove_thm
  (`LEADSTO2_thm4`,
   "!(p1:*->bool) p2 q Pr.
       (LEADSTO2 p1 q Pr) /\ (LEADSTO2 p2 q Pr) ==> LEADSTO2 (p1 \/* p2) q Pr",
   REWRITE_TAC [LEADSTO2;LEADSTO2Fn] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL LEADSTO2_thm4_lemma2)) THEN
   ACCEPT_TAC (UNDISCH_ALL (SPEC_ALL LEADSTO2_thm4_lemma4)));;


% Prove:

   This is more difficult and we need to use structural induction

%

%
  Prove the induction theorem:

  |- !X p q Pr.

      (!p q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p ENSURES r)Pr /\ X r q Pr ==> X p q Pr) /\
        (!P. (!p. p In P ==> X p q Pr) ==> X(LUB P)q Pr))

     ==>

      LEADSTO2 p q Pr ==> X p q Pr
%
let LEADSTO2_thm8 = prove_thm
  (`LEADSTO2_thm8`,
   "!X (p:*->bool) q Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p ENSURES r)Pr /\ X r q Pr ==> (X p q Pr)) /\
        (!P. (!p. p In P ==> X p q Pr) ==> (X (LUB P) q Pr)))
     ==> ((LEADSTO2 p q Pr) ==> X p q Pr)",
   REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL CONJ_ASSOC)] (BETA_RULE
    (SPEC "\(p:*->bool) (q:*->bool) (Pr:(*->*)list). X p q Pr:bool"
     (REWRITE_RULE [LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam]
        (ASSUME "LEADSTO2 (p:*->bool) q Pr"))))) THEN
   RES_TAC);;

%
  We now use LEADSTO2_thm8 to prove a slightly modified writing of the wanted
  theorem:

     !p q Pr. (LEADSTO2 p q Pr) ==> (!r. LEADSTO2 q r Pr ==> LEADSTO2 p r Pr)

%

%
  We get by specialization:

  |- (!p' q'.

       ((p' ENSURES q')Pr ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p' r Pr)) /\

       (!r.
         (p' ENSURES r)Pr /\ (!r'. LEADSTO2 q' r' Pr ==> LEADSTO2 r r' Pr)
            ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p' r Pr)) /\

       (!P.
         (!p''. p'' In P ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p'' r Pr))
            ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2(LUB P)r Pr)))

    ==>

      LEADSTO2 p q Pr ==> (!r. LEADSTO2 q r Pr ==> LEADSTO2 p r Pr)

%
let LEADSTO2_thm2a = (BETA_RULE (SPECL
  ["\p q Pr. !r:*->bool. LEADSTO2 q r Pr ==> LEADSTO2 p r Pr";
   "p:*->bool";"q:*->bool";"Pr:(*->*)list"] LEADSTO2_thm8));;

%
  We prove the implications of Rel_thm2a:
%

%
  |- !p' q'. (p' ENSURES q')Pr ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p' r Pr)
%
let LEADSTO2_thm2b = TAC_PROOF
  (([],
   "!(p':*->bool) q'.
     ((p' ENSURES q')Pr ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p' r Pr))"),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO2_thm1);;

%
  |- !p' q' r.
    (p' ENSURES r)Pr /\ (!r'. LEADSTO2 q' r' Pr ==> LEADSTO2 r r' Pr) ==>
    (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p' r Pr)
%
let LEADSTO2_thm2c = TAC_PROOF
  (([],
   "!(p':*->bool) q'.
     (!r.
       (p' ENSURES r)Pr /\ (!r'. LEADSTO2 q' r' Pr ==> LEADSTO2 r r' Pr) ==>
       (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p' r Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   IMP_RES_TAC LEADSTO2_thm1);;

%
  |- !p' q' P.
      (!p''. p'' In P ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p'' r Pr)) ==>
         (!r. LEADSTO2 q' r Pr ==> LEADSTO2(LUB P)r Pr)
%
let LEADSTO2_thm2d_lemma1 = TAC_PROOF
  (([],
   "!(q':*->bool) r Pr.
     LEADSTO2 q' r Pr ==>
      (!p'':*->bool. p'' In P ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p'' r Pr))
          ==> (!p'':*->bool. p'' In P ==> LEADSTO2 p'' r Pr)"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO2_thm2d = TAC_PROOF
  (([],
   "!(p':*->bool) q'.
      (!P:(*->bool)->bool.
       (!p''. p'' In P ==> (!r. LEADSTO2 q' r Pr ==> LEADSTO2 p'' r Pr)) ==>
       (!r. LEADSTO2 q' r Pr ==> LEADSTO2(LUB P)r Pr))"),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO2_thm2d_lemma1 THEN
   IMP_RES_TAC LEADSTO2_thm3);;

%
  Hence by rewriting we get:

  |- LEADSTO2 p q Pr ==> (!r. LEADSTO2 q r Pr ==> LEADSTO2 p r Pr)

%
let LEADSTO2_thm2e =
 (REWRITE_RULE [LEADSTO2_thm2b;LEADSTO2_thm2c;LEADSTO2_thm2d] LEADSTO2_thm2a);;

% Now we may Prove:

  |- !p r q Pr. LEADSTO2 p r Pr /\ LEADSTO2 r q Pr ==> LEADSTO2 p q Pr

%
let LEADSTO2_thm2 = prove_thm
  (`LEADSTO2_thm2`,
   "!(p:*->bool) r q Pr.
       (LEADSTO2 p r Pr) /\ (LEADSTO2 r q Pr) ==> (LEADSTO2 p q Pr)",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO2_thm2e);;

%
  |- !p q Pr.
    (p ENSURES q)Pr \/
    (?r. LEADSTO2 p r Pr /\ LEADSTO2 r q Pr) \/
    (?P. (p = LUB P) /\ (!p. p In P ==> LEADSTO2 p q Pr))
   =
    LEADSTO2 p q Pr
%
let LEADSTO2_thm5 = prove_thm
  (`LEADSTO2_thm5`,
   "!(p:*->bool) q Pr.
       ((p ENSURES q)Pr \/
        (?r. (LEADSTO2 p r Pr) /\ (LEADSTO2 r q Pr)) \/
        (?P. (p = (LUB P)) /\ (!p. p In P ==> LEADSTO2 p q Pr)))
      =
       (LEADSTO2 p q Pr)",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (UNDISCH (SPEC_ALL LEADSTO2_thm0))
        ;
         IMP_RES_TAC LEADSTO2_thm2
        ;
         IMP_RES_TAC LEADSTO2_thm3 THEN
         ASM_REWRITE_TAC []
        ]
     ;
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        REPEAT STRIP_TAC THEN
        ACCEPT_TAC (ONCE_REWRITE_RULE [ASSUME "(p:*->bool) = p'"] (ASSUME
         "LEADSTO2 (p:*->bool) q Pr"))
       ]
     ]);;

%
  |- !p q Pr.
    (p ENSURES q)Pr \/
    (?r. (p ENSURES r)Pr /\ LEADSTO2 r q Pr) \/
    (?P. (p = ?* P) /\ (!i. LEADSTO2(P i)q Pr))
   =
    LEADSTO2 p q Pr
%
let LEADSTO2_thm6 = prove_thm
  (`LEADSTO2_thm6`,
   "!(p:*->bool) q Pr.
       ((p ENSURES q)Pr \/
        (?r. (p ENSURES r)Pr /\ (LEADSTO2 r q Pr)) \/
        (?P. (p = (LUB P)) /\ (!p. p In P ==> LEADSTO2 p q Pr)))
      =
       (LEADSTO2 p q Pr)",
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (UNDISCH (SPEC_ALL LEADSTO2_thm0))
        ;
         IMP_RES_TAC LEADSTO2_thm1
        ;
         IMP_RES_TAC LEADSTO2_thm3 THEN
         ASM_REWRITE_TAC []
        ]
     ;
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC "\(p':*->bool). (p = p') => T | F" THEN
      REWRITE_TAC [LUB;In] THEN
      BETA_TAC THEN
      CONJ_TAC THENL
       [
        ACCEPT_TAC (SPEC_ALL LEADSTO_thm5_lemma2)
       ;
        REWRITE_TAC [LEADSTO_thm5_lemma3] THEN
        REPEAT STRIP_TAC THEN
        ACCEPT_TAC (ONCE_REWRITE_RULE [ASSUME "(p:*->bool) = p'"] (ASSUME
         "LEADSTO2 (p:*->bool) q Pr"))
       ]
     ]);;

%
  Now we are able to prove another induction principle
%

%
  We need a lemma

%
let LEADSTO2_thm7_lemma01 = TAC_PROOF
  (([],
  "(!p':*->bool.
      p' In P ==> LEADSTO2 p' q Pr /\ (LEADSTO2 p' q Pr ==> X p' q Pr))
    =
     ((!p'. p' In P ==> LEADSTO2 p' q Pr) /\
      (!p'. p' In P ==> LEADSTO2 p' q Pr ==> X p' q Pr))"),
  EQ_TAC THEN
  REPEAT STRIP_TAC THEN
  RES_TAC);;

let LEADSTO2_thm7_lemma = TAC_PROOF
  (([],
   "!X Pr.
     (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r.
          (p ENSURES r)Pr /\
          LEADSTO2 r q Pr /\
          (LEADSTO2 r q Pr ==> X r q Pr) ==>
          LEADSTO2 p q Pr ==>
          X p q Pr) /\
        (!P.
          (!p. p In P ==> LEADSTO2 p q Pr) /\
          (!p. p In P ==> LEADSTO2 p q Pr ==> X p q Pr) ==>
          LEADSTO2(LUB P)q Pr ==>
          X(LUB P)q Pr))
    =
     (!(p:*->bool) q.
         ((p ENSURES q)Pr ==>
          LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q Pr)) /\
         (!r.
           (p ENSURES r)Pr /\
           LEADSTO2 r q Pr /\
           (LEADSTO2 r q Pr ==> X r q Pr) ==>
           LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q Pr)) /\
         (!P.
           (!p'.
             p' In P ==>
             LEADSTO2 p' q Pr /\ (LEADSTO2 p' q Pr ==> X p' q Pr)) ==>
           LEADSTO2(LUB P)q Pr /\ (LEADSTO2(LUB P)q Pr ==> X(LUB P)q Pr)))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     IMP_RES_TAC LEADSTO2_thm0
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO2_thm1
    ;
     RES_TAC
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [LEADSTO2_thm7_lemma01] (ASSUME
      "!p':*->bool. p' In P
         ==> LEADSTO2 p' q Pr /\ (LEADSTO2 p' q Pr ==> X p' q Pr)")) THEN
     IMP_RES_TAC LEADSTO2_thm3 
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [LEADSTO2_thm7_lemma01] (ASSUME
      "!p':*->bool. p' In P
         ==> LEADSTO2 p' q Pr /\ (LEADSTO2 p' q Pr ==> X p' q Pr)")) THEN
     RES_TAC
    ;
     RES_TAC
    ;
     RES_TAC
    ;
     ASSUME_TAC (REWRITE_RULE [SYM LEADSTO2_thm7_lemma01] (CONJ
      (ASSUME "!p:*->bool. p In P ==> LEADSTO2 p q Pr")
      (ASSUME "!p:*->bool. p In P ==> LEADSTO2 p q Pr ==> X p q Pr"))) THEN
     RES_TAC
    ]);;

%
  The induction theorem:

  |- !X p q Pr.

    (!p q.

      ((p ENSURES q)Pr ==> X p q Pr) /\

      (!r.
        (p ENSURES r)Pr /\ LEADSTO2 r q Pr /\ (LEADSTO2 r q Pr ==> X r q Pr)
            ==> LEADSTO2 p q Pr ==> X p q Pr) /\

      (!P.
        (!p. p In P ==> LEADSTO2 p q Pr) /\
        (!p. p In P ==> LEADSTO2 p q Pr ==> X p q Pr)
            ==> LEADSTO2(LUB P)q Pr ==> X(LUB P)q Pr))
   ==>

    LEADSTO2 p q Pr ==> X p q Pr

%
let LEADSTO2_thm7 = prove_thm
  (`LEADSTO2_thm7`,
   "!X (p:*->bool) q Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p ENSURES r)Pr /\ (LEADSTO2 r q Pr) /\
             ((LEADSTO2 r q Pr) ==> X r q Pr)
            ==> ((LEADSTO2 p q Pr) ==> X p q Pr)) /\
        (!P. (!p. p In P ==> LEADSTO2 p q Pr) /\
             (!p.  p In P ==> LEADSTO2 p q Pr ==> X p q Pr)
            ==> ((LEADSTO2 (LUB P) q Pr) ==> X (LUB P) q Pr)))
     ==> ((LEADSTO2 p q Pr) ==> X p q Pr)",
   REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL LEADSTO2_thm7_lemma)]
    (BETA_RULE (SPEC 
      "\(p:*->bool) q Pr. (LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q Pr))"
         (REWRITE_RULE [LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam]
           (ASSUME "LEADSTO2 (p:*->bool) q Pr"))))) THEN
   RES_TAC);;

%
  Finally we want to prove that LEADSTO is equal to LEADSTO2:
%

%
  We do the proving as two implication proofs:
%

%
  |- !R Pr.
    (!p q.
      ((p ENSURES q)Pr ==> R p q Pr) /\
      (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
      (!P. (!p. p In P ==> R p q Pr) ==> R(LUB P)q Pr))
   ==>
    (!p q.
      ((p ENSURES q)Pr ==> R p q Pr) /\
      (!r. (p ENSURES r)Pr /\ R r q Pr ==> R p q Pr) /\
      (!P. (!p. p In P ==> R p q Pr) ==> R(LUB P)q Pr))

%
let LEADSTO_EQ_LEADSTO2a = TAC_PROOF
  (([],
   "!R (Pr:(*->*)list).
       (!p q. ((p ENSURES q)Pr ==> R p q Pr) /\
              (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
              (!P. (!p. p In P ==> R p q Pr) ==> R (LUB P) q Pr))
            ==>
       (!p q. ((p ENSURES q)Pr ==> R p q Pr) /\
              (!r. (p ENSURES r)Pr /\ R r q Pr ==> R p q Pr) /\
              (!P. (!p. p In P ==> R p q Pr) ==> R (LUB P) q Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
  |- !p q Pr. LEADSTO2 p q Pr ==> (p LEADSTO q)Pr
%
let LEADSTO_EQ_LEADSTO2b_lemma = TAC_PROOF
  (([],
   "(!(p:*->bool) q.
        ((p ENSURES q)Pr ==> R p q Pr) /\
        (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
        (!P. (p = LUB P) /\ (!p'. p' In P ==> R p' q Pr) ==> R p q Pr))
   ==>
    (!p q.
        ((p ENSURES q)Pr ==> R p q Pr) /\
        (!r. R p r Pr /\ R r q Pr ==> R p q Pr) /\
        (!P. (!p'. p' In P ==> R p' q Pr) ==> R (LUB P) q Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ACCEPT_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
    "!p:*->bool. (p = LUB P) ==> R p (q:*->bool) (Pr:(*->*)list)"))));;

let LEADSTO_EQ_LEADSTO2b = TAC_PROOF
  (([],
   "!(p:*->bool) q Pr. LEADSTO2 p q Pr ==> (p LEADSTO q) Pr"),
   REWRITE_TAC [LEADSTO;LeadstoRel;
                LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL LEADSTO_EQ_LEADSTO2b_lemma)) THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL LEADSTO_EQ_LEADSTO2a)) THEN
   RES_TAC);;

%
 |- (!p' q'.
      ((p' ENSURES q')Pr ==> LEADSTO2 p' q' Pr) /\
      (!r. LEADSTO2 p' r Pr /\ LEADSTO2 r q' Pr ==> LEADSTO2 p' q' Pr) /\
      (!P. (p' = LUB P) /\ 
           (!p''. p'' In P ==> LEADSTO2 p'' q' Pr) ==> LEADSTO2 p' q' Pr))
     ==>
      (p LEADSTO q)Pr ==> LEADSTO2 p q Pr
%
let LEADSTO_EQ_LEADSTO2c = (SPECL
  ["LEADSTO2:(*->bool)->(*->bool)->((*->*)list)->bool";
   "p:*->bool";"q:*->bool";"Pr:(*->*)list"] LEADSTO_thm21);;

%
  |- !p q Pr. (p LEADSTO q)Pr ==> LEADSTO2 p q Pr
%
let LEADSTO_EQ_LEADSTO2d =
   (GEN_ALL (REWRITE_RULE [LEADSTO2_thm0;LEADSTO2_thm2;LEADSTO2_thm3a]
                           LEADSTO_EQ_LEADSTO2c));;

%
  The equivalence proof:

  |- !p q Pr. (p LEADSTO q)Pr = LEADSTO2 p q Pr

%
let LEADSTO_EQ_LEADSTO2 = prove_thm
  (`LEADSTO_EQ_LEADSTO2`,
   "!(p:*->bool) q Pr. (p LEADSTO q)Pr = LEADSTO2 p q Pr",
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
    [
     REWRITE_TAC [LEADSTO_EQ_LEADSTO2d]
    ;
     REWRITE_TAC [LEADSTO_EQ_LEADSTO2b]
    ]);;

%
  Hence now we may conclude all theorems proven valid for both relations
%

%
  We get the last two induction principles for LEADSTO:
%

%
  |- !X p q Pr.

    (!p q.

      ((p ENSURES q)Pr ==> X p q Pr) /\

      (!r. (p ENSURES r)Pr /\ X r q Pr ==> X p q Pr) /\

      (!P. (!p. p In P ==> X p q Pr) ==> X(LUB P)q Pr)) ==>

   ==>

    (p LEADSTO q)Pr ==> X p q Pr
%
let LEADSTO_thm31 = prove_thm
   (`LEADSTO_thm31`,
    "!X (p:*->bool) q Pr.
      (!p q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r. (p ENSURES r)Pr /\ X r q Pr ==> X p q Pr) /\
        (!P. (!p. p In P ==> X p q Pr) ==> X (LUB P) q Pr))
     ==>
      (p LEADSTO q)Pr ==> X p q Pr",
    ACCEPT_TAC (REWRITE_RULE
     [SYM (SPEC_ALL LEADSTO_EQ_LEADSTO2)] LEADSTO2_thm8));;

%
  The theorem may also be written:
%
let LEADSTO_thm32 = prove_thm
 (`LEADSTO_thm32`,
  "!X.
    (!p q Pr.   (p ENSURES q)Pr ==> X p q Pr) /\
    (!p r q Pr. (p ENSURES r)Pr /\ X r q Pr ==> X p q Pr) /\
    (!P q Pr. (!p. p In P ==> X p q Pr) ==> X(LUB P)q Pr)
   ==>
     !(p:*->bool) q Pr. (p LEADSTO q)Pr ==> X p q Pr",
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (REWRITE_RULE
   [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
    ASSUME "!(p:*->bool) (r:*->bool) (q:*->bool) Pr.
              (p ENSURES r)Pr /\ X r q Pr ==> X p q Pr";
    ASSUME "!(P:(*->bool)->bool) (q:*->bool) (Pr:(*->*)list).
              (!p. p In P ==> X p q Pr) ==> X(LUB P)q Pr"]
     (SPEC_ALL LEADSTO_thm31)) THEN
  RES_TAC);;


%
  |- !X p q Pr.

    (!p q.

      ((p ENSURES q)Pr ==> X p q Pr) /\

      (!r.
        (p ENSURES r)Pr /\
        (r LEADSTO q)Pr /\
        ((r LEADSTO q)Pr ==> X r q Pr)
           ==> (p LEADSTO q)Pr ==> X p q Pr) /\

      (!P.
        (!p. p In P ==> (p LEADSTO q)Pr) /\
        (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
           ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))

    ==>

    (p LEADSTO q)Pr ==> X p q Pr
%
let LEADSTO_thm33 = prove_thm
  (`LEADSTO_thm33`,
   "!X (p:*->bool) q Pr.
    (!p q.
      ((p ENSURES q)Pr ==> X p q Pr) /\
      (!r.
        (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\
        ((r LEADSTO q)Pr ==> X r q Pr) ==>
        (p LEADSTO q)Pr ==> X p q Pr) /\
      (!P.
        (!p. p In P ==> (p LEADSTO q)Pr) /\
        (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr) ==>
        ((LUB P) LEADSTO q)Pr ==> X (LUB P) q Pr))
      ==>
        (p LEADSTO q)Pr ==> X p q Pr",
   ACCEPT_TAC (REWRITE_RULE
     [SYM (SPEC_ALL LEADSTO_EQ_LEADSTO2)] LEADSTO2_thm7));;

%
  We may now derive the theorem:
%
let LEADSTO_thm34 = prove_thm
  (`LEADSTO_thm34`,
   "!X.
    (!p q Pr. (p ENSURES q)Pr ==> X p q Pr) /\
    (!p r q Pr.
        (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\
        ((r LEADSTO q)Pr ==> X r q Pr) ==>
        (p LEADSTO q)Pr ==> X p q Pr) /\
    (!P q Pr.
      (!p. p In P ==> (p LEADSTO q)Pr) /\
      (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr) ==>
      ((LUB P) LEADSTO q)Pr ==> X (LUB P) q Pr)
      ==>
        !(p:*->bool) q Pr. (p LEADSTO q)Pr ==> X p q Pr",
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (REWRITE_RULE
   [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
    ASSUME "!(p:*->bool) r q Pr. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\
        ((r LEADSTO q)Pr ==> X r q Pr) ==> (p LEADSTO q)Pr ==> X p q Pr";
    ASSUME "!(P:(*->bool)->bool) q Pr.
        (!p. p In P ==> (p LEADSTO q)Pr) /\
        (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr) ==>
        ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr"]
     (SPEC_ALL LEADSTO_thm33)) THEN
  RES_TAC);;


%
  and the theorem:

  |- !X Pr.

    (!p q. (p ENSURES q)Pr ==> X p q Pr) /\

    (!p r q.
      (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X r q Pr
                           ==> X p q Pr) /\

    (!P q.
      (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                           ==> X(LUB P)q Pr)

   ==>

    (!p q. (p LEADSTO q)Pr ==> X p q Pr)

  which may be used for deriving a tactic supporting given programs.
%
let LEADSTO_thm34a_lemma1 = TAC_PROOF
  (([],
   "!P q Pr. (!p:*->bool. p In P ==> (p LEADSTO q)Pr) ==>
       (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
          ==> (!p. p In P ==> X p q Pr)"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   RES_TAC);;

let LEADSTO_thm34a_lemma2 = TAC_PROOF
  (([],
   "!P q Pr. (!p:*->bool. p In P ==> (p LEADSTO q)Pr) ==>
                   (!p. p In P ==> X p q Pr) ==>
                       (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm34a_lemma3 = TAC_PROOF
  (([],
   "((!(p:*->bool) q. (p ENSURES q)Pr ==> X p q Pr) /\
       (!p r q.
         (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X r q Pr ==> X p q Pr) /\
       (!P q.
         (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr) ==>
         X(LUB P)q Pr))
     =
    (!p q.
     ((p ENSURES q)Pr ==> X p q Pr) /\
     (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
                      ==> (p LEADSTO q)Pr ==> X p q Pr) /\
     (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\
          (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr)
                      ==> ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr))"),
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     RES_TAC
    ;
     RES_TAC
    ;
     ASSUME_TAC (UNDISCH_ALL (SPEC_ALL LEADSTO_thm34a_lemma1)) THEN
     RES_TAC
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm2 THEN
     ACCEPT_TAC (REWRITE_RULE
      [ASSUME "((p:*->bool) ENSURES r)Pr";
       ASSUME "((r:*->bool) LEADSTO q)Pr";
       ASSUME "(X:(*->bool)->(*->bool)->(*->*)list->bool) r q Pr";
       ASSUME "((p:*->bool) LEADSTO q)Pr"]
      (SPEC_ALL (CONJUNCT1 (CONJUNCT2 (SPEC_ALL (ASSUME
        "!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r.
          (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
             ==> (p LEADSTO q)Pr ==> X p q Pr) /\
        (!P.
          (!p. p In P ==> (p LEADSTO q)Pr) /\
          (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr) ==>
          ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr)"))))))
    ;
     IMP_RES_TAC LEADSTO_thm3a THEN
     ASSUME_TAC (UNDISCH_ALL (SPEC_ALL LEADSTO_thm34a_lemma2)) THEN
     ACCEPT_TAC (REWRITE_RULE
      [ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr";
       ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr ==> X p q Pr";
       ASSUME "((LUB (P:(*->bool)->bool)) LEADSTO q)Pr"]
      (SPEC_ALL (CONJUNCT2 (CONJUNCT2 (SPEC_ALL (ASSUME
        "!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q Pr) /\
        (!r.
          (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ ((r LEADSTO q)Pr ==> X r q Pr)
             ==> (p LEADSTO q)Pr ==> X p q Pr) /\
        (!P.
          (!p. p In P ==> (p LEADSTO q)Pr) /\
          (!p. p In P ==> (p LEADSTO q)Pr ==> X p q Pr) ==>
          ((LUB P) LEADSTO q)Pr ==> X(LUB P)q Pr)"))))))
    ]);;

%
  The theorem for the tactic
%
let LEADSTO_thm34a = prove_thm
  (`LEADSTO_thm34a`,
   "!X Pr.
    (!p q. (p ENSURES q)Pr ==> X p q Pr) /\
    (!p r q.
        (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X r q Pr
          ==> X p q Pr) /\
    (!P q.
      (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
          ==> X (LUB P) q Pr)
      ==>
        !(p:*->bool) q. (p LEADSTO q)Pr ==> X p q Pr",
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN 
  REPEAT GEN_TAC THEN
  ACCEPT_TAC (REWRITE_RULE
   [ASSUME "!(p:*->bool) q. (p ENSURES q)Pr ==> X p q Pr";
    ASSUME "!(p:*->bool) r q.
        (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X r q Pr ==> X p q Pr";
    ASSUME "!P (q:*->bool).
        (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr) ==>
        X(LUB P)q Pr"]
     (REWRITE_RULE [SYM (SPEC_ALL LEADSTO_thm34a_lemma3)]
       (SPEC_ALL LEADSTO_thm33))));;

let LEADSTO_thm34b = prove_thm
  (`LEADSTO_thm34b`,
   "!X:(*->bool)->(*->bool)->(*->*)list->bool.
    (!p q st Pr. (p ENSURES q)(CONS st Pr) ==> X p q (CONS st Pr)) /\
    (!p r q st Pr.
        (p ENSURES r)(CONS st Pr) /\ (r LEADSTO q)(CONS st Pr) /\
         X r q (CONS st Pr)
          ==> X p q (CONS st Pr)) /\
    (!P q st Pr.
      (!p. p In P ==> (p LEADSTO q)(CONS st Pr)) /\
      (!p. p In P ==> X p q (CONS st Pr))
          ==> X (LUB P) q (CONS st Pr))
      ==>
        !p q st Pr. (p LEADSTO q)(CONS st Pr) ==> X p q (CONS st Pr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE [ASSUME "((p:*->bool) LEADSTO q)(CONS st Pr)"]
   (SPEC_ALL (REWRITE_RULE 
    [ASSUME
      "!(p:*->bool) q st Pr. (p ENSURES q)(CONS st Pr) ==> X p q(CONS st Pr)";
     ASSUME "!(p:*->bool) r q st Pr.
        (p ENSURES r)(CONS st Pr) /\ (r LEADSTO q)(CONS st Pr) /\
        X r q(CONS st Pr) ==> X p q(CONS st Pr)";
     ASSUME "!P (q:*->bool) st Pr.
        (!p. p In P ==> (p LEADSTO q)(CONS st Pr)) /\
        (!p. p In P ==> X p q(CONS st Pr)) ==> X(LUB P)q(CONS st Pr)"]
      (SPECL ["X:(*->bool)->(*->bool)->(*->*)list->bool";"CONS (st:*->*) Pr"]
              LEADSTO_thm34a)))));;


%
  Now we may introduce some tactics for supporting structural induction
  of leadsto relations:
%
loadf `leadsto_induct0`;;



%
 Prove:

  |- !p q st Pr.
       (p ENSURES q)(CONS st Pr) /\ (p' LEADSTO q')(CONS st Pr) /\
       (q UNLESS r)(CONS st Pr) /\ (q' UNLESS r)(CONS st Pr)
          ==> ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)
%
let LEADSTO_thm35_lemma00 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr.
     (p ENSURES q)(CONS st Pr) /\ (p' LEADSTO q')(CONS st Pr) /\
     (q UNLESS r)(CONS st Pr) /\ (q' UNLESS r)(CONS st Pr)
         ==> ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (MP (SPECL
    ["p:*->bool";"q:*->bool";"(CONS st Pr):(*->*)list"] ENSURES_cor2)
       (ASSUME "((p:*->bool) ENSURES q)(CONS st Pr)")) THEN
   ASSUME_TAC (MP (SPECL
    ["p:*->bool";"q:*->bool";"r:*->bool";"(CONS st Pr):(*->*)list"]
     UNLESS_thm8)
      (CONJ (MP (SPECL ["p:*->bool";"q:*->bool";"(CONS st Pr):(*->*)list"]
                        ENSURES_cor2)
        (ASSUME "((p:*->bool) ENSURES q)(CONS st Pr)"))
        (ASSUME "((q:*->bool) UNLESS r)(CONS st Pr)"))) THEN
   ASSUME_TAC (MP (SPECL
     ["p':*->bool";"q':*->bool";"(p:*->bool) \/* q";"r:*->bool";
      "st:*->*";"Pr:(*->*)list"] LEADSTO_thm29) (CONJ
        (ASSUME "((p':*->bool) LEADSTO q')(CONS st Pr)")
        (ASSUME "(((p:*->bool) \/* q) UNLESS r)(CONS st Pr)"))) THEN
   ASSUME_TAC (MP (SPECL ["p:*->bool";"(p:*->bool) \/* q";
                          "p':*->bool"] IMPLY_WEAK_AND_lemma)
              (SPECL ["p:*->bool";"q:*->bool"] OR_IMPLY_WEAK_lemma)) THEN
   ASSUME_TAC (MP (SPECL
     ["(p:*->bool) /\* p'";"(p':*->bool) /\* (p \/* q)";
        "st:*->*";"Pr:(*->*)list"] LEADSTO_thm25) (ONCE_REWRITE_RULE
      [(SPECL ["(p:*->bool) \/* q";"p':*->bool"] AND_COMM_lemma)]
       (ASSUME "!s:*. (p /\* p')s ==> ((p \/* q) /\* p')s"))) THEN
   ASSUME_TAC (MP (SPECL
    ["(p:*->bool) /\* p'";"(p':*->bool) /\* (p \/* q)";
       "((q':*->bool) /\* (p \/* q)) \/* r";"CONS (st:*->*) Pr"] LEADSTO_thm1)
     (CONJ
       (ASSUME "(((p:*->bool) /\* p') LEADSTO (p' /\* (p \/* q)))(CONS st Pr)")
       (ASSUME "((p' /\* (p \/* q)) LEADSTO ((q' /\* (p \/* q)) \/* r))
                (CONS (st:*->*) Pr)"))) THEN
   ASSUME_TAC (MP (SPECL
    ["p:*->bool";"q:*->bool";"q':*->bool";"r:*->bool";
     "st:*->*";"Pr:(*->*)list"] LEADSTO_thm29)
      (CONJ (MP (SPECL ["p:*->bool";"q:*->bool";"CONS (st:*->*) Pr"]
                        LEADSTO_thm0)
        (ASSUME "((p:*->bool) ENSURES q)(CONS st Pr)"))
        (ASSUME "((q':*->bool) UNLESS r)(CONS st Pr)"))) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [SPECL
    ["((q':*->bool) /\* q) \/* r";"p:*->bool";"q':*->bool"]
     OR_AND_COMM_lemma] (ONCE_REWRITE_RULE [SPECL
      ["(q':*->bool) /\* p";"((q':*->bool) /\* q) \/* r"]
       OR_COMM_lemma] (REWRITE_RULE [OR_ASSOC_lemma]
      (REWRITE_RULE [AND_OR_DISTR_lemma] (ASSUME
         "(((p:*->bool) /\* p') LEADSTO
           ((q' /\* (p \/* q)) \/* r))(CONS st Pr)"))))) THEN
   ACCEPT_TAC (ONCE_REWRITE_RULE [OR_COMM_lemma] (REWRITE_RULE [OR_OR_lemma]
    (REWRITE_RULE [OR_ASSOC_lemma] (ONCE_REWRITE_RULE[OR_AND_COMM_lemma]
    (REWRITE_RULE [OR_OR_lemma] (REWRITE_RULE [SYM (SPEC_ALL OR_ASSOC_lemma)]
    (ONCE_REWRITE_RULE [OR_COMM_lemma] (REWRITE_RULE [OR_ASSOC_lemma]
    (ONCE_REWRITE_RULE [OR_OR_COMM_lemma] (MP (SPECL
      ["(p:*->bool) /\* p'";"((q':*->bool) /\* q) \/* r";
       "(p:*->bool) /\* q'";"((q:*->bool) /\* q') \/* r";
       "st:*->*";"Pr:(*->*)list"] LEADSTO_thm28) (CONJ
       (ASSUME "((p /\* p') LEADSTO (((q' /\* q) \/* r) \/* (p /\* q')))
                   (CONS (st:*->*) Pr)")
       (ASSUME "((p /\* q') LEADSTO ((q /\* q') \/* r))
                   (CONS (st:*->*) Pr)")))))))))))));;


let LEADSTO_thm35_lemma01_1 = TAC_PROOF
  (([],
   "!(q:*->bool) (q':*->bool) r'' p r s.
        ((((q /\* q') \/* r'') \/* (p /\* r)) \/* ((q' /\* q) \/* r''))s =
        (((q /\* q') \/* r'') \/* (p /\* r))s"),
   REWRITE_TAC [\/*;/\*] THEN
   BETA_TAC THEN
   REPEAT GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let LEADSTO_thm35_lemma01_2 =
    GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:*" (SPEC_ALL
      LEADSTO_thm35_lemma01_1))));;

let LEADSTO_thm35_lemma01_3 = TAC_PROOF
  (([],
   "(!p:*->bool. p In P ==>
        (!p'' q r r'.
          (r LEADSTO q)(CONS st Pr) ==>
          (p'' ENSURES r)(CONS st Pr) ==>
          (q' UNLESS r')(CONS st Pr) ==>
          (q UNLESS r')(CONS st Pr) ==>
          (!p' q' r''.
            (p' LEADSTO q')(CONS st Pr) ==>
            (q UNLESS r'')(CONS st Pr) ==>
            (q' UNLESS r'')(CONS st Pr) ==>
            ((r /\* p') LEADSTO ((q /\* q') \/* r''))(CONS st Pr)) ==>
          ((p'' /\* p) LEADSTO ((q /\* q') \/* r'))(CONS st Pr)))
      ==>
      (!p'' q r r'.
          (r LEADSTO q)(CONS st Pr) ==>
          (p'' ENSURES r)(CONS st Pr) ==>
          (q' UNLESS r')(CONS st Pr) ==>
          (q UNLESS r')(CONS st Pr) ==>
          (!p' q' r''.
            (p' LEADSTO q')(CONS st Pr) ==>
            (q UNLESS r'')(CONS st Pr) ==>
            (q' UNLESS r'')(CONS st Pr) ==>
            ((r /\* p') LEADSTO ((q /\* q') \/* r''))(CONS st Pr)) ==>
          (!p. p In P ==>
                 ((p'' /\* p) LEADSTO ((q /\* q') \/* r'))(CONS st Pr)))"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm35_lemma01_4 = TAC_PROOF
  (([],
   "!(P:(*->bool)->bool) r q st Pr.
    (!p. p In P ==> ((p /\* r) LEADSTO q)(CONS st Pr)) ==>
    (!p. p In P ==> (p LEADSTO q)(CONS st Pr)) ==>
    (((LUB P) /\* r) LEADSTO q)(CONS st Pr)"),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm3a THEN
   ASSUME_TAC (SPECL
    ["LUB (P:(*->bool)->bool)";"r:*->bool"] SYM_AND_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL (SPECL
    ["(LUB P) /\* (r:*->bool)";"(LUB P):*->bool"] ENSURES_cor1))) THEN
   IMP_RES_TAC LEADSTO_thm0 THEN
   IMP_RES_TAC LEADSTO_thm1);;

let LEADSTO_thm35_lemma01_5 = TAC_PROOF
  (([],
   "!(p':*->bool) P p p''.
      p' In (\p''. ?p'''. p''' In P /\ (p'' = p /\* p'''))
     =
      (?p'''. p''' In P /\ (p' = p /\* p'''))"),
   REWRITE_TAC [In] THEN
   BETA_TAC THEN
   REWRITE_TAC []);;

let LEADSTO_thm35_lemma01_6 = TAC_PROOF
  (([],
   "!s:*.
      (p /\* (LUB P))s =
      (LUB(\p''. ?p'. p' In P /\ (p'' = p /\* p')))s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LUB;/\*] THEN
   BETA_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THENL
    [
     EXISTS_TAC "\s:*. p s /\ p' s" THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC "p':*->bool" THEN
     ASM_REWRITE_TAC [In]
    ;
     STRIP_ASSUME_TAC (BETA_RULE (SUBS [ASSUME "p' = (\s:*. p s /\ p''' s)"]
                                       (ASSUME "(p':*->bool) s")))
    ;
     EXISTS_TAC "p''':*->bool" THEN
     REWRITE_TAC [REWRITE_RULE [In] (ASSUME "(p''':*->bool) In P")] THEN
     STRIP_ASSUME_TAC (BETA_RULE (SUBS [ASSUME "p' = (\s:*. p s /\ p''' s)"]
                                       (ASSUME "(p':*->bool) s")))
    ]);;

let LEADSTO_thm35_lemma01_7 = TAC_PROOF
  (([],
   "!(P:(*->bool)->bool) r' q q' st Pr.
    (!p'. p' In P ==> ((p /\* p') LEADSTO ((q /\* q') \/* r'))(CONS st Pr))
      ==>
        (!p'. (?p'''. p''' In P /\ (p' = p /\* p''')) ==>
                             (p' LEADSTO ((q /\* q') \/* r'))(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []);;

let LEADSTO_thm35_lemma01_8 = TAC_PROOF
  (([],
   "!(P:(*->bool)->bool) r' q q' st Pr.
       (!p'.
        p' In P ==> ((p /\* p') LEADSTO ((q /\* q') \/* r'))(CONS st Pr))
          ==> (((p /\* (LUB P)) LEADSTO ((q /\* q') \/* r'))(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm35_lemma01_5] (SPECL
     ["\p'':*->bool. ?p'. p' In P /\ (p'' = (p /\* p'))";
      "(q /\* q') \/* (r':*->bool)";"CONS (st:*->*) Pr"]
     LEADSTO_thm3a)) THEN
   ASSUME_TAC (REWRITE_RULE [(UNDISCH (SPEC_ALL LEADSTO_thm35_lemma01_7))]
      (ASSUME "(!p':*->bool.
         (?p'''. p''' In P /\ (p' = p /\* p''')) ==>
         (p' LEADSTO ((q /\* q') \/* r'))(CONS st Pr)) ==>
       ((LUB(\p''. ?p'. p' In P /\ (p'' = p /\* p'))) LEADSTO
        ((q /\* q') \/* r'))
       (CONS st Pr)")) THEN
   ASM_REWRITE_TAC [REWRITE_RULE [ETA_AX] (MK_ABS LEADSTO_thm35_lemma01_6)]);;

let LEADSTO_thm35_lemma01_9 = TAC_PROOF
  (([],
   "(!p:*->bool.
        p In P ==>
        (!p' q' r.
          (p' LEADSTO q')(CONS st Pr) ==>
          (q UNLESS r)(CONS st Pr) ==>
          (q' UNLESS r)(CONS st Pr) ==>
          ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)))
     ==>
     ((!p' q' r.
          (p' LEADSTO q')(CONS st Pr) ==>
          (q UNLESS r)(CONS st Pr) ==>
          (q' UNLESS r)(CONS st Pr) ==>
       (!p. p In P ==>
          ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr))))"),
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm35_lemma01_10 = TAC_PROOF
  (([],
  "(!p:*->bool. p In P ==> ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr))
      ==>
    (!p. p In P ==> ((p' /\* p) LEADSTO ((q /\* q') \/* r))(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ONCE_REWRITE_TAC [SPECL ["p':*->bool";"p:*->bool"] AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_OR_lemma] THEN
   ASM_REWRITE_TAC []);;

let LEADSTO_thm35_lemma01 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr.
     (p LEADSTO q)(CONS st Pr) ==>
       !p' q' r. (p' LEADSTO q')(CONS st Pr)
           ==> (q UNLESS r)(CONS st Pr) ==> (q' UNLESS r)(CONS st Pr)
                  ==> ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)"),
   LEADSTO_INDUCT0_TAC THENL
    [
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC LEADSTO_thm35_lemma00
    ;
     REPEAT STRIP_TAC THEN
     UNDISCH_TAC "!(p':*->bool) q' r'.
        (p' LEADSTO q')(CONS st Pr) ==>
        (q UNLESS r')(CONS st Pr) ==>
        (q' UNLESS r')(CONS st Pr) ==>
        ((r /\* p') LEADSTO ((q /\* q') \/* r'))(CONS st Pr)" THEN
     UNDISCH_TAC "((q:*->bool) UNLESS r')(CONS st Pr)" THEN
     UNDISCH_TAC "((q':*->bool) UNLESS r')(CONS st Pr)" THEN
     UNDISCH_TAC "((p:*->bool) ENSURES r)(CONS st Pr)" THEN
     UNDISCH_TAC "((r:*->bool) LEADSTO q)(CONS st Pr)" THEN
     SPEC_TAC ("r':*->bool", "r':*->bool") THEN
     SPEC_TAC ("r:*->bool", "r:*->bool") THEN
     SPEC_TAC ("q:*->bool", "q:*->bool") THEN
     SPEC_TAC ("p:*->bool", "p:*->bool") THEN
     UNDISCH_TAC "((p':*->bool) LEADSTO q')(CONS st Pr)" THEN
     SPEC_TAC ("Pr:(*->*)list", "Pr:(*->*)list") THEN
     SPEC_TAC ("st:*->*", "st:*->*") THEN
     SPEC_TAC ("q':*->bool", "q':*->bool") THEN
     SPEC_TAC ("p':*->bool", "p':*->bool") THEN
     LEADSTO_INDUCT0_TAC THENL
      [
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC LEADSTO_thm2 THEN
       IMP_RES_TAC LEADSTO_thm35_lemma00 THEN
       ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
       ACCEPT_TAC (ASSUME
        "(((p':*->bool) /\* p) LEADSTO ((q' /\* q) \/* r'))(CONS st Pr)")
      ;
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC LEADSTO_thm2 THEN
       IMP_RES_TAC LEADSTO_thm0 THEN
       UNDISCH_TAC "!(p:*->bool) q r'' r'.
        (r'' LEADSTO q)(CONS st Pr) ==>
        (p ENSURES r'')(CONS st Pr) ==>
        (q' UNLESS r')(CONS st Pr) ==>
        (q UNLESS r')(CONS st Pr) ==>
        (!p' q' r'''.
          (p' LEADSTO q')(CONS st Pr) ==>
          (q UNLESS r''')(CONS st Pr) ==>
          (q' UNLESS r''')(CONS st Pr) ==>
          ((r'' /\* p') LEADSTO ((q /\* q') \/* r'''))(CONS st Pr)) ==>
        ((p /\* r) LEADSTO ((q /\* q') \/* r'))(CONS st Pr)" THEN
       ASM_REWRITE_TAC [] THEN
       STRIP_TAC THEN
       ASSUME_TAC (UNDISCH (SPECL
         ["p:*->bool";"r':*->bool";"CONS (st:*->*) Pr"] ENSURES_cor2)) THEN
       ASSUME_TAC (UNDISCH (SPECL
         ["p':*->bool";"r:*->bool";"CONS (st:*->*) Pr"] ENSURES_cor2)) THEN
       RES_TAC THEN
       ASSUME_TAC (REWRITE_RULE
        [ASSUME "((p:*->bool)UNLESS r')(CONS st Pr)";
         ASSUME "((p':*->bool)ENSURES r)(CONS st Pr)"]
          (SPECL
            ["p:*->bool";"r':*->bool";"p':*->bool";"r:*->bool";
             "CONS (st:*->*) Pr"] ENSURES_thm4)) THEN
       IMP_RES_TAC LEADSTO_thm0 THEN
       ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL OR_ASSOC_lemma)]
        (ONCE_REWRITE_RULE [OR_COMM_lemma] (REWRITE_RULE [
          (ASSUME
            "(((r':*->bool) /\* r) LEADSTO ((q /\* q') \/* r''))(CONS st Pr)");
          (ASSUME "(((p:*->bool) /\* p') LEADSTO
            (((p /\* r) \/* (p' /\* r')) \/* (r' /\* r)))(CONS st Pr)")] (SPECL
           ["(p:*->bool) /\* p'";"((p:*->bool) /\* r) \/* (p' /\* r')";
            "(r':*->bool) /\* r";"((q:*->bool) /\* q') \/* r''";"st:*->*";
            "Pr:(*->*)list"] LEADSTO_thm28)))) THEN
       IMP_RES_TAC LEADSTO_thm2 THEN
       ASSUME_TAC (REWRITE_RULE [LEADSTO_thm35_lemma01_2] (REWRITE_RULE
        [(ONCE_REWRITE_RULE [SPECL ["r':*->bool";"p':*->bool"] AND_COMM_lemma]
        (ASSUME
          "(((r':*->bool) /\* p') LEADSTO ((q /\* q') \/* r''))(CONS st Pr)"));
         (ASSUME "(((p:*->bool) /\* p') LEADSTO
                  ((((q /\* q') \/* r'') \/* (p /\* r)) \/* (p' /\* r')))
                  (CONS st Pr)")] (SPECL
          ["(p:*->bool) /\* p'";"(((q:*->bool) /\* q') \/* r'') \/* (p /\* r)";
           "(p':*->bool) /\* r'";"((q':*->bool) /\* q) \/* r''";"st:*->*";
           "Pr:(*->*)list"] LEADSTO_thm28))) THEN
       ACCEPT_TAC (REWRITE_RULE [OR_OR_lemma] (REWRITE_RULE
        [(ASSUME
           "(((p:*->bool) /\* r) LEADSTO ((q /\* q') \/* r''))(CONS st Pr)");
         (ASSUME "(((p:*->bool) /\* p') LEADSTO
                  (((q /\* q') \/* r'') \/* (p /\* r)))(CONS st Pr)")] (SPECL
           ["(p:*->bool) /\* p'";"((q:*->bool) /\* q') \/* r''";
            "(p:*->bool) /\* r";"((q:*->bool) /\* q') \/* r''";"st:*->*";
            "Pr:(*->*)list"] LEADSTO_thm28)))
      ;
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC LEADSTO_thm0 THEN
       IMP_RES_TAC LEADSTO_thm2 THEN
       IMP_RES_TAC LEADSTO_thm35_lemma01_3 THEN
       IMP_RES_TAC LEADSTO_thm35_lemma01_8
      ]
    ;
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC LEADSTO_thm35_lemma01_9 THEN
     IMP_RES_TAC LEADSTO_thm35_lemma01_10 THEN
     IMP_RES_TAC LEADSTO_thm35_lemma01_8 THEN
     ONCE_REWRITE_TAC
      [SPECL ["LUB (P:(*->bool)->bool)";"p':*->bool"] AND_COMM_lemma] THEN
     ASM_REWRITE_TAC []
    ]);;

%
  Now prove the completion theorem:

  |- !p q p' q' r st Pr.
      (p LEADSTO q)(CONS st Pr) /\ (p' LEADSTO q')(CONS st Pr) /\
      (q UNLESS r)(CONS st Pr) /\ (q' UNLESS r)(CONS st Pr)
         ==> ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)
%
let LEADSTO_thm35 = prove_thm
  (`LEADSTO_thm35`,
   "!(p:*->bool) q p' q' r st Pr.
     (p LEADSTO q)(CONS st Pr) /\ (p' LEADSTO q')(CONS st Pr) /\
     (q UNLESS r)(CONS st Pr) /\ (q' UNLESS r)(CONS st Pr)
        ==> ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm35_lemma01);;

% ***************************************************************************

       We now prove the theorem valid for proving bounds of progress.

  *************************************************************************** %

%
  We need to define the metric predicates EQmetric and LESSmetric
%

%
	EQmetric is the state abstracted predicate expressing that the metric
	function M must have the value m in the state s.
%
let EQmetric = new_infix_definition
  (`EQmetric`, "EQmetric (M:*->num) m = \s. M s = m");;

%
	LESSmetric is the state abstracted predicate expressing that the metric
	function M must have a value less than m in the state s.
%
let LESSmetric = new_infix_definition
  (`LESSmetric`, "LESSmetric (M:*->num) m = \s. M s < m");;

%-----------------------------------------------------------------------------%
%
  Lemmas
%
%-----------------------------------------------------------------------------%

let LEADSTO_thm36_lemma00 = BETA_RULE
   (SPEC "\n. (((p:*->bool) /\* (M EQmetric n)) LEADSTO q)(CONS st Pr)"
         GEN_INDUCT_thm);;

let LEADSTO_thm36_lemma01 = TAC_PROOF
  (([],
   "!(M:*->num) m. (p /\* (M EQmetric m)) = ((\i. p /\* (M EQmetric i))m)"),
   BETA_TAC THEN
   REWRITE_TAC []);;

let LEADSTO_thm36_lemma02 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr M m.
       (!n. n < (SUC m) ==> ((p /\* (M EQmetric n)) LEADSTO q)(CONS st Pr)) ==>
             (!n. n < m ==> ((p /\* (M EQmetric n)) LEADSTO q)(CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   STRIP_ASSUME_TAC
     (MP (SPEC "n:num" (ASSUME "!n. n < (SUC m) ==>
           (((p:*->bool) /\* (M EQmetric n)) LEADSTO q)(CONS st Pr)"))
         (MP (SPECL ["n:num";"m:num"] LESS_SUC) (ASSUME "n < m"))));;

let LEADSTO_thm36_lemma03 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr M m.
      (!n. n < m ==> ((p /\* (M EQmetric n)) LEADSTO q) (CONS st Pr)) ==>
        ((\</* (\i. p /\* (M EQmetric i))m) LEADSTO q) (CONS st Pr)"),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   INDUCT_TAC THENL
     [
      REWRITE_TAC [\</*;LEADSTO_cor12;LEADSTO_cor11;NOT_LESS_0]
     ;
      DISCH_TAC THEN
      REWRITE_TAC [\</*] THEN
      BETA_TAC THEN
      ASSUME_TAC (UNDISCH_ALL (SPEC_ALL LEADSTO_thm36_lemma02)) THEN
      ASSUME_TAC (MP
       (ASSUME "(!n. n < m ==> ((p /\* (M EQmetric n)) LEADSTO q)(CONS st Pr))
                    ==> ((\</*(\i. p /\* (M EQmetric i))m) LEADSTO q)
                         (CONS (st:*->*) Pr)")
       (ASSUME "!n. n < m ==> ((p /\* (M EQmetric n)) LEADSTO q)
                         (CONS (st:*->*) Pr)")) THEN
      ASSUME_TAC (REWRITE_RULE [LESS_SUC_REFL] (SPEC "m:num"
       (ASSUME "!n. n < (SUC m) ==> ((p /\* (M EQmetric n)) LEADSTO q)
                         (CONS (st:*->*) Pr)"))) THEN
      STRIP_ASSUME_TAC (MP (SPECL
       ["\</*(\i. (p:*->bool) /\* (M EQmetric i))m";
        "(p:*->bool) /\* (M EQmetric m)";"q:*->bool";"CONS (st:*->*) Pr"]
        LEADSTO_thm4) (CONJ
         (ASSUME "((\</*(\i. p /\* (M EQmetric i))m) LEADSTO q)
                    (CONS (st:*->*) Pr)")
         (ASSUME "((p /\* (M EQmetric m)) LEADSTO q)(CONS (st:*->*) Pr)")))
     ]);;

let LEADSTO_thm36_lemma04 = TAC_PROOF
  (([],
   "!M:*->num. (!m s. (M LESSmetric m)s = (\</* (\i. M EQmetric i) m) s)"),
   GEN_TAC THEN
   INDUCT_TAC THENL
     [
      REWRITE_TAC [LESSmetric;EQmetric;\</*;FALSE_DEF;NOT_LESS_0]
     ;
      GEN_TAC THEN
      REWRITE_TAC [\</*;\/*;LESSmetric;LESS_THM] THEN
      BETA_TAC THEN
      EQ_TAC THENL
        [
         STRIP_TAC THENL
           [
            DISJ2_TAC THEN
            REWRITE_TAC [EQmetric] THEN
            BETA_TAC THEN
            ASM_REWRITE_TAC []
           ;
            DISJ1_TAC THEN
            ASM_REWRITE_TAC [SYM (SPEC_ALL(BETA_RULE (REWRITE_RULE [LESSmetric]
             (ASSUME "!s:*. (M LESSmetric m)s = \</*(\i. M EQmetric i)m s"))))]
           ]
        ;
         STRIP_TAC THENL
           [
            DISJ2_TAC THEN
            ASM_REWRITE_TAC [SPEC_ALL (BETA_RULE (REWRITE_RULE [LESSmetric]
             (ASSUME "!s:*. (M LESSmetric m)s = \</*(\i. M EQmetric i)m s")))]
           ;
            DISJ1_TAC THEN
            STRIP_ASSUME_TAC (BETA_RULE (REWRITE_RULE [EQmetric]
             (ASSUME "(M EQmetric m)(s:*)")))
           ]
        ]
     ]);;

let LEADSTO_thm36_lemma05 = TAC_PROOF
  (([],
   "!(M:*->num) m. (M LESSmetric m) = (\</* (\i. M EQmetric i) m)"),
   REWRITE_TAC [LESSmetric;EQmetric;
                BETA_RULE ((REWRITE_RULE [LESSmetric;EQmetric]) (MK_ABS
                  (SPECL ["M:*->num";"m:num"] LEADSTO_thm36_lemma04)))] THEN
   REWRITE_TAC [ETA_AX]);;

let LEADSTO_thm36_lemma06 = TAC_PROOF
  (([],
  "!(p:*->bool) M q Pr.
   (!m. ((p /\* (M EQmetric m)) LEADSTO ((p /\* (M LESSmetric m)) \/* q))Pr)
      ==> (!m. ((p /\* (M EQmetric m)) LEADSTO
               ((p /\* (\</*(\i. M EQmetric i)m)) \/* q))Pr)"),
   REWRITE_TAC [LEADSTO_thm36_lemma05]);;

let LEADSTO_thm36_lemma07 = TAC_PROOF
  (([],
   "!(p:*->bool) M m.
      (\</*(\i. p /\* (M EQmetric i))m) = (p /\* (\</*(\i. M EQmetric i)m))"),
   GEN_TAC THEN GEN_TAC THEN
   INDUCT_TAC THENL
     [
      REWRITE_TAC [\</*;AND_FALSE_lemma]
     ;
      REWRITE_TAC [\</*] THEN
      BETA_TAC THEN
      ASM_REWRITE_TAC [SYM (SPEC_ALL AND_OR_DISTR_lemma)]]);;

let LEADSTO_thm36_lemma08 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr M.
       (!m. ((p /\* (M EQmetric m)) LEADSTO
           ((p /\* (M LESSmetric m)) \/* q)) (CONS st Pr)) ==>
       (!m. (!n. n < m ==> ((p /\* (M EQmetric n)) LEADSTO q)(CONS st Pr)) ==>
                   ((p /\* (M EQmetric m)) LEADSTO q) (CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm36_lemma07]
    (MP (SPEC_ALL LEADSTO_thm36_lemma03)
        (ASSUME "!n. n < m ==> ((p /\* (M EQmetric n)) LEADSTO q)
                   (CONS (st:*->*) Pr)"))) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [OR_COMM_lemma] (SPEC_ALL (UNDISCH (SPECL
    ["p:*->bool";"M:*->num";"q:*->bool";"CONS (st:*->*) Pr"]
     LEADSTO_thm36_lemma06)))) THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [OR_OR_lemma]
    (MP (SPECL ["(p:*->bool) /\* (M EQmetric m)";"q:*->bool";
                "(p:*->bool) /\* (\</*(\i. M EQmetric i)m)";
                "q:*->bool";"st:*->*";"Pr:(*->*)list"]
                LEADSTO_thm28)
      (CONJ (ASSUME "(((p:*->bool) /\* (M EQmetric m)) LEADSTO
                      (q \/* (p /\* (\</*(\i. M EQmetric i)m)))) (CONS st Pr)")
            (ASSUME "((p /\* (\</*(\i. M EQmetric i)m)) LEADSTO q)
                        (CONS (st:*->*) Pr)")))));;

let LEADSTO_thm36_lemma09 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr M.
       (!m. ((p /\* (M EQmetric m)) LEADSTO
            ((p /\* (M LESSmetric m)) \/* q)) (CONS st Pr)) ==>
                (!m. ((p /\* (M EQmetric m)) LEADSTO q) (CONS st Pr))"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL LEADSTO_thm36_lemma08)) THEN
   STRIP_ASSUME_TAC (SPEC "m:num" (UNDISCH_ALL LEADSTO_thm36_lemma00)));;

let LEADSTO_thm36_lemma10s = TAC_PROOF
  (([],
   "!(p:*->bool) M s.
       (p /\* ($?*(\n. M EQmetric n)))s = ($?*(\i. p /\* (M EQmetric i)))s"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [/\*;?*;EQmetric] THEN
   BETA_TAC THEN
   EQ_TAC THENL
     [
      STRIP_TAC THEN
      EXISTS_TAC "x:num" THEN
      ASM_REWRITE_TAC []
     ;
      STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      EXISTS_TAC "x:num" THEN
      ASM_REWRITE_TAC []
     ]);;

%
  Needed due to SPEC
%
let LEADSTO_thm36_lemma10 = TAC_PROOF
  (([],
   "!(p:*->bool) M.
       (p /\* ($?*(\n. M EQmetric n))) = ($?*(\i. p /\* (M EQmetric i)))"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [
     REWRITE_RULE [SPEC "(p:*->bool) /\* ($?*(\n. M EQmetric n))"
                        (INST_TYPE [(":*",":*");(":bool",":**")] ETA_AX);
                   SPEC "$?*(\i. (p:*->bool) /\* (M EQmetric i))"
                        (INST_TYPE [(":*",":*");(":bool",":**")] ETA_AX)]
         (MK_ABS (SPECL ["p:*->bool";"M:*->num"] LEADSTO_thm36_lemma10s))]);;

let LEADSTO_thm36_lemma11s = TAC_PROOF
  (([],
   "!(M:*->num) s. ($?* (\n. M EQmetric n))s = TRUE s"),
   REWRITE_TAC [?*;EQmetric;TRUE_DEF] THEN
   BETA_TAC THEN
   REPEAT GEN_TAC THEN
   EXISTS_TAC "(M:*->num) s" THEN
   REFL_TAC);;

let LEADSTO_thm36_lemma11 = TAC_PROOF
  (([],
   "!(M:*->num). ($?* (\n. M EQmetric n)) = TRUE"),
   GEN_TAC THEN
   REWRITE_TAC [REWRITE_RULE
     [SPEC "$?*(\n. (M:*->num) EQmetric n)"
           (INST_TYPE [(":*",":*");(":bool",":**")] ETA_AX);
      SPEC "TRUE:*->bool" (INST_TYPE [(":*",":*");(":bool",":**")] ETA_AX)]
        (MK_ABS (SPEC "M:*->num" LEADSTO_thm36_lemma11s))]);;

let LEADSTO_thm36_lemma12 = TAC_PROOF
  (([],
   "!(p:*->bool) q st Pr M.
      (!m. ((p /\* (M EQmetric m)) LEADSTO
           ((p /\* (M LESSmetric m)) \/* q))(CONS st Pr))
             ==> ((p /\* ($?* (\n. M EQmetric n))) LEADSTO q)(CONS st Pr)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [LEADSTO_thm36_lemma01] (MP
    (SPEC_ALL LEADSTO_thm36_lemma09)
    (ASSUME "!m. ((p /\* (M EQmetric m)) LEADSTO
                 ((p /\* (M LESSmetric m)) \/* q)) (CONS (st:*->*) Pr)"))) THEN
   IMP_RES_TAC LEADSTO_thm3c THEN
   ASM_REWRITE_TAC [LEADSTO_thm36_lemma10]);;

let LEADSTO_thm36 = prove_thm
  (`LEADSTO_thm36`,
   "!(p:*->bool) q st Pr M.
      (!m. ((p /\* (M EQmetric m)) LEADSTO ((p /\* (M LESSmetric m)) \/* q))
                                           (CONS st Pr))
             ==> (p LEADSTO q)(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm36_lemma12 THEN
   ACCEPT_TAC (REWRITE_RULE [LEADSTO_thm36_lemma11;AND_TRUE_lemma]
    (ASSUME
      "(((p:*->bool) /\* ($?*(\n. M EQmetric n))) LEADSTO q)(CONS st Pr)")));;

%
  We prove a new induction theorem:
%
let LEADSTO_thm37_lemma00 = TAC_PROOF
  (([],
   "((!p:*->bool. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q)) =
    (!p'. p' In P ==> (p' LEADSTO q)Pr /\ X p' q)"),
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm37_lemma01 = TAC_PROOF
  (([],
   "(!p':*->bool. p' In P ==> (p' LEADSTO q)Pr /\ X p' q) =
    ((!p'. p' In P ==> (p' LEADSTO q)Pr) /\ (!p'. p' In P ==> X p' q))"),
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm37_lemma02 = TAC_PROOF
  (([],
   "!(X:(*->bool)->(*->bool)->bool) Pr.
       (!p q.
         ((p ENSURES q)Pr ==> (p LEADSTO q)Pr /\ X p q) /\
         (!r.
           (p LEADSTO r)Pr /\ X p r /\ (r LEADSTO q)Pr /\ X r q ==>
           (p LEADSTO q)Pr /\ X p q) /\
         (!P.
           (p = LUB P) /\ (!p'. p' In P ==> (p' LEADSTO q)Pr /\ X p' q) ==>
           (p LEADSTO q)Pr /\ X p q))
      =
        (!p q.
        ((p ENSURES q)Pr ==> X p q) /\
        (!r.
          (p LEADSTO r)Pr /\ X p r /\ (r LEADSTO q)Pr /\ X r q ==> X p q) /\
        (!P.
          (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q) ==>
          X(LUB P)q))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL
    [
     RES_TAC
    ;
     RES_TAC
    ;
     ASSUME_TAC (REWRITE_RULE [LEADSTO_thm37_lemma00] (CONJ
       (ASSUME "!p:*->bool. p In P ==> (p LEADSTO q)Pr")
       (ASSUME "!p. p In P ==> (X:(*->bool)->(*->bool)->bool) p q"))) THEN
     RES_TAC THEN
     ACCEPT_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
      "!p. (p = LUB P) ==> (X:(*->bool)->(*->bool)->bool) p q")))
    ;
     IMP_RES_TAC LEADSTO_thm0
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm1 THEN
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm1 THEN
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO_thm37_lemma01 THEN
     IMP_RES_TAC LEADSTO_thm3
    ;
     IMP_RES_TAC LEADSTO_thm37_lemma01 THEN
     RES_TAC THEN
     ASM_REWRITE_TAC []
    ]);;

let LEADSTO_thm37 = prove_thm
  (`LEADSTO_thm37`,
   "!X p q Pr.
      (!(p:*->bool) q.
        ((p ENSURES q)Pr ==> X p q) /\
        (!r. (p LEADSTO r)Pr /\ X p r /\ (r LEADSTO q)Pr /\ X r q
                         ==> X p q) /\
        (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q)
                         ==> X (LUB P) q))
     ==> ((p LEADSTO q)Pr ==> X p q)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm37_lemma02]
    (REWRITE_RULE [SYM (SPEC_ALL CONJ_ASSOC)] (BETA_RULE (SPEC
     "\(p:*->bool) q Pr. (p LEADSTO q)Pr /\ (X p q)" 
       (REWRITE_RULE [LEADSTO;LeadstoRel]
         (ASSUME "((p:*->bool) LEADSTO q)Pr")))))) THEN
   RES_TAC);;

%
  The theorem useful for an induction tactic
%
let LEADSTO_thm38 = prove_thm
  (`LEADSTO_thm38`,
   "!X.
      (!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q) /\
      (!p r q Pr. (p LEADSTO r)Pr /\ X p r /\ (r LEADSTO q)Pr /\ X r q
                                          ==> X p q) /\
      (!P q Pr. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q)
                                          ==> X (LUB P) q)
     ==> (!p q Pr. (p LEADSTO q)Pr ==> X p q)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q";
     ASSUME "!(p:*->bool) r q Pr.
               (p LEADSTO r)Pr /\ X p r /\ (r LEADSTO q)Pr /\ X r q
                                                ==> X p q";
     ASSUME "!(P:(*->bool)->bool) q Pr.
        (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q)
                                                ==> X (LUB P) q";
     ASSUME "((p:*->bool) LEADSTO q)Pr"] (SPEC_ALL LEADSTO_thm37)));;


let LEADSTO_thm39_lemma00 = TAC_PROOF
  (([],
   "!(X:(*->bool)->(*->bool)->bool) Pr.
       ((!p. p In P ==> LEADSTO2 p q Pr) /\ (!p. p In P ==> X p q)) =
        (!p. p In P ==> LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm39_lemma01 = TAC_PROOF
  (([],
   "!(X:(*->bool)->(*->bool)->bool) Pr.
       (!p q.
         ((p ENSURES q)Pr ==>
          LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q)) /\
         (!r.
           (p ENSURES r)Pr /\
           LEADSTO2 r q Pr /\
           (LEADSTO2 r q Pr ==> X r q) ==>
           LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q)) /\
         (!P.
           (!p'.
             p' In P ==>
             LEADSTO2 p' q Pr /\ (LEADSTO2 p' q Pr ==> X p' q)) ==>
           LEADSTO2(LUB P)q Pr /\ (LEADSTO2(LUB P)q Pr ==> X(LUB P)q)))
      =
      (!p q.
        ((p ENSURES q)Pr ==> X p q) /\
        (!r. (p ENSURES r)Pr /\ LEADSTO2 r q Pr /\ X r q ==> X p q) /\
        (!P.
          (!p. p In P ==> LEADSTO2 p q Pr) /\ (!p. p In P ==> X p q) ==>
          X(LUB P)q))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL
    [
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO2_thm1 THEN
     ACCEPT_TAC (REWRITE_RULE
      [ASSUME "((p:*->bool) ENSURES r)Pr";
       ASSUME "LEADSTO2 (r:*->bool) q Pr";
       ASSUME "LEADSTO2 (p:*->bool) q Pr";
       ASSUME "(X:(*->bool)->(*->bool)->bool) r q"]
      (SPEC_ALL (CONJUNCT1 (CONJUNCT2 (SPEC_ALL
       (ASSUME "!(p:*->bool) q.
        ((p ENSURES q)Pr ==> LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q)) /\
        (!r.
          (p ENSURES r)Pr /\ LEADSTO2 r q Pr /\
          (LEADSTO2 r q Pr ==> X r q) ==>
          LEADSTO2 p q Pr /\ (LEADSTO2 p q Pr ==> X p q)) /\
        (!P.
          (!p'. p' In P ==> LEADSTO2 p' q Pr /\ (LEADSTO2 p' q Pr ==> X p' q))
        ==> LEADSTO2(LUB P)q Pr /\ (LEADSTO2(LUB P)q Pr ==> X(LUB P)q))"))))))
    ;
     ASSUME_TAC (REWRITE_RULE [LEADSTO_thm39_lemma00] (CONJ
      (ASSUME "!p:*->bool. p In P ==> LEADSTO2 p q Pr")
      (ASSUME "!p. p In P ==> (X:(*->bool)->(*->bool)->bool) p q"))) THEN
     IMP_RES_TAC LEADSTO2_thm3a THEN
     ASSUME_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
      "!p:*->bool. (p = LUB P) ==> LEADSTO2 p q Pr"))) THEN
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO2_thm0
    ;
     RES_TAC
    ;
     IMP_RES_TAC LEADSTO2_thm1
    ;
     RES_TAC
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL LEADSTO_thm39_lemma00)]
      (ASSUME "!p':*->bool. p' In P ==> (LEADSTO2 p' q)Pr /\
                                        (LEADSTO2 p' q Pr ==> X p' q)")) THEN
     IMP_RES_TAC LEADSTO2_thm3a THEN
     ACCEPT_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
      "!p:*->bool. (p = LUB P) ==> LEADSTO2 p q Pr")))
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL LEADSTO_thm39_lemma00)]
      (ASSUME "!p':*->bool. p' In P ==> (LEADSTO2 p' q)Pr /\
                                        (LEADSTO2 p' q Pr ==> X p' q)")) THEN
     RES_TAC
    ]);;


let LEADSTO_thm39 = prove_thm
  (`LEADSTO_thm39`,
   "!(X:(*->bool)->(*->bool)->bool) p q Pr.
    (!p q. ((p ENSURES q)Pr ==> X p q) /\
            (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ (X r q) ==> X p q) /\
            (!P. (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q)
               ==> X (LUB P) q))
      ==> ((p LEADSTO q)Pr ==> X p q)",
   REWRITE_TAC [LEADSTO_EQ_LEADSTO2] THEN
   REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm39_lemma01] (BETA_RULE
    (SPEC "\(p:*->bool) q Pr. (LEADSTO2 p q Pr /\
                              (LEADSTO2 p q Pr ==> X p q))"
     (REWRITE_RULE [LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam]
        (ASSUME "LEADSTO2 (p:*->bool) q Pr"))))) THEN
   RES_TAC);;


%
  The theorem useful for an induction tactic
%
let LEADSTO_thm40 = prove_thm
  (`LEADSTO_thm40`,
   "!X.
    (!p q Pr. (p ENSURES q)Pr ==> X p q) /\
    (!p r q Pr.
        (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X r q ==> X p q) /\
    (!P q Pr.
        (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q)
            ==> X (LUB P) q)
      ==>
        (!(p:*->bool) q Pr. (p LEADSTO q)Pr ==> X p q)",
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (REWRITE_RULE
   [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q";
    ASSUME "!(p:*->bool) r q Pr. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\
        X r q ==> X p q";
    ASSUME "!P (q:*->bool) Pr. (!p. p In P ==> (p LEADSTO q)Pr) /\
        (!p. p In P ==> X p q) ==> X (LUB P) q"]
     (SPEC_ALL LEADSTO_thm39)) THEN
  RES_TAC);;

%
  Finally let us present the most compact form of the two induction principles
  used in [CM88]
%

%
  The first induction principle (actually a weakening of LEADSTO_thm23):
%
let LEADSTO_thm41 = prove_thm
 (`LEADSTO_thm41`,
  "!X.
        (!p q Pr. (p ENSURES q)Pr ==> X p q Pr) /\
        (!p r q Pr. (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
                        ==> X p q Pr) /\
        (!p P q Pr. (p = LUB P) /\
                  (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                        ==> X p q Pr)
     ==> (!(p:*->bool) q Pr. (p LEADSTO q) Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (UNDISCH (SPEC_ALL (REWRITE_RULE
    [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) r q Pr.
      (p LEADSTO r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) P q Pr. (p = LUB P) /\
                (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                         ==> X p q Pr";
     ASSUME "((p:*->bool) LEADSTO q)Pr"] (SPEC_ALL LEADSTO_thm23)))));;

%
  Now prove the second induction principle:
%
let LEADSTO_thm42_lemma00 = TAC_PROOF
  (([],
   "!X Pr.
       (!p:*->bool. p In P ==> LEADSTO2 p q Pr /\ X p q Pr) =
      ((!p. p In P ==> LEADSTO2 p q Pr) /\ (!p. p In P ==> X p q Pr))"),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let LEADSTO_thm42_lemma01 = TAC_PROOF
  (([],
   "!X Pr.
      (!(p:*->bool) q.
       ((p ENSURES q)Pr ==> X p q Pr) /\
       (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
            ==> X p q Pr) /\
       (!P. (p = (LUB P)) /\
            (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
            ==> X p q Pr))
      =
      (!p q.
       ((p ENSURES q)Pr ==> X p q Pr) /\
       (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X r q Pr ==> X p q Pr) /\
       (!P. (p = (LUB P)) /\
            (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
            ==> X p q Pr))"),
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

let LEADSTO_thm42_lemma02 = TAC_PROOF
  (([],
   "!X Pr.
     (!(p:*->bool) q.
      ((p ENSURES q)Pr ==> X p q Pr) /\
      (!r. (p ENSURES r)Pr /\ LEADSTO2 r q Pr /\ X r q Pr ==> X p q Pr) /\
      (!P. (p = LUB P) /\
           (!p. p In P ==> LEADSTO2 p q Pr) /\
           (!p. p In P ==> X p q Pr) ==> X p q Pr))
    =
     (!p q.
      ((p ENSURES q)Pr ==> LEADSTO2 p q Pr /\ X p q Pr) /\
      (!r. (p ENSURES r)Pr /\ LEADSTO2 r q Pr /\ X r q Pr
               ==> LEADSTO2 p q Pr /\ X p q Pr) /\
      (!P. (!p. p In P ==> LEADSTO2 p q Pr /\ X p q Pr)
               ==> LEADSTO2 (LUB P) q Pr /\ X (LUB P) q Pr))"),
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THENL
    [
     IMP_RES_TAC LEADSTO2_thm0
    ;
     IMP_RES_TAC LEADSTO2_thm1
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [LEADSTO_thm42_lemma00] (ASSUME
      "!p:*->bool. p In P ==> LEADSTO2 p q Pr /\ X p q Pr")) THEN
     IMP_RES_TAC LEADSTO2_thm3
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [LEADSTO_thm42_lemma00] (ASSUME
      "!p:*->bool. p In P ==> LEADSTO2 p q Pr /\ X p q Pr")) THEN
     RES_TAC THEN
     ACCEPT_TAC (REWRITE_RULE [] (SPEC "LUB (P:(*->bool)->bool)" (ASSUME
     "!p. (p = LUB P)
        ==> (X:(*->bool)->(*->bool)->((*->*)list)->bool)p q Pr")))
    ;
     ASSUME_TAC (REWRITE_RULE [SYM (SPEC_ALL LEADSTO_thm42_lemma00)] (CONJ
      (ASSUME "!p:*->bool. p In P ==> LEADSTO2 p q Pr")
      (ASSUME "!p. p In P
            ==> (X:(*->bool)->(*->bool)->((*->*)list)->bool) p q Pr"))) THEN
     RES_TAC THEN
     ASM_REWRITE_TAC []
    ]);;

%
  The strongest version of the second induction theorem:
%
let LEADSTO_thm42 = prove_thm
 (`LEADSTO_thm42`,
   "!X Pr.
     (!(p:*->bool) q.
       ((p ENSURES q)Pr ==> X p q Pr) /\
       (!r. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
           ==> X p q Pr) /\
       (!P. (p = (LUB P)) /\
            (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
            ==> X p q Pr))
     ==> (!(p:*->bool) q. (p LEADSTO q) Pr ==> X p q Pr)",
   REWRITE_TAC [LEADSTO_thm42_lemma01] THEN
   REWRITE_TAC [LEADSTO_EQ_LEADSTO2] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (BETA_RULE (SPEC
     "\(p:*->bool) q Pr. (LEADSTO2 p q Pr) /\ (X p q Pr)" 
       (REWRITE_RULE [LEADSTO2;LEADSTO2Fn_EQ_LEADSTO2Fam;LEADSTO2Fam]
         (ASSUME "LEADSTO2 (p:*->bool) q Pr")))) THEN
   ASSUME_TAC (REWRITE_RULE [LEADSTO_thm42_lemma02] (ASSUME
    "!(p:*->bool) q.
      ((p ENSURES q)Pr ==> X p q Pr) /\
      (!r. (p ENSURES r)Pr /\ LEADSTO2 r q Pr /\ X r q Pr ==> X p q Pr) /\
      (!P. (p = LUB P) /\
           (!p. p In P ==> LEADSTO2 p q Pr) /\ (!p. p In P ==> X p q Pr) ==>
              X p q Pr)")) THEN
   RES_TAC);;

%
  The second induction principle (actually a weakening of LEADSTO_thm42a):
%
let LEADSTO_thm43 = prove_thm
 (`LEADSTO_thm43`,
  "!X.
      (!p q Pr. (p ENSURES q)Pr ==> X p q Pr) /\
      (!p r q Pr. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\ X p r Pr /\ X r q Pr
                        ==> X p q Pr) /\
      (!p P q Pr. (p = (LUB P)) /\
                  (!p. p In P ==> (p LEADSTO q)Pr) /\ (!p. p In P ==> X p q Pr)
                        ==> X p q Pr)
     ==> (!(p:*->bool) q Pr. (p LEADSTO q) Pr ==> X p q Pr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (UNDISCH (SPEC_ALL (REWRITE_RULE
    [ASSUME "!(p:*->bool) q Pr. (p ENSURES q)Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) r q Pr. (p ENSURES r)Pr /\ (r LEADSTO q)Pr /\
                                   X p r Pr /\ X r q Pr ==> X p q Pr";
     ASSUME "!(p:*->bool) P q Pr. (p = LUB P) /\
                                  (!p. p In P ==> (p LEADSTO q)Pr) /\
                                  (!p. p In P ==> X p q Pr) ==> X p q Pr";
     ASSUME "((p:*->bool) LEADSTO q)Pr"] (SPEC_ALL LEADSTO_thm42)))));;


% ****************************************************************************

     The last corollaries using the completion theorem:

  **************************************************************************** %

let LEADSTO_cor13_lemma01 = TAC_PROOF
  (([],
   "!(Q:num->(*->bool)) r s.
       ((((/<=\* Q i) \/* r) /\* ((Q(SUC i)) \/* r)) \/* r)s
      =
       ((/<=\* Q (SUC i)) \/* r)s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [/<=\*;\/*;/\*] THEN
   BETA_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);;

let LEADSTO_cor13 = prove_thm
  (`LEADSTO_cor13`,
   "!(P:num->(*->bool)) Q r st Pr.
       (!i. ((P i) LEADSTO ((Q i) \/* r)) (CONS st Pr)) /\
       (!i. ((Q i) UNLESS r) (CONS st Pr)) ==>
         (!i. ((/<=\* P i) LEADSTO ((/<=\* Q i) \/* r)) (CONS st Pr))",
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   INDUCT_TAC THENL
    [
     ASM_REWRITE_TAC [/<=\*]
    ;
     IMP_RES_TAC UNLESS_cor17 THEN
     ASSUME_TAC (SPEC_ALL
      (ASSUME "!i. ((/<=\* (Q:num->*->bool) i) UNLESS r)(CONS st Pr)")) THEN
     ASSUME_TAC (SPEC "SUC i" (ASSUME
      "!i. (((P:num->(*->bool)) i) LEADSTO ((Q i) \/* r))(CONS st Pr)")) THEN
     ASSUME_TAC (SPEC "SUC i" (ASSUME
       "!i. (((Q:num->(*->bool)) i) UNLESS r)(CONS st Pr)")) THEN
     ASSUME_TAC (REWRITE_RULE
      [ASSUME "((/<=\* (Q:num->*->bool) i) UNLESS r)(CONS st Pr)";UNLESS_thm1]
       (SPECL
        ["/<=\* (Q:num->(*->bool))i";"r:*->bool";"r:*->bool";"CONS(st:*->*)Pr"]
          UNLESS_thm8)) THEN
     ASSUME_TAC (REWRITE_RULE
      [ASSUME "(((Q:num->*->bool)(SUC i)) UNLESS r)(CONS st Pr)";UNLESS_thm1]
       (SPECL
        ["(Q:num->(*->bool))(SUC i)";"r:*->bool";"r:*->bool";"CONS(st:*->*)Pr"]
          UNLESS_thm8)) THEN
     ACCEPT_TAC (REWRITE_RULE
      [REWRITE_RULE [ETA_AX]
         (MK_ABS (GEN "s:*" (SPEC_ALL LEADSTO_cor13_lemma01)));
       SYM (SPEC_ALL (CONJUNCT2 /<=\*))] (REWRITE_RULE
        [ASSUME "((/<=\* (P:num->*->bool)i) LEADSTO ((/<=\* Q i) \/* r))
                   (CONS st Pr)";
         ASSUME "(((P:num->*->bool)(SUC i)) LEADSTO ((Q(SUC i)) \/* r))
                   (CONS st Pr)";
         ASSUME "(((/<=\* (Q:num->*->bool) i) \/* r) UNLESS r)(CONS st Pr)";
         ASSUME "((((Q:num->*->bool)(SUC i)) \/* r) UNLESS r)(CONS st Pr)"]
          (SPECL ["/<=\* (P:num->*->bool)i";"(/<=\* (Q:num->*->bool)i) \/* r";
                  "(P:num->*->bool)(SUC i)";"((Q:num->*->bool)(SUC i)) \/* r";
                  "r:*->bool";"st:*->*";"Pr:(*->*)list"] LEADSTO_thm35)))
     ]);;

% Prove:

   !p q r b p' q' r' b' Pr.
        (p  LEADSTO (q  \/* r))  Pr /\ (q  UNLESS b) Pr /\
        (p' LEADSTO (q' \/* r')) Pr /\ (q' UNLESS b') Pr ==>
            ((p /\* p') LEADSTO ((q /\* q') \/* ((r \/* b) \/* (r' \/* b'))) Pr

 Hint:
   Show that:
       b  ==> (r \/* b) \/* (r' \/* b')
       b' ==> (r \/* b) \/* (r' \/* b')
   use these as assumptions for the unless properties in using the
   weakening theorem we then have
       q  unless (r \/* b) \/* (r' \/* b') in st^Pr,
       q' unless (R \/* B) \/* (R' \/* B') in st^Pr,
   now show that:
       r  ==> (r \/* b) \/* (r' \/* b')
       r' ==> (r \/* b) \/* (r' \/* b')
   use these to derive the leadto properties:
       r  leadsto ((r \/* b) \/* (r' \/* b')) in st^Pr
       r' leadsto ((r \/* b) \/* (r' \/* b')) in st^Pr
   by using the cancellation theorem of leadsto we get
       p  leadsto q  \/* ((r \/* b) \/* (r' \/* b')) in st^Pr
       p' leadsto q' \/* ((r \/* b) \/* (r' \/* b')) in st^Pr
   now we are ready to use the theorem of completion:
       p  leadsto q  \/* ((r \/* b) \/* (r' \/* b')) in st^Pr,
       q  unless (r \/* b) \/* (r' \/* b') in st^Pr,
       p' leadsto q  \/* ((r \/* b) \/* (r' \/* b')) in st^Pr,
       q' unless (r \/* b) \/* (r' \/* b') in st^Pr
    ----------------------------------------------------------------------
      (p /\* p') leadsto (q /\* q')  \/* ((r \/* b) \/* (r' \/* b')) in st^Pr

%

% Prove:

   !p q r p' q' Pr.
     (p  LEADSTO (q  \/* r)) Pr /\ (q  UNLESS r) Pr /\
     (p' LEADSTO (q' \/* r)) Pr /\ (q' UNLESS r) Pr ==>
            ((p /\* p') LEADSTO ((q /\* q') \/* r)) Pr

%
let LEADSTO_cor14 = prove_thm
  (`LEADSTO_cor14`,
   "!(p:*->bool) q r p' q' st Pr.
         (p  LEADSTO (q  \/* r))(CONS st Pr) /\ (q  UNLESS r)(CONS st Pr) /\
         (p' LEADSTO (q' \/* r))(CONS st Pr) /\ (q' UNLESS r)(CONS st Pr)
             ==>
                 ((p /\* p') LEADSTO ((q /\* q') \/* r))(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL ["r:*->bool";"CONS (st:*->*) Pr"] UNLESS_thm1) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((q:*->bool) UNLESS r)(CONS st Pr)";"((r:*->bool) UNLESS r)(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (REWRITE_RULE [OR_OR_lemma] (UNDISCH_ALL (SPECL
    ["q:*->bool";"r:*->bool";"r:*->bool";"r:*->bool";"CONS (st:*->*) Pr"]
     UNLESS_thm7))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((q':*->bool)UNLESS r)(CONS st Pr)";"((r:*->bool) UNLESS r)(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (REWRITE_RULE [OR_OR_lemma] (UNDISCH_ALL (SPECL
    ["q':*->bool";"r:*->bool";"r:*->bool";"r:*->bool";"CONS (st:*->*) Pr"]
     UNLESS_thm7))) THEN
   ASSUME_TAC (SPECL
    ["p:*->bool";"(q:*->bool) \/* r";
     "p':*->bool";"(q':*->bool) \/* r";"r:*->bool";"st:*->*";"Pr:(*->*)list"]
     LEADSTO_thm35) THEN
   RES_TAC THEN
   UNDISCH_TAC "(((p:*->bool) /\* p') LEADSTO
                (((q \/* r) /\* (q' \/* r)) \/* r))(CONS st Pr)" THEN
   ONCE_REWRITE_TAC [SPECL
    ["(q:*->bool) \/* r";"r:*->bool";"q':*->bool"] AND_OR_COMM_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
    ["(r:*->bool) \/* q'";"r:*->bool";"q:*->bool"] OR_COMM_AND_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL OR_AND_DISTR_lemma))] THEN
   ONCE_REWRITE_TAC [SPECL
    ["r:*->bool";"(q:*->bool) /\* q'"] OR_COMM_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;OR_OR_lemma]);;


%
   !p q r b p' q' r' b' Pr.
     (p  LEADSTO (q  \/* r))  Pr /\ (q  UNLESS b)  Pr /\
     (p' LEADSTO (q' \/* r')) Pr /\ (q' UNLESS b') Pr ==>
        ((p /\* p') LEADSTO ((q /\* q') \/* ((r \/* b) \/* (r' \/* b')))) Pr
%
let LEADSTO_cor15 = prove_thm
  (`LEADSTO_cor15`,
   "!(p:*->bool) q r b p' q' r' b' st Pr.
       (p  LEADSTO (q  \/* r))(CONS st Pr)  /\ (q  UNLESS b)(CONS st Pr) /\
       (p' LEADSTO (q' \/* r'))(CONS st Pr) /\ (q' UNLESS b')(CONS st Pr)
         ==>
         ((p /\* p') LEADSTO
          ((q /\* q') \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr)",
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL
    ["b:*->bool";"(r:*->bool) \/* (r' \/* b')"] OR_IMPLY_WEAK_lemma) THEN
   REWRITE_TAC [SYM (SPECL ["b:*->bool";"r:*->bool";"(r':*->bool) \/* b'"]
                OR_ASSOC_lemma)] THEN
   ONCE_REWRITE_TAC [SPECL ["(r':*->bool) \/* b'";"r:*->bool";"b:*->bool"]
                            OR_COMM_OR_lemma] THEN
   DISCH_TAC THEN
   MP_TAC (SPECL
    ["b':*->bool";"(r':*->bool) \/* (r \/* b)"] OR_IMPLY_WEAK_lemma) THEN
   REWRITE_TAC [SYM (SPECL ["b':*->bool";"r':*->bool";"(r:*->bool) \/* b"]
                             OR_ASSOC_lemma)] THEN
   ONCE_REWRITE_TAC [SPECL ["(r:*->bool) \/* b";"r':*->bool";"b':*->bool"]
                             OR_COMM_OR_lemma] THEN
   ONCE_REWRITE_TAC [SPECL ["(r':*->bool) \/* b'";"(r:*->bool) \/* b"]
                            OR_COMM_lemma] THEN
   DISCH_TAC THEN
   MP_TAC (SPECL
    ["r:*->bool";"(b:*->bool) \/* (r' \/* b')"] OR_IMPLY_WEAK_lemma) THEN
   REWRITE_TAC [SYM (SPECL ["r:*->bool";"b:*->bool";"(r':*->bool) \/* b'"]
                            OR_ASSOC_lemma)] THEN
   DISCH_TAC THEN
   MP_TAC (SPECL
    ["r':*->bool";"(b':*->bool) \/* (r \/* b)"] OR_IMPLY_WEAK_lemma) THEN
   REWRITE_TAC [SYM (SPECL ["r':*->bool";"b':*->bool";"(r:*->bool) \/* b"]
                            OR_ASSOC_lemma)] THEN
   ONCE_REWRITE_TAC [SPECL ["(r':*->bool) \/* b'";"(r:*->bool) \/* b"]
                            OR_COMM_lemma] THEN
   DISCH_TAC THEN
   REWRITE_TAC [SYM (SPECL ["(r:*->bool) \/* b";"(r':*->bool) \/* b'";
                            "(q:*->bool) /\* q'"]
                            OR_ASSOC_lemma)] THEN
   ONCE_REWRITE_TAC [SPECL
    ["(((r:*->bool) \/* b) \/* (r' \/* b'))";"(q:*->bool) /\* q'"]
     OR_COMM_lemma] THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((q:*->bool) UNLESS b)(CONS st Pr)";
     "!s:*. b s ==> ((r \/* b) \/* (r' \/* b'))s"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["q:*->bool";"b:*->bool";"((r:*->bool) \/* b) \/* (r' \/* b')";
     "CONS (st:*->*) Pr"]
     UNLESS_thm3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((q':*->bool) UNLESS b')(CONS st Pr)";
     "!s:*. b' s ==> ((r \/* b) \/* (r' \/* b'))s"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["q':*->bool";"b':*->bool";"((r:*->bool) \/* b) \/* (r' \/* b')";
     "CONS (st:*->*) Pr"]
     UNLESS_thm3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["r:*->bool";"((r:*->bool) \/* b) \/* (r' \/* b')";
     "st:*->*";"Pr:(*->*)list"] LEADSTO_thm25)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["r':*->bool";"((r:*->bool) \/* b) \/* (r' \/* b')";
     "st:*->*";"Pr:(*->*)list"] LEADSTO_thm25)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((p:*->bool) LEADSTO (q \/* r))(CONS st Pr)";
     "((r:*->bool) LEADSTO ((r \/* b) \/* (r' \/* b')))(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["p:*->bool";"q:*->bool";"r:*->bool";
     "((r:*->bool) \/* b) \/* (r' \/* b')";"st:*->*";"Pr:(*->*)list"]
     LEADSTO_thm28)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((p':*->bool) LEADSTO (q' \/* r'))(CONS st Pr)";
     "((r':*->bool) LEADSTO ((r \/* b) \/* (r' \/* b')))(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["p':*->bool";"q':*->bool";"r':*->bool";
     "((r:*->bool) \/* b) \/* (r' \/* b')";"st:*->*";"Pr:(*->*)list"]
     LEADSTO_thm28)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((p:*->bool) LEADSTO (q \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr)";
     "((q:*->bool) UNLESS ((r \/* b) \/* (r' \/* b')))(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((p':*->bool) LEADSTO(q' \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr)";
     "((q':*->bool) UNLESS ((r \/* b) \/* (r' \/* b')))(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((p:*->bool) LEADSTO(q \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr) /\
      ((q:*->bool) UNLESS ((r \/* b) \/* (r' \/* b')))(CONS st Pr)";
     "((p':*->bool)LEADSTO(q' \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr) /\
      ((q':*->bool) UNLESS ((r \/* b) \/* (r' \/* b')))(CONS st Pr)"]
     AND_INTRO_THM)) THEN
   UNDISCH_TAC
    "(((p:*->bool) LEADSTO(q \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr) /\
      (q UNLESS ((r \/* b) \/* (r' \/* b')))(CONS st Pr)) /\
      (p' LEADSTO (q' \/* ((r \/* b) \/* (r' \/* b'))))(CONS st Pr) /\
      (q' UNLESS ((r \/* b) \/* (r' \/* b')))(CONS st Pr)" THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC))] THEN
   DISCH_TAC THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
    ["p:*->bool";"q:*->bool";"((r:*->bool) \/* b) \/* (r' \/* b'):*->bool";
     "p':*->bool";"q':*->bool";"st:*->*";"Pr:(*->*)list"]
     LEADSTO_cor14)));;


% Prove:

 |- !P Q R B Pr.
  (!i. ((P i) LEADSTO ((Q i) \/* (R i)))Pr) /\ (!i. ((Q i) UNLESS (B i))Pr) ==>
  (!i. ((/<=\* P i) LEADSTO ((/<=\* Q i) \/* ((\<=/* R i) \/* (\<=/* B i))))Pr)

%
let LEADSTO_cor16_lemma1 = TAC_PROOF
  (([],
   "!(Q:num->(*->bool)) R B i s.
      ((/<=\* Q(SUC i)) \/*
         ((((\<=/* R i) \/* (\<=/* B i)) \/* (\<=/* B i)) \/*
          ((R(SUC i)) \/* (B(SUC i)))))s =
      ((/<=\* Q(SUC i)) \/* ((\<=/* R(SUC i)) \/* (\<=/* B(SUC i))))s"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [\/*;/<=\*;\<=/*;/\*] THEN
   BETA_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);;


let LEADSTO_cor16 = prove_thm
  (`LEADSTO_cor16`,
   "!(P:num->(*->bool)) Q R B st Pr.
      (!i. ((P i) LEADSTO ((Q i) \/* (R i)))(CONS st Pr)) /\
        (!i. ((Q i) UNLESS (B i))(CONS st Pr)) ==>
          (!i. ((/<=\* P i) LEADSTO
              ((/<=\* Q i) \/* ((\<=/* R i) \/* (\<=/* B i)))) (CONS st Pr))",
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   INDUCT_TAC THENL
    [
     ASM_REWRITE_TAC [/<=\* ;\<=/*] THEN
     ASSUME_TAC (ONCE_REWRITE_RULE [OR_ASSOC_lemma] (SPECL
      ["((Q:num->(*->bool))0) \/* (R 0)";"((B:num->(*->bool))0)"]
       OR_IMPLY_WEAK_lemma)) THEN
     ASSUME_TAC (SPEC "0" (ASSUME
      "!i.(((P:num->(*->bool))i) LEADSTO ((Q i) \/* (R i)))(CONS st Pr)")) THEN
     IMP_RES_TAC LEADSTO_cor9
    ;
     ASSUME_TAC (SPEC "SUC i" (ASSUME
      "!i.(((P:num->(*->bool))i) LEADSTO ((Q i) \/* (R i)))(CONS st Pr)")) THEN
     ASSUME_TAC (SPEC "SUC i" (ASSUME
       "!i. (((Q:num->(*->bool)) i) UNLESS (B i))(CONS st Pr)")) THEN
     ASSUME_TAC (SPEC "i:num" (UNDISCH_ALL (SPECL
      ["Q:num->(*->bool)";"B:num->(*->bool)";"CONS st Pr:(*->*)list"]
       UNLESS_cor16))) THEN
     ACCEPT_TAC (REWRITE_RULE [REWRITE_RULE [ETA_AX] 
                         (MK_ABS (GEN "s:*" (SPEC_ALL LEADSTO_cor16_lemma1)))]
     (REWRITE_RULE [SYM (SPEC_ALL (CONJUNCT2 /<=\*))] (REWRITE_RULE
      [ASSUME "((/<=\* (P:num->*->bool) i) LEADSTO
                 ((/<=\* Q i) \/* ((\<=/* R i) \/* (\<=/* B i))))(CONS st Pr)";
       ASSUME "(((P:num->*->bool)(SUC i)) LEADSTO ((Q(SUC i)) \/* (R(SUC i))))
                 (CONS st Pr)";
       ASSUME "(((Q:num->*->bool)(SUC i)) UNLESS (B(SUC i)))(CONS st Pr)";
       ASSUME "((/<=\* (Q:num->*->bool) i) UNLESS (\<=/* B i))(CONS st Pr)"]
         (SPECL
           ["/<=\* (P:num->(*->bool))i";"/<=\* (Q:num->(*->bool))i";
            "(\<=/* (R:num->(*->bool))i) \/* (\<=/* (B:num->(*->bool))i)";
            "\<=/* (B:num->(*->bool))i";
            "(P:num->(*->bool))(SUC i)";"(Q:num->(*->bool))(SUC i)";
            "(R:num->(*->bool))(SUC i)";"(B:num->(*->bool))(SUC i)";
            "st:*->*";"Pr:(*->*)list"]
            LEADSTO_cor15))))
    ]);;

close_theory();;
