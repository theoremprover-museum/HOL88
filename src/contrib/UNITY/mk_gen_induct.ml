% -*- Emacs Mode: fundamental -*- %


%-----------------------------------------------------------------------------%
%
   File:         mk_gen_induct.ml

   Description:  This file proves the theorem of general induction on natural
                 numbers by using the theorem of primitive recursion.

   Authors:      (c) Copyright by Flemming Andersen
   Date:         June 7. 1990
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
%

system `/bin/rm gen_induct.th`;;

new_theory`gen_induct`;;

%-----------------------------------------------------------------------------%
%
	The idea in the proof is that if we can prove a stronger lemma:

		(!m. (!n. n < m ==> P n) ==> P m)) ==> (!m n. n < m ==> P n)

	Since we are able to prove that:

		(!m n. n < m ==> P n) ==> (!m. P m)

	We can conclude the general induction principle on natural numbers
        by weakening (Modus Ponens) the proven lemma.

	We need the following lemmas to prove the theorem:
%
%-----------------------------------------------------------------------------%

%
	!P. (!m n. n <= m ==> P n) ==> (!m. P m)
%
let GEN_INDUCT_lemma1 = prove_thm
  (`GEN_INDUCT_lemma1`,
   "!P. (!m n. n <= m ==> P n) ==> (!m. P m)",
   GEN_TAC THEN
   REWRITE_TAC [LESS_OR_EQ] THEN
   DISCH_TAC THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [LESS_SUC_REFL] (SPECL ["m:num";"m:num"]
     (ASSUME "!(m:num) n. n < m \/ (n = m) ==> P n"))));;

%
	!m n. (n <= m) = (n < SUC m)
%
let GEN_INDUCT_lemma2 = prove_thm
  (`GEN_INDUCT_lemma2`,
   "!m n. (n <= m) = (n < SUC m)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [LESS_OR_EQ] THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         STRIP_ASSUME_TAC (UNDISCH (SPECL ["n:num";"m:num"] LESS_SUC))
        ;
         ASM_REWRITE_TAC [LESS_SUC_REFL]]
     ;
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [SYM
        (ONCE_REWRITE_RULE [DISJ_SYM] (SPECL ["n:num";"m:num"] LESS_THM))]]);;

%
	!P. (!m. (!n. n < m ==> (P n)) ==> (P m)) ==> (!m n. n <= m ==> P n)
%
let GEN_INDUCT_lemma3 = prove_thm
  (`GEN_INDUCT_lemma3`,
   "!P. (!m:num. (!n. n < m ==> (P n)) ==> (P m)) ==>
                   (!m n. n <= m ==> P n)",
   GEN_TAC THEN
   DISCH_TAC THEN
   INDUCT_TAC THENL
     [
      REWRITE_TAC [LESS_OR_EQ;NOT_LESS_0] THEN
      REPEAT STRIP_TAC THEN
      PURE_REWRITE_TAC [ASSUME "n = 0"] THEN
      STRIP_ASSUME_TAC (REWRITE_RULE [NOT_LESS_0]
        (SPEC "0" (ASSUME "!m:num. (!n. n < m ==> P n) ==> P m")))
     ;
      GEN_TAC THEN
      REWRITE_TAC [LESS_OR_EQ] THEN
      ASSUME_TAC (REWRITE_RULE [GEN_INDUCT_lemma2]
       (ASSUME "!n:num. n <= m ==> P n")) THEN
      STRIP_TAC THENL
        [
         RES_TAC
        ;
         ASM_REWRITE_TAC [] THEN
         STRIP_ASSUME_TAC (MP
          (SPEC "SUC m" (ASSUME "!m:num. (!n. n < m ==> P n) ==> P m"))
          (ASSUME "!n. n < (SUC m) ==> P n"))
        ]
     ]);;

%
	!P. (!(m:num). (!n. n < m ==> (P n)) ==> (P m)) ==> (!m. P m)
%
let GEN_INDUCT_thm = prove_thm
  (`GEN_INDUCT_thm`,
   "!P. (!(m:num). (!n. n < m ==> (P n)) ==> (P m)) ==> (!m. P m)",
   GEN_TAC THEN
   STRIP_TAC THEN
   ASSUME_TAC (UNDISCH (SPEC_ALL GEN_INDUCT_lemma3)) THEN
   STRIP_ASSUME_TAC (UNDISCH (SPEC_ALL GEN_INDUCT_lemma1)));;

close_theory();;

