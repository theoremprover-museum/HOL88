%
-------------------------------------------------------------------------------
The numeral library supports numeral representation of numbers (where a
numeral is a list of digits less than a radix, and together with a radix,
represents a single number).

Things to change:

  Support numerals in the parser and pretty printer.
  Finish the definitions and proofs already laid out.

Revision history (most recent first):

* January 1994          John Harrison

  Dependence on |more_lists|, and implicitly |more_arithmetic| removed; this
  mainly involved changing names to those now used in the core:

    SNOC_DEF -> SNOC
    EVERY -> ALL_EL [constant name]
    EVERY_DEF -> ALL_EL [theorem name]

*  The following definitions were required:
*
*    REPLICATE  (no longer required. It is defined in the system list theory)
*               
  and the following theorems:

    ADDL_GREATER
    ADDR_GREATER
    LENGTH_CLAUSES
    LESS_MULT_PLUS_DIFF
    SNOC_BUTLAST
    LESS_LESS_MONO
    NOT_EQ_LESS_EQ
    GREATER_NOT_ZERO
    LESS_IS_NOT_LESS_OR_EQ

  However the following no longer needed to be proved:

    SNOC_APPEND

  The |reduce| library was not actually used, so the load has been eliminated.

* November 1993         John Harrison

  Prove:
    SNOC_APPEND
    BASEN_APPEND
    IS_BASEN_APPEND
    BASEN_TRAILING
    BASEN_LEADING
    NORMALIZED_LENGTHS
    NORMALIZED_BASEN_11
  Strengthened IS_BASEN_CONS.
  Simplified the proof of BASEN_ONTO.

* March-April 1993            Tim Leonard

  Define:
    IS_NORMALIZED
    IS_BASEN
    BASEN
    BASEN_DIGITS
    LOG
  Prove:
    IS_NORMALIZED_NIL
    IS_NORMALIZED_CONS
    IS_BASEN_NIL
    IS_BASEN_CONS
    IS_BASEN_CONS_IMP_LESS
    IS_BASEN_CONS_IMP_IS_BASEN
    BASEN_ZEROS
    BASEN_EMPTY_EQ_0
    BASEN_CONS_0
    BASEN_DIGIT_EQ_DIGIT
    BASEN_EXP_N
    BASEN_LESS_EXP_LENGTH
    BASEN_LESS_OR_EQ_EXP_LENGTH
    BASEN_11
    BASEN_EXP_LESS_OR_EQ
    BASEN_EXP_LESS
    BASEN_ONTO
    BASEN_SNOC
    LOG_1
-------------------------------------------------------------------------------
%

can unlink `numeral.th`;;

new_theory `numeral`;;


%
Define |define|.
%

loadt `define`;;


%
-------------------------------------------------------------------------------
Various arithmetic lemmas.
-------------------------------------------------------------------------------
%

%
NOT_0_IMP_0_LESS =
  |- !n. ~(n = 0) = 0 < n
%

let NOT_0_IMP_0_LESS =
  PROVE (
    "! n. ~(n = 0) = (0 < n)",
    INDUCT_TAC THEN REWRITE_TAC [NOT_LESS_0; NOT_SUC; LESS_0]);;


%
LESS_OR_EQ_IMP_LESS_OR_EQ_ADD =
  |- !m n p. m <= n ==> m <= (n + p)
%

let LESS_OR_EQ_IMP_LESS_OR_EQ_ADD =
  ( GEN_ALL o
    (REWRITE_RULE [LESS_EQ_ADD]) o
    (SPECL ["m: num"; "n: num"; "n + p"])
  ) LESS_EQ_TRANS;;


%
MULT_NONNEG_MONO_LESS_OR_EQ =
  |- !m n. 0 < m ==> n <= (m * n)
%

let MULT_NONNEG_MONO_LESS_OR_EQ =
  PROVE (
    "! m n. 0 < m ==> n <= m * n",
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    INDUCT_TAC THEN
    ASM_REWRITE_TAC [NOT_LESS_0; LESS_0] THEN
    INDUCT_TAC THENL
    [
      REWRITE_TAC [MULT; LESS_OR_EQ]
    ;
      REWRITE_TAC [
        MULT;
        ONCE_REWRITE_RULE [ADD_SYM] ADD;
        LESS_EQ_MONO] THEN
      UNDISCH_TAC "n <= (n * (SUC m))" THEN
      REWRITE_TAC [LESS_OR_EQ_IMP_LESS_OR_EQ_ADD]
    ]);;

%----------------------------------------------------------------------------%
% Compatibility with |more_arithmetic| and |more_lists|. [JRH 94.01.16]      %
%----------------------------------------------------------------------------%

let ADDR_GREATER = prove_thm(`ADDR_GREATER`,
  "!m n p. m < n ==> m < (n + p)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN
  EXISTS_TAC "n:num" THEN ASM_REWRITE_TAC[LESS_EQ_ADD]);;

let ADDL_GREATER = prove_thm(`ADDL_GREATER`,
  "!m n p. m < n ==> m < (p + n)",
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADDR_GREATER);;

let LENGTH_CLAUSES = prove_thm(`LENGTH_CLAUSES`,
  "(LENGTH([]:(*)list) = 0) /\
   (!h t. LENGTH(CONS (h:*) t) = SUC(LENGTH t)) /\
   (!x l. LENGTH(SNOC (x:*) l) = SUC(LENGTH l)) /\
   (!(l1:(*)list) l2. LENGTH(APPEND l1 l2) = (LENGTH l1) + (LENGTH l2)) /\
   (!l:(*)list. LENGTH(REVERSE l) = LENGTH l)",
  REWRITE_TAC[LENGTH; LENGTH_REVERSE; LENGTH_SNOC; LENGTH_APPEND]);;

% deleted by WW 2 Feb. 94
let REPLICATE = new_prim_rec_definition(`REPLICATE`,
  "(REPLICATE 0 (e:*) = []) /\
   (REPLICATE (SUC n) e = CONS e (REPLICATE n e))");;
%

let LESS_MULT_PLUS_DIFF = prove_thm(`LESS_MULT_PLUS_DIFF`,
  "!n k l. k < l ==> ((k * n) + n) <= (l * n)",
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; LESS_EQ_MONO_ADD_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [] [ADD_SYM] THEN
  REWRITE_TAC[LESS_EQ_MONO_ADD_EQ] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[MULT_CLAUSES; LESS_EQ_ADD]);;

let SNOC_BUTLAST = prove_thm(`SNOC_BUTLAST`,
  "!l:(*)list. ~NULL l ==> (SNOC(LAST l)(BUTLAST l) = l)",
  INDUCT_THEN SNOC_INDUCT ASSUME_TAC THEN
  ASM_REWRITE_TAC[NULL; BUTLAST; LAST]);;

let LESS_LESS_MONO = prove_thm(`LESS_LESS_MONO`,
  "!m n p q. m < p /\ n < q ==> (m + n) < (p + q)",
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC "p + n" THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [] [ADD_SYM] THEN
  ASM_REWRITE_TAC[LESS_MONO_ADD_EQ]);;

let NOT_EQ_LESS_EQ = prove_thm(`NOT_EQ_LESS_EQ`,
  "!a b. ~(a = b) = a < b \/ b < a",
  REPEAT GEN_TAC THEN EQ_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LESS] THENL
   [DISCH_THEN(SUBST1_TAC o MATCH_MP LESS_EQUAL_ANTISYM);
    DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[LESS_EQ_REFL]);;

let GREATER_NOT_ZERO = prove_thm(`GREATER_NOT_ZERO`,
  "!x. 0 < x ==> ~(x = 0)",
  GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC LESS_REFL);;

let LESS_IS_NOT_LESS_OR_EQ = prove_thm(`LESS_IS_NOT_LESS_OR_EQ`,
  "!x y. x < y = ~(y <= x)",
  MATCH_ACCEPT_TAC(GSYM NOT_LESS_EQUAL));;

%
-------------------------------------------------------------------------------
Theorems about REPLICATE.
-------------------------------------------------------------------------------
%

let LENGTH_REPLICATE =
  PROVE (
    "! n (e: *). LENGTH (REPLICATE n e) = n",
    INDUCT_TAC THEN
    ASM_REWRITE_TAC [LENGTH; REPLICATE; INV_SUC_EQ]);;


let EVERY_REPLICATE =
  PROVE (
    "! n (e: *). ALL_EL ($= e) (REPLICATE n e)",
    INDUCT_TAC THEN
    ASM_REWRITE_TAC [REPLICATE; ALL_EL]);;


%
-------------------------------------------------------------------------------
Define IS_NORMALIZED.
-------------------------------------------------------------------------------
%

define "IS_NORMALIZED digits =
  (digits = []) \/ (0 < HD digits)";;


%
-------------------------------------------------------------------------------
Theorems about IS_NORMALIZED.
-------------------------------------------------------------------------------
%

let IS_NORMALIZED_NIL =
  prove_thm (`IS_NORMALIZED_NIL`,
    "IS_NORMALIZED []",
    REWRITE_TAC [IS_NORMALIZED]);;

let IS_NORMALIZED_CONS =
  prove_thm (`IS_NORMALIZED_CONS`,
    "! e l. IS_NORMALIZED (CONS e l) = (0 < e)",
    REWRITE_TAC [IS_NORMALIZED;HD;NOT_CONS_NIL]);;


%
-------------------------------------------------------------------------------
Define IS_BASEN.
-------------------------------------------------------------------------------
%

define "IS_BASEN radix digits =
  ALL_EL ($> radix) digits";;


%
-------------------------------------------------------------------------------
Theorems about IS_BASEN.
-------------------------------------------------------------------------------
%

%
IS_BASEN_NIL =
  |- !r. IS_BASEN r[]
%

let IS_BASEN_NIL =
  prove_thm (`IS_BASEN_NIL`,
    "! r. IS_BASEN r []",
    REWRITE_TAC [IS_BASEN; ALL_EL]);;


%
IS_BASEN_CONS =
  |- !r l e. (IS_BASEN r(CONS e l) = e < r /\ IS_BASEN r l)
%

let IS_BASEN_CONS =
  prove_thm (`IS_BASEN_CONS`,
    "! r l e. (IS_BASEN r (CONS e l) = (e < r) /\ (IS_BASEN r l))",
    REWRITE_TAC [IS_BASEN; ALL_EL; GREATER]);;


%
IS_BASEN_CONS_IMP_LESS =
  |- !r l e. 1 < r ==> IS_BASEN r(CONS e l) ==> e < r
%

let IS_BASEN_CONS_IMP_LESS =
  prove_thm (`IS_BASEN_CONS_IMP_LESS`,
    "! r l e. (1 < r) ==> IS_BASEN r (CONS e l) ==> e < r",
    REWRITE_TAC [IS_BASEN; ALL_EL; GREATER] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;


%
IS_BASEN_CONS_IMP_IS_BASEN =
  |- !r l e. 1 < r ==> IS_BASEN r(CONS e l) ==> IS_BASEN r l
%

let IS_BASEN_CONS_IMP_IS_BASEN =
  prove_thm (`IS_BASEN_CONS_IMP_IS_BASEN`,
    "! r l e. (1 < r) ==> IS_BASEN r (CONS e l) ==> IS_BASEN r l",
    REWRITE_TAC [IS_BASEN; ALL_EL; GREATER] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;


%
-------------------------------------------------------------------------------
Define BASEN.
-------------------------------------------------------------------------------
%

let BASEN = new_recursive_definition false list_Axiom `BASEN`
  "(! radix. BASEN radix [] = 0) /\
   (! radix digit digits.
      BASEN radix (CONS digit digits) =
        (digit * radix EXP (LENGTH digits)) + BASEN radix digits)";;


%
-------------------------------------------------------------------------------
Theorems about BASEN.
-------------------------------------------------------------------------------
%

%
A numeral of all zeros has a value of zero.

BASEN_ZEROS =
  |- !r n. BASEN r(REPLICATE n 0) = 0
%

let BASEN_ZEROS =
  prove_thm (`BASEN_ZEROS`,
    "! r n. BASEN r (REPLICATE n 0) = 0",
    GEN_TAC THEN
    INDUCT_TAC THEN
    ASM_REWRITE_TAC [REPLICATE; BASEN; MULT_CLAUSES; ADD_CLAUSES]);;


%
BASEN_EMPTY_EQ_0 =
  |- !r l. 1 < r ==> IS_NORMALIZED l ==> ((BASEN r l = 0) = (l = []))
%

let one_less_exp_lemma =
  let zero_less_exp_lemma =
    PROVE (
      "! n m. 0 < n ==> 0 < n EXP m",
      INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_LESS_0; ZERO_LESS_EXP]) in
  ( (MATCH_MP zero_less_exp_lemma) o
    UNDISCH o
    (REWRITE_RULE [SYM (num_CONV "1")]) o
    (SPECL ["0"; "r: num"])
  ) SUC_LESS;;

let BASEN_EMPTY_EQ_0 =
  prove_thm (`BASEN_EMPTY_EQ_0`,
    "! r l. 1 < r ==> IS_NORMALIZED l ==> ((BASEN r l = 0) = (l = []))",
    let lemma =
      (
        (MATCH_MP ADDR_GREATER) o
        (SPEC "h * (r EXP (LENGTH (l: num list)))") o
        (MATCH_MP ADDL_GREATER) o
        (SPEC "LENGTH (l: num list)")
      ) one_less_exp_lemma in
    GEN_TAC THEN
    LIST_INDUCT_TAC THENL
    [
      REWRITE_TAC [BASEN]
    ;
      INDUCT_TAC THENL
      [
        REWRITE_TAC [IS_NORMALIZED; NOT_CONS_NIL; HD; NOT_LESS_0]
      ;
        REWRITE_TAC [IS_NORMALIZED; HD; LESS_0; NOT_CONS_NIL; BASEN] THEN
        DISCH_TAC THEN
        REWRITE_TAC [NOT_0_IMP_0_LESS; MULT; lemma]
      ]
    ]);;


%
A numeral's leading zeros can be ignored without affecting its value.

BASEN_CONS_0 =
  |- !r l. BASEN r(CONS 0 l) = BASEN r l
%

let BASEN_CONS_0 =
  prove_thm (`BASEN_CONS_0`,
    "! r l. BASEN r (CONS 0 l) = BASEN r l",
    REWRITE_TAC [BASEN; MULT_CLAUSES; ADD_CLAUSES]);;


%
BASEN_SNOC =
  |- !r e l. BASEN r(SNOC e l) = ((BASEN r l) * r) + e
%

let BASEN_SNOC =
  prove_thm (`BASEN_SNOC`,
    "! r e l. BASEN r (SNOC e l) = ((BASEN r l) * r) + e",
    GEN_TAC THEN
    GEN_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [
        SNOC;
        BASEN;
        LENGTH_CLAUSES;
        EXP;
        MULT_CLAUSES;
        ADD_CLAUSES;
        RIGHT_ADD_DISTRIB;
        ADD_ASSOC;
        EQ_MONO_ADD_EQ] THEN
    SUBST_TAC [SPECL ["r: num"; "r EXP (LENGTH (l: num list))"] MULT_SYM] THEN
    REWRITE_TAC [MULT_ASSOC]);;


%
A single-digit numeral has a value equal to the digit.

BASEN_DIGIT_EQ_DIGIT =
  |- !r e. BASEN r[e] = e
%

let BASEN_DIGIT_EQ_DIGIT =
  prove_thm (`BASEN_DIGIT_EQ_DIGIT`,
    "! r e. BASEN r [e] = e",
    REWRITE_TAC [BASEN; LENGTH; EXP; MULT_CLAUSES; ADD_CLAUSES]);;


%
A numeral consisting of 1 followed by zeros has a value of the radix raised
to a power equal to the number of zeros.
%

let BASEN_EXP_N =
  prove_thm (`BASEN_EXP_N`,
    "! r n. BASEN r (CONS 1 (REPLICATE n 0)) = r EXP n",
    GEN_TAC THEN
    INDUCT_TAC THENL
    [
      REWRITE_TAC [
        BASEN;
        EXP;
        LENGTH_REPLICATE;
        REPLICATE;
        MULT_CLAUSES;
        ADD_CLAUSES]
    ;
      REWRITE_TAC [
        BASEN;
        BASEN_ZEROS;
        LENGTH_REPLICATE;
        MULT_CLAUSES;
        ADD_CLAUSES]
    ]);;


%
Every n-digit numeral in base r is less than r^n.

BASEN_LESS_EXP_LENGTH =
  |- !r l. 1 < r ==> IS_BASEN r l ==> (BASEN r l) < (r EXP (LENGTH l))
%

let BASEN_LESS_EXP_LENGTH =
  prove_thm (`BASEN_LESS_EXP_LENGTH`,
    "! (r: num) (l: num list).
      (1 < r) ==> IS_BASEN r l ==> BASEN r l < (r EXP (LENGTH l))",
    let lemma =
      let first =
        ( UNDISCH o
          snd o
          EQ_IMP_RULE o
          (SPECL ["m: num"; "n: num"; "k * n"])
        ) LESS_MONO_ADD_EQ in
      let second =
        ( UNDISCH o
          SPEC_ALL o
          (ONCE_REWRITE_RULE [ADD_SYM])
        ) LESS_MULT_PLUS_DIFF in
      ( (ONCE_REWRITE_RULE [ADD_SYM]) o
        GEN_ALL o
        DISCH_ALL o
        (MATCH_MP LESS_LESS_EQ_TRANS)
      ) (CONJ first second) in
    GEN_TAC THEN
    LIST_INDUCT_TAC THENL
    [
      REWRITE_TAC [
        BASEN;
        LENGTH;
        EXP;
        num_CONV "1";
        LESS_0]
    ;
      PURE_REWRITE_TAC [BASEN;EXP;LENGTH] THEN
      GEN_TAC THEN
      POP_ASSUM (\asm.
        DISCH_THEN (\less_radix.
         DISCH_THEN (\is_basen_cons.
           let is_basen_both = SPEC (rand (concl less_radix)) IS_BASEN_CONS in
            let (head_less, is_basen) =
              CONJ_PAIR (REWRITE_RULE [is_basen_both] is_basen_cons) in
            let tail_less = MP (MP asm less_radix) is_basen in
          ASSUME_TAC tail_less THEN
        ASSUME_TAC head_less))) THEN
      UNDISCH_TAC "(BASEN r l) < (r EXP (LENGTH l))" THEN
      UNDISCH_TAC "h < r" THEN
      REWRITE_TAC [lemma]
    ]);;


%
Every n-digit numeral in base r is less than or equal to r^n - 1.

BASEN_LESS_OR_EQ_EXP_LENGTH =
  |- !r l. 1 < r ==> IS_BASEN r l ==> (BASEN r l) <= ((r EXP (LENGTH l)) - 1)
%

let BASEN_LESS_OR_EQ_EXP_LENGTH =
  save_thm (`BASEN_LESS_OR_EQ_EXP_LENGTH`,
  ( GEN_ALL o
    DISCH_ALL o
    (DISCH "IS_BASEN r l") o
    (MATCH_MP SUB_LESS_OR) o
    UNDISCH_ALL o
    SPEC_ALL
  ) BASEN_LESS_EXP_LENGTH);;


%
BASEN_11 =
  |- !r l1 l2.
      1 < r ==>
      IS_BASEN r l1 ==>
      IS_BASEN r l2 ==>
      (LENGTH l1 = LENGTH l2) ==>
      (BASEN r l1 = BASEN r l2) ==>
      (l1 = l2)
%

let numeral_lemma =
  let exploit thm =
    let t = (SPEC "q: num" (UNDISCH (SPECL ["n: num"; "r: num"] thm))) in
    let t' = (SPEC "q': num" (UNDISCH (SPECL ["n: num"; "r': num"] thm))) in
    let lemma = REWRITE_RULE [ASSUME "((q * n) + r = (q' * n) + r')"] t in
    REWRITE_RULE [lemma] t' in
  GEN_ALL (DISCH_ALL (CONJ (exploit MOD_MULT) (exploit DIV_MULT)));;

let basen_and_eq_lemma =
  let less_radix =
    ASSUME "1 < r" in
  let is_basen_cons_l1 =
    ASSUME "IS_BASEN r(CONS h l1)" in
  let is_basen_cons_l2 =
    ASSUME "IS_BASEN r(CONS h' l2)" in
  let length_eq =
    ASSUME "(LENGTH (l1: num list) = LENGTH (l2: num list))" in
  let is_basen_cons =
    MATCH_MP IS_BASEN_CONS_IMP_IS_BASEN less_radix in
  let is_basen_l1 = MATCH_MP is_basen_cons is_basen_cons_l1 in
  let is_basen_l2 = MATCH_MP is_basen_cons is_basen_cons_l2 in
  let t =
    REWRITE_RULE [LENGTH; length_eq]
    (MATCH_MP (MATCH_MP BASEN_LESS_EXP_LENGTH less_radix) is_basen_l1) in
  let t' =
    REWRITE_RULE [LENGTH]
    (MATCH_MP (MATCH_MP BASEN_LESS_EXP_LENGTH less_radix) is_basen_l2) in
    UNDISCH (SPECL ["h: num"; "h': num"]
      (MATCH_MP (MATCH_MP numeral_lemma t') t));;

let BASEN_11 =
  prove_thm (`BASEN_11`,
    "! r l1 l2. (1 < r) ==> (IS_BASEN r l1) ==> (IS_BASEN r l2) ==>
    (LENGTH l1 = LENGTH l2) ==> (BASEN r l1 = BASEN r l2) ==> (l1 = l2)",
    REPEAT GEN_TAC THEN
    SPEC_TAC ("r: num", "r: num") THEN
    SPEC_TAC ("l2: num list", "l2: num list") THEN
    SPEC_TAC ("l1: num list", "l1: num list") THEN
    REPEAT (INDUCT_THEN list_INDUCT ASSUME_TAC ORELSE GEN_TAC) THENL
    [
    REPEAT DISCH_TAC THEN REFL_TAC
    ;
    REWRITE_TAC [LENGTH; SUC_NOT]
    ;
    REWRITE_TAC [LENGTH; NOT_SUC]
    ;
    PURE_REWRITE_TAC [LENGTH;INV_SUC_EQ;BASEN;CONS_11] THEN
    DISCH_TAC THEN
    DISCH_TAC THEN
    DISCH_TAC THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REWRITE_TAC [basen_and_eq_lemma] THEN
    IMP_RES_TAC IS_BASEN_CONS_IMP_IS_BASEN THEN
    let induction_asm =
      ASSUME "!l2 r. 1 < r ==> IS_BASEN r l1 ==> IS_BASEN r l2 ==>
        (LENGTH l1 = LENGTH l2) ==> (BASEN r l1 = BASEN r l2) ==>
        (l1 = l2)" in
    REWRITE_TAC [MP ((UNDISCH o UNDISCH o UNDISCH o UNDISCH o SPEC_ALL) induction_asm)
      ((hd o CONJUNCTS) basen_and_eq_lemma)]
    ]);;


%
For all normalized, nonzero, n-digit numerals in base r, r^(n - 1) is
less than or equal to the numeral.

BASEN_EXP_LESS_OR_EQ =
  |- !r l.
      1 < r ==>
      ~NULL l ==>
      IS_NORMALIZED l ==>
      IS_BASEN r l ==>
      (r EXP ((LENGTH l) - 1)) <= (BASEN r l)
%

let BASEN_EXP_LESS_OR_EQ =
  prove_thm (`BASEN_EXP_LESS_OR_EQ`,
    "!r l. 1 < r ==> ~NULL l ==> IS_NORMALIZED l ==> IS_BASEN r l ==>
     (r EXP (LENGTH l - 1)) <= (BASEN r l)",
    GEN_TAC THEN
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [
        NULL;
        BASEN;
        LENGTH; num_CONV "1"; SUB_MONO_EQ] THEN
    REWRITE_TAC [
        SYM (num_CONV "1");
        SUB_0] THEN
    GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    IMP_RES_THEN
      (\t. ASSUME_TAC (REWRITE_RULE [HD;NOT_CONS_NIL] t)) IS_NORMALIZED THEN
    REWRITE_TAC [MATCH_MP LESS_OR_EQ_IMP_LESS_OR_EQ_ADD
      ((UNDISCH_ALL o SPECL ["h: num"; "x: num"]) MULT_NONNEG_MONO_LESS_OR_EQ)]);;


%
For all normalized, nonzero, n-digit numerals in base r, r^(n - 1) - 1 is
less than the numeral.

BASEN_EXP_LESS =
  |- !r l.
      IS_BASEN r l ==>
      IS_NORMALIZED l ==>
      ~NULL l ==>
      1 < r ==>
      ((r EXP ((LENGTH l) - 1)) - 1) < (BASEN r l)
%

let BASEN_EXP_LESS =
  save_thm (`BASEN_EXP_LESS`,
  let lemma1 =
    PROVE (
      "! n m. 0 < n ==> (n <= m = (n - 1) < m)",
      INDUCT_TAC THEN
      REWRITE_TAC [
        NOT_LESS_0;
        (GEN_ALL o SYM o SPEC_ALL) LESS_EQ;
        num_CONV "1";
        SUB_MONO_EQ;
        SUB_0]) in
  let lemma2 =
    PROVE (
      "! n m. 1 < n ==> 0 < n EXP m",
      INDUCT_TAC THEN ASM_REWRITE_TAC [ZERO_LESS_EXP; NOT_LESS_0]) in
  let eq = MATCH_MP lemma1
    (UNDISCH_ALL (SPECL ["r: num"; "LENGTH (l: num list) - 1"] lemma2)) in
  ( GEN_ALL o
    DISCH_ALL o
    (REWRITE_RULE [eq]) o
    UNDISCH_ALL o
    SPEC_ALL
  ) BASEN_EXP_LESS_OR_EQ);;


%
Every numeral has a value.

BASEN_ONTO =
  |- !r l. ?n. BASEN r l = n
%

let BASEN_ONTO =
  prove_thm (`BASEN_ONTO`,
    "!r l. ?n. BASEN r l = n",
    REPEAT GEN_TAC THEN EXISTS_TAC "BASEN r l" THEN REFL_TAC);;


%
BASEN_APPEND =
  |- !r l m. BASEN r (APPEND l m) =
     ((r EXP (LENGTH m)) * BASEN r l) + BASEN r m
%

let BASEN_APPEND = prove_thm(`BASEN_APPEND`,
  "!r l m. BASEN r (APPEND l m) =
                ((r EXP (LENGTH m)) * BASEN r l) + BASEN r m",
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; BASEN; MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[LENGTH_APPEND; EXP_ADD] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));;


%
IS_BASEN_APPEND =
  |- !r l m. IS_BASEN r (APPEND l m) = IS_BASEN r l /\ IS_BASEN r m
%

let IS_BASEN_APPEND = prove_thm(`IS_BASEN_APPEND`,
  "!r l m. IS_BASEN r (APPEND l m) = IS_BASEN r l /\ IS_BASEN r m",
  GEN_TAC THEN LIST_INDUCT_TAC THEN TRY(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[IS_BASEN; ALL_EL; APPEND] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[CONJ_ASSOC]);;

%
The value of the trailing digits of a nonzero numeral is the value of the
numeral, modulo a power of the radix.

BASEN_TRAILING =
  |- ! r l. 1 < r ==> IS_BASEN r l ==> ~NULL l ==>
     BASEN r (TL l) = (BASEN r l) MOD r EXP (LENGTH l - 1)
%

let BASEN_TRAILING = prove_thm(`BASEN_TRAILING`,
  "!r l. 1 < r ==> IS_BASEN r l ==> ~NULL l ==>
      (BASEN r (TL l) = (BASEN r l) MOD r EXP (LENGTH l - 1))",
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC "l:num list" list_CASES) THEN
  REWRITE_TAC[NULL; LENGTH; HD; TL; SUC_SUB1] THEN
  STRUCT_CASES_TAC(SPEC "r:num" num_CASES) THEN
  REWRITE_TAC[num_CONV "1"; LESS_MONO_EQ; NOT_LESS_0] THEN
  REWRITE_TAC[BASEN; MATCH_MP MOD_TIMES (SPEC_ALL ZERO_LESS_EXP)] THEN
  REPEAT DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC LESS_MOD THEN
  MP_TAC(SPECL ["SUC n"; "t:num list"] BASEN_LESS_EXP_LENGTH) THEN
  ASM_REWRITE_TAC[num_CONV "1"; LESS_MONO_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_BASEN; ALL_EL]) THEN
  ASM_REWRITE_TAC[IS_BASEN; ALL_EL]);;

%
The value of the leading digits of a nonzero numeral is the value of the
numeral divided by a power of the radix.

BASEN_LEADING =
  |- ! r l. 1 < r ==> IS_BASEN r l ==> ~NULL l ==>
     (BASEN r (BUTLAST l) = (BASEN r l) DIV r)
%

let BASEN_LEADING = prove_thm(`BASEN_LEADING`,
  "!r l. 1 < r ==> IS_BASEN r l ==> ~NULL l ==>
      (BASEN r (BUTLAST l) = (BASEN r l) DIV r)",
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SNOC_BUTLAST) THEN
  REWRITE_TAC[BUTLAST] THEN
  REWRITE_TAC[SNOC_APPEND; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[ADD_CLAUSES; SUC_SUB1] THEN
  REWRITE_TAC[BASEN_APPEND; LENGTH; EXP; MULT_CLAUSES] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC DIV_MULT THEN
  UNDISCH_TAC "IS_BASEN r l" THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SNOC_BUTLAST) THEN
  REWRITE_TAC[LAST] THEN REWRITE_TAC[SNOC_APPEND] THEN
  REWRITE_TAC[IS_BASEN_APPEND; IS_BASEN] THEN
  REWRITE_TAC[BASEN; ALL_EL; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES; GREATER] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

%
If two normalized basen numerals have the same value, then they have the same
length.

NORMALIZED_BASEN_11 =
  |- !l1 l2 r.
        1 < r ==>
        IS_BASEN r l1 ==>
        IS_BASEN r l2 ==>
        IS_NORMALIZED l1 ==>
        IS_NORMALIZED l2 ==>
        (BASEN r l1 = BASEN r l2) ==>
        (LENGTH l1 = LENGTH l2)
%

let NORMALIZED_LENGTHS_LEMMA = prove_thm(`NORMALIZED_LENGTHS_LEMMA`,
  "!l1 l2 r.
     ~(1 < r /\
       IS_BASEN r l1 /\
       IS_BASEN r l2 /\
       IS_NORMALIZED l1 /\
       IS_NORMALIZED l2 /\
       (BASEN r l1 = BASEN r l2) /\
       LENGTH l1 < LENGTH l2)",
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC "l2:num list" list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_LESS_0] THEN REWRITE_TAC[LESS_THM] THEN
  ONCE_REWRITE_TAC[DISJ_SYM] THEN REWRITE_TAC[GSYM LESS_OR_EQ] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
  REWRITE_TAC[BASEN] THEN DISCH_TAC THEN
  MP_TAC(SPECL ["r:num"; "l1:num list"] BASEN_LESS_EXP_LENGTH) THEN
  ASM_REWRITE_TAC[NOT_LESS] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
  EXISTS_TAC "h * (r EXP (LENGTH (t:num list)))" THEN
  REWRITE_TAC[LESS_EQ_ADD] THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
  EXISTS_TAC "r EXP (LENGTH(t:num list))" THEN CONJ_TAC THENL
   [FIRST_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LESS_EQ_EXISTS]) THEN
    REWRITE_TAC[EXP_ADD] THEN ONCE_REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC MULT_NONNEG_MONO_LESS_OR_EQ THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IS_NORMALIZED_CONS]) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC "1 < r" THEN
  STRUCT_CASES_TAC(SPEC "r:num" num_CASES) THEN
  REWRITE_TAC[num_CONV "1"; LESS_MONO_EQ; NOT_LESS_0; ZERO_LESS_EXP]);;

let NORMALIZED_LENGTHS = prove_thm(`NORMALIZED_LENGTHS`,
  "!l1 l2 r.
        1 < r ==>
        IS_BASEN r l1 ==>
        IS_BASEN r l2 ==>
        IS_NORMALIZED l1 ==>
        IS_NORMALIZED l2 ==>
        (BASEN r l1 = BASEN r l2) ==>
        (LENGTH l1 = LENGTH l2)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
  GEN_REWRITE_TAC I [] [GSYM(CONJUNCT1 NOT_CLAUSES)] THEN
  PURE_REWRITE_TAC[DE_MORGAN_THM; NOT_LESS_EQUAL] THEN
  CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC NORMALIZED_LENGTHS_LEMMA THENL
   [MAP_EVERY EXISTS_TAC ["l2:num list"; "l1:num list"; "r:num"];
    MAP_EVERY EXISTS_TAC ["l1:num list"; "l2:num list"; "r:num"]] THEN
  ASM_REWRITE_TAC[]);;


%
If two normalized basen numerals have the same value, then they have the same
digits.

NORMALIZED_BASEN_11 =
  |- !l1 l2 r.
        1 < r ==>
        IS_BASEN r l1 ==>
        IS_BASEN r l2 ==>
        IS_NORMALIZED l1 ==>
        IS_NORMALIZED l2 ==>
        (BASEN r l1 = BASEN r l2) ==> (l1 = l2)
%

let NORMALIZED_BASEN_11 = prove_thm(`NORMALIZED_BASEN_11`,
  "!l1 l2 r.
        1 < r ==>
        IS_BASEN r l1 ==>
        IS_BASEN r l2 ==>
        IS_NORMALIZED l1 ==>
        IS_NORMALIZED l2 ==>
        (BASEN r l1 = BASEN r l2) ==> (l1 = l2)",
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL ["l1:num list"; "l2:num list"; "r:num"] NORMALIZED_LENGTHS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL ["r:num"; "l1:num list"; "l2:num list"] BASEN_11) THEN
  ASM_REWRITE_TAC[]);;


%
-------------------------------------------------------------------------------
Define BASEN_DIGITS.
-------------------------------------------------------------------------------
%

%
div_mod_lemma =
  [1 < r] |- (n = ((n DIV (r EXP m)) * (r EXP m)) + (n MOD (r EXP m))) /\
             (n MOD (r EXP m)) < (r EXP m)
%

let div_mod_lemma =
  ( (SPEC "n: num") o
    (MATCH_MP DIVISION) o
    SPEC_ALL
  ) one_less_exp_lemma;;


%
BASEN covers 0 .. (r EXP m) - 1.

BASEN_ONTO_MOD_LEMMA =
  |- !m n r.
      ?l. 1 < r ==> n < (r EXP m) ==> (LENGTH l = m) /\ (n = BASEN r l)
%

let BASEN_ONTO_MOD_LEMMA =
  PROVE (
    "!m n r.
        ?l. 1 < r ==> n < (r EXP m) ==> (LENGTH l = m) /\ (n = BASEN r l)",
    INDUCT_TAC THEN
    PURE_REWRITE_TAC [EXP;MULT_CLAUSES;ADD_CLAUSES] THENL
    [
      REPEAT GEN_TAC THEN
      REWRITE_TAC [num_CONV "1";LESS_THM;NOT_LESS_0] THEN
      EXISTS_TAC "NIL: num list" THEN
      ASM_REWRITE_TAC [LENGTH;BASEN]
    ;
      REPEAT GEN_TAC THEN
      EXISTS_TAC "CONS (n DIV (r EXP m))
        (@ l. 1 < r ==> (n MOD (r EXP m)) < (r EXP m) ==> (LENGTH l = m) /\ ((n MOD (r EXP m)) = BASEN r l))" THEN
      ASM_REWRITE_TAC [LENGTH; BASEN; INV_SUC_EQ] THEN
      let induct_asm =
        ASSUME "!n r.
        ?l.
         1 < r ==> n < (r EXP m) ==> (LENGTH l = m) /\ (n = BASEN r l)" in
      let exists_lemma =
        ( UNDISCH o
          (CONV_RULE (DEPTH_CONV BETA_CONV)) o
          (REWRITE_RULE [EXISTS_DEF]) o
          (SPECL ["n MOD (r EXP m)"; "r: num"])
        ) induct_asm in
      let [exists_lemma1; exists_lemma2] =
        CONJUNCTS (MP exists_lemma (CONJUNCT2 div_mod_lemma)) in
      DISCH_TAC THEN
      REWRITE_TAC [exists_lemma1; SYM exists_lemma2] THEN
      DISCH_TAC THEN
      ACCEPT_TAC (CONJUNCT1 div_mod_lemma)
    ]);;


%
BASEN_MOD_ONTO_LEMMA =
  |- !n m r.
      ?l. 1 < r ==> (LENGTH l = n) /\ (BASEN r l = m MOD (r EXP n))
%

let BASEN_MOD_ONTO_LEMMA =
  PROVE (
    "! n m r. ?l. 1 < r ==> (LENGTH l = n) /\ (BASEN r l = m MOD (r EXP n))",
    let x =
      SPECL ["n: num"; "m MOD (r EXP n)"; "r: num"] BASEN_ONTO_MOD_LEMMA in
    let y = CONJUNCT2 (SPECL ["m: num"; "n: num"]
      (GEN_ALL div_mod_lemma)) in
    REPEAT GEN_TAC THEN
    STRIP_ASSUME_TAC x THEN
    EXISTS_TAC "l: num list" THEN
    STRIP_TAC THEN
    ASSUME_TAC y THEN
    RES_TAC THEN
    ASM_REWRITE_TAC []);;


%
Prove the existence of a function with the required properties.

BASEN_DIGITS_EXISTS =
  |- ?f.
      !n m r.
       1 < r ==>
       (LENGTH(f r n m) = n) /\ (BASEN r(f r n m) = m MOD (r EXP n))
%

let BASEN_DIGITS_EXISTS =
  PROVE (
    "?f. !n m r. 1 < r ==>
      (LENGTH (f r n m) = n) /\ (BASEN r(f r n m) = m MOD r EXP n)",
    EXISTS_TAC "\r n m. @l. 1 < r ==>
      (LENGTH l = n) /\ (BASEN r l = m MOD r EXP n)" THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN
    CONV_TAC SELECT_CONV THEN
    MATCH_ACCEPT_TAC BASEN_MOD_ONTO_LEMMA);;


%
Introduce the function by a constant specification.

BASEN_DIGITS =
  |- !n m r.
      1 < r ==>
      (LENGTH(BASEN_DIGITS r n m) = n) /\
      (BASEN r(BASEN_DIGITS r n m) = m MOD (r EXP n))
%

let BASEN_DIGITS =
  new_specification `BASEN_DIGITS` [`constant`,`BASEN_DIGITS`]
  BASEN_DIGITS_EXISTS;;


%
-------------------------------------------------------------------------------
Define SELECT_TAC:

Given a goal of this form:
        P (@ x. Q x)
break it into two subgoals:
        ! x. Q x ==> P x                ? x. Q x

For example, given the goal
        (@ x. x < 1) < 2
create two subgoals:
        ! x. x < 1 ==> x < 2            ? x. x < 1

Restrictions:

The select term (@ x. Q x) must not have free variables that are bound by P,
or the tactic is invalid.  Instead, to use it in such a circumstance, remove
the quantifiers in P that bind the free variables in Q (using GEN_TAC, for
example) before using SELECT_TAC.

There may well be other restrictions I haven't thought of.  I haven't thought
about free variables in the assumptions, for example, to see if they cause
problems.
-------------------------------------------------------------------------------
%

%
The internal function dest_compound_select takes a term (`the containing
term`) and a term list (`the bound list`), searches the containing term for a
subterm (`the select term`) headed by `@`, and returns a 3-tuple consisting
of:
  1) the select term.
  2) the modified variable --- a variable with a name that is free in the
     bound list, and with the same type as the variable of the select term.
  3) the modified containing term --- a version of the containing term in
     which the select term is replaced by the modified variable.
%

let SELECT_TAC ((asms: term list), gl) =
  let name_of var = fst (dest_var var) in
  letrec primed name conflicts =
    if mem name conflicts then primed (name ^ `'`) conflicts else name in
  letrec dest_compound_select (conflicts: string list) (tm: term) =
    if is_select tm then
      let (select_var, select_body) = dest_select tm in
      let new_var_name = primed (name_of select_var) conflicts in
      let new_var = mk_var (new_var_name, type_of select_var) in
      (tm, new_var, new_var)
    else if is_abs tm then
      let (abs_var, abs_body) = dest_abs tm in
      let conflicts' = (name_of abs_var) . conflicts in
      let restore_abs (select_tm, new_var, containing_tm) =
        (select_tm, new_var, mk_abs(abs_var, containing_tm)) in
      restore_abs (dest_compound_select conflicts' abs_body)
    else
      let (operator, operand) = dest_comb tm in
      ( let restore_operand (select_tm, new_var, containing_tm) =
          (select_tm, new_var, mk_comb(containing_tm, operand)) in
        restore_operand (dest_compound_select conflicts operator) )
      ?
      let restore_operator (select_tm, new_var, containing_tm) =
        (select_tm, new_var, mk_comb(operator, containing_tm)) in
        restore_operator (dest_compound_select conflicts operand) in
  let SELECT_MP_LEMMA =
    PROVE (
      "! P Q. (! x: *. Q x ==> P x) ==> (? x. Q x) ==> P (@ x. Q x)",
      GEN_TAC THEN
      GEN_TAC THEN
      DISCH_TAC THEN
      PURE_ONCE_REWRITE_TAC [EXISTS_DEF] THEN
      BETA_TAC THEN
      ASM_REWRITE_TAC []) in
  let asms_frees = flat (map frees asms) in
  let conflicts =
    map (fst o dest_var) asms_frees in
  let (select_tm, new_var, containing_tm) =
    dest_compound_select conflicts gl in
  let P = mk_abs (new_var, containing_tm) in
  let Q = snd (dest_comb select_tm) in
  let prove_beta pred =
    PROVE (mk_eq (mk_comb (pred,new_var), snd (dest_abs pred)),
      BETA_TAC THEN REFL_TAC) in
  let specialized_lemma =
    ( (PURE_ONCE_REWRITE_RULE [prove_beta Q]) o
      (PURE_ONCE_REWRITE_RULE [prove_beta P]) o
      (ISPECL [mk_abs (new_var, containing_tm);
               snd (dest_comb select_tm)])
      ) SELECT_MP_LEMMA in
  let sg1,sg2 =
    ( I # (fst o dest_imp) o
      dest_imp o
      snd o
      dest_thm
    ) specialized_lemma in
  let subgoals = [ (asms,sg1); (asms,sg2) ] in
  let justification =
    \[th1;th2]. MATCH_MP (MATCH_MP specialized_lemma th1) th2 in
  (subgoals, justification);;


%
-------------------------------------------------------------------------------
More theorems about EXP.
-------------------------------------------------------------------------------
%

let EXP_1 =
  PROVE (
    "! r. r EXP 1 = r",
    REWRITE_TAC [num_CONV "1"; EXP; MULT_CLAUSES; ADD_CLAUSES]);;


let MULT_POS_MONO =
  PROVE (
    "! m n. 0 < n ==> m <= (m * n)",
    GEN_TAC THEN
    INDUCT_TAC THEN
    REWRITE_TAC [NOT_LESS_0; MULT_CLAUSES; LESS_EQ_ADD]);;


let POS_EXP_POS =
  PROVE (
    "! r x. 0 < r ==> 0 < x ==> r <= r EXP x",
    let lemma =
      GEN_ALL (
        MP (SPECL ["SUC n"; "(SUC n) EXP m"] MULT_POS_MONO)
           (SPEC_ALL ZERO_LESS_EXP)) in
    REPEAT (INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0]) THEN
    REWRITE_TAC [EXP; lemma]);;


let LESS_LEMMA1 = theorem `prim_rec` `LESS_LEMMA1`;;

let LESS_MONO_REV = theorem `arithmetic` `LESS_MONO_REV`;;


let MULT_LESS_MULT =
  PROVE (
    "! m n p q. m < n ==> p < q ==> (m * p) < (n * q)",
    REPEAT (INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_LESS_0; LESS_SUC]) THENL
    [
      REWRITE_TAC [MULT_CLAUSES; LESS_0; ADD_CLAUSES]
    ;
      REWRITE_TAC [MULT_CLAUSES; LESS_0; ADD_CLAUSES]
    ;
      REWRITE_TAC [MULT_CLAUSES; LESS_0; ADD_CLAUSES]
    ;
      REPEAT DISCH_TAC THEN
      ONCE_REWRITE_TAC [MULT_CLAUSES] THEN
      IMP_RES_TAC LESS_MONO_REV THEN
      RES_TAC THEN
      IMP_RES_TAC LESS_LESS_MONO
    ]);;


let MULT_POS_STRICT_MONO =
  PROVE (
    "! m n p. n < p ==> n < ((SUC m) * p)",
    REWRITE_TAC [MULT_CLAUSES; ADDL_GREATER]);;


let EXP_LESS_EXP =
  PROVE (
    "! m n n'. 1 < m ==> n < n' ==> (m EXP n) < (m EXP n')",
    INDUCT_TAC THENL
    [
      REWRITE_TAC [NOT_LESS_0]
    ;
      POP_ASSUM (\t. ALL_TAC)
    ] THEN
    SPEC_TAC ("m: num", "m: num") THEN
    INDUCT_TAC THEN
    REWRITE_TAC [num_CONV "1"; LESS_MONO_EQ; NOT_LESS_0] THEN
    POP_ASSUM (\t. REWRITE_TAC [LESS_0]) THEN
    GEN_TAC THEN
    INDUCT_TAC THEN
    REWRITE_TAC [NOT_LESS_0] THEN
    DISCH_TAC THEN
    IMP_RES_TAC LESS_LEMMA1 THENL
    [
      ASM_REWRITE_TAC [LESS_EXP_SUC_MONO]
    ;
      ALL_TAC
    ] THEN
    REWRITE_TAC [EXP] THEN
    RES_TAC THEN
    UNDISCH_TAC "((SUC(SUC m)) EXP n) < ((SUC(SUC m)) EXP n')" THEN
    REWRITE_TAC [MULT_POS_STRICT_MONO]);;


%
EXP_2_STRICT_MONO =
  |- !m n. 1 < m ==> 1 < n ==> m < (m EXP n)
%

let EXP_2_STRICT_MONO =
  ( GEN_ALL o
    (REWRITE_RULE [SYM (num_CONV "1")]) o
    (REWRITE_RULE [num_CONV "1"; EXP; MULT_CLAUSES; ADD_CLAUSES]) o
    (SPECL ["m: num"; "1"; "n: num"])
  ) EXP_LESS_EXP;;


let NUM_CASES_DISJ =
  PROVE (
    "! n m. m < n \/ (m = n) \/ (n < m)",
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC "(m: num) = n" THEN
    ASM_REWRITE_TAC [GSYM NOT_EQ_LESS_EQ]);;


let MULT_POS_STRICT_MONO2 =
  PROVE (
    "! m n1 n2. 0 < m ==> ((m * n1) < (m * n2) = n1 < n2)",
    INDUCT_TAC THEN REWRITE_TAC [NOT_LESS_0; LESS_MULT_MONO]);;


%
-------------------------------------------------------------------------------
Define LOG.
-------------------------------------------------------------------------------
%

define "LOG r n =
  @ x. (r EXP x) <= n /\ n < (r EXP (x + 1))";;


%
-------------------------------------------------------------------------------
Theorems about LOG.
-------------------------------------------------------------------------------
%

let LOG_1 =
  prove_thm (`LOG_1`,
    "! r. 1 < r ==> (LOG r 1 = 0)",
    REWRITE_TAC [LOG] THEN
    GEN_TAC THEN
    DISCH_TAC THEN
    SELECT_TAC THENL
    [
      GEN_TAC THEN
      UNDISCH_TAC "1 < r" THEN
      DISCH_TAC THEN
      DISJ_CASES_TAC (SPEC "x: num" LESS_0_CASES) THENL
      [
        ASM_REWRITE_TAC [UNDISCH (SPEC "r: num" GREATER_NOT_ZERO); DE_MORGAN_THM]
      ;
        ASM_REWRITE_TAC [UNDISCH (SPEC "x: num" GREATER_NOT_ZERO); DE_MORGAN_THM]
      ] THEN
      DISJ1_TAC THEN
      REWRITE_TAC [GSYM LESS_IS_NOT_LESS_OR_EQ] THEN
      SUBGOAL_THEN "1 < r /\ r <= (r EXP x)"
        (\thm. ACCEPT_TAC (MATCH_MP LESS_LESS_EQ_TRANS thm)) THEN
      ASM_REWRITE_TAC [LESS_OR_EQ] THEN
      IMP_RES_TAC (GSYM (REWRITE_RULE [SYM (num_CONV "1"); LESS_OR_EQ] (SPEC "0" LESS_OR))) THENL
      [
        DISJ1_TAC THEN
        IMP_RES_TAC EXP_2_STRICT_MONO
      ;
        DISJ2_TAC THEN
        ASM_CASES_TAC "r = 0" THEN
        RES_TAC THEN
        ASM_REWRITE_TAC [num_CONV "1"; EXP; MULT_CLAUSES; ADD_CLAUSES]
      ]
    ;
      EXISTS_TAC "0" THEN
      REWRITE_TAC [
        num_CONV "1";
        LESS_OR_EQ;
        EXP;
        MULT_CLAUSES;
        ADD_CLAUSES] THEN
      ASM_REWRITE_TAC [SYM (num_CONV "1")]
    ]);;


close_theory ();;

