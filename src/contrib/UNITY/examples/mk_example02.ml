% -*- Emacs Mode: fundamental -*- %


%------------------------------------------------------------------------------

   File:         mk_example02.ml

   Author:       (c) Copyright Flemming Andersen 1990
   Date:         August 23, 1990

   Description:  

      This example is a slightly modified version of the example:

	Parallel Program Design, A Foundation
	K. Mani Chandy & Jayadev Misra.
	Page 139-140.

      This small example is a (rudimentary) example of the readers writers
      problem. The program intuitively ensures progress for writers, but to
      ease proving I changed the program in one statement.

      The modification was made in the assignment {set-b} such that this
      statement is only enabled if the variable B was not already TRUE.  In
      addition the boolean variable B is represented as an integer variable
      having the state dependant value 0 (zero) as FALSE and the value 1 for
      TRUE.

      One of the purposes if this example is to show how one may represent and
      work with programs containing integer variables and how one may
      primitively solve the representation of different variable types. The
      solution may be improved by choosing another way of representing the
      program state.

      The example still has to be completed with the proof of two program
      properties.

------------------------------------------------------------------------------%


%
   First we start by initiating the HOL system:
%

%
   Remove a potentially old example theory
%
system `/bin/rm example02.th`;;

%
   Load the unity prototype system into HOL
%
loadt`l_unity`;;

%
   Define a new theory for elaborating the example.
%
new_theory`example02`;;

% =========================================================================== %
%
   Now we are ready to start the work on the example:
%
% =========================================================================== %

% --------------------------------------------------------------------------- %
%
   This example will not be complete but only contain enough details and proofs
   to give an introductionary understanding of how to work with the current
   HOL-UNITY prototype system.

   First we prove some lemmas about the specification, next we define a
   representation of the example UNITY program and finally we prove that one
   of the assumed safety properties are really satisfied by the given program.

   These three steps in the example are supposed to represent a way of working
   with the present prototype system.

%
% --------------------------------------------------------------------------- %



% --------------------------------------------------------------------------- %
%
   Lemmas derived from the given specification:
%
% --------------------------------------------------------------------------- %

%
   We define the boolean variable b by an integer variable representing true
   if equal to one (s b = 1) and false otherwise
%

%
  The example in the book specifies that for any k, if we are in a state
  satisfying (nr = k) /\ (k > 0), then the example program in a finite number
  of program transitions must arrive a state s' in which ~(nr = k) is satisfied
  In UNITY this is formally specified as:

     (!k. (nr = k) /\ (k > 0) leadsto ~(nr = k) Pr

  Such predicates are actually state abstracted properties in which the logical
  expressions implicitly takes a state as argument. That is, the variable nr
  has a value (s nr) in the state s.

  The PSP theorem allows us to derive a stronger leadsto property having a
  (weaker) leadsto property and an unless property:

        p --> q,      r unless b
      ----------------------------
        p /\ r --> (q /\ r) \/ b

  we use the theorem (LEADSTO_thm29) to prove a theorem using the prototype
  system. The chosen proof corresponds to one of the proofs given in the
  book example.
%


% --------------------------------------------------------------------------- %
%
   Defining a program representation: 
%
% --------------------------------------------------------------------------- %

% PROGRAM VARIABLES %
%-------------------%
%
  We start by defining an enumerated like type representing the variables
  NR, NW, NQ and B as named constants in the program.
%
let Vtype_Axiom = define_type `Vtype_Axiom` `Vtype = NR | NW | NQ | B`;;

%
  To prove the needed properties, we must have some additionally information
  about the type:
%
let exists_Vtype_thm = prove_rec_fn_exists Vtype_Axiom 
      "(f NR = 0) /\ (f NW = 1) /\ (f NQ = 2) /\ (f B = 3)";;

%
  Now we are able to prove the trivial Vtype theorem, that all variables are
  distinct.
%
let Vtype_thm1 = TAC_PROOF
  (([],
   "~(NR = NW) /\ ~(NW = NR) /\ ~(NR = NQ) /\ ~(NQ = NR) /\
    ~(NR =  B) /\ ~(B  = NR) /\ ~(NW = NQ) /\ ~(NQ = NW) /\
    ~(NW =  B) /\ ~(NQ = NW) /\ ~(NQ =  B) /\ ~(B  = NQ)"),
   STRIP_ASSUME_TAC exists_Vtype_thm THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM (\thm. MP_TAC
     (CONJ (REWRITE_RULE [thm] (ASSUME "(f:Vtype->num) NR = 0"))
     (CONJ (REWRITE_RULE [thm] (ASSUME "(f:Vtype->num) NW = 1"))
     (CONJ (REWRITE_RULE [thm] (ASSUME "(f:Vtype->num) NQ = 2"))
           (REWRITE_RULE [thm] (ASSUME "(f:Vtype->num) B  = 3")))))) THEN
   ASM_REWRITE_TAC [num_CONV "3";num_CONV "2";num_CONV "1"] THEN
   REWRITE_TAC [INV_SUC_EQ] THEN
   REWRITE_TAC [NOT_SUC] THEN
   REWRITE_TAC [ONCE_REWRITE_RULE [EQ_SYM_EQ] NOT_SUC]);;


% PROGRAM REPRESENTATION %
%------------------------%
%
  In order to be able to define a UNITY program as a set (list representation)
  of state transitions we need to define every conditional assignment in terms
  a state transition function.

  Having such a function (MK_COND) we can represent a UNITY program as a list
  of such functions.
%

%
   We define a state transition function STr, which updates a variable nm to a
   value given by the state dependent expression v. The value of v i defined by
   the state s. ST returns a new state that is defined by s' except that the
   variable nm is given tha value of v in the state s.
%
let ST = new_definition
  (`ST`,
   "ST ((nm:Vtype),(val:(Vtype->num)->num)) s s' =
         (\n. (n = nm) => (val s) | (s' n))");;

%
   We now define the function STL, which reflects the state transition as
   a result of a set (list representation) of assignments by recursively
   using the ST function for the state transition given by each assignment.
%
let STL = new_recursive_definition false list_Axiom `STL`
   "(STL (s:Vtype->num) s' [] = s') /\
    (STL s s' (CONS (as:(Vtype#((Vtype->num)->num))) asl) =
                          (STL s (ST as s s') asl))";;

%
   Finally a UNITY assignment is a conditional state transition defined by a
   state dependent enabling condition c and a list of parallel assignments.
%
let MK_COND = new_definition (`MK_COND`,
   "MK_COND (c, asl) (s:Vtype->num) = ((c s) => (STL s s asl) | s)");;

let COND_lemma1a = TAC_PROOF
  (([],
   "!c nm n val s nx. (MK_COND (c, [(nm,val)]) (s:Vtype->num)) nx =
           (\s n. (((n = nm) /\ (c s)) => val s | s n))s nx"),
   REWRITE_TAC [MK_COND;STL;ST] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REPEAT COND_CASES_TAC THENL
    [
     BETA_TAC THEN
     ONCE_REWRITE_TAC [CONJUNCT1 (ASSUME "((nx:Vtype) = nm) /\ T")] THEN
     REWRITE_TAC []
    ;
     BETA_TAC THEN
     REWRITE_TAC
      [REWRITE_RULE [NOT_CLAUSES] (ASSUME "~(((nx:Vtype) = nm) /\ T)")]
    ;
     MP_TAC
      (REWRITE_RULE [NOT_CLAUSES] (ASSUME "((nx:Vtype) = nm) /\ F")) THEN
     REWRITE_TAC []
    ;
     REWRITE_TAC []
    ]);;

%
  |- !c nm val.
         MK_COND(c,[nm,val]) = (\s n. (((n = nm) /\ c s) => val s | s n))
%
let COND_lemma1 =
   (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:Vtype->num"
     (REWRITE_RULE [ETA_AX] (MK_ABS
       (GEN "nx:Vtype" (SPEC_ALL COND_lemma1a))))))));;

let COND_lemma2a = TAC_PROOF
  (([],
   "!c nm n val s nx. (MK_COND (c, [(nm,val)]) (s:Vtype->num)) nx =
           (\s n. ((n = nm) => ((c s) => (val s) | (s n)) | s n))s nx"),
   REWRITE_TAC [MK_COND;STL;ST] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REPEAT COND_CASES_TAC THENL
    [
     BETA_TAC THEN
     ONCE_REWRITE_TAC [(ASSUME "((nx:Vtype) = nm)")] THEN
     REWRITE_TAC []
    ;
     BETA_TAC THEN
     REWRITE_TAC [(ASSUME "~((nx:Vtype) = nm)")]
    ;
     REWRITE_TAC []
    ;
     REWRITE_TAC []
    ]);;

%
  |- !c nm val.
       MK_COND(c,[nm,val]) = (\s n. ((n = nm) => (c s => val s | s n) | s n))
%
let COND_lemma2 =
   (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:Vtype->num"
     (REWRITE_RULE [ETA_AX] (MK_ABS
       (GEN "nx:Vtype" (SPEC_ALL COND_lemma2a))))))));;

let COND_lemma3a = TAC_PROOF
  (([],
   "!c nm n val s nx. (MK_COND (c, [(nm,val)]) (s:Vtype->num)) nx =
           (\s n. ((c s) => ((n = nm) => (val s) | (s n)) | s n))s nx"),
   REWRITE_TAC [MK_COND;STL;ST] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REPEAT COND_CASES_TAC THENL
    [
     BETA_TAC THEN
     ONCE_REWRITE_TAC [(ASSUME "((nx:Vtype) = nm)")] THEN
     REWRITE_TAC []
    ;
     BETA_TAC THEN
     REWRITE_TAC [(ASSUME "~((nx:Vtype) = nm)")]
    ;
     REWRITE_TAC []
    ;
     REWRITE_TAC []
    ]);;

%
  |- !c nm val.
        MK_COND(c,[nm,val]) = (\s n. (c s => ((n = nm) => val s | s n) | s n))
%
let COND_lemma3 =
   (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:Vtype->num"
     (REWRITE_RULE [ETA_AX] (MK_ABS
       (GEN "nx:Vtype" (SPEC_ALL COND_lemma3a))))))));;

let COND_lemma4a = TAC_PROOF
  (([],
   "!(c:(Vtype->num)->bool) nm val s nx.
      (MK_COND (c, (CONS (nm,val) asl)) s) nx
     =
      (\s. (c s => STL s (MK_COND (c, [(nm,val)]) s) asl | s))s nx"),
   REWRITE_TAC [MK_COND;STL;ST] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REPEAT COND_CASES_TAC THENL
    [
     REWRITE_TAC []
    ;
     REWRITE_TAC []
    ]);;

%
  |- !c nm val asl.
       MK_COND(c, CONS (nm, val) asl)
     =
       (\s. (c s => STL s (MK_COND(c, [(nm,val)])s) asl | s))
%
let COND_lemma4 =
   (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:Vtype->num"
     (REWRITE_RULE [ETA_AX] (MK_ABS
       (GEN "nx:Vtype" (SPEC_ALL COND_lemma4a))))))));;

let COND_lemma5a = TAC_PROOF
  (([],
   "!(c:(Vtype->num)->bool) nm val s nx.
     MK_COND(c,CONS(nm,val)asl)s nx =
       (c s => STL s(\n. (((n = nm) /\ c s) => val s | s n))asl | s)nx"),
   REWRITE_TAC [MK_COND;STL;ST] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REPEAT COND_CASES_TAC THENL
    [
     REWRITE_TAC []
    ;
     REWRITE_TAC []
    ]);;

%
  |- !c nm val asl.

      MK_COND(c,CONS(nm,val)asl)
   =
      (\s. (c s => STL s(\n. (((n = nm) /\ c s) => val s | s n))asl | s))
%
let COND_lemma5 =
   (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:Vtype->num"
     (REWRITE_RULE [ETA_AX] (MK_ABS
       (GEN "nx:Vtype" (SPEC_ALL COND_lemma5a))))))));;

let COND_lemma6a = TAC_PROOF
  (([],
   "!(c:(Vtype->num)->bool) nm val s nx.
     MK_COND(c,CONS(nm,val)asl)s nx =
       (c s => STL s(\n. ((n = nm) => val s | s n))asl | s)nx"),
   REWRITE_TAC [MK_COND;STL;ST]);;

%
  |- !c nm val asl.
    MK_COND(c,CONS(nm,val)asl) =
    (\s. (c s => STL s(\n. ((n = nm) => val s | s n))asl | s))
%
let COND_lemma6 =
   (GEN_ALL (REWRITE_RULE [ETA_AX] (MK_ABS (GEN "s:Vtype->num"
     (REWRITE_RULE [ETA_AX] (MK_ABS
       (GEN "nx:Vtype" (SPEC_ALL COND_lemma6a))))))));;

% --------------------------------------------------------------------------- %
%
   Defining the program:
%
% --------------------------------------------------------------------------- %

% CONCRETE PROGRAM %
%------------------%
%
   The previous definition allows us to define the example program in the
   following way:
%
let t = "\s:Vtype->num. N - ((s NR) + (N * (s NW)))";;

let startwrite = "MK_COND((\s:Vtype->num. (^t s) >= 1 /\ ~((s B) = 1)),
                          [NR, (\s. (s NR) + 1)])";;
let endwrite  = "MK_COND(TRUE, [NR, (\s. (s NR) - 1)])";;
let startread = "MK_COND((\s. ((^t s) >= N) /\ (s NQ) > 0),
               [(NW, (\s. (s NW) + 1));(NQ, (\s. (s NQ) - 1));(B, (\s. 0))])";;
let endread   = "MK_COND(TRUE, [NW, (\s. (s NW) - 1)])";;
let set_b     = "MK_COND(~* (\s. s B = 1), [B,  (\s. (s NQ) > 0 => 1 | 0)])";;

let Prog = "[^startwrite;^endwrite;^startread;^endread;^set_b]";;


% --------------------------------------------------------------------------- %
%
   Now we may prove the properties given in the specification example as
   follows:
%
% --------------------------------------------------------------------------- %


%
   To make the proving easier, we use the lemmas:
   (Such lemmas are obvious to the reader but unfortunately not easy to prove
    in HOL)
%
let U9_lemma1 = TAC_PROOF
  (([],
   "!k. k > 0 ==> (k - 1) < k"),
   INDUCT_TAC THENL
     [
      REWRITE_TAC [NOT_LESS_0;GREATER;LESS_REFL]
     ;
      DISCH_TAC THEN
      REWRITE_TAC [SYM (SPEC "SUC k" PRE_SUB1);PRE;LESS_SUC_REFL]
     ]);;

let U9_lemma2 = TAC_PROOF
   (([],
    "!N M. ~((N - M) > N)"),
    REWRITE_TAC [GREATER] THEN
    INDUCT_TAC THENL
      [
       REWRITE_TAC [SUB_0;LESS_REFL]
      ;
       REWRITE_TAC [SUB] THEN
       GEN_TAC THEN
       REPEAT COND_CASES_TAC THENL
         [
          REWRITE_TAC [NOT_LESS_0]
         ;
          ASM_REWRITE_TAC [LESS_MONO_EQ]
         ]]);;

let U9_lemma3 = TAC_PROOF
  (([],
   "!(n:num) m. ((SUC n) - (SUC m)) = (n - m)"),
   INDUCT_TAC THENL
     [
      INDUCT_TAC THEN
      REWRITE_TAC [SUB;LESS_SUC_REFL;LESS_0]
     ;
      INDUCT_TAC THEN
      ONCE_REWRITE_TAC [SUB] THEN
      ASM_REWRITE_TAC [LESS_MONO_EQ]
     ]);;

let U9_lemma4 = TAC_PROOF
  (([],
   "!n m. (n - m) < (SUC n)"),
   INDUCT_TAC THENL
     [
      REWRITE_TAC [SUB_0;LESS_0]
     ;
      INDUCT_TAC THENL
        [
         REWRITE_TAC [SUB_0;LESS_SUC_REFL]
        ;
         REWRITE_TAC [U9_lemma3] THEN
         ACCEPT_TAC (REWRITE_RULE
          [ASSUME "!m. (n - m) < (SUC n)";(SPEC "SUC n" LESS_SUC_REFL)]
            (SPECL ["n - m";"SUC n";"SUC (SUC n)"] LESS_TRANS))
        ]
     ]);;

let U9_lemma5 = TAC_PROOF
  (([],
   "!(N:num) k. (k > 0) ==> (N > 0) ==> ((N - (k + (N * (s NW)))) < N)"),
   REWRITE_TAC [GREATER] THEN
   INDUCT_TAC THENL
     [
      REWRITE_TAC [NOT_LESS_0]
     ;
      INDUCT_TAC THENL
        [
         REWRITE_TAC [NOT_LESS_0]
        ;
         REWRITE_TAC
          [ADD;U9_lemma3;
           SPECL ["N:num";"k + ((SUC N) * (s NW))"] U9_lemma4]
        ]
     ]);;

let U9_lemma6 = TAC_PROOF
  (([],
   "!n m. (n < m) = ~(n >= m)"),
   REWRITE_TAC [GREATER_OR_EQ;DE_MORGAN_THM] THEN
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ACCEPT_TAC (REWRITE_RULE [(SPECL ["m:num";"n:num"] LESS_ANTISYM)]
          (CONJ (REWRITE_RULE [GREATER] (ASSUME "n > m"))
                (ASSUME "n < m")))
        ;
         ACCEPT_TAC (REWRITE_RULE [ASSUME "(n:num) = m";LESS_REFL]
                       (ASSUME "n < m"))
        ]
     ;
      ONCE_REWRITE_TAC [GREATER;EQ_SYM_EQ] THEN
      REWRITE_TAC [LESS_CASES_IMP]
     ]);;

%
  |- !N k. k > 0 ==> N > 0 ==> ~(N - (k + (N * (s NW)))) >= N
%
let U9_lemma7 = REWRITE_RULE [U9_lemma6] U9_lemma5;;

%
   Let us prove that the safety property:

	(B = 1) /\ (NR = k) /\ (k > 0) unless (B = 1) /\ (NR < k) in Pr

   holds for the previously defined example program.

   The property is proven in six steps. 5 proofs, one for each statetransition
   in the program and one proof using the 5 proofs to prove that the property 
   of the entire program holds.
%

let U9_tr1_thm1 = TAC_PROOF
  (([],
   "!N. (N > 0) ==>
     (!k:num.
      (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
       ((\s. s B = 1) /\* (\s. s NR < k))) [^startwrite])"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS;UNLESS_STMT;MK_COND;STL;ST;/\*;\/*;~*;TRUE_DEF] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let U9_tr2_thm1 = TAC_PROOF
  (([],
   "!N. (N > 0) ==>
     (!k:num.
      (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
       ((\s. s B = 1) /\* (\s. s NR < k))) [^endwrite])"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS;UNLESS_STMT;MK_COND;STL;ST;/\*;\/*;~*;TRUE_DEF] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   BETA_TAC THEN
   ASM_REWRITE_TAC [Vtype_thm1;ONCE_REWRITE_RULE [EQ_SYM_EQ] Vtype_thm1] THEN
   DISJ2_TAC THEN
   ACCEPT_TAC (MP (SPEC_ALL U9_lemma1) (ASSUME "k > 0")));;

let U9_tr3_thm1 = TAC_PROOF
  (([],
   "!N. (N > 0) ==>
     (!k:num.
      (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
       ((\s. s B = 1) /\* (\s. s NR < k))) [^startread])"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS;UNLESS_STMT;MK_COND;STL;ST;/\*;\/*;~*;TRUE_DEF] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT COND_CASES_TAC THENL
     [ % 2 Subgoals %
      MP_TAC (REWRITE_RULE
        [ASSUME "(N - (k + (N * (s NW)))) >= N /\ (s NQ) > 0"]
          (MP (MP (SPEC_ALL U9_lemma7) (ASSUME "k > 0")) 
              (ASSUME "N > 0"))) THEN
      REWRITE_TAC []
     ;
      ASM_REWRITE_TAC []
     ]);;

let U9_tr4_thm1 = TAC_PROOF
  (([],
   "!N. (N > 0) ==>
     (!k:num.
      (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
       ((\s. s B = 1) /\* (\s. s NR < k))) [^endread])"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [UNLESS;UNLESS_STMT;MK_COND;STL;ST;/\*;\/*;~*;TRUE_DEF] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   BETA_TAC THEN
   ASM_REWRITE_TAC [Vtype_thm1;ONCE_REWRITE_RULE [EQ_SYM_EQ] Vtype_thm1]);;

let U9_tr5_thm1 = TAC_PROOF
  (([],
   "!N. (N > 0) ==>
     (!k:num.
      (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
       ((\s. s B = 1) /\* (\s. s NR < k))) [^set_b])"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [UNLESS;UNLESS_STMT;MK_COND;STL;ST;/\*;\/*;~*;
                TRUE_DEF;FALSE_DEF] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

%
   Now we may prove that the property holds for the given program
%
let U9 = TAC_PROOF
  (([],
   "!N. (N > 0) ==>
     (!k:num.
      (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
       ((\s. s B = 1) /\* (\s. s NR < k))) ^Prog)"),
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [UNLESS] THEN
   REWRITE_TAC
    [UNDISCH_ALL (REWRITE_RULE [UNLESS] (SPEC_ALL U9_tr1_thm1));
     UNDISCH_ALL (REWRITE_RULE [UNLESS] (SPEC_ALL U9_tr2_thm1));
     UNDISCH_ALL (REWRITE_RULE [UNLESS] (SPEC_ALL U9_tr3_thm1));
     UNDISCH_ALL (REWRITE_RULE [UNLESS] (SPEC_ALL U9_tr4_thm1));
     UNDISCH_ALL (REWRITE_RULE [UNLESS] (SPEC_ALL U9_tr5_thm1))]);;

%
  Now assume we have proven
%

let U7 =
   "((\s. s NQ > 0) ENSURES ((\s. s NW = 1) \/* (\s. s B = 1))) ^Prog";;
let U8 =
   "(((\s. s B = 1) /\* (\s. s NR = 0)) ENSURES ((\s. s NW = 1))) ^Prog";;

%
  We have proven (U9)

   !k. (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
         ((\s. s B = 1) /\* (\s. s NR < k))) ^Prog
%

%
  From the specification we have:
%
let U4 =
   "!k. (((\s. s NR = k) /\* (\s. k > 0)) LEADSTO (~* (\s. s NR = k))) ^Prog";;

%
  Now we may prove:

    (U5)

       !N. (N > 0) ==> (U4) /\ (U7) /\ (U8)

          ==> ((\s. s NQ > 0) LEADSTO (\s. s NW = 1)) Prog
%

let U5_lemma1 = TAC_PROOF
  (([],
   "!s. (((\s. s NR = k) /\* (\s. k > 0)) /\*
          ((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0)))) s
       =
    ((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) s"),
   REWRITE_TAC [/\*] THEN
   BETA_TAC THEN
   GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

%
  |- ((\s. s NR = k) /\* (\s. k > 0)) /\*
   ((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) =
   (\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))
%
let U5_lemma2 = REWRITE_RULE [ETA_AX] (MK_ABS U5_lemma1);;

let U5_lemma3 = TAC_PROOF
  (([],
   "!s. (((~*(\s. s NR = k)) /\*
           ((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0)))) \/*
          ((\s. s B = 1) /\* (\s. (s NR) < k))) s
       =
        ((\s. s B = 1) /\* (\s. (s NR) < k)) s"),
   REWRITE_TAC [/\*;\/*;~*] THEN
   BETA_TAC THEN
   GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
   RES_TAC);;

%
  |- ((~*(\s. s NR = k)) /\*
    ((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0)))) \/*
   ((\s. s B = 1) /\* (\s. (s NR) < k)) =
   (\s. s B = 1) /\* (\s. (s NR) < k)
%
let U5_lemma4 = REWRITE_RULE [ETA_AX] (MK_ABS U5_lemma3);;

%
  |- (((\s. s B = 1) /\* (\s. s NR = 0)) LEADSTO
     (((\s. s B = 1) /\* (\s. (s NR) < 0)) \/*
      ((\s. s B = 1) /\* (\s. s NR = 0))))
     (CONS st Pr)
%
let U5_lemma5 =
   (REWRITE_RULE
      [(ISPECL ["(\s. s B = 1) /\* (\s. s NR = 0)";
                "(\s. s B = 1) /\* (\s. (s NR) < 0)"] SYM_OR_IMPLY_WEAK_lemma);
       (SPEC_ALL (ISPECL ["(\s. s B = 1) /\* (\s. s NR = 0)"] LEADSTO_thm12))]
         (ISPECL ["(\s. s B = 1) /\* (\s. s NR = 0)";
                  "(\s. s B = 1) /\* (\s. s NR = 0)";
                  "((\s. s B = 1) /\* (\s. (s NR) < 0)) \/*
                   ((\s. s B = 1) /\* (\s. s NR = 0))";
                  "st:(Vtype->num)->(Vtype->num)";
                  "Pr:((Vtype->num)->(Vtype->num))list"]
                  LEADSTO_cor9));;

let U5_lemma6 = TAC_PROOF
  (([],
   "(!k. (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) LEADSTO
          ((\s. s B = 1) /\* (\s. (s NR) < k))) (CONS st Pr))
      ==>
    (!m. (((\s. s B = 1) /\* (\s. s NR = m)) LEADSTO
         (((\s. s B = 1) /\* (\s. (s NR) < m)) \/*
          ((\s. s B = 1) /\* (\s. s NR = 0)))) (CONS st Pr))"),
   DISCH_TAC THEN
   INDUCT_TAC THENL
    [
     REWRITE_TAC [U5_lemma5]
    ;
     ACCEPT_TAC (REWRITE_RULE [(REWRITE_RULE
      [GREATER;LESS_0;REWRITE_RULE [TRUE_DEF] AND_TRUE_lemma] (SPEC "SUC m"
        (ASSUME
          "!k. (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) LEADSTO
                ((\s. s B = 1) /\* (\s. (s NR) < k))) (CONS st Pr)")));
            (ISPECL ["((\s. s B = 1) /\* (\s. (s NR) < (SUC m)))";
                   "((\s. s B = 1) /\* (\s. s NR = 0))"]
                    OR_IMPLY_WEAK_lemma)]
        (SPEC_ALL (ISPECL ["(\s. s B = 1) /\* (\s. (s NR) = (SUC m))";
                    "(\s. s B = 1) /\* (\s. (s NR) < (SUC m))";
                    "((\s. s B = 1) /\* (\s. (s NR) < (SUC m))) \/*
                     ((\s. s B = 1) /\* (\s. s NR = 0))";
                    "st:(Vtype->num)->(Vtype->num)";
                    "Pr:((Vtype->num)->(Vtype->num))list"]
                    LEADSTO_cor9)))
    ]);;

let U5 = TAC_PROOF
  (([],
   "!N. (N > 0) ==> (^Prog = Pr) ==> ^U4 /\ ^U7 /\ ^U8 ==>
      ((\s. s NQ > 0) LEADSTO (\s. s NW = 1)) ^Prog"),
   GEN_TAC THEN
   DISCH_TAC THEN
   DISCH_TAC THEN
   MP_TAC (UNDISCH_ALL (SPEC_ALL U9)) THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm0 THEN
   ASSUME_TAC (GEN "k:num" (REWRITE_RULE
    [U5_lemma2;U5_lemma4] (REWRITE_RULE
      [ASSUME "!k.
       (((\s. s NR = k) /\* (\s. k > 0)) LEADSTO (~*(\s. (s NR) = k))) Pr";
       ASSUME "!k.
       (((\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))) UNLESS
        ((\s. s B = 1) /\* (\s. (s NR) < k))) Pr"] (ISPECL
          ["(\s. s NR = k) /\* (\s. k > 0)";"~*(\s:Vtype->num. (s NR) = k)";
           "(\s. s B = 1) /\* ((\s. s NR = k) /\* (\s. k > 0))";
           "(\s. s B = 1) /\* (\s. (s NR) < k)";
           "st:(Vtype->num)->(Vtype->num)";
           "Pr:((Vtype->num)->(Vtype->num))list"] LEADSTO_thm29)))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL U5_lemma6)) THEN
   ASSUME_TAC (UNDISCH_ALL (BETA_RULE (ISPECL
    ["\s. s B = 1";"(\s. s B = 1) /\* (\s. s NR = 0)";
     "st:(Vtype->num)->(Vtype->num)";
     "Pr:((Vtype->num)->(Vtype->num))list";"\s:Vtype->num. s NR"]
     (REWRITE_RULE [EQmetric;LESSmetric] LEADSTO_thm36)))) THEN
   IMP_RES_TAC LEADSTO_thm1 THEN
   IMP_RES_TAC LEADSTO_thm28 THEN
   ACCEPT_TAC (REWRITE_RULE [OR_OR_lemma] (ASSUME
    "((\s. (s NQ) > 0) LEADSTO ((\s. s NW = 1) \/* (\s. s NW = 1)))Pr")));;


%
  This completes the example
%

% close_theory();; %
