
%=============================================================================
  FILE:         aci.ml
  
  DESCIPTION:   Generalizing an associative and commutative operation with
                identity to finite sets.

  AUTHOR:       Ching-Tsun Chou
  
  LAST CHANGED: Tue Oct  6 14:56:08 PDT 1992
=============================================================================%

new_theory `aci` ;;

%-----------------------------------------------------------------------------
  Need the new `pred_sets` library by Tom Melham.
-----------------------------------------------------------------------------%

load_library `pred_sets`  ;;

%-----------------------------------------------------------------------------
  Miscellaneous ML functions.
-----------------------------------------------------------------------------%

let sing x = [x] ;;

%-----------------------------------------------------------------------------
  (Stolen from Brian Graham.)
-----------------------------------------------------------------------------%

let SELECT_UNIQUE_RULE (x,y) th1 th2 =
  let Q = mk_abs (x, subst [x,y] (concl th1))
  in
  let th1' = SUBST [SYM (BETA_CONV "^Q ^y"), "b:bool"] "b:bool" th1
  in
  ( MP (SPECL ["$@ ^Q"; y] th2)
       (CONJ (CONV_RULE BETA_CONV (SELECT_INTRO th1')) th1) )
;;
        
let SELECT_UNIQUE_TAC:tactic (gl,g) =
  let Q,y = dest_eq g
  in
  let x,Qx = dest_select Q
  in
  let x' = variant (x.freesl(g.gl))x
  in
  let Qx' = subst [x', x] Qx
  in
  ([gl,subst [y,x]Qx;
    gl, "!^x ^x'. (^Qx /\ ^Qx') ==> (^x = ^x')"],
   (\thl. SELECT_UNIQUE_RULE (x,y) (hd thl) (hd (tl thl))))
;;

%-----------------------------------------------------------------------------
  "ASSOC_COMM_ID_DEF op id" holds iff "op" is an associative and commutative
  operation with identity "id".
-----------------------------------------------------------------------------%

let ASSOC_COMM_ID_DEF = new_definition(`ASSOC_COMM_ID_DEF`,
"
  ASSOC_COMM_ID (op : ** -> ** -> **) (id : **) =
    ( ! a b c . (op a (op b c)) = (op (op a b) c) ) /\
    ( ! a b .          (op a b) = (op b a) ) /\
    ( ! a .           (op a id) = a )
");;

%-----------------------------------------------------------------------------
  The following is based on ideas stolen from Tom Melham's definition
  of cardinality ("CARD") in the library "pred_sets".
-----------------------------------------------------------------------------%

let REL = " REL : (** -> ** -> **) -> ** -> (* -> **) -> (* -> bool) -> **
            -> num -> bool " ;;

%-----------------------------------------------------------------------------
  "REL op id f s a n" holds iff set s has cardinality n and doing
  operation op on f(x)'s with x ranging over s has result a, 
  where a = id if s = { }.
-----------------------------------------------------------------------------%

let ACI_REL_DEF =
"
  ( ! op id f s a .   ^REL op id f s a 0       = (s = { }) /\ (a = id) ) /\
  ( ! op id f s a n . ^REL op id f s a (SUC n) =
      ? x b . x IN s /\ ^REL op id f (s DELETE x) b n /\ (a = op (f x) b) )
" ;;

%-----------------------------------------------------------------------------
  Prove that relation "REL", as recursively defined above, exists.
-----------------------------------------------------------------------------%

let ACI_REL_EXISTS = prove_rec_fn_exists num_Axiom ACI_REL_DEF ;;

%-----------------------------------------------------------------------------
  All lemmas below about "REL" assume "ASSOC_COMM_ID op id".
-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------
  "REL op id f s a 1" holds iff s = {x} and a = f(x) for some x.
-----------------------------------------------------------------------------%

let ACI_REL_1_LEMMA = PROVE(
"
  ^ACI_REL_DEF ==>
    ! op id . ASSOC_COMM_ID op id ==>
      ! f s a . ^REL op id f s a (SUC 0) = ? x . (s = {x}) /\ (a = f x)
" , (
  DISCH_THEN \ ACI_REL_asm .
    REPEAT GEN_TAC THEN
    DISCH_THEN \ ASSOC_COMM_ID_asm .
      let [_; _; ID_asm] =
          (CONJUNCTS o PURE_ONCE_REWRITE_RULE [ASSOC_COMM_ID_DEF])
          ASSOC_COMM_ID_asm
      in
      REPEAT GEN_TAC THEN
      PURE_REWRITE_TAC [ACI_REL_asm] THEN
      EQ_TAC THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC "x : *" THENL
      [ IMP_RES_TAC DELETE_EQ_SING THEN
        ASM_REWRITE_TAC [ID_asm]
        ;
        EXISTS_TAC "id : **" THEN
        ASM_REWRITE_TAC [ID_asm; IN_SING; SING_DELETE] ]
) ) ;;

%-----------------------------------------------------------------------------
  If "REL op id f s a (SUC n)" holds, then it does not matter which element
  of s to delete in the recursive definition of "REL".
-----------------------------------------------------------------------------%

let ACI_REL_SUC_LEMMA = PROVE(
"
  ^ACI_REL_DEF ==>
    ! op id . ASSOC_COMM_ID op id ==>
      ! n f s a . ^REL op id f s a (SUC n) ==>
        ! x . x IN s ==>
          ? b . ^REL op id f (s DELETE x) b n /\ (a = op (f x) b)
" , (
  DISCH_THEN \ ACI_REL_asm .
    REPEAT GEN_TAC THEN
    DISCH_THEN \ ASSOC_COMM_ID_asm .
      let [ASSOC_asm; COMM_asm; ID_asm] =
            (CONJUNCTS o PURE_ONCE_REWRITE_RULE [ASSOC_COMM_ID_DEF])
            ASSOC_COMM_ID_asm
      and SING_lemma =
            itlist (C MATCH_MP) [ASSOC_COMM_ID_asm; ACI_REL_asm]
            ACI_REL_1_LEMMA
      in
      INDUCT_TAC THENL
      [ PURE_REWRITE_TAC [SING_lemma; CONJUNCT1 ACI_REL_asm] THEN
        REPEAT (FILTER_STRIP_TAC "IN : * -> (* -> bool) -> bool") THEN
        ASM_REWRITE_TAC [IN_SING] THEN
        DISCH_TAC THEN
        EXISTS_TAC "id : **" THEN
        ASM_REWRITE_TAC [ID_asm; SING_DELETE]
        ;
        REPEAT GEN_TAC THEN
        GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
                        [ ] [ACI_REL_asm] THEN
        REPEAT STRIP_TAC THEN
        ASM_CASES_TAC "x' = x : *" THENL
        [ EXISTS_TAC "b : **" THEN
          ASM_REWRITE_TAC [ ]
          ;
          FIRST_ASSUM (ASSUME_TAC o NOT_EQ_SYM) THEN
          IMP_RES_TAC IN_DELETE THEN
          RES_TAC THEN
          EXISTS_TAC "(op : ** -> ** -> **) (f (x : *)) b'" THEN
          CONJ_TAC THENL
          [ PURE_REWRITE_TAC [ACI_REL_asm] THEN
            EXISTS_TAC "x : *" THEN
            EXISTS_TAC "b' : **" THEN
            PURE_ONCE_REWRITE_TAC [DELETE_COMM] THEN
            ASM_REWRITE_TAC [ ]
            ;
            ASM_REWRITE_TAC [ ] THEN
            CONV_TAC (AC_CONV (ASSOC_asm, COMM_asm)) ] ] ]
) ) ;;

%-----------------------------------------------------------------------------
  Therefore, for any (op, id, f, s), there is at most one pair (a, n)
  such that "REL op id f s a n" holds.
-----------------------------------------------------------------------------%

let ACI_REL_UNIQUE_LEMMA = PROVE(
"
  ^ACI_REL_DEF ==>
    ! op id . ASSOC_COMM_ID op id ==>
      ! n1 n2 f s a1 a2 . ^REL op id f s a1 n1 ==>
                          ^REL op id f s a2 n2 ==> (a1 = a2) /\ (n1 = n2)
" , (
  REPEAT (FILTER_STRIP_TAC "n1 : num") THEN
  INDUCT_TAC THEN
  INDUCT_TAC THENL
  [ PURE_ASM_REWRITE_TAC [ ] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [ ]
    ;
    PURE_ASM_REWRITE_TAC [ ] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC MEMBER_NOT_EMPTY
    ;
    PURE_ASM_REWRITE_TAC [ ] THEN REPEAT STRIP_TAC THEN
    IMP_RES_TAC MEMBER_NOT_EMPTY
    ;
    REPEAT GEN_TAC THEN
    DISCH_TAC THEN
    PURE_ASM_REWRITE_TAC [ ] THEN
    STRIP_TAC THEN
    IMP_RES_TAC ACI_REL_SUC_LEMMA THEN
    RES_TAC THEN
    FILTER_ASM_REWRITE_TAC
      ( let op = "op : ** -> ** -> **" and f  = "f : * -> **"
        in
        C mem ["a1 = ^op(^f x)b'"; "a2 = ^op(^f x)b";
               "b' = b : **"; "n1 = n2 : num"]
      ) [ ] ]
) ) ;;

%-----------------------------------------------------------------------------
  Furthermore, if s is finite, then there must exist a pair (a, n)
  such that "REL op id f s a n" holds.
-----------------------------------------------------------------------------%

let ACI_REL_EXISTS_LEMMA = PROVE(
"
  ^ACI_REL_DEF ==>
    ! op id . ASSOC_COMM_ID op id ==>
      ! f s . FINITE s ==>
        ? a n . ^REL op id f s a n
" , (
  REPEAT (FILTER_STRIP_TAC "s : * -> bool") THEN
  SET_INDUCT_TAC THENL
  [ EXISTS_TAC "id : **" THEN
    EXISTS_TAC "0" THEN
    ASM_REWRITE_TAC [ ]
    ;
    FIRST_ASSUM CHOOSE_TAC THEN
    FIRST_ASSUM CHOOSE_TAC THEN
    EXISTS_TAC "(op : ** -> ** -> **) (f (e : *)) a" THEN
    EXISTS_TAC "SUC n" THEN
    PURE_ASM_REWRITE_TAC [ ] THEN
    EXISTS_TAC "e : *" THEN
    EXISTS_TAC "a : **" THEN
    IMP_RES_TAC DELETE_NON_ELEMENT THEN
    ASM_REWRITE_TAC [IN_INSERT; DELETE_INSERT] ]
) ) ;;

%-----------------------------------------------------------------------------
  Hence, if s is finite, then "@ b . ? n . REL op id f s b n" does have
  the desired property of satisfying "\ a . ? n . REL op id f s a n".
-----------------------------------------------------------------------------%

let ACI_REL_SELECT_LEMMA = PROVE(
"
  ^ACI_REL_DEF ==>
    ! op id . ASSOC_COMM_ID op id ==>
      ! f s a . FINITE s ==>
        ( ( (@ b . ? n . ^REL op id f s b n) = a ) =
                 ( ? n . ^REL op id f s a n) )
" , (
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC ACI_REL_EXISTS_LEMMA THEN
  EQ_TAC THENL
  [ DISCH_THEN (\asm. PURE_ONCE_REWRITE_TAC [SYM asm]) THEN
    CONV_TAC SELECT_CONV THEN
    ASM_REWRITE_TAC [ ]
    ;
    STRIP_TAC THEN
    SELECT_UNIQUE_TAC THENL
    [ EXISTS_TAC "n : num" THEN
      ASM_REWRITE_TAC [ ]
      ;
      REPEAT STRIP_TAC THEN
      IMP_RES_TAC ACI_REL_UNIQUE_LEMMA ] ]
) ) ;;

%-----------------------------------------------------------------------------
  Now, prove that "\ op id f s . @ b . ? n . REL op id f s b n" defines
  the function that performs op on f(x)'s with x ranging over s,
  for any op and id such that "ASSOC_COMM_ID op id".
-----------------------------------------------------------------------------%

let ACI_OP_EXISTS = PROVE(
"
  ? OP : (** -> ** -> **) -> ** -> (* -> **) -> (* -> bool) -> ** .
  ! op id . ASSOC_COMM_ID op id ==>
    ( ! f . OP op id f { } = id ) /\
    ( ! f s x . FINITE s ==>
      ( OP op id f (x INSERT s) = (x IN s) => (OP op id f s)
                                  | (op (f x) (OP op id f s)) ) )
" , (
  STRIP_ASSUME_TAC ACI_REL_EXISTS THEN
  EXISTS_TAC "\ op id f s . @ b . ? n . ^REL op id f s b n" THEN
  CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT STRIP_TAC THENL
  [ ASSUME_TAC (INST_TYPE [(":*", ":**")] FINITE_EMPTY) THEN
    IMP_RES_TAC ACI_REL_SELECT_LEMMA THEN
    PURE_ASM_REWRITE_TAC [ ] THEN
    EXISTS_TAC "0" THEN
    ASM_REWRITE_TAC [ ]
    ;
    IMP_RES_THEN (ASSUME_TAC o ISPEC "x : *") FINITE_INSERT THEN
    IMP_RES_TAC ACI_REL_SELECT_LEMMA THEN
    PURE_ASM_REWRITE_TAC [ ] THEN
    IMP_RES_TAC ACI_REL_EXISTS_LEMMA THEN
    ASM_CASES_TAC "(x : *) IN s" THEN
    ASM_REWRITE_TAC [ ] THENL
    [ IMP_RES_THEN (\th. REWRITE_TAC [th]) ABSORPTION THEN
      CONV_TAC SELECT_CONV THEN
      ASM_REWRITE_TAC [ ]
      ;
      FIRST_ASSUM (CHOOSE_TAC o SPEC_ALL) THEN
      FIRST_ASSUM CHOOSE_TAC THEN
      EXISTS_TAC "SUC n" THEN
      ASM_REWRITE_TAC [ ] THEN
      EXISTS_TAC "x : *" THEN
      EXISTS_TAC "a : **" THEN
      ASM_REWRITE_TAC [IN_INSERT; DELETE_INSERT] THEN
      IMP_RES_THEN (\th. ASM_REWRITE_TAC [th]) DELETE_NON_ELEMENT THEN
      AP_TERM_TAC THEN
      ASM_REWRITE_TAC [ ] ] ]
) ) ;;

%-----------------------------------------------------------------------------
  Finally, introduce a constant ACI_OP for OP via a constant specification.
-----------------------------------------------------------------------------%

let ACI_OP_DEF =
  new_specification `ACI_OP_DEF` [(`constant`, `ACI_OP`)] ACI_OP_EXISTS ;;

let ACI_OP =
  " ACI_OP : (** -> ** -> **) -> ** -> (* -> **) -> (* -> bool) -> ** " ;;

%-----------------------------------------------------------------------------
  ACI_OP on singletons.
-----------------------------------------------------------------------------%

let ACI_OP_SING = prove_thm(`ACI_OP_SING`,
"
  ! op id . ASSOC_COMM_ID op id ==>
    ! f x . ^ACI_OP op id f {x} = f x
", (
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (INST_TYPE [(":*", ":**")] FINITE_EMPTY) THEN
  IMP_RES_TAC ACI_OP_DEF THEN
  FIRST_ASSUM (ASSUME_TAC o el 3 o CONJUNCTS o
               PURE_ONCE_REWRITE_RULE [ASSOC_COMM_ID_DEF]) THEN
  ASM_REWRITE_TAC [NOT_IN_EMPTY]
) ) ;;

%-----------------------------------------------------------------------------
  ACI_OP on unions.
-----------------------------------------------------------------------------%

let ACI_OP_UNION = prove_thm(`ACI_OP_UNION`,
"
  ! op id . ASSOC_COMM_ID op id ==>
    ! f s . FINITE s ==>
      ! t . FINITE t ==>
        ( op (^ACI_OP op id f (s UNION t))
             (^ACI_OP op id f (s INTER t))
        = op (^ACI_OP op id f s)
             (^ACI_OP op id f t) )
", (
  REPEAT GEN_TAC THEN
  DISCH_THEN \ ASSOC_COMM_ID_asm .
    let [ASSOC_asm; COMM_asm; _] =
          (CONJUNCTS o PURE_ONCE_REWRITE_RULE [ASSOC_COMM_ID_DEF])
          ASSOC_COMM_ID_asm
    in
    let AC_conv = AC_CONV (ASSOC_asm, COMM_asm)
    in
    let (LR_AC_TAC : thm_tactic) (th) (asl, g) =
          let th' = EQT_ELIM (AC_conv " ^(lhs g) = ^(lhs (concl th)) ")
                    TRANS th TRANS
                    EQT_ELIM (AC_conv " ^(rhs (concl th)) = ^(rhs g) ")
          in ACCEPT_TAC th' (asl, g)
    in
    let ACI_OP_asm = MATCH_MP ACI_OP_DEF ASSOC_COMM_ID_asm
    in
    GEN_TAC THEN
    SET_INDUCT_TAC THEN
    REPEAT STRIP_TAC THENL
    [ REWRITE_TAC [UNION_EMPTY; INTER_EMPTY; ACI_OP_asm] THEN
      CONV_TAC AC_conv
      ;
      RES_THEN (ASSUME_TAC o AP_TERM "(op : ** -> ** -> **) (f (e : *))") THEN
      REWRITE_TAC [INSERT_UNION; INSERT_INTER] THEN
      ASM_CASES_TAC "(e : *) IN t" THEN
      ASM_REWRITE_TAC [ ] THENL
      [ IMP_RES_THEN (ASSUME_TAC o ISPEC "t : * -> bool") INTER_FINITE THEN
        IMP_RES_THEN (ASM_REWRITE_TAC o append [IN_INTER] o sing) ACI_OP_asm
        ;
        IMP_RES_TAC FINITE_UNION THEN
        IMP_RES_THEN (ASM_REWRITE_TAC o append [IN_UNION] o sing) ACI_OP_asm
      ] THEN
      FIRST_ASSUM LR_AC_TAC ]
) ) ;;

let ACI_OP_DISJOINT = prove_thm(`ACI_OP_DISJOINT`,
"
  ! op id . ASSOC_COMM_ID op id ==>
    ! f s t . FINITE s /\ FINITE t /\ DISJOINT s t ==>
      ( (^ACI_OP op id f (s UNION t)) 
      = op (^ACI_OP op id f s) (^ACI_OP op id f t) )
", (
  PURE_ONCE_REWRITE_TAC [DISJOINT_DEF] THEN
  REPEAT STRIP_TAC THEN
  REPEAT_GTCL IMP_RES_THEN
    (PURE_ONCE_REWRITE_TAC o sing o SYM o SPEC_ALL) ACI_OP_UNION THEN
  IMP_RES_THEN (ASM_REWRITE_TAC o sing) ACI_OP_DEF THEN
  IMP_RES_THEN (REWRITE_TAC o sing o assert (mem "id : **" o vars o concl))
    ASSOC_COMM_ID_DEF
) ) ;;
