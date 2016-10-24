
%=============================================================================
  FILE:         use_pred.ml
  
  DESCIPTION:   ML code for using Logic of Predicates.

  AUTHOR:       Ching-Tsun Chou
  
  CREATED:      Sun May 31 14:20:59 PDT 1992
  LAST CHANGED: Tue Oct  6 12:21:31 PDT 1992
=============================================================================%

%-----------------------------------------------------------------------------
  Load Boulton's tautology checker.
-----------------------------------------------------------------------------%

load_library `taut` ;;

%-----------------------------------------------------------------------------
  Load the theory.
-----------------------------------------------------------------------------%

if (draft_mode ()) then
( print_string (`Declaring theory "pred" a new parent ...`) ;
  print_newline () ;
  new_parent `pred` )
else
( print_string (`Loading theory "pred" ...`) ;
  print_newline () ;
  load_theory `pred` )
;;

%-----------------------------------------------------------------------------
  Activate binders. (Probably not needed in v.2.1 of HOL.)
-----------------------------------------------------------------------------%

( print_string (`Activating binders ...`) ;
  print_newline() ;
  activate_all_binders `pred` )
;;

%-----------------------------------------------------------------------------
  Special symbols.
-----------------------------------------------------------------------------%

new_special_symbol `~~`     ;;
new_special_symbol `//\\\\` ;;
new_special_symbol `\\\\//` ;;
new_special_symbol `==>>`   ;;
new_special_symbol `==`     ;;
new_special_symbol `!!`     ;;
new_special_symbol `??`     ;;
new_special_symbol `|=`     ;;

%-----------------------------------------------------------------------------
  Repeatedly apply a function until it fails.
-----------------------------------------------------------------------------%

letrec repeat f x = (let y = f x in repeat f y) ? x ;;

%-----------------------------------------------------------------------------
  SPEC_ALL_VAR is the same as SPEC_ALL except that it also returns the list
  of SPEC'ed variables.  Modified from SPEC_ALL in drul.ml.
-----------------------------------------------------------------------------%

let SPEC_ALL_VAR =
    let f v (vs,l) = let v' = variant vs v in (v'.vs, v'.l) in
    \th. let (hvs, con) = (freesl # I) (dest_thm th) in
         let fvs = frees con and vars = fst (strip_forall con) in
         let s_vars = snd (itlist f vars (hvs @ fvs, [ ])) in
         (s_vars,  SPECL s_vars th)
;;

%-----------------------------------------------------------------------------
  Unfolding and folding beta conversions for lifted quantifiers.
-----------------------------------------------------------------------------%

let pred_BETA_UNFOLD_CONV (q : term) =
  let v = (bndvar o rator o rator o body o rand) q
  in
  ( GEN_ALPHA_CONV v THENC
    (RAND_CONV o ABS_CONV o RATOR_CONV) BETA_CONV
  ) q
;;

let pred_BETA_FOLD_CONV =
  let REV_BETA_CONV v p = (SYM o BETA_CONV) "(\ ^v . ^p) ^v"
  in
  \ (q : term) .
    let v = (bndvar o rand) q
    in
    ( (RAND_CONV o ABS_CONV o RATOR_CONV) (REV_BETA_CONV v)
    ) q
;;

%-----------------------------------------------------------------------------
  Unfolding and folding conversions for lifted logical operators.
-----------------------------------------------------------------------------%

let pred_LOGIC_UNFOLD_CONV (REW_CONVs : conv list) =
  let [     TT_CONV ;
            FF_CONV ;
           NEG_CONV ;
          CONJ_CONV ;
          DISJ_CONV ;
           IMP_CONV ;
            EQ_CONV ;
        FORALL_CONV ;
        EXISTS_CONV ] = REW_CONVs
  in
  letrec UNFOLD_CONV (t : term) =
      ( ( FIRST_CONV [TT_CONV; FF_CONV] )
        ORELSEC
        ( FIRST_CONV [NEG_CONV]
          THENC (RAND_CONV) UNFOLD_CONV )
        ORELSEC
        ( FIRST_CONV [CONJ_CONV; DISJ_CONV; IMP_CONV; EQ_CONV]
          THENC (RAND_CONV) UNFOLD_CONV
          THENC (RATOR_CONV o RAND_CONV) UNFOLD_CONV )
        ORELSEC
        ( FIRST_CONV [FORALL_CONV; EXISTS_CONV]
          THENC pred_BETA_UNFOLD_CONV
          THENC (RAND_CONV o ABS_CONV) UNFOLD_CONV )
        ORELSEC
        ( ALL_CONV )
      ) t
  in
  UNFOLD_CONV
;;

let pred_LOGIC_FOLD_CONV (REW_CONVs : conv list) =
  let [     TT_CONV ;
            FF_CONV ;
           NEG_CONV ;
          CONJ_CONV ;
          DISJ_CONV ;
           IMP_CONV ;
            EQ_CONV ;
        FORALL_CONV ;
        EXISTS_CONV ] = REW_CONVs
  in
  letrec FOLD_CONV (t : term) =
      let RAND_CONV_1 = (RAND_CONV) FOLD_CONV
      and RAND_CONV_2 = (RAND_CONV) FOLD_CONV THENC
                        (RATOR_CONV o RAND_CONV) FOLD_CONV
      and RAND_CONV_b = (RAND_CONV o ABS_CONV) FOLD_CONV THENC
                        pred_BETA_FOLD_CONV
      in
      ( if (t = "T")     then TT_CONV
        if (t = "F")     then FF_CONV
        if (is_neg    t) then RAND_CONV_1 THENC NEG_CONV
        if (is_conj   t) then RAND_CONV_2 THENC CONJ_CONV
        if (is_disj   t) then RAND_CONV_2 THENC DISJ_CONV
        if (is_imp    t) then RAND_CONV_2 THENC IMP_CONV
        if (is_eq     t) then RAND_CONV_2 THENC EQ_CONV
        if (is_forall t) then RAND_CONV_b THENC FORALL_CONV
        if (is_exists t) then RAND_CONV_b THENC EXISTS_CONV
                         else ALL_CONV
      ) t
  in
  FOLD_CONV
;;

%-----------------------------------------------------------------------------
  Unfolding and folding tactics and rules for lifted sequents.
-----------------------------------------------------------------------------%

let FIX_X_REWRITE_CONV (x : term) (eq : thm) =
  PROVE_HYP (REFL x) o ((REWRITE_CONV o ADD_ASSUM "^x = ^x" o ISPEC x) eq)
;;

let ( pred_SEQ_UNFOLD .
      pred_SEQ_AUX_UNFOLD_NIL .
      pred_SEQ_AUX_UNFOLD_CONS .
      pred_LOGIC_UNFOLDs ) ,
    ( pred_SEQ_FOLD .
      pred_SEQ_AUX_FOLD_NIL .
      pred_SEQ_AUX_FOLD_CONS .
      pred_LOGIC_FOLDs ) =
  ((CONJUNCTS # CONJUNCTS) o CONJ_PAIR) (theorem `pred` `pred_UNFOLD_FOLD`)
;;

let pred_SEQ_UNFOLD_RULE (x : term) =
  let SEQ_CONV = REWRITE_CONV pred_SEQ_UNFOLD
  and SEQ_AUX_CONV_NIL  = FIX_X_REWRITE_CONV x pred_SEQ_AUX_UNFOLD_NIL
  and SEQ_AUX_CONV_CONS = FIX_X_REWRITE_CONV x pred_SEQ_AUX_UNFOLD_CONS
  and LOGIC_CONV = pred_LOGIC_UNFOLD_CONV
                   ( map (FIX_X_REWRITE_CONV x) pred_LOGIC_UNFOLDs )
  in
  \ (th : thm) .
    let (vl, th') = SPEC_ALL_VAR th
    in
    ( GENL vl
    o CONV_RULE (SEQ_AUX_CONV_NIL THENC LOGIC_CONV)
    o repeat ( UNDISCH
             o CONV_RULE (SEQ_AUX_CONV_CONS THENC
                          (RATOR_CONV o RAND_CONV) LOGIC_CONV) )
    o ISPEC x
    o CONV_RULE SEQ_CONV
    ) th'
;;

let pred_SEQ_UNFOLD_TAC (x : term) =
  let SEQ_CONV = REWRITE_CONV pred_SEQ_UNFOLD
  and SEQ_AUX_CONV_NIL  = FIX_X_REWRITE_CONV x pred_SEQ_AUX_UNFOLD_NIL
  and SEQ_AUX_CONV_CONS = FIX_X_REWRITE_CONV x pred_SEQ_AUX_UNFOLD_CONS
  and LOGIC_CONV = pred_LOGIC_UNFOLD_CONV
                   ( map (FIX_X_REWRITE_CONV x) pred_LOGIC_UNFOLDs )
  in
  CONV_TAC SEQ_CONV
  THEN X_GEN_TAC x
  THEN REPEAT
       ( CONV_TAC SEQ_AUX_CONV_CONS THEN
         DISCH_THEN (ASSUME_TAC o CONV_RULE LOGIC_CONV) )
  THEN CONV_TAC (SEQ_AUX_CONV_NIL THENC LOGIC_CONV)
  THEN POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)
;;

let pred_SEQ_FOLD_TAC (x : term) =
  let SEQ_CONV = REWRITE_CONV pred_SEQ_FOLD
  and SEQ_AUX_CONV_NIL  = FIX_X_REWRITE_CONV x pred_SEQ_AUX_FOLD_NIL
  and SEQ_AUX_CONV_CONS = FIX_X_REWRITE_CONV x pred_SEQ_AUX_FOLD_CONS
  and LOGIC_CONV = pred_LOGIC_FOLD_CONV
                   ( map (FIX_X_REWRITE_CONV x) pred_LOGIC_FOLDs )
  in
  POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)
  THEN CONV_TAC (LOGIC_CONV THENC SEQ_AUX_CONV_NIL)
  THEN REPEAT
       ( POP_ASSUM (MP_TAC o CONV_RULE LOGIC_CONV)
         THEN CONV_TAC SEQ_AUX_CONV_CONS )
  THEN SPEC_TAC (x, x)
  THEN CONV_TAC SEQ_CONV
;;

%-----------------------------------------------------------------------------
  Lifting tactics.
-----------------------------------------------------------------------------%

let pred_SEQ_VAR = genvar o hd o snd o dest_type o type_of o rand ;;

let POP_PUSH_ASSUM_LIST (tac : tactic) =
  POP_ASSUM_LIST ( \ asl . tac THEN MAP_EVERY ASSUME_TAC (rev asl) )
;;

let pred_TAUT_TAC (asl, g) =
  let x = pred_SEQ_VAR g
  in
  ( pred_SEQ_UNFOLD_TAC x THEN TAUT_TAC ) (asl, g)
;;

let pred_TCL (tac : tactic) =
  let pred_TAC (asl, g) =
    let x = pred_SEQ_VAR g
    in
    ( pred_SEQ_UNFOLD_TAC x THEN tac THEN pred_SEQ_FOLD_TAC x ) (asl, g)
  in
  POP_PUSH_ASSUM_LIST pred_TAC
;;

let pred_TTCL (ttac : thm_tactic) (th : thm) =
  let pred_TAC (asl, g) =
    let x = pred_SEQ_VAR g
    in
    let th' = pred_SEQ_UNFOLD_RULE x th
    in
    ( pred_SEQ_UNFOLD_TAC x THEN ttac th' THEN pred_SEQ_FOLD_TAC x ) (asl, g)
  in
  POP_PUSH_ASSUM_LIST pred_TAC
;;
