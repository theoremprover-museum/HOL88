
%=============================================================================
  FILE:         mk_pred.ml
  
  DESCIPTION:   Definitions and basic theorems for Logic of Predicates.
  
  AUTHOR:       Ching-Tsun Chou
  
  CREATED:      Sun May 31 14:19:57 PDT 1992
  LAST CHANGED: Tue Oct  6 11:55:13 PDT 1992
=============================================================================%

new_theory `pred` ;;

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
  Logical operators on predicates.
-----------------------------------------------------------------------------%

let pred_TT_DEF = new_definition (`pred_TT_DEF`,
"
  (TT) (x : *) = T
") ;;

let pred_FF_DEF = new_definition (`pred_FF_DEF`,
"
  (FF) (x : *) = F
") ;;

let pred_NEG_DEF = new_definition (`pred_NEG_DEF`,
"
  (~~ P) (x : *) = ~ (P x)
") ;;

let pred_CONJ_DEF = new_infix_definition (`pred_CONJ_DEF`,
"
  ($//\\ P Q) (x : *) = (P x) /\ (Q x)
") ;;
  
let pred_DISJ_DEF = new_infix_definition (`pred_DISJ_DEF`,
"
  ($\\// P Q) (x : *) = (P x) \/ (Q x)
") ;;

let pred_IMP_DEF = new_infix_definition (`pred_IMP_DEF`,
"
  ($==>> P Q) (x : *) = (P x) ==> (Q x)
") ;;

let pred_EQ_DEF = new_infix_definition (`pred_EQ_DEF`,
"
  ($==   P Q) (x : *) = ((P x) = (Q x : bool))
") ;;

let pred_FORALL_DEF = new_binder_definition (`pred_FORALL_DEF`,
"
  ($!! R) (x : *) = (! i : *i . R i x)
") ;;

let pred_EXISTS_DEF = new_binder_definition (`pred_EXISTS_DEF`,
"
  ($?? R) (x : *) = (? i : *i . R i x)
") ;;

%-----------------------------------------------------------------------------
  Sequent.
-----------------------------------------------------------------------------%

let pred_SEQ_AUX_DEF = new_list_rec_definition (`pred_SEQ_AUX_DEF`,
"
  ( PSEQ NIL         Q (x : *) = (Q x)                   ) /\
  ( PSEQ (CONS P Ps) Q (x : *) = (P x) ==> (PSEQ Ps Q x) )
") ;;

let pred_SEQ_DEF = new_infix_definition (`pred_SEQ_DEF`,
"
  $|= Ps Q = (! x : * . PSEQ Ps Q x)
") ;;

%-----------------------------------------------------------------------------
  Theorem for Unfolding and folding.
-----------------------------------------------------------------------------%

let pred_UNFOLD_FOLD = prove_thm (`pred_UNFOLD_FOLD`,
"
  ( ( ! Ps Q . (Ps |= Q) = (! x : * . PSEQ Ps Q x) )
    /\
    ( ! x : * . ! Q .      (PSEQ NIL         Q x) = (Q x)                   ) /\
    ( ! x : * . ! Q P Ps . (PSEQ (CONS P Ps) Q x) = (P x) ==> (PSEQ Ps Q x) )
    /\
    ( ! x : * .               (TT) x = T                  ) /\
    ( ! x : * .               (FF) x = F                  ) /\
    ( ! x : * . ! P   .     (~~ P) x = ~ (P x)            ) /\
    ( ! x : * . ! P Q . (P //\\ Q) x = (P x) /\ (Q x)     ) /\
    ( ! x : * . ! P Q . (P \\// Q) x = (P x) \/ (Q x)     ) /\
    ( ! x : * . ! P Q . (P ==>> Q) x = (P x) ==> (Q x)    ) /\
    ( ! x : * . ! P Q . (P  ==  Q) x = ((P x) = (Q x))    ) /\
    ( ! x : * . ! R .      ($!! R) x = (! i : *i . R i x) ) /\
    ( ! x : * . ! R .      ($?? R) x = (? i : *i . R i x) ) )
  /\
  ( ( ! Ps Q . (! x : * . PSEQ Ps Q x) = (Ps |= Q) )
    /\
    ( ! x : * . ! Q .      (Q x)                   = (PSEQ NIL         Q x) ) /\
    ( ! x : * . ! Q P Ps . (P x) ==> (PSEQ Ps Q x) = (PSEQ (CONS P Ps) Q x) )
    /\
    ( ! x : * .         T                  =       (TT) x ) /\
    ( ! x : * .         F                  =       (FF) x ) /\
    ( ! x : * . ! P   . ~ (P x)            =     (~~ P) x ) /\
    ( ! x : * . ! P Q . (P x) /\ (Q x)     = (P //\\ Q) x ) /\
    ( ! x : * . ! P Q . (P x) \/ (Q x)     = (P \\// Q) x ) /\
    ( ! x : * . ! P Q . (P x) ==> (Q x)    = (P ==>> Q) x ) /\
    ( ! x : * . ! P Q . ((P x) = (Q x))    = (P  ==  Q) x ) /\
    ( ! x : * . ! R .   (! i : *i . R i x) =    ($!! R) x ) /\
    ( ! x : * . ! R .   (? i : *i . R i x) =    ($?? R) x ) )
", (
  REWRITE_TAC
  [ pred_SEQ_DEF ; pred_SEQ_AUX_DEF ;
    pred_TT_DEF ; pred_FF_DEF ; pred_NEG_DEF ;
    pred_CONJ_DEF ; pred_DISJ_DEF ; pred_IMP_DEF ; pred_EQ_DEF ;
    pred_FORALL_DEF ; pred_EXISTS_DEF ]
)) ;;

%-----------------------------------------------------------------------------
  Change from draft mode to proof mode.
-----------------------------------------------------------------------------%

close_theory () ;;
