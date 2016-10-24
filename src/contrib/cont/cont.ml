
%=============================================================================
  FILE:         cont.ml
  
  DESCIPTION:   ML code for interactive theorem proving
                with theorem continuation functions.

  AUTHOR:       Ching-Tsun Chou
  
  LAST CHANGED: Tue Oct  6 14:29:49 PDT 1992
=============================================================================%

let f = expandf ;;

let f_ttac_tac (ttac_tac : thm_tactic -> tactic)
    : void -> thm =
  letref th = ARB_THM
  in
  let ttac : thm_tactic = ( \ th' . th := th' ; ALL_TAC )
  in
  ( \ () . f (ttac_tac ttac) ; th )
;;

let f_DISCH_THEN              = f_ttac_tac DISCH_THEN
and f_INDUCT_THEN (th : thm)  = f_ttac_tac (INDUCT_THEN th)
and f_RES_THEN                = f_ttac_tac RES_THEN
and f_STRIP_GOAL_THEN         = f_ttac_tac STRIP_GOAL_THEN
and f_SUBGOAL_THEN (t : term) = f_ttac_tac (SUBGOAL_THEN t)
;;

let f_ttac_ttac (ttac_ttac : thm_tactic -> thm -> tactic)
    : void -> thm -> thm =
  letref th = ARB_THM
  in
  let ttac : thm_tactic = ( \ th' . th := th' ; ALL_TAC )
  in
  ( \ () t . f (ttac_ttac ttac t) ; th )
;;

let f_ALL_THEN                           = f_ttac_ttac ALL_THEN
and f_ANTE_RES_THEN                      = f_ttac_ttac ANTE_RES_THEN
and f_CHOOSE_THEN                        = f_ttac_ttac CHOOSE_THEN
and f_CONJUNCTS_THEN                     = f_ttac_ttac CONJUNCTS_THEN
and f_DISJ_CASES_THEN                    = f_ttac_ttac DISJ_CASES_THEN
and f_FREEZE_THEN                        = f_ttac_ttac FREEZE_THEN
and f_IMP_RES_THEN                       = f_ttac_ttac IMP_RES_THEN
and f_NO_THEN                            = f_ttac_ttac NO_THEN
and f_STRIP_THM_THEN                     = f_ttac_ttac STRIP_THM_THEN
and f_X_CASES_THEN (xll: term list list) = f_ttac_ttac (X_CASES_THEN xll)
and f_X_CHOOSE_THEN (x : term)           = f_ttac_ttac (X_CHOOSE_THEN x)
;;

let f_ttac_ftac (ttac_ftac : thm_tactic -> term -> tactic)
    : void -> term -> thm =
  letref th = ARB_THM
  in
  let ttac : thm_tactic = ( \ th' . th := th' ; ALL_TAC )
  in
  ( \ () x . f (ttac_ftac ttac x) ; th )
;;

let f_FILTER_DISCH_THEN = f_ttac_ftac FILTER_DISCH_THEN
and f_FILTER_STRIP_THEN = f_ttac_ftac FILTER_STRIP_THEN
;;

let f_ttac_ttac_ttac (ttac_ttac_ttac : thm_tactic -> thm_tactic -> thm -> tactic)
    : void -> void -> thm -> (thm # thm) =
  letref th1 = ARB_THM and th2 = ARB_THM
  in
  let ttac1 : thm_tactic = ( \ th1' . th1 := th1' ; ALL_TAC )
  and ttac2 : thm_tactic = ( \ th2' . th2 := th2' ; ALL_TAC )
  in
  ( \ () () t . f (ttac_ttac_ttac ttac1 ttac2 t) ; (th1,th2) )
;;

let f_CONJUNCTS_THEN2  = f_ttac_ttac_ttac CONJUNCTS_THEN2
and f_DISJ_CASES_THEN2 = f_ttac_ttac_ttac DISJ_CASES_THEN2
;;
;;

let f_ttacl_ttac (ttacl_ttac : thm_tactic list -> thm -> tactic)
    : void list -> thm -> thm list =
  letref thl = [ ] : thm list
  in
  let ttacl : int -> thm_tactic list =
      letrec ttacl' (m : int) =
        if (m = 0) then [ ]
                   else ( \ th' . thl := thl @ [th'] ; ALL_TAC ).(ttacl' (m - 1))
      in
      ( \ n . thl := [ ] ; ttacl' n)
  in
  ( \ vl t . f (ttacl_ttac (ttacl (length vl)) t) ; thl )
;;

let f_CASES_THENL                         = f_ttacl_ttac CASES_THENL
and f_DISJ_CASES_THENL                    = f_ttacl_ttac DISJ_CASES_THENL
and f_X_CASES_THENL (xll: term list list) = f_ttacl_ttac (X_CASES_THENL xll)
;;
