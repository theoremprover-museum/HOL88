% File: RCfunction_ex1.ml

  Function example
%

new_theory `RCfunctionex`;;

% --- Simple function: length of a list by counting  --- %

let lenf_DEF = new_definition(`lenf_DEF`,
 "lenf = (assign \l:(*)list.(0,l)) seq
         (do (\(r,l).~(l=[]))
             (assign \(r,l).(SUC r,TL l))) seq
         (assign \(r,l).r)");;

let flen_thm = prove
 ("fcall lenf = (LENGTH:(*)list->num)",
  MATCH_MP_TAC fcall_thm THEN PORT[lenf_DEF] THEN REPEAT CONJ_TAC THENL
  [conj_TAC
  ;strict_TAC
  ;GEN_TAC THEN seq_correct_TAC "\(r,l:(*)list).(r=0)/\(l=u0)" THENL
   [assign_correct_TAC []
   ;seq_correct_TAC "\(r,l:(*)list).(r=LENGTH(u0:(*)list))" THENL
    [do_correct_TAC "\(r,l:(*)list).LENGTH(u0:(*)list) = r + LENGTH l"
                    "\(r:num,l:(*)list).LENGTH l" [ADD_CLAUSES;LENGTH] THEN
     GEN_TAC THEN assign_correct_TAC [] THEN
     PRT[and_DEF] THEN GEN_TAC THEN PBETA_TAC THEN RT[] THEN
     CASE_TAC "SND(u:num#(*)list)" list_CASES [NOT_CONS_NIL;LENGTH;TL] THEN
     BOUND_TAC THEN RT[LESS_SUC_REFL;ADD_CLAUSES]
    ;assign_correct_TAC []
  ]]]);;
