% File: RCex_procedure1.ml

  Procedure examples
  NB: uses the more_lists library
%

load_library `more_lists`;;

% --- Simple procedures  --- %

% simple example %
let proc1 = "nondass \(x:*x,y:*y)(x',y').(x'=y)/\(y'=x)";;
let G = "\(a:bool,b:num,c:num,d:bool).(b,c)";;
let thm1 = prove_pcall proc1 G;;

% another example, to check %
let proc2 = "nondass \x:num. \x'. x' = SUC x";;
let G = "\(a:bool,b:num,c:num,d:bool).c";;
let thm2 = prove_pcall proc2 G;;

% example with precondition %
let proc3 = "(assert \x.0<x) seq (nondass \x x'. x = SUC x')";;
let G = "\(a:bool,b:num,c:num,d:bool).c";;
let thm3 = prove_pcall_pre proc3 G;;


% --- A list reversing procedure --- %

let preverse_DEF = new_definition(`preverse_DEF`,"preverse =
   (assign \l:(*)list.([]:(*)list,l)) seq
   (do (\(rl,l).~(l=[]))
       (assign \(rl,l).(CONS(HD l)rl,TL l))) seq
   (assign \(rl,l).rl)");;
let thm1 = prove
 ("correct (\l:(*)list.l=l0) preverse (\l. l = REVERSE l0)",
  PORT[preverse_DEF] THEN
  seq_correct_TAC "\(rl:(*)list,l:(*)list).(rl=[])/\(l=l0)" THENL
  [assign_correct_TAC []
  ;seq_correct_TAC "\(rl:(*)list,l:(*)list).(rl = REVERSE l0)" THENL
   [do_correct_TAC "\(rl:(*)list,l).REVERSE l0 = APPEND(REVERSE l)rl" 
                   "\(rl:(*)list,l:(*)list).LENGTH l"
                   [APPEND_CLAUSES;REVERSE_CLAUSES] THEN
    GEN_TAC THEN assign_correct_TAC [] THEN RT[and_DEF] THEN
    STATE_GEN_TAC "rl:(*)list,l:(*)list" THEN
    CASE_TAC "l:(*)list" list_CASES [NOT_CONS_NIL;HD;TL] THEN
    LRT[LENGTH;REVERSE;GSYM APPEND_ASSOC;APPEND] THEN
    BOUND_TAC THEN RT[LESS_SUC_REFL]
   ;assign_correct_TAC []
  ]]);;
let reverse_spec = "nondass \l:(*)list. \l'. l' = REVERSE l";;
let thm2 = prove
 ("^reverse_spec ref preverse",
  PORT[SYM assign_eq_nondass] THEN MATCH_MP_TAC impl_assign THEN 
  RT[thm1;preverse_DEF] THEN mono_TAC);;

let G = "\(x:num,y:(num)list,z:bool).y";;
let V = "\(x:num,y:(num)list,z:bool).one";;

prove_pcall_ref thm2 G;;
% result is theorem which says that a call to preverse with parameter
  function \(x,y,z).y in fact reverses y and leaves rest unchanged:
|- (nondass
    (\(x,y,z) (x',y',z'). (y' = REVERSE y) /\ (x = x') /\ (z = z'))) ref
   (pcall preverse (\(x,y,z). y) (\(x,y,z). (x,z)))
%

prove_xpcall_ref thm2 G V;;
% shows that call with value parameter of type :one is equivalent
  to call without any value parameter %


% --- a recursive procedure --- %

let peven_DEF = new_definition(`peven_DEF`,"peven =
  mu (\X. cond (\(r:bool,x). x=0)
               (assign \(r,x).(T,x))
               ((assign \(r,x).(r,PRE x)) seq
                X seq
                (assign \(r,x).((~r),x))))");;
let even_spec = "nondass \(r:bool,x)(r',x':num). r' = EVEN x";;
let thm1 = prove
 ("^even_spec ref peven",
  PORT[peven_DEF] THEN MATCH_MP_TAC mu_thm THEN REPEAT CONJ_TAC THENL
  [BETA_TAC THEN regular_TAC
  ;mono_TAC
  ;BETA_TAC THEN EXISTS_TAC "\(r:bool,x:num).x" THEN GEN_TAC THEN
   LPRT[ref_DEF;cond_DEF;seq_DEF;nondass_DEF;assign_DEF;assert_DEF] THEN
   GEN_TAC THEN LPRT[implies_DEF;and_DEF;or_DEF;not_DEF] THEN PBETA_TAC THEN
   STATE_GEN_TAC "r:bool,x:num" THEN
   CASE_TAC "x:num" num_CASES [NOT_SUC;EVEN;PRE] THENL
   [STRIP_TAC THEN POP_ASSUM(ACCEPT_TAC o RR[] o SPEC "T,0")
   ;STRIP_TAC THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN RT[LESS_SUC_REFL] THEN
    REPEAT STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
    POP_ASSUM(ACCEPT_TAC o RR[] o SPEC "(~EVEN n),SND(u':bool#num)")
  ]]);;
prove_pcall_ref thm1 "\(a:num,b:bool,c:bool,d:num).(b,d)";;
% result:
|- (nondass
    (\(a,b,c,d) (a',b',c',d'). (b' = EVEN d) /\ (a = a') /\ (c = c'))) ref
   (pcall peven (\(a,b,c,d). (b,d)) (\(a,b,c,d). (a,c)))
%


% --- Recursive procedure with self-call: list reversal --- %

let rev_spec = "nondass \l:(*)list. \l'. l' = REVERSE l";;
let rev_DEF = new_definition(`rev_DEF`,
  "rev =
     mu \X. (nondass \l:(*)list. \(x:*,l').l'=l) seq
            (cond (\(x,l).l=[])
              (assign \(x,l).l)
              ((assign \(x,l).(HD l,TL l)) seq
               (pcall X (\(x,l).l) (\(x,l).x)) seq
               (assign \(x,l).(SNOC x l))))");;
let thm1 = prove_pcall_pre 
     "(assert(\u:(*)list.(LENGTH u)<i)) seq (nondass \l l'. l' = REVERSE l)"
     "\(x:*,l:(*)list).l";;
let thm2 = prove
 ("^rev_spec ref rev",
  PORT[rev_DEF] THEN MATCH_MP_TAC mu_thm THEN REPEAT CONJ_TAC THENL
  [BETA_TAC THEN regular_TAC
  ;mono_TAC
  ;EXISTS_TAC "\l:(*)list.LENGTH l" THEN GEN_TAC THEN BETA_TAC THEN 
   LPRT[SYM thm1;ref_DEF;seq_DEF;cond_DEF;seq_DEF;nondass_DEF;
        assign_DEF;assert_DEF] THEN
   GEN_TAC THEN LPRT[implies_DEF;and_DEF;or_DEF;not_DEF] THEN PBETA_TAC THEN
   GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN
   POP_ASSUM(ASSUME_TAC o CONV_RULE FORALL_1PT_CONV) THEN
   STATE_GEN_TAC "x:*,l:(*)list" THEN DISCH_THEN SUBST1_TAC THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   CASE_TAC "u:(*)list" list_CASES [NOT_CONS_NIL;HD;TL;LENGTH;REVERSE] THEN
   LRT[LESS_SUC_REFL;GSYM SNOC_DEF;APPEND_CLAUSES] THEN
   REPEAT STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN ART[]
  ]);;
prove_pcall_ref thm2 "\(a:num,b:(num)list,c:bool,d:num).b";;
%
|- (nondass
    (\(a,b,c,d) (a',b',c',d').
      (b' = REVERSE b) /\ (a = a') /\ (c = c') /\ (d = d'))) ref
   (pcall rev(\(a,b,c,d). b)(\(a,b,c,d). (a,c,d)))
%


% --- Procedure with value parameters --- %

let REMOVE_DEF = new_list_rec_definition(`REMOVE_DEF`,
  "(REMOVE (x:*) [] = []) /\
   (REMOVE x (CONS h t) = (x=h) => REMOVE x t | CONS h (REMOVE x t))");;
let remove_spec = "nondass \l:(*)list. \l'. l' = REMOVE a l";;
let premov_DEF = new_definition(`premov_DEF`,
  "premov a =
     (assign \l:(*)list.([],l)) seq
     (do (\(x,l).~(l=[]))
         (cond (\(x,l). HD l = a)
            (assign \(x,l).(x,TL l))
            (assign \(x,l).(SNOC (HD l) x,TL l)) )) seq
     (assign \(x,l).x)");;
let thm1 = prove
 ("^remove_spec ref (premov a)",
  PORT[SYM assign_eq_nondass] THEN MATCH_MP_TAC impl_assign THEN 
  CONJ_TAC THENL
  [PORT[premov_DEF] THEN mono_TAC
  ;PORT[premov_DEF] THEN GEN_TAC THEN
   seq_correct_TAC "\(x:(*)list,l:(*)list).(x=[])/\(l=u0)" THENL
   [assign_correct_TAC []
   ;seq_correct_TAC "\(x:(*)list,l:(*)list).(x = REMOVE a u0)" THENL
    [do_correct_TAC "\(x:(*)list,l).REMOVE a u0 = APPEND x (REMOVE a l)" 
                    "\(x:(*)list,l:(*)list).LENGTH l"
                    [APPEND_CLAUSES;REMOVE_DEF] THEN
     GEN_TAC THEN cond_correct_TAC THENL
     [assign_correct_TAC [] THEN RT[and_DEF] THEN
      STATE_GEN_TAC "x:(*)list,l:(*)list" THEN
      CASE_TAC "l:(*)list" list_CASES [NOT_CONS_NIL;HD;TL;LENGTH] THEN
      STRIP_TAC THEN ART[REMOVE_DEF] THEN
      POP_ASSUM(SUBST1_TAC o SYM) THEN RT[LESS_SUC_REFL]
     ;assign_correct_TAC [] THEN LRT[and_DEF;not_DEF] THEN
      STATE_GEN_TAC "x:(*)list,l:(*)list" THEN
      CASE_TAC "l:(*)list" list_CASES [NOT_CONS_NIL;HD;TL;LENGTH] THEN
      STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN 
      POP_ASSUM SUBST1_TAC THEN PORT[REMOVE_DEF] THEN
      POP_ASSUM(\t.RT[GSYM t]) THEN 
      LRT[SNOC_APPEND_CONS;GSYM APPEND_ASSOC;APPEND_CLAUSES;LESS_SUC_REFL]
     ]
    ;assign_correct_TAC []
  ]]]);;

let G = "\(a:bool,b:(num)list,c:num).b";;
let V = "\(a:bool,b:(num)list,c:num).SUC c";;
prove_xpcall_ref thm1 G V;;
%
|- (nondass
    (\(a,b,c) (a',b',c'). (b' = REMOVE(SUC c)b) /\ (a = a') /\ (c = c'))) ref
   (xpcall premov (\(a,b,c). b) (\(a,b,c). (a,c)) (\(a,b,c). SUC c))
%