
new_theory `mut_rec_tools`;;

% EA_SWITCH bytter om paa eksistens og forall, de frie variable bliver til %
% parametre. %

let EA_SWITCH = prove_thm (`EA_SWITCH`, "!t:*->(*1->*2)->bool. (!x:*. ?f:*1->*2. t x f) = (?f':*->*1->*2. !x:*. t x (f' x))",
                        GEN_TAC THEN
                        EQ_TAC THENL [
                        DISCH_TAC THEN
                        (EXISTS_TAC "(\y:*. (@f:*1->*2. t y f))") THEN
                        (POP_ASSUM MP_TAC) THEN
                        (PURE_ONCE_REWRITE_TAC [EXISTS_DEF]) THEN
                        BETA_TAC THEN
                        (REWRITE_TAC []);
                        DISCH_TAC THEN
                        GEN_TAC THEN
                        (EXISTS_TAC "(@f':*->*1->*2. !x:*. t x (f' x)) x") THEN
                        (POP_ASSUM MP_TAC) THEN
                        (PURE_ONCE_REWRITE_TAC [EXISTS_DEF]) THEN
                        BETA_TAC THEN
                        (DISCH_THEN (ASSUME_TAC o (SPEC "x:*"))) THEN
                        (PURE_ONCE_ASM_REWRITE_TAC [])]);;

% The following theorem is ONLY dependent on the number of %
% mutually recursive types ...                             %

%
2:
|- !t. (?p q. t p q) /\
       (!xa xb ya yb. t xa ya /\ t xb yb ==> (xa = xb) /\ (ya = yb)) ==>
       (?! p q. t p q)
3:
|- !t. (?p q r. t p q r) /\
       (!xa xb ya yb za zb.
          t xa ya za /\ t xb yb zb ==>
            (xa = xb) /\ (ya = yb) /\ (za = zb)
       ) ==>
       (?! p q r. t p q r)
i:
|- !t. (?x1 .. xi. t x1 .. xi) /\
       (!x1 y1 .. xi yi).
          t x1 .. xi /\ t y1 .. yi ==>
            (x1=y1) /\ .. /\ (xi=yi)
       ) ==>
       (?! x1 .. xi. t x1 .. xi)
%


let our_exists_unique_thm_2 =
  prove_thm(`our_exists_unique_thm_2`, make_exists_unique_term 2,
    (REPEAT STRIP_TAC) THEN
    (CONV_TAC EXISTS_UNIQUE_CONV) THEN
    CONJ_TAC THENL [
     OUR_EXISTS_TAC THEN
     (CONV_TAC EXISTS_UNIQUE_CONV) THEN
     CONJ_TAC THENL [
      OUR_EXISTS_TAC THEN
      (FIRST_ASSUM ACCEPT_TAC)
     ;
      BETA_TAC THEN
      (REPEAT GEN_TAC) THEN
      (FIRST_ASSUM (\th. ACCEPT_TAC (
      (\x. let t1 = SPECL ["x1:*";"x1:*";"x:**";"y:**"] x in
           let (lhs,_) = dest_imp (concl t1) in
           let t2 = UNDISCH t1 in
           let t3 = hd(rev(CONJUNCTS t2)) in
           DISCH lhs t3)
      th)
       ? NO_TAC))
     ]
    ;
     (CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV)) THEN
     BETA_TAC THEN
     (REPEAT GEN_TAC) THEN
     (DISCH_THEN STRIP_ASSUME_TAC) THEN
     (\(asl,w).FIRST_ASSUM (\th. ACCEPT_TAC (
      (\x. let t1 = SPECL ["x:*";"y:*";"x2':**";"x2'':**"] x in
           let c1 = ASSUME (pick 4 asl) and
               c2 = ASSUME (pick 2 asl) in
           let conj = CONJ c1 c2 in
           let t2 = MP t1 conj in
           (foldr1 CONJ) (rev(tl(rev(CONJUNCTS t2))))) th)
       ? NO_TAC) (asl,w))
    ]);;

let OUR_EXISTS_UNIQUE_TAC_2 :tactic (asl,w) = 
  letrec doit f x n =
    if n=0 then ([],x)
    else
     let (v,body) = f x in
     let (vs, remains) = doit f body (n-1) in
     (v.vs, remains) in
  let (vars,body)= doit (dest_abs o snd o dest_comb) w 2 in
  let (term_subst, type_subst) =
     match "t:*->**->bool" (list_mk_abs (vars, body)) in
  let instantiated_thm= SPEC (fst(hd term_subst))
                        (INST_TYPE type_subst our_exists_unique_thm_2) in
  let (antecedent, conclusion) = dest_imp(concl instantiated_thm) in
  [(asl, antecedent)], (\l. CONV_RULE
                           (DEPTH_CONV BETA_CONV)
                           (MP instantiated_thm (hd l)));;

let our_exists_unique_thm_3 =
   prove_exists_unique_thm OUR_EXISTS_UNIQUE_TAC_2 3;;

let OUR_EXISTS_UNIQUE_TAC_3 =
   make_our_exists_unique_tac our_exists_unique_thm_3 3;;

let our_exists_unique_thm_4 =
   prove_exists_unique_thm OUR_EXISTS_UNIQUE_TAC_3 4;;

let OUR_EXISTS_UNIQUE_TAC_4 =
   make_our_exists_unique_tac our_exists_unique_thm_4 4;;

close_theory();;
