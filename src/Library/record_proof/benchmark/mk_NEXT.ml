%
 Theorem for projection of a sequence of microcycles into a single macrocycle.
%

timer true;;

set_flag(`compile_on_the_fly`, true);;

new_theory `NEXT`;;

new_proof_file`mk_NEXT.prf`;;

begin_proof `NEXT`;;

let NEXT =
 new_definition
  (`NEXT`,
   "!done x1 x2.
     NEXT (x1,x2) done =
      (x1 < x2) /\ (done x2) /\ (!x. (x1 < x) /\ (x < x2) ==> ~done x)");;

end_proof();;

begin_proof `STABLE`;;
let STABLE =
 new_definition
  (`STABLE`,
   "!i:num->*. !x1 x2.
     STABLE (x1,x2) i = !x. (x1 <= x) /\ (x < x2) ==> (i x = i x1)");;

end_proof();;

let NEXT_SUC1 =
 prove_thm
  (`NEXT_SUC1`,
   "!done x. done(SUC x) ==> NEXT (x,SUC x) done",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[NEXT]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[LESS_SUC_REFL]
    THEN IMP_RES_TAC LESS_LESS_SUC
    THEN ASM_REWRITE_TAC[]);;

begin_proof `LESS_SUC_EQ_LEMMA`;;
% LESS_SUC_EQ_LEMMA = |- ~(n = SUC m) ==> m < n ==> (SUC m) < n %
let LESS_SUC_EQ_LEMMA =
 (DISCH_ALL
  (MP (SPEC_ALL LESS_SUC_EQ_COR)
      (CONJ (ASSUME "m < n") (NOT_EQ_SYM(ASSUME "~(n = SUC m)")))));;
end_proof();;

let NEXT_SUC2 =
 prove_thm
  (`NEXT_SUC2`,
   "!done x1 x2.
     NEXT (x1,x2) done /\ ~done(SUC x1) ==> NEXT (SUC x1,x2) done",
   REPEAT GEN_TAC
    THEN REWRITE_TAC[NEXT]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SUC_LESS
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC
         (SPECL["done:num->bool";"x2:num";"SUC x1"]
               (INST_TYPE[":num",":*"]FUN_EQ_LEMMA))
    THEN IMP_RES_TAC LESS_SUC_EQ_LEMMA
    THEN ASM_REWRITE_TAC[]);;

let STABLE_SUC =
 prove_thm
  (`STABLE_SUC`,
   "!x1 x2. !i:num->*. STABLE (x1,x2) i ==> STABLE (SUC x1,x2) i",
   REPEAT GEN_TAC
    THEN REWRITE_TAC[STABLE;LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC SUC_LESS
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASSUME_TAC(SPEC "x1:num" LESS_SUC_REFL)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;

begin_proof `SUC_LEMMA`;;
let SUC_LEMMA =
 let [th1;th2;th3;th4] = CONJUNCTS ADD_CLAUSES
 in
 save_thm(`SUC_LEMMA`,LIST_CONJ[th1;th2;SYM th3;th4]);;
end_proof();;

begin_proof`stb_SUC`;;
let stb_SUC =
 SPEC 
  "SUC x"
  (ASSUME "!x'. x <= x' /\ x' < ((SUC x) + d) ==> ((i:num->*) x' = i x)");;
end_proof();;

% Proof modified for HOL version 1.12 		[TFM 91.01.28]	%
let STABLE_LEMMA =
 prove_thm
  (`STABLE_LEMMA`,
   "!x d. !i:num->*.
     STABLE (x,(SUC x)+d) i /\ ~(d = 0) ==> (i x = i(SUC x))",
   REWRITE_TAC[STABLE]
    THEN REPEAT STRIP_TAC
    THEN ASSUME_TAC stb_SUC
    THEN IMP_RES_TAC(SPECL["SUC x";"d:num"]LESS_ADD_NONZERO)
    THEN CONV_TAC SYM_CONV 
    THEN FIRST_ASSUM MATCH_MP_TAC 
    THEN ASSUME_TAC(SPEC "x:num" LESS_EQ_SUC_REFL)
    THEN ASM_REWRITE_TAC[]);;

let NEXT_LEMMA1 =
 prove_thm
  (`NEXT_LEMMA1`,
   "!done x1 x2.
     NEXT (x1,x2) done /\ NEXT (x1,x3) done ==> (x2 = x3)",
   REPEAT GEN_TAC
    THEN REWRITE_TAC[NEXT]
    THEN STRIP_TAC
    THEN ASM_CASES_TAC "x2:num = x3"
    THEN ASM_CASES_TAC "x2 < x3"
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC LESS_CASES_IMP
    THEN RES_TAC);;

let next_SUC =
 DISCH_ALL
  (REWRITE_RULE
   [ADD_CLAUSES] 
   (SUBS[ASSUME "d = 0"](ASSUME "(done:num->bool)((SUC x) + d)")));;

let NEXT_LEMMA2 =
 prove_thm
  (`NEXT_LEMMA2`,
   "!x d done.
     NEXT (x,(SUC x)+d) done /\ ~done(SUC x) ==> ~(d = 0)",
   REWRITE_TAC[NEXT]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC next_SUC
    THEN RES_TAC);;

let NEXT_THM =
 prove_thm
  (`NEXT_THM`,
   "!FUN:*#**->**.
    !f:**->bool. !g:*#**->**. !done:num->bool. !i:num->*. !s:num->**.
    (!x. (done x = f(s x)) /\ (s(x+1) = g(i x,s x))) /\
    (!a b. FUN(a,b) = (f b => b | FUN(a,g(a,b))))    ==>
    (!d x.
      NEXT(x,x+d)done /\ STABLE(x,x+d)i ==> 
      (s(x+d) = FUN(i x,g(i x,s x))))",
   let [done_s;FUN] = CONJUNCTS 
     (ASSUME  "(!x. (done x = f(s x)) /\ (s(SUC x) = g(i x,s x))) /\
          (!a b. (FUN:*#**->**)(a,b) = (f b => b | FUN(a,g(a,b))))") in
   let ind_hyp = ASSUME
     "!x. NEXT(x,x + d)done /\ STABLE(x,x + d)i ==>
          (s(x + d) = (FUN:*#**->**)(i x,g(i x,s x)))" in
   let s_tm = ASSUME 
     "s((SUC x) + d) = (FUN:*#**->**)(i(SUC x),g(i(SUC x),s(SUC x)))"
   in
   REPEAT GEN_TAC
    THEN REWRITE_TAC[SYM(SPEC_ALL ADD1)]
    THEN REPEAT DISCH_TAC
    THEN INDUCT_TAC
    THENL [REWRITE_TAC[NEXT;LESS_REFL;ADD_CLAUSES];ALL_TAC]
    THEN REWRITE_TAC[SUC_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC "done(SUC x):bool"
    THENL
     [IMP_RES_TAC NEXT_SUC1
       THEN IMP_RES_TAC NEXT_LEMMA1
       THEN IMP_RES_TAC ADD_INV_0
       THEN REWRITE_TAC[ASSUME "d=0";ADD_CLAUSES]
       THEN REWRITE_TAC
             ([SPECL["(i:num->*)x";"(g:*#**->**)(i(x:num),s x)"]FUN;
               ASSUME "done(SUC x):bool"]@
              (map SYM (CONJUNCTS(SPEC_ALL done_s))));
      ALL_TAC]
    THEN ASSUME_TAC(SPEC "SUC x" ind_hyp)
    THEN IMP_RES_TAC STABLE_SUC
    THEN IMP_RES_TAC NEXT_SUC2
    THEN RES_TAC
    THEN REWRITE_TAC[s_tm]
    THEN SUBST_TAC[SPECL["(i:num->*)x";"(g:*#**->**)(i(x:num),s x)"]FUN]
    THEN REWRITE_TAC
          (ASSUME "~done(SUC x)" .(map SYM (CONJUNCTS(SPEC_ALL done_s))))
    THEN IMP_RES_TAC NEXT_LEMMA2
    THEN IMP_RES_TAC STABLE_LEMMA
    THEN REWRITE_TAC[ASSUME "(i:num->*) x = i(SUC x)";done_s]);;

close_proof_file();;
close_theory();;

quit();;

