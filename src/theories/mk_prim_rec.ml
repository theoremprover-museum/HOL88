%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_prim_rec.ml                                        %
%                                                                             %
%     DESCRIPTION:      Prove the primitive recusion theorem                  %
%                                                                             %
%     PARENTS:          num.th                                                %
%     WRITES FILES:     prim_rec.th                                           %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%
%
 In this file, which should be loaded into basic-hol after deleting
 hol/prim_rec.th, we prove the primitive recursion theorem directly
 from Peano's axioms (which are actually theorems in HOL). 
 These `axioms' define the type ":num" and two
 constants "0:num" and "SUC:num->num", they are:
  
    NOT_SUC   |- !n. ~(SUC n = 0)

    INV_SUC   |- !m n. (SUC m = SUC n) ==> (m = n)

    INDUCTION |- !P. (P 0 /\ (!n. P n ==> P(SUC n))) ==> !n. P n

 Using INDUCTION one can define an induction rule and tactic. 
 The rule is an ML function:

  INDUCT: (thm # thm) -> thm

    A1 |- t[0]      A2 |- !n. t[n] ==> t[SUC n]
  -----------------------------------------------
              A1 u A2 |- !n. t[n]

 The tactic is:

             [A] !n.t[n]
   ================================
    [A] t[0]  ,  [A,t[n]] t[SUC x]

 From now on we only make (non-recursive) definitions and prove theorems. 

 The following definition of < is from Hodges's article in "The Handbook of 
 Philosophical Logic" (page 111):

    m < n = ?P. (!n. P(SUC n) ==> P n) /\ P m /\ ~(P n)


 The following consequence of INV_SUC will be useful for rewriting:

  |- !m n. (SUC m  =  SUC n)  =  (m  =  n)

 It is used in SUC_ID and PRIM_REC_EXISTS below. We establish it by
 forward proof. 

 After proving this we prove some standard properties of <.
%

new_theory `prim_rec`;;

new_parent `num`;;

% Added TFM 88.04.02						%
let NOT_SUC     = theorem `num` `NOT_SUC`
and INV_SUC     = theorem `num` `INV_SUC`
and INDUCTION   = theorem `num` `INDUCTION`;;

let LESS = 
    new_infix_definition
    (`LESS`,
     "$< m n = ?P. (!n. P(SUC n) ==> P n) /\ P m /\ ~(P n)");;

% ------------------------------------------------------------- %
% We need to load in the induction tactic.  It's in ml/ind.ml	%
% but it is part of hol rather than basic hol, so it's loaded   %
% in uncompiled (since it may not have been recompiled since    %
% basic-hol was last rebuilt.		       [TFM 88.04.02]   %
%								%
% Modified to load ind.ml, to ensure that it's uncompiled.	%
% ------------------------------------------------------------- %

loadt (concat ml_dir_pathname `ind.ml`);;

% And create an induction tactic 				%
% Added: TFM 88.03.31						%
let INDUCT_TAC = INDUCT_THEN INDUCTION ASSUME_TAC;;

let INV_SUC_EQ =
 save_thm
  (`INV_SUC_EQ`, 
   GEN_ALL
     (IMP_ANTISYM_RULE
      (SPEC_ALL INV_SUC)
      (DISCH "m:num = n" (AP_TERM "SUC" (ASSUME "m:num = n")))));;

let LESS_REFL =
 prove_thm
  (`LESS_REFL`,
   "!n. ~(n < n)",
   GEN_TAC THEN REWRITE_TAC[LESS;NOT_AND]);;

let SUC_LESS =
 prove_thm
  (`SUC_LESS`,
   "!m n. (SUC m) < n  ==>  m < n",
   REWRITE_TAC[LESS]
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC "P:num->bool"
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;

let NOT_LESS_0 =
 prove_thm
  (`NOT_LESS_0`,
   "!n. ~(n < 0)",
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_REFL]
    THEN IMP_RES_TAC(CONTRAPOS(SPECL["n:num";"0"]SUC_LESS))
    THEN ASM_REWRITE_TAC[]);;

let LESS_0_0 =
 prove_thm
  (`LESS_0_0`,
   "0 < SUC 0",
   REWRITE_TAC[LESS]
    THEN EXISTS_TAC "\x.x=0"
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[NOT_SUC]);;

let LESS_MONO =
 prove_thm
  (`LESS_MONO`,
   "!m n. m < n ==> SUC m < SUC n",
   REWRITE_TAC[LESS]
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC "\x.(x = SUC m) \/ (P x)"
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC
          (DISCH_ALL
           (CONTRAPOS(SPEC"n:num"(ASSUME "!n'. P(SUC n')  ==>  P n'"))))
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN IMP_RES_TAC INV_SUC 
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME "n:num = m"](ASSUME "~(P(n:num))")))
    THEN RES_TAC);;

let LESS_SUC_REFL =
 prove_thm
  (`LESS_SUC_REFL`,
   "!n. n < SUC n",
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_0_0]
    THEN IMP_RES_TAC LESS_MONO
    THEN ASM_REWRITE_TAC[]);;

let LESS_SUC =
 prove_thm
 (`LESS_SUC`,
  "!m n. m < n ==> m < SUC n",
  REWRITE_TAC [LESS] 
   THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC "P:num->bool"
   THEN IMP_RES_TAC
         (CONTRAPOS(SPEC "n:num" (ASSUME "!n'. P(SUC n')  ==>  P n'")))
   THEN ASM_REWRITE_TAC[]);;

let LESS_LEMMA1 =
 prove_thm
  (`LESS_LEMMA1`,
   "!m n. m < SUC n ==> (m = n) \/ (m < n)",
   REWRITE_TAC[LESS]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC "m:num = n"
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC "\x:num. ~(x = n) /\ (P x)"
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME "n':num = n"](ASSUME"P(SUC n'):bool")))
    THEN ASSUME_TAC(REFL"n:num")
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;

let LESS_LEMMA2 =
 prove_thm
  (`LESS_LEMMA2`,
   "!m n. (m = n) \/ (m < n) ==> m < SUC n",
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_SUC
    THEN ASM_REWRITE_TAC[LESS_SUC_REFL]);;

% |- !m n. m < (SUC n)  =  (m  =  n)  \/  m < n %

let LESS_THM =
 save_thm
  (`LESS_THM`,
   GEN_ALL(IMP_ANTISYM_RULE(SPEC_ALL LESS_LEMMA1)(SPEC_ALL LESS_LEMMA2)));;

let LESS_SUC_IMP =
 prove_thm
  (`LESS_SUC_IMP`,
   "!m n. (m < SUC n) ==> ~(m = n) ==> (m < n)",
   REWRITE_TAC[LESS_THM]   
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;

let LESS_0 =
 prove_thm
  (`LESS_0`,
   "!n. 0 < (SUC n)",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[LESS_THM]);;

let EQ_LESS =
 prove_thm
  (`EQ_LESS`,
   "!n. (SUC m = n) ==> (m < n)",
   INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC;LESS_THM]
    THEN DISCH_TAC
    THEN IMP_RES_TAC INV_SUC
    THEN ASM_REWRITE_TAC[]);;

let SUC_ID =
 prove_thm
  (`SUC_ID`,
   "!n. ~(SUC n = n)",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_SUC;INV_SUC_EQ]);;

let NOT_LESS_EQ =
 prove_thm
  (`NOT_LESS_EQ`,
   "!m n. (m = n) ==> ~(m < n)",
   REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC[LESS_REFL]);;

let LESS_NOT_EQ =
 prove_thm
  (`LESS_NOT_EQ`,
   "!m n. m < n ==> ~(m = n)",
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME "m:num = n"](ASSUME "m < n")))
    THEN IMP_RES_TAC LESS_REFL
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;

%
 Now we start a new theory in which we will prove that:

   |- !x f. ?fun.
       (fun 0 = x) /\
       (!m. fun(SUC m) = f(fun m)m)

  We start by defining a (higher order) function SIMP_REC and
  proving that:

    |- !m x f.
        (SIMP_REC x f 0 = x) /\
        (SIMP_REC x f (SUC m) = f(SIMP_REC x f m))

  We then define a function PRIM_REC in terms of SIMP_REC and prove that:

    |- !m x f.
        (PRIM_REC x f 0  = x) /\
        (PRIM_REC x f (SUC m) = f(PRIM_REC x f m)m)

  This is sufficient to justify any primitive recursive definition
  because a definition:

      fun 0 x1 ... xn       = f1(x1, ... ,xn)

      fun (SUC m) x1 ... xn = f2(fun m x1 ... xn, m, x1, ... ,xn)

  is equivalent to:

      fun 0       = \x1 ... xn. f1(x1, ... ,xn)

      fun (SUC m) = \x1 ... xn. f2(fun m x1 ... xn, m, x1, ... ,xn)
                  = (\f m x1 ... xn. f2(f x1 ... xn, m, x1, ... ,xn))(fun m)m
   
  which defines f to be:

      PRIM_REC
       (\x1 ... xn. f1(x1, ... ,xn))
       (\f m x1 ... xn. f2(f x1 ... xn, m, x1, ... ,xn))
%

let SIMP_REC_REL =
 new_definition
  (`SIMP_REC_REL`,
   "!fun:num->*. !x:*. !f:*->*. !n:num.
      SIMP_REC_REL fun x f n =
       (fun 0 = x) /\ !m. m < n ==> (fun(SUC m) = f(fun m))");;

let SIMP_REC_FUN =
 new_definition
  (`SIMP_REC_FUN`,
   "SIMP_REC_FUN (x:*) (f:*->*) (n:num) = 
     @fun. SIMP_REC_REL fun x f n");;

let SIMP_REC =
 new_definition
  (`SIMP_REC`,
   "SIMP_REC (x:*) (f:*->*) (n:num) = 
     SIMP_REC_FUN x f (SUC n) n");;

%
   |- (?fun. SIMP_REC_REL fun x f n)  =
       (SIMP_REC_FUN x f n 0  =  x)  /\
       (!m.
         m < n  ==>
         (SIMP_REC_FUN x f n (SUC m)  =  f(SIMP_REC_FUN x f n m)))
%

let SIMP_REC_FUN_LEMMA =
 let t1 = "?fun:num->*. SIMP_REC_REL fun x f n"
 and t2 = "SIMP_REC_REL (@fun:num->*. SIMP_REC_REL fun x f n) x f n"
 in
 let th1 = DISCH t1 (SELECT_RULE(ASSUME t1))
 and th2 = DISCH t2 (EXISTS(t1, "@fun:num->*.SIMP_REC_REL fun x f n")(ASSUME t2))
 in
 let th3 = 
  PURE_REWRITE_RULE[SYM(SPEC_ALL SIMP_REC_FUN)](IMP_ANTISYM_RULE th1 th2)
 in
 save_thm
  (`SIMP_REC_FUN_LEMMA`,
   th3 TRANS DEPTH_CONV(REWR_CONV SIMP_REC_REL)(rhs(concl th3)));;

%
    A |- ~(t1 = t2)
   -----------------
    A |- ~(t2 = t1)

Deleted by WW 26 Jan 94. Use the global version

let NOT_EQ_SYM th =
 let t = (mk_eq o (\(x,y).(y,x)) o dest_eq o dest_neg o concl) th
 in
 MP (SPEC t IMP_F) (DISCH t (MP th (SYM(ASSUME t))));;
%

% Following proof revised for version 1.12 resolution. 	 [TFM 91.01.18] %

let SIMP_REC_EXISTS =
 prove_thm
  (`SIMP_REC_EXISTS`,
   "!x f n. ?fun:(num->*). SIMP_REC_REL fun x f n",
   GEN_TAC THEN GEN_TAC THEN
   INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THEN
   PURE_REWRITE_TAC[SIMP_REC_REL] THENL
   [EXISTS_TAC "\p:num.(x:*)" THEN REWRITE_TAC[NOT_LESS_0];
    EXISTS_TAC "\p. ((p=(SUC n)) => 
                    f(SIMP_REC_FUN (x:*) f n n) | SIMP_REC_FUN x f n p)" THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[NOT_EQ_SYM(SPEC_ALL NOT_SUC)] THEN
    IMP_RES_TAC SIMP_REC_FUN_LEMMA THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC "m:num = n" THEN
    IMP_RES_TAC LESS_NOT_EQ THEN
    IMP_RES_TAC LESS_SUC_IMP THEN RES_TAC THEN
    ASM_REWRITE_TAC[LESS_THM;INV_SUC_EQ;SUC_ID]]);;

%
   |- !x f n.
       (SIMP_REC_FUN x f n 0  =  x)  /\
       (!m.
         m < n  ==>
         (SIMP_REC_FUN x f n (SUC m)  =  f(SIMP_REC_FUN x f n m)))
%

% No longer saved in prim_rec.th.		        [TFM 90.04.25] %

let SIMP_REC_FUN_THM =
   GEN_ALL(EQ_MP(SPEC_ALL SIMP_REC_FUN_LEMMA)(SPEC_ALL SIMP_REC_EXISTS));;

let SIMP_REC_FUN_THM1 = 
    GEN_ALL(CONJUNCT1(SPEC_ALL SIMP_REC_FUN_THM));;

let SIMP_REC_FUN_THM2 =
    GEN "n:num" (CONJUNCT2(SPEC_ALL SIMP_REC_FUN_THM));;

% Proof modified for new RES_TAC 			[TFM 90.04.25]  %
% Also, result not now saved in prim_rec.th.				%

let SIMP_REC_UNIQUE =
    TAC_PROOF
    (([], "!n m1 m2 (x:*) f.
            (n < m1) ==>
            (n < m2) ==>
            (SIMP_REC_FUN x f m1 n = SIMP_REC_FUN x f m2 n)"),
    INDUCT_TAC
     THEN ASM_REWRITE_TAC[SIMP_REC_FUN_THM1]
     THEN REPEAT GEN_TAC
     THEN REPEAT DISCH_TAC
     THEN IMP_RES_TAC SUC_LESS
     THEN IMP_RES_TAC SIMP_REC_FUN_THM2
     THEN ASM_REWRITE_TAC[]
     THEN RES_TAC
     THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let LESS_SUC_SUC =
 prove_thm
  (`LESS_SUC_SUC`,
   "!m. m < SUC m /\ m < SUC(SUC m)",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[LESS_THM]);;

let SIMP_REC_THM =
 prove_thm
  (`SIMP_REC_THM`,
   "!(x:*) f.
     (SIMP_REC x f 0 = x) /\
     (!m. SIMP_REC x f (SUC m) = f(SIMP_REC x f m))",
    ASM_REWRITE_TAC
     [SIMP_REC;SIMP_REC_FUN_THM1;
      MP(SPECL["SUC(SUC m)";"m:num"]SIMP_REC_FUN_THM2)
        (CONJUNCT2(SPEC_ALL LESS_SUC_SUC));
      MP
       (MP(SPEC_ALL(SPECL["m:num";"SUC(SUC m)";"SUC m"]SIMP_REC_UNIQUE))
          (CONJUNCT2(SPEC_ALL LESS_SUC_SUC)))
       (CONJUNCT1(SPEC_ALL LESS_SUC_SUC))]);;

%
 We now use simple recursion to prove that:

   |- !x f. ?fun.
       (fun 0 = x) /\
       (!m. fun(SUC m) = f(fun m)m)

  We proceed by defining a function PRIM_REC and proving that:

   |- !m x f.
       (PRIM_REC x f 0  = x) /\
       (PRIM_REC x f (SUC m) = f(PRIM_REC x f m)m)
%


%
 First we define a partial inverse to SUC called PRE such that:

   (PRE 0 = 0) /\ (!m. PRE(SUC m) = m)
%

let PRE_DEF =
 new_definition(`PRE_DEF`, "PRE m = ((m=0) => 0 | @n. m = SUC n)");;

% Now we prove some theorems: %

% |- (@n. m = n) = m %

let SELECT_LEMMA = 
 let th = SELECT_INTRO(EQ_MP (SYM(BETA_CONV "(\n:*. m = n) m")) (REFL "m:*"))
 in SYM(EQ_MP(BETA_CONV(concl th))th);;

let PRE =
 prove_thm
  (`PRE`,
   "(PRE 0 = 0) /\ (!m. PRE(SUC m) = m)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRE_DEF;INV_SUC_EQ;NOT_SUC;SELECT_LEMMA]);;

let PRIM_REC_FUN =
 new_definition
  (`PRIM_REC_FUN`,
   "PRIM_REC_FUN (x:*) (f:*->num->*) =
     SIMP_REC (\n:num. x) (\fun n. f(fun(PRE n))n)");;

let PRIM_REC_EQN =
 prove_thm
  (`PRIM_REC_EQN`,
   "!(x:*) f.
     (!n. PRIM_REC_FUN x f 0 n = x) /\
     (!m n. PRIM_REC_FUN x f (SUC m) n = f (PRIM_REC_FUN x f m (PRE n)) n)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC [PRIM_REC_FUN;SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[]);;

let PRIM_REC =
 new_definition
  (`PRIM_REC`,
   "PRIM_REC (x:*) f m = PRIM_REC_FUN x f m (PRE m)");;

let PRIM_REC_THM =
 prove_thm
  (`PRIM_REC_THM`,
   "!x f.
     (PRIM_REC (x:*) f 0 = x) /\
     (!m. PRIM_REC x f (SUC m) = f(PRIM_REC x f m)m)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRIM_REC;PRIM_REC_FUN;SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV BETA_CONV)
    THEN REWRITE_TAC[PRE]);;


% --------------------------------------------------------------------- %
% Unique existence theorem for prim rec definitions on num.		%
%									%
% ADDED TFM 88.04.02							%
% --------------------------------------------------------------------- %

let num_Axiom =
    prove_thm
    (`num_Axiom`,
     "!e:*. !f. ?! fn. ((fn 0) = e) /\ (!n. fn(SUC n) = f (fn n) n)",
     REPEAT GEN_TAC THEN
     CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
     [EXISTS_TAC "PRIM_REC (e:*) (f:*->num->*)" THEN
      REWRITE_TAC [PRIM_REC_THM];
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REPEAT STRIP_TAC THEN
      CONV_TAC FUN_EQ_CONV THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC []]);;
       

close_theory();;

quit();;
