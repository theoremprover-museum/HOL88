
% Theory of fixedpoints of predicates in HOL %

new_theory `fixpoints`;;

% Definition of the Scott ordering on predicates %

new_infix_definition
 (`LESS_DEF`,
  "$<< f1 f2 = !x:*. f1 x ==> f2 x");;

% Non constructive definition of the least fixed-point operator %

new_definition
 (`FIX`,
  "FIX fun =
   @f:*->bool. (fun f = f) /\ !f'. (fun f' = f') ==> (f << f')");;

% A function for getting the iterates f^n x, where:

     f    : * -> *
     ITER : num -> (*->*) -> (*->*)

     ITER n f x = f^n x
%

new_prim_rec_definition
 (`ITER`,
  "(ITER 0       f x = (x:*)) /\
   (ITER (SUC n) f x = f(ITER n f x))");;

% Limit of a chain of predicates 

     U c  =  c(0) u c(1) u ... u c(n) u ...  =  \x.?n. c n x
     n
%

new_definition
 (`LUB`,
  "LUB c = \x:*.?n:num. c n x");;

% The bottom (least defined) predicate %

let BOT =
 new_definition(`BOT`, "BOT : *->bool = \x.F");;

% Limit of the chain of iterates 

     BOT u fun BOT u fun(fun BOT) ... u fun^n BOT u ...

     LIM_ITER fun = U ITER n fun BOT
                    n

                  = LUB (\n. ITER n fun BOT)
%

new_definition
 (`LIM_ITER`,
  "LIM_ITER(fun:(*->bool)->(*->bool)) = LUB (\n. ITER n fun BOT)");;

% c : num -> (*->bool) is a chain if

     c(0) << c(1) << ... << c(n) << ...
%

new_definition
 (`CHAIN`,
  "CHAIN (c:num->*->bool) = !n. (c n) << (c(SUC n))");;

% An example of a chain that will be useful to us is:

     p1 << p2 << p2 << ... << p2 << ...

%

new_definition
 (`TRIV_CHAIN`,
  "TRIV_CHAIN p1 p2 : num->* = (\n. ((n=0) => p1 | p2))");;

map (load_definition `-`) (words `CHAIN TRIV_CHAIN LESS_DEF`);;

let TRIV_CHAIN_LEMMA =
 prove_thm
  (`TRIV_CHAIN_LEMMA`,
   "!(p1:*->bool) p2. p1 << p2 ==> CHAIN(TRIV_CHAIN p1 p2)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[CHAIN;TRIV_CHAIN]
    THEN BETA_TAC
    THEN INDUCT_TAC
    THENL
     [ASM_REWRITE_TAC[NOT_SUC];
      REWRITE_TAC[NOT_SUC;LESS_DEF]
     ]);;

% fun is monotonic (|- MONO fun) if

     p1 << p2 ==> fun p1 << fun p2
%

new_definition
 (`MONO`,
  "MONO (fun:(*->bool)->(*->bool)) = 
    !p1 p2. (p1 << p2) ==> (fun p1 << fun p2)");;

% fun is continuous (|- CONTINUOUS fun) if for all chains

     c0 << c1 << ... << cn << ...

  we have

     fun(U cn) = U (fun cn)
         n       n

  i.e.

     CHAIN c ==> fun(\x.?n. c n x) = \x.?n. fun (c n) x
%

new_definition
 (`CONTINUOUS`,
  "CONTINUOUS (fun:(*->bool)->(*->bool)) =
    !c:num->*->bool. 
      CHAIN c ==> (fun(LUB c) = LUB(\n.fun(c n)))");;

load_definitions `fixpoints`;;
load_theorems    `fixpoints`;;

let CHAIN_ITER =
 prove_thm
  (`CHAIN_ITER`,
   "!fun:(*->bool)->(*->bool).
      MONO fun ==> CHAIN (\n. ITER n fun BOT)",
   REWRITE_TAC[CHAIN;BOT]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN INDUCT_TAC
    THEN BETA_TAC
    THENL
     [REWRITE_TAC[ITER;LESS_DEF]; ALL_TAC]
    THEN EVERY_ASSUM (UNDISCH_TAC o concl)
    THEN BETA_TAC
    THEN REWRITE_TAC[MONO;ITER]
    THEN REPEAT DISCH_TAC
    THEN RES_TAC);;

% I suspect the next two lemmas are lurking somewhere in the system;
  it is quicker to reprove them than mount a search!.

  (Added later: FUN_EQ_CONV is what is wanted.)
%

let EXT_LEMMA =
 prove_thm
  (`EXT_LEMMA`,
   "!(f:*->**) g. (f = g) = (!x. f x = g x)",
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[EQ_EXT]
    THEN DISCH_TAC
    THEN ASM_REWRITE_TAC[]);;

let COND_FUN =
 prove_thm
  (`COND_FUN`,
   "!p (f:*->**) g x. (p => f | g) x = (p => f x | g x)",
   REPEAT STRIP_TAC
    THEN ASM_CASES_TAC "p:bool"
    THEN ASM_REWRITE_TAC[]);;

let COND_MP =
 prove_thm
  (`COND_MP`,
   "!p x y. 
     (p ==> (p => x | y) ==> x) /\ (~p ==> (p => x | y) ==> y)",
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC "p:bool"
    THEN ASM_REWRITE_TAC[]);;

let EXISTS_COND_DISJ =
 prove_thm
  (`EXISTS_COND_DISJ`,
   "!n x y. (?n. ((n=0) => x | y)) = x \/ y",
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [ASM_CASES_TAC "n=0"
       THEN IMP_RES_TAC COND_MP
       THEN ASM_REWRITE_TAC[];
      EXISTS_TAC "0"
       THEN REWRITE_TAC[];
      EXISTS_TAC "SUC 0"
       THEN REWRITE_TAC[NOT_SUC]]
    THEN ASM_REWRITE_TAC[]);;

let EQ_DISJ =
 prove_thm
  (`EQ_DISJ`,
   "!x y. (x \/ y = y) = (x ==> y)",
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC "x:bool"
    THEN ASM_CASES_TAC "y:bool"
    THEN ASM_REWRITE_TAC[]);;

let LUB_CHAIN_LEMMA =
 prove_thm
  (`LUB_CHAIN_LEMMA`,
   "!(p1:*->bool) p2. (p1 << p2) = (LUB(TRIV_CHAIN p1 p2) = p2)",
   REPEAT GEN_TAC
    THEN REWRITE_TAC[LUB;LESS_DEF;TRIV_CHAIN;EXT_LEMMA]
    THEN BETA_TAC
    THEN REWRITE_TAC[COND_FUN;EXISTS_COND_DISJ;EQ_DISJ]);;

let LAMB_TRIV_CHAIN =
 prove_thm
  (`LAMB_TRIV_CHAIN`,
   "!(fun:(*->bool)->(*->bool)) p1 p2.
      (\n. fun(TRIV_CHAIN p1 p2 n)) = TRIV_CHAIN (fun p1) (fun p2)",
   REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[EXT_LEMMA]
    THEN REWRITE_TAC[TRIV_CHAIN]
    THEN BETA_TAC 
    THEN GEN_TAC
    THEN ASM_CASES_TAC "x=0"
    THEN ASM_REWRITE_TAC[NOT_SUC]);;

let CONT_MONO =
 prove_thm
  (`CONT_MONO`,
   "!fun:(*->bool)->(*->bool). CONTINUOUS fun ==> MONO fun",
   GEN_TAC
    THEN REWRITE_TAC[CONTINUOUS;MONO]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC TRIV_CHAIN_LEMMA
    THEN RES_TAC
    THEN ASSUM_LIST
          (\thl. ASSUME_TAC
                  (REWRITE_RULE
                    [LAMB_TRIV_CHAIN]
                    (hd(mapfilter SYM thl))))
    THEN REWRITE_TAC[LUB_CHAIN_LEMMA]
    THEN ONCE_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC
          [EQ_MP (SPEC_ALL LUB_CHAIN_LEMMA) (ASSUME "(p1:*->bool)<<p2")]);;

% Proof that the limit of the iterates is a fixed point %

let FIX_LEMMA =
 prove_thm
  (`FIX_LEMMA`,
   "!fun:(*->bool)->(*->bool).
     CONTINUOUS fun ==> (fun(LIM_ITER fun) = LIM_ITER fun)",
   REWRITE_TAC[LIM_ITER;ITER]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC CONT_MONO
    THEN IMP_RES_TAC CHAIN_ITER
    THEN ASSUM_LIST
          (\thl. ASSUME_TAC(hd(mapfilter (EQ_MP (SPEC_ALL CONTINUOUS)) thl)))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN BETA_TAC
    THEN REWRITE_TAC[SYM(SPEC_ALL(CONJUNCT2 ITER))]
    THEN REWRITE_TAC[LUB]
    THEN CONV_TAC FUN_EQ_CONV
    THEN REPEAT STRIP_TAC
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[EXISTS_TAC "SUC n"; EXISTS_TAC "n:num"]
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_THEN
          (ASSUME_TAC o BETA_RULE o SPEC_ALL)
          (fst(EQ_IMP_RULE (SPEC_ALL CHAIN)))
    THEN ASSUM_LIST 
          (\thl. ASSUME_TAC
                  (hd
                   (mapfilter 
                    (MATCH_MP (fst(EQ_IMP_RULE (SPEC_ALL LESS_DEF)))) thl)))
    THEN RES_TAC);;

% Proof that if fun f = f then fun^n f BOT << f %

let LEAST_FIX_LEMMA =
 prove_thm
  (`LEAST_FIX_LEMMA`,
   "!fun:(*->bool)->(*->bool).
      CONTINUOUS fun ==> !f. (fun f = f) ==> !n. ITER n fun BOT << f",
   REWRITE_TAC[BOT]
    THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC
    THEN INDUCT_TAC
    THENL[REWRITE_TAC[ITER;LESS_DEF]; ALL_TAC]
    THEN REWRITE_TAC[ITER]
    THEN IMP_RES_TAC CONT_MONO
    THEN ASSUM_LIST(\thl. ASSUME_TAC(hd(mapfilter (EQ_MP (SPEC_ALL MONO)) thl)))
    THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
    THEN RES_TAC);;

% Proof that the limit of the iterates is the least fixed point %

let LEAST_FIX_THM =
 prove_thm
  (`LEAST_FIX_THM`,
   "!fun:(*->bool)->(*->bool).
      CONTINUOUS fun ==> !f. (fun f = f) ==> (LIM_ITER fun << f)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[LIM_ITER;LUB;LESS_DEF]
    THEN GEN_TAC
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_THEN (IMP_RES_TAC o REWRITE_RULE[LESS_DEF]) LEAST_FIX_LEMMA);;

% LIM_ITER fun is the least fixed point of fun %

let LIM_ITER_THM =
 prove_thm
  (`LIM_ITER_THM`,
   "!fun:(*->bool)->(*->bool).
      CONTINUOUS fun ==> 
       ((fun(LIM_ITER fun) = LIM_ITER fun) /\ 
        !f. (fun f = f) ==> (LIM_ITER fun << f))",
   REPEAT STRIP_TAC
    THENL
     [IMP_RES_TAC FIX_LEMMA;
      IMP_RES_TAC LEAST_FIX_THM]);;

% Proof that a least fixed point exists %

let FIX_EXISTS =
 prove_thm
  (`FIX_EXISTS`,
   "!fun:(*->bool)->(*->bool).
      CONTINUOUS fun ==> 
       ?f. (fun f = f) /\ !f'. (fun f' = f') ==> (f << f')",
   GEN_TAC
    THEN DISCH_TAC
    THEN EXISTS_TAC "LIM_ITER (fun:(*->bool)->(*->bool))" 
    THEN MATCH_MP_TAC LIM_ITER_THM
    THEN FIRST_ASSUM ACCEPT_TAC);;

% Proof that FIX is the least fixed point %

let FIX_THM =
 prove_thm
  (`FIX_THM`,
   "!fun:(*->bool)->(*->bool).
      CONTINUOUS fun ==> 
       ((fun(FIX fun) = FIX fun) /\ 
        !f. (fun f = f) ==> (FIX fun << f))",
   GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[FIX]
    THEN IMP_RES_THEN (\th. REWRITE_TAC[SELECT_RULE th]) FIX_EXISTS);;

let ANTISYM_LEMMA =
 prove_thm
  (`ANTISYM_LEMMA`,
   "!(f g:*->bool). (f << g) /\ (g << f) ==> (f = g)",
   REWRITE_TAC[LESS_DEF]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN EQ_TAC
    THEN ASM_REWRITE_TAC[]);;

let FIX_LIM_ITER_THM =
 prove_thm
  (`FIX_LIM_ITER_THM`,
   "!fun:(*->bool)->(*->bool).
      CONTINUOUS fun ==> (FIX fun = LIM_ITER fun)",
   REPEAT STRIP_TAC
    THEN IMP_RES_THEN ASSUME_TAC FIX_THM
    THEN IMP_RES_TAC LIM_ITER_THM
    THEN RES_TAC
    THEN IMP_RES_TAC ANTISYM_LEMMA);;

% A predicate p admits induction if:

     p x1 /\ p x2 ... /\ p xn /\ ...  ==> p(U xn)
                                            n
%

let ADMITS_INDUCTION =
 new_definition
  (`ADMITS_INDUCTION`,
   "ADMITS_INDUCTION (p:(*->bool)->bool) =
     !c. CHAIN c /\ (!n. p(c n)) ==> p(LUB c)");;

% If p is a Hoare_logic predicate:

     p(f) = !s1 s2. p s1 /\ f(s1,s2) ==> q s2

  then p admits induction.
%

let HOARE_ADMITS_LEMMA =
 prove_thm
 (`HOARE_ADMITS_LEMMA`,
  "!p q : *->bool.
    ADMITS_INDUCTION(\f. !s1 s2. p s1 /\ f(s1,s2) ==> q s2)",
  REWRITE_TAC[ADMITS_INDUCTION;CHAIN;LUB]
   THEN BETA_TAC
   THEN BETA_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC);;

% Lemma: if fun is continuous and p BOT and
  !f. p f ==> p(fun f), then p is true of all
  the iterates fun^n BOT.
%

let SCOTT_INDUCTION_LEMMA =
 prove_thm
  (`SCOTT_INDUCTION_LEMMA`,
   "!(p:(*->bool)->bool) fun.
     CONTINUOUS fun /\
     p BOT /\ 
     (!f. p f ==> p(fun f)) 
     ==> 
     !n. p(ITER n fun BOT)",
   REWRITE_TAC[BOT]
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[ITER]
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC);;

% Scott Induction (Computation Induction) %

let SCOTT_INDUCTION_THM =
 prove_thm
  (`SCOTT_INDUCTION_THM`,
   "!(p:(*->bool)->bool) fun.
     ADMITS_INDUCTION p /\ 
     CONTINUOUS fun     /\
     p BOT              /\ 
     (!f. p f ==> p(fun f)) 
     ==> 
     p(FIX fun)",
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC FIX_LIM_ITER_THM
    THEN ASM_REWRITE_TAC[LIM_ITER]
    THEN IMP_RES_TAC SCOTT_INDUCTION_LEMMA
    THEN IMP_RES_TAC CONT_MONO
    THEN IMP_RES_TAC CHAIN_ITER
    THEN IMP_RES_TAC 
          (hd(IMP_CANON(fst(EQ_IMP_RULE (SPEC_ALL ADMITS_INDUCTION)))))
    THEN ASSUM_LIST (IMP_RES_TAC o BETA_RULE o (el 1)));;


quit();; % Needed for Common Lisp %
