
%============================================================================%
% This file contains examples to illustrate the HOL tools to support         %
% programming logics provided in the library prog_logic88.                   %
% The principles underlying these tools are described in the paper:          %
%                                                                            %
%    "Mechanizing Programming Logics in Higher Order Logic",                 %
%    by M.J.C. Gordon, in "Current Trends in Hardware Verification and       %
%    Automated Theorem Proving" edited by P.A. Subrahmanyam and              %
%    Graham Birtwistle, Springer-Verlag, 1989.                               %
%                                                                            %
% It is hoped that if the ML phrases in this file are evaluated in the       %
% order given, the results will illustrate the contents of the library.      %
%                                                                            %
%============================================================================%

%----------------------------------------------------------------------------%
% The naming convention used below is that ML variables th1, th2, etc        %
% are pure logic theorems, hth1, hth2, etc name theorems of Hoare Logic and  %
% tth1, tth2, etc name theorems in the Hoare Logic of total correctness      %
% (however, theorems of Hoare Logic (for both partial and total correctness) %
% are really only specially printed theorems of pure logic).                 %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% Examples to illustrate the special parsing and printing. This is           %
% currently done in Lisp, but it is hoped eventually to provide ML-level     %
% facilities to support user programmable syntax. Work on this will be       %
% part of an Esprit Basic Research Action joint with Philips and IMEC.       %
%----------------------------------------------------------------------------%


%----------------------------------------------------------------------------%
% Examples to illustrate forward proof using Hoare Logic (hoare_logic.ml).   %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% Load in the generated parser for the language.                             %
%----------------------------------------------------------------------------%

loadf `loader`;;

%----------------------------------------------------------------------------%
% The Assignment Axiom                                                       %
%----------------------------------------------------------------------------%

let hth1 = ASSIGN_AX (MK_NICE `"{(R=x) /\\ (Y=y)}"`) (MK_NICE `"R := X"`);;
let hth2 = ASSIGN_AX (MK_NICE `"{(R=x) /\\ (X=y)}"`) (MK_NICE `"X := Y"`);;

pretty_off();;

hth1;;

MK_SPEC;;

pretty_on();;

%----------------------------------------------------------------------------%
% The Sequencing Rule                                                        %
%----------------------------------------------------------------------------%

let hth1 = ASSIGN_AX (MK_NICE `"{(R=x) /\\ (Y=y)}"`) (MK_NICE `"R:=X"`);;
let hth2 = ASSIGN_AX (MK_NICE `"{(R=x) /\\ (X=y)}"`) (MK_NICE `"X:=Y"`);;
let hth3 = ASSIGN_AX (MK_NICE `"{(Y=x) /\\ (X=y)}"`) (MK_NICE `"Y:=R"`);;

SEQ_THM;;

let hth4 = SEQ_RULE (hth1,hth2);;
let hth5 = SEQ_RULE (hth4,hth3);;

let hth6 = SEQL_RULE[hth1;hth2;hth3];;

%----------------------------------------------------------------------------%
% Precondition Strengthening                                                 %
%----------------------------------------------------------------------------%

let th1  = DISCH_ALL(CONTR "((X:num=x) /\ (Y:num=y))" (ASSUME (MK_NICE `"F"`)));;

let hth7 = PRE_STRENGTH_RULE(th1,hth5);; 

%----------------------------------------------------------------------------%
% Postcondition Weakening                                                    %
%----------------------------------------------------------------------------%

let th2  = prove("((Y:num=x) /\ (X:num=y)) ==> T", REWRITE_TAC[]);;

let hth8 = POST_WEAK_RULE(hth5,th2);;

%----------------------------------------------------------------------------%
% On-armed Conditional Rule                                                  %
%----------------------------------------------------------------------------%

new_theory`MAX` ? extend_theory `MAX` ? ();;

let MAX =
 new_definition
  (`MAX`, "MAX(m,n) = ((m>n) => m | n)") ? definition `MAX` `MAX` ;;

let hth9 = ASSIGN_AX "{X = MAX(x,y)}" (MK_NICE `"X := Y"`);;

let MAX_LEMMA1 =
 theorem `MAX` `MAX_LEMMA1`
 ?
 prove_thm
  (`MAX_LEMMA1`,
   "((X=x) /\ (Y=y)) /\ (Y>X) ==> (Y=MAX(x,y))",
   REWRITE_TAC[MAX;GREATER]
    THEN REPEAT STRIP_TAC
    THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
    THEN ASM_CASES_TAC (MK_NICE `"Y<X"`)
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC LESS_ANTISYM);;

let hth10 = PRE_STRENGTH_RULE(MAX_LEMMA1,hth9);;

let MAX_LEMMA2 =
 theorem `MAX` `MAX_LEMMA2`
 ?
 prove_thm
  (`MAX_LEMMA2`,
   "((X=x) /\ (Y=y)) /\ ~(Y>X) ==> (X=MAX(x,y))",
   REWRITE_TAC[MAX;GREATER;NOT_LESS;LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
    THEN ASM_CASES_TAC (MK_NICE `"Y<X"`)
    THEN ASM_REWRITE_TAC[]
   THEN RES_TAC);;

let hth11 = IF1_RULE(hth10,MAX_LEMMA2);;

%----------------------------------------------------------------------------%
% Two-armed Conditional Rule                                                 %
%----------------------------------------------------------------------------%

let hth12 = ASSIGN_AX "{R = MAX(x,y)}" (MK_NICE `"R := Y"`);;

let hth13 = PRE_STRENGTH_RULE(MAX_LEMMA1,hth12);;

let hth14 = ASSIGN_AX "{R = MAX(x,y)}" (MK_NICE `"R := X"`);;

let hth15 = PRE_STRENGTH_RULE(MAX_LEMMA2,hth14);;

let hth16 = IF2_RULE(hth13,hth15);;

%----------------------------------------------------------------------------%
% The WHILE-Rule                                                             %
%----------------------------------------------------------------------------%

let hth17 = ASSIGN_AX (MK_NICE `"{X = R + (Y * Q)}"`) 
                      (MK_NICE `"Q := (Q + 1)"`);;

let hth18 = ASSIGN_AX (MK_NICE `"{X = R + (Y * (Q + 1))}"`) 
                      (MK_NICE `"R := (R-Y)"`);;

let hth19 = SEQ_RULE(hth18,hth17);;

let th2 =
 prove
  ((MK_NICE `"((X = R + (Y * Q)) /\\ (Y<=R)) ==> 
              (X = (R - Y) + (Y * (Q + 1)))"`),
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_CLAUSES]
    THEN ONCE_REWRITE_TAC[SPEC (MK_NICE `"Y*Q"`) ADD_SYM]
    THEN ONCE_REWRITE_TAC[ADD_ASSOC]
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]);;

let hth20 = PRE_STRENGTH_RULE(th2,hth19);;

let hth21 = WHILE_RULE hth20;;

pretty_off();;

WHILE_THM;;

%----------------------------------------------------------------------------%
% The pretty printer needs more work ...                                     %
%----------------------------------------------------------------------------%

pretty_on();;

WHILE_THM;;  % "{p s /\ b s}" should print as "{p /\ s}" %

let hth22 =
 SEQL_RULE
  [ASSIGN_AX (MK_NICE `"{X = R + (Y * 0)}"`) (MK_NICE `"R := X"`);
   ASSIGN_AX (MK_NICE `"{X = R + (Y * Q)}"`) (MK_NICE `"Q := 0"`);
   hth21];;

let th3 =
 prove
  ((MK_NICE `"(~(Y <= R)) = (R < Y)"`),
   ONCE_REWRITE_TAC[SYM(SPEC (MK_NICE `"R<Y"`) (hd(CONJUNCTS NOT_CLAUSES)))]
    THEN PURE_REWRITE_TAC[NOT_LESS]
    THEN REFL_TAC);;

let hth23 = REWRITE_RULE[th3;MULT_CLAUSES;ADD_CLAUSES]hth22;;

let hth24 =
 SEQL_RULE
  [ASSIGN_AX (MK_NICE `"{X = R + (Y * 0)}"`) (MK_NICE `"R := X"`);
   ASSIGN_AX (MK_NICE `"{X = R + (Y * Q)}"`) (MK_NICE `"Q := 0"`);
   WHILE_RULE
    (PRE_STRENGTH_RULE
      (th2,SEQL_RULE
            [ASSIGN_AX (MK_NICE `"{X = R + (Y * (Q + 1))}"`) 
                       (MK_NICE `"R := (R-Y)"`);
             ASSIGN_AX (MK_NICE `"{X = R + (Y * Q)}"`) 
                       (MK_NICE `"Q := (Q + 1)"`)]))];;

%----------------------------------------------------------------------------%
% Examples to illustrate the generation of verification conditions           %
% using tactics (vc_gen.ml).                                                 %
%----------------------------------------------------------------------------%

let goal = g and apply = expandf;;

goal (MK_NICE
      `"{T}
        (R:=X;
         Q:=0;
         assert{(R = X) /\\ (Q = 0)};
         while Y<=R
          do (invariant{X = (R + (Y * Q))};
              R := R-Y; Q := Q+1))
        {(R < Y) /\\ (X = (R + (Y * Q)))}"`);;

apply(SEQ_TAC);;

apply(SEQ_TAC);;
apply(ASSIGN_TAC);;
apply(REWRITE_TAC[]);;

apply(WHILE_TAC);;

apply(STRIP_TAC);;
apply(ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES]);;

apply(SEQ_TAC);;
apply(ASSIGN_TAC);;
apply(ACCEPT_TAC th2);;

apply(REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]);;
apply(DISCH_TAC);;
apply(ASM_REWRITE_TAC[]);;

let VC_TAC =
 REPEAT(ASSIGN_TAC 
         ORELSE SEQ_TAC 
         ORELSE IF1_TAC 
         ORELSE IF2_TAC 
         ORELSE WHILE_TAC);;

goal (MK_NICE
      `"{T}
        (R:=X;
         Q:=0;
         assert{(R = X) /\\ (Q = 0)};
         while Y<=R
          do (invariant{X = (R + (Y * Q))};
              R := R-Y; Q := Q+1))
        {(R < Y) /\\ (X = (R + (Y * Q)))}"`);;

apply(VC_TAC);;

apply(REWRITE_TAC[]);;

apply(STRIP_TAC);;
apply(ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES]);;

apply(ACCEPT_TAC th2);;

apply(REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]);;
apply(DISCH_TAC);;
apply(ASM_REWRITE_TAC[]);;
 
prove
 ((MK_NICE
        `"{T}
          (R:=X;
           Q:=0;
           assert{(R = X) /\\ (Q = 0)};
           while Y<=R
            do (invariant{X = (R + (Y * Q))};
                R:=R-Y; Q:=Q+1))
          {(R < Y) /\\ (X = (R + (Y * Q)))}"`),
   VC_TAC
    THENL
     [REWRITE_TAC[];
      STRIP_TAC
       THEN ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES];
      ACCEPT_TAC th2;
      REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]
       THEN DISCH_TAC
       THEN ASM_REWRITE_TAC[]
     ]);;


%----------------------------------------------------------------------------%
% The Hoare Logic of total correctness in HOL (halts_logic.ml)               %
%----------------------------------------------------------------------------%

let tth1 =
 ASSIGN_T_AX (MK_NICE `"{(0 < Y /\\ (X = R + (Y * Q))) /\\ R < r}"`)
             (MK_NICE `"Q := (Q + 1)"`);;

pretty_off();;

tth1;;

T_SPEC;;

HALTS;;

pretty_on();;

let tth2 =
 ASSIGN_T_AX (MK_NICE `"{(0 < Y /\\ (X = R + (Y * (Q + 1)))) /\\ R < r}"`)
             (MK_NICE `"R := (R-Y)"`);;

let tth3 = SEQ_T_RULE(tth2,tth1);;

let th4 =
 prove
  ("!m. 0 < m ==> !n. 0 < n ==> (n - m) < n",
   INDUCT_TAC
    THEN REWRITE_TAC[LESS_REFL;LESS_0]
    THEN INDUCT_TAC
    THEN REWRITE_TAC[LESS_REFL;LESS_0;SUB;LESS_MONO_EQ]
    THEN ASM_CASES_TAC "n < SUC m"
    THEN ASM_REWRITE_TAC[LESS_0;LESS_MONO_EQ]
    THEN ASM_CASES_TAC "0 < n"
    THEN RES_TAC
    THEN POP_ASSUM_LIST
          (\[th1;th2;th3;th4].
             STRIP_ASSUME_TAC(REWRITE_RULE[NOT_LESS](CONJ th1 th2)))
    THEN IMP_RES_TAC LESS_EQ_TRANS
    THEN IMP_RES_TAC OR_LESS
    THEN IMP_RES_TAC NOT_LESS_0);;

let th5 =
 prove
  ("!m n p. m < n /\ n <= p ==> m < p",
   REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASSUM_LIST(\[th1;th2;th3]. REWRITE_TAC[SYM th2])
    THEN ASM_REWRITE_TAC[]);;

let th6 =
 prove
  ((MK_NICE `"((0 < Y /\\ (X = R + (Y * Q))) /\\ (Y<=R) /\\ (R = r))
     ==> (0 < Y /\\ (X = (R - Y) + (Y * (Q + 1)))) /\\ (R - Y) < r"`),
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_CLAUSES]
    THEN ONCE_REWRITE_TAC[SPEC "Y*Q" ADD_SYM]
    THEN ONCE_REWRITE_TAC[ADD_ASSOC]
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC th5
    THEN ASSUM_LIST(\thl. REWRITE_TAC[SYM(el 4 thl)])
    THEN IMP_RES_TAC th4);;

let tth4 = PRE_STRENGTH_T_RULE(th6,tth3);;

let tth5 = WHILE_T_RULE tth4;;

let tth6 =
 SEQL_T_RULE
  [ASSIGN_T_AX (MK_NICE `"{(0 < Y) /\\ (X = R + (Y * 0))}"`) 
               (MK_NICE `"R := X"`);
   ASSIGN_T_AX (MK_NICE `"{(0 < Y) /\\ (X = R + (Y * Q))}"`)
               (MK_NICE `"Q := 0"`);
   tth5];;

let th7 =
 prove
  ((MK_NICE `"(~(Y <= R)) = (R < Y)"`),
   ONCE_REWRITE_TAC[SYM(SPEC "R<Y" (hd(CONJUNCTS NOT_CLAUSES)))]
    THEN PURE_REWRITE_TAC[NOT_LESS]
    THEN REFL_TAC);;

let tth7 = REWRITE_RULE[th7;MULT_CLAUSES;ADD_CLAUSES]tth6;;

let tth6 =
 SEQL_T_RULE
  [ASSIGN_T_AX (MK_NICE `"{(0 < Y) /\\ (X = R + (Y * 0))}"`)
               (MK_NICE `"R := X"`);
   ASSIGN_T_AX (MK_NICE `"{(0 < Y) /\\ (X = R + (Y * Q))}"`) 
               (MK_NICE `"Q := 0"`);
   WHILE_T_RULE
    (PRE_STRENGTH_T_RULE
      (th6,SEQL_T_RULE
            [ASSIGN_T_AX (MK_NICE `"{((0 < Y) /\\ (X = R + (Y * (Q + 1)))) /\\ 
                                     (R < r)}"`)
                         (MK_NICE `"R := (R-Y)"`);
             ASSIGN_T_AX (MK_NICE `"{((0 < Y) /\\ (X = R + (Y * Q))) /\\ 
                                    (R < r)}"`)
                         (MK_NICE `"Q := (Q + 1)"`)]))];;

%----------------------------------------------------------------------------%
% Verification conditions for total correctness (halts_vc_gen)               %
%----------------------------------------------------------------------------%

goal
 (MK_NICE
  `"[0 < Y]
    (R := X;
     Q := 0;
     assert{(0 < Y) /\\ (R=X) /\\ (Q=0)};
     while Y <= R
      do (invariant{(0 < Y) /\\ (X = R + (Y * Q))}; variant{R};
          R := R-Y; Q := Q+1))
    [(X = R + (Y * Q)) /\\ R < Y]"`);;

apply(VC_T_TAC);;

apply(REWRITE_TAC[]);;

apply(STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES]);;

apply(ACCEPT_TAC th6);;

apply(REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]);;
apply(DISCH_TAC);;
apply(ASM_REWRITE_TAC[]);;

let DIV_CORRECT =
 prove
  ((MK_NICE `"[0 < Y]
              (R:=X;
               Q:=0;
               assert{(0 < Y) /\\ (R = X) /\\ (Q = 0)};
               while Y<=R
                do (invariant{(0 < Y) /\\ (X = (R + (Y * Q)))};
                    variant{R};
                    R:=R-Y; Q:=Q+1))
              [(R < Y) /\\ (X = (R + (Y * Q)))]"`),
   VC_T_TAC
    THENL
     [REWRITE_TAC[];
      STRIP_TAC
       THEN ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES];
      ACCEPT_TAC th6;
      REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]
       THEN DISCH_TAC
       THEN ASM_REWRITE_TAC[]
     ]);;

pretty_off();;

DIV_CORRECT;;

pretty_on();;

%----------------------------------------------------------------------------%
% To see how weakest preconditions and dynamic logic can be represented in   %
% HOL, browse the files mk_dijkstra.ml and mk_dynamic_logic.ml, respectively.%
%----------------------------------------------------------------------------%
