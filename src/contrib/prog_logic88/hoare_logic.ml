
% Axioms and rules of Hoare logic (uses theorems in `hoare_thms`). %

%<

load_library`string`;; 

load_theory `hoare_thms` ? ();;  

loadx `syntax_functions`;; 

loadx `hol_match`;; 

load_theorems `hoare_thms`;;

let BND = definition `semantics` `BND`;;

% 
   BND_CONV "BND e `X` s `X`"   --->   |- BND e `X` s `X` = e
   BND_CONV "BND e `X` s `Y`"   --->   |- BND e `X` s `Y` = (s `Y`)
                                           (if `X` is not equal to `Y`)
%

% The following two theorems are proved in hoare_thms 
  and used in BND_CONV

let BND_THM1 =
 prove_thm
  (`BND_THM1`,
   "!e x s. BND e x s x = e",
   REWRITE_TAC[BND]
    THEN BETA_TAC
    THEN REWRITE_TAC[]);;

let BND_THM2 =
 prove_thm
  (`BND_THM2`,
   "!e x s y. ~(y = x) ==> (BND e x s y = (s y))",
   REWRITE_TAC[BND]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]);;
%

load_theorem `hoare_thms` `BND_THM1`;;
load_theorem `hoare_thms` `BND_THM2`;;

>%

% |- t1 = t2  ,  t   --->   |- t = t[t2/t1] %

let SUBS_CONV th t =
 let x = genvar(type_of t)
 in
 let t1 = mk_eq(x,t)
 in
 let th1 = DISCH t1 (SUBS [th] (ASSUME t1))
 in
 MP(INST[t,x]th1)(REFL t);;

let BND_CONV t =
 let (),[e;x;s;y] = strip_comb t
 in
 if x = y
  then SPECL[e;x;s]BND_THM1
  else 
   let yx = mk_eq(y,x)
   in
   MP(SPECL[e;x;s;y]BND_THM2)
     (EQ_MP(el 4 (CONJUNCTS (SPEC yx EQ_CLAUSES)))(string_EQ_CONV yx));;

% Assignment Axiom.  ASSIGN_AX :

    "P" "{X := E}"   --->   |- MK_SPEC({P[E/X]}, MK_ASSIGN(`X`,{E}), {P}) 
%

let ASSIGN_AX p c = 
 (let x,e = dest_assign c
  in
  let th1 = SPECL[p;x;e]ASSIGN_THM
  in
  let t1 = (snd o dest_abs o fst o dest_spec o concl)th1
  in
  let t2 = (hd o snd o strip_comb o snd o dest_comb) t1
  in
  let th2 = RIGHT_CONV_RULE (SUBS_CONV(BETA_CONV t2)) (BETA_CONV t1)
  in
  let th3 = RIGHT_CONV_RULE (ONCE_DEPTH_CONV BND_CONV) th2
  in
  let th4 = ABS "s:state" th3
  in
  SUBS[th4]th1
 ) ? failwith `ASSIGN_AX`;;


% Test example:

   let p = "{(X + Y = x) /\ (Y = y)}";;
   let c = "X := (X + Y)";;
   ASSIGN_AX p c;;

   let hth1 = ASSIGN_AX "{(R=x) /\ (Y=y)}" "R := X";;
   let hth2 = ASSIGN_AX "{(R=x) /\ (X=y)}" "X := Y";;

   let p = "{(p:num list->bool)[X;Y]}";;
   let c = "X := e X Y";;
   ASSIGN_AX p c;;

%

% Sequencing Rule. SEQ_RULE:

     |- {P} C1 {Q}  ,  |- {Q} C2 {R}
     -------------------------------
           |- {P} C1;C2 {R}

 
     |- MK_SPEC({P},C1,{Q})   ,   |- MK_SPEC({Q},C2,{R})
     -------------------------------------------------------------
                 |- MK_SPEC({P},MK_SEQ(C1,C2),{R})

%

let SEQ_RULE(hth1,hth2) = 
 MATCH_MP SEQ_THM (CONJ hth1 hth2) ? failwith `SEQ_RULE`;;

% Derived Sequencing Rule. SEQL_RULE :

     |- {P1} C1 {Q1}, ...  , |- {Q(n-1)} Cn {Rn}
     -------------------------------------------
            |- {P1} C1;...;Cn {Rn}


     |- MK_SPEC({P1},C1,{Q1}), ... , |- MK_SPEC({Q(n-1)},Cn,{Rn})
     ------------------------------------------------------------
          |- MK_SPEC({P1},MK_SEQ(MK_SEQ(C1,C2), ... ,Cn),{Rn})

%

letrec SEQL_RULE thl =
 (if null thl     then fail
  if null(tl thl) then hd thl
                  else SEQL_RULE(SEQ_RULE(hd thl,hd(tl thl)).tl(tl thl))
 ) ? failwith `SEQL_RULE`;;

% Test examples:

   pretty_on();;

   let hth1 = ASSIGN_AX "{(R=x) /\ (Y=y)}" "R:=X";;
   let hth2 = ASSIGN_AX "{(R=x) /\ (X=y)}" "X:=Y";;
   let hth3 = ASSIGN_AX "{(Y=x) /\ (X=y)}" "Y:=R";;

   let hth4 = SEQ_RULE (hth1,hth2);;
   let hth5 = SEQ_RULE (hth4,hth3);;

   let hth6 = SEQL_RULE[hth1;hth2;hth3];;

%

% Precondition Strengthening. PRE_STRENGTH_RULE:

       |- P' ==> P  ,  |- {P} C {Q}
       ----------------------------
            |- {P'} C {Q}


       |- P' ==> P   ,   |- MK_SPEC({P},C,{Q})
       --------------------------------------------
               |- MK_SPEC({P'},C,{Q})

%


let PRE_STRENGTH_RULE(th,hth) = 
 HOL_MATCH_MP 
  PRE_STRENGTH_THM 
 (CONJ (TRANS_THM th) hth)
 ? failwith `PRE_STRENGTH_RULE`;;

% Test examples:

   let hth1 = ASSIGN_AX "{(R=x) /\ (Y=y)}" "R:=X";;
   let hth2 = ASSIGN_AX "{(R=x) /\ (X=y)}" "X:=Y";;
   let hth3 = ASSIGN_AX "{(Y=x) /\ (X=y)}" "Y:=R";;

   let hth4 = SEQ_RULE (hth1,hth2);;
   let hth5 = SEQ_RULE (hth4,hth3);;

   let th  = DISCH_ALL(CONTR "((X:num=x) /\ (Y:num=y))" (ASSUME "F"))
   and hth = hth5;;

   let hth6 = PRE_STRENGTH_RULE(th,hth);; 

%

% Postcondition Weakening. POST_WEAK_RULE:

       |- {P} C {Q}  ,  |- Q ==> Q'
     -------------------------------
           |- {P} C {Q'}


       |- MK_SPEC({P},C,{Q})   ,   |- Q ==> Q'
       --------------------------------------------
               |- MK_SPEC({P'},C,{Q'})

%

let POST_WEAK_RULE(hth,th) = 
 HOL_MATCH_MP 
  POST_WEAK_THM 
 (CONJ hth (TRANS_THM th))
 ? failwith `POST_WEAK_RULE`;;

% Test

   let hth1 = ASSIGN_AX "{(R=x) /\ (Y=y)}" "R:=X";;
   let hth2 = ASSIGN_AX "{(R=x) /\ (X=y)}" "X:=Y";;
   let hth3 = ASSIGN_AX "{(Y=x) /\ (X=y)}" "Y:=R";;

   let hth4 = SEQ_RULE (hth1,hth2);;
   let hth5 = SEQ_RULE (hth4,hth3);;

   let th  = TAC_PROOF(([],"((Y:num=x) /\ (X:num=y)) ==> T"), REWRITE_TAC[]);;

   let hth6 = POST_WEAK_RULE(hth5,th);;

%


% One-armed Conditional Rule. IF1_RULE:

       |- {P /\ B} C {Q}  ,  |- P /\ ~B ==> Q
       --------------------------------------
              |- {P} if B then C {Q}


       |- MK_SPEC({P/\B},C,{Q})   ,   |- P /\ ~B ==> Q
       ----------------------------------------------------
            |- MK_SPEC({P},MK_IF1({B},C),{Q}          

%

let IF1_RULE(hth,th) = 
 HOL_MATCH_MP 
  IF1_THM 
 (CONJ hth (TRANS_THM th))
 ? failwith `IF1_RULE`;;

% Examples for testing:

   new_theory`MAX` ? extend_theory `MAX` ? ();;

   let MAX =
    new_definition
     (`MAX`, "MAX(m,n) = ((m>n) => m | n)") ? definition `MAX` `MAX` ;;

   let hth1 = ASSIGN_AX "{X = MAX(x,y)}" "X := Y";;

   let MAX_LEMMA1 =
    theorem `MAX` `MAX_LEMMA1`
    ?
    prove_thm
     (`MAX_LEMMA1`,
      "((X=x) /\ (Y=y)) /\ (Y>X) ==> (Y=MAX(x,y))",
      REWRITE_TAC[MAX;GREATER]
       THEN REPEAT STRIP_TAC
       THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
       THEN ASM_CASES_TAC "Y<X"
       THEN ASM_REWRITE_TAC[]
       THEN IMP_RES_TAC LESS_ANTISYM);;

   let hth2 = PRE_STRENGTH_RULE(MAX_LEMMA1,hth1);;

   let MAX_LEMMA2 =
    theorem `MAX` `MAX_LEMMA2`
    ?
    prove_thm
     (`MAX_LEMMA2`,
      "((X=x) /\ (Y=y)) /\ ~(Y>X) ==> (X=MAX(x,y))",
      REWRITE_TAC[MAX;GREATER;NOT_LESS;LESS_OR_EQ]
       THEN REPEAT STRIP_TAC
       THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
       THEN ASM_CASES_TAC "Y<X"
       THEN ASM_REWRITE_TAC[]
       THEN RES_TAC);;

   let hth3 = IF1_RULE(hth2,MAX_LEMMA2);;

%


% Two-armed Conditional Rule. IF2_RULE:

       |- {P /\ B} C1 {Q}  ,  |- {P /\ ~B} C2 {Q}
       ------------------------------------------
             |- {P} if B then C1 else C2 {Q}

       |- MK_SPEC({P/\B},{C1},{Q})   ,   |- MK_SPEC({P/\~B},{C2},{Q})
       --------------------------------------------------------------
                  |- MK_SPEC({P},MK_IF2({B},C1,C2),{Q})

%

let IF2_RULE (hth1,hth2) =
 HOL_MATCH_MP IF2_THM (CONJ hth1 hth2) ? failwith `IF2_RULE`;;


% Examples

   let MAX =
    new_definition
     (`MAX`, "MAX(m,n) = ((m>n) => m | n)") ? definition `MAX` `MAX`;;

   let hth1 = ASSIGN_AX "{R = MAX(x,y)}" "R := Y";;

   let MAX_LEMMA1 =
    theorem `MAX` `MAX_LEMMA1`
    ?
    prove_thm
     (`MAX_LEMMA1`,
      "((X=x) /\ (Y=y)) /\ (Y>X) ==> (Y=MAX(x,y))",
      REWRITE_TAC[MAX;GREATER]
       THEN REPEAT STRIP_TAC
       THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
       THEN ASM_CASES_TAC "Y<X"
       THEN ASM_REWRITE_TAC[]
       THEN IMP_RES_TAC LESS_ANTISYM);;

   let hth2 = PRE_STRENGTH_RULE(MAX_LEMMA1,hth1);;

   let hth3 = ASSIGN_AX "{R = MAX(x,y)}" "R := X";;

   let MAX_LEMMA2 =
    theorem `MAX` `MAX_LEMMA2`
    ?
    prove_thm
     (`MAX_LEMMA2`,
      "((X=x) /\ (Y=y)) /\ ~(Y>X) ==> (X=MAX(x,y))",
      REWRITE_TAC[MAX;GREATER;NOT_LESS;LESS_OR_EQ]
       THEN REPEAT STRIP_TAC
       THEN ASSUM_LIST(\thl. ONCE_REWRITE_TAC(mapfilter SYM thl))
       THEN ASM_CASES_TAC "Y<X"
       THEN ASM_REWRITE_TAC[]
       THEN RES_TAC);;

   let hth4 = PRE_STRENGTH_RULE(MAX_LEMMA2,hth3);;

   let hth5 = IF2_RULE(hth2,hth4);;

%


% WHILE-Rule. WHILE_RULE:

                 |- {P /\ B} C {P}
           -----------------------------
           |- {P} while B do C {P /\ ~B}


                 |- MK_SPEC({P /\ B},C,{P})
            -----------------------------------------
            |- MK_SPEC({P},MK_WHILE({B},C),{P /\ ~B})

%

let WHILE_RULE hth =
 HOL_MATCH_MP WHILE_THM hth ? failwith `WHILE_RULE`;;

% Examples

 let hth1 = ASSIGN_AX "{X = R + (Y * Q)}" "Q := (Q + 1)";;

 let hth2 = ASSIGN_AX "{X = R + (Y * (Q + 1))}" "R := (R-Y)";;

 let hth3 = SEQ_RULE(hth2,hth1);;

 let th1 =
  TAC_PROOF
   (([], "(X = R + (Y * Q)) /\ (Y<=R) ==> (X = (R - Y) + (Y * (Q + 1)))"),
    REPEAT STRIP_TAC
     THEN REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_CLAUSES]
     THEN ONCE_REWRITE_TAC[SPEC "Y*Q" ADD_SYM]
     THEN ONCE_REWRITE_TAC[ADD_ASSOC]
     THEN IMP_RES_TAC SUB_ADD
     THEN ASM_REWRITE_TAC[]);;

  let hth4 = PRE_STRENGTH_RULE(th1,hth3);;

  let hth5 = WHILE_RULE hth4;;

  let hth6 =
   SEQL_RULE
    [ASSIGN_AX "{X = R + (Y * 0)}" "R := X";
     ASSIGN_AX "{X = R + (Y * Q)}" "Q := 0";
     hth5];;

  let th2 =
   TAC_PROOF
    (([],"~(Y <= R) = (R < Y)"),
     ONCE_REWRITE_TAC[SYM(SPEC "R<Y" (hd(CONJUNCTS NOT_CLAUSES)))]
     THEN PURE_REWRITE_TAC[NOT_LESS]
     THEN REFL_TAC);;

  let hth7 = REWRITE_RULE[th2;MULT_CLAUSES;ADD_CLAUSES]hth6;;

  let hth6 =
   SEQL_RULE
    [ASSIGN_AX "{X = R + (Y * 0)}" "R := X";
     ASSIGN_AX "{X = R + (Y * Q)}" "Q := 0";
     WHILE_RULE
      (PRE_STRENGTH_RULE
        (th1,SEQL_RULE
              [ASSIGN_AX "{X = R + (Y * (Q + 1))}" "R := (R-Y)";
               ASSIGN_AX "{X = R + (Y * Q)}" "Q := (Q + 1)"]))];;

%
