
% Axioms and rules of Hoare logic for total correctness %

%<
load_library`string`;; 

load_theory `halts_logic` ? ();; 

loadx `syntax_functions`;; 
>%

% dest_t_spec "T_SPEC(p,c,q)" --> ("p","c","q") %

let dest_t_spec t =
 (let n,[p;c;q] = ((I # dest_tuple) o dest_comb) t
  in
  if n = "T_SPEC"
   then (p,c,q)
   else fail
 ) ? failwith `dest_t_spec`;;



load_theorems `halts_thms`;;

%< Only needed if hoare_logic not loaded first

loadx `hol_match`;; 

load_theorems `hoare_thms`;; 

let BND = definition `semantics` `BND`;; 
  
% |- t1 = t2  ,  t   --->   |- t = t[t2/t1] %

let SUBS_CONV th t =
 let x = genvar(type_of t)
 in
 let t1 = mk_eq(x,t)
 in
 let th1 = DISCH t1 (SUBS [th] (ASSUME t1))
 in
 MP(INST[t,x]th1)(REFL t);;

% 
   BND_CONV "BND e `X` s `X`"   --->   |- BND_CONV "BND e `X` s `X` = e
   BND_CONV "BND e `X` s `Y`"   --->   |- BND_CONV "BND e `X` s `Y` = (s `Y`)
                                           (if `X` is not equal to `Y`)
%

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
>%

% Assignment Axiom.  ASSIGN_T_AX :

    "P" "{X := E}"   --->   |- T_SPEC({P[E/X]}, MK_ASSIGN(`X`,{E}), {P}) 
%

let ASSIGN_T_AX p c = 
 (let x,e = dest_assign c
  in
  let th1 = SPECL[p;x;e]ASSIGN_T_THM
  in
  let t1 = (snd o dest_abs o fst o dest_t_spec o concl)th1
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
 ) ? failwith `ASSIGN_T_AX`;;


% Test example:

   pretty_on();;

   let p = "{(X + Y = x) /\ (Y = y)}";;
   let c = "X := (X + Y)";;
   ASSIGN_T_AX p c;;

   let hth1 = ASSIGN_T_AX "{(R=x) /\ (Y=y)}" "R := X";;
   let hth2 = ASSIGN_T_AX "{(R=x) /\ (X=y)}" "X := Y";;

   let p = "{(p:num list->bool)[X;Y]}";;
   let c = "X := e X Y";;
   ASSIGN_T_AX p c;;

%

% Sequencing Rule. SEQ_T_RULE:

     |- [P] C1 [Q]  ,  |- [Q] C2 [R]
     -------------------------------
           |- [P] C1;C2 [R]

 
     |- T_SPEC({P},C1,{Q})   ,   |- T_SPEC({Q},C2,{R})
     -------------------------------------------------
                 |- T_SPEC({P},MK_SEQ(C1,C2),{R})

%

let SEQ_T_RULE(hth1,hth2) = 
 MATCH_MP SEQ_T_THM (CONJ hth1 hth2) ? failwith `SEQ_T_RULE`;;

% Derived Sequencing Rule. SEQL_T_RULE :

     |- [P1] C1 [Q1], ...  , |- [Q(n-1)] Cn [Rn]
     -------------------------------------------
            |- [P1] C1;...;Cn [Rn]


     |- T_SPEC({P1},C1,{Q1}), ... , |- T_SPEC({Q(n-1)},Cn,{Rn})
     ------------------------------------------------------------
          |- T_SPEC({P1},MK_SEQ(MK_SEQ(C1,C2), ... ,Cn),{Rn})

%

letrec SEQL_T_RULE thl =
 (if null thl     then fail
  if null(tl thl) then hd thl
                  else SEQL_T_RULE(SEQ_T_RULE(hd thl,hd(tl thl)).tl(tl thl))
 ) ? failwith `SEQL_T_RULE`;;

% Test examples:

   let hth1 = ASSIGN_T_AX "{(R=x) /\ (Y=y)}" "R:=X";;
   let hth2 = ASSIGN_T_AX "{(R=x) /\ (X=y)}" "X:=Y";;
   let hth3 = ASSIGN_T_AX "{(Y=x) /\ (X=y)}" "Y:=R";;

   let hth4 = SEQ_T_RULE (hth1,hth2);;
   let hth5 = SEQ_T_RULE (hth4,hth3);;

   let hth6 = SEQL_T_RULE[hth1;hth2;hth3];;

%

% Precondition Strengthening. PRE_STRENGTH_T_RULE:

       |- P' ==> P  ,  |- [P] C [Q]
       ----------------------------
            |- [P'] C [Q]


       |- P' ==> P   ,   |- T_SPEC({P},C,{Q})
       --------------------------------------------
               |- T_SPEC({P'},C,{Q})

%


let PRE_STRENGTH_T_RULE(th,hth) = 
 HOL_MATCH_MP 
  PRE_STRENGTH_T_THM 
 (CONJ (TRANS_THM th) hth)
 ? failwith `PRE_STRENGTH_T_RULE`;;

% Test examples:

   let hth1 = ASSIGN_T_AX "{(R=x) /\ (Y=y)}" "R:=X";;
   let hth2 = ASSIGN_T_AX "{(R=x) /\ (X=y)}" "X:=Y";;
   let hth3 = ASSIGN_T_AX "{(Y=x) /\ (X=y)}" "Y:=R";;

   let hth4 = SEQ_T_RULE (hth1,hth2);;
   let hth5 = SEQ_T_RULE (hth4,hth3);;

   let th  = DISCH_ALL(CONTR "((X:num=x) /\ (Y:num=y))" (ASSUME "F"))
   and hth = hth5;;

   let hth6 = PRE_STRENGTH_T_RULE(th,hth);;

%

% Postcondition Weakening. POST_WEAK_T_RULE:

       |- [P] C [Q]  ,  |- Q ==> Q'
     -------------------------------
           |- [P] C [Q']


       |- T_SPEC({P},C,{Q})   ,   |- Q ==> Q'
       --------------------------------------------
               |- T_SPEC({P'},C,{Q'})

%

let POST_WEAK_T_RULE(hth,th) = 
 HOL_MATCH_MP 
  POST_WEAK_T_THM 
 (CONJ hth (TRANS_THM th))
 ? failwith `POST_WEAK_T_RULE`;;

% Test

   let hth1 = ASSIGN_T_AX "{(R=x) /\ (Y=y)}" "R:=X";;
   let hth2 = ASSIGN_T_AX "{(R=x) /\ (X=y)}" "X:=Y";;
   let hth3 = ASSIGN_T_AX "{(Y=x) /\ (X=y)}" "Y:=R";;

   let hth4 = SEQ_T_RULE (hth1,hth2);;
   let hth5 = SEQ_T_RULE (hth4,hth3);;

   let th  = TAC_PROOF(([],"((Y:num=x) /\ (X:num=y)) ==> T"), REWRITE_TAC[]);;

   let hth6 = POST_WEAK_T_RULE(hth5,th);;

%


% One-armed Conditional Rule. IF1_T_RULE:

       |- [P /\ B] C [Q]  ,  |- P /\ ~B ==> Q
       --------------------------------------
              |- [P] if B then C [Q]


       |- T_SPEC({P/\B},C,{Q})   ,   |- P /\ ~B ==> Q
       ----------------------------------------------------
            |- T_SPEC({P},MK_IF1({B},C),{Q}          

%

let IF1_T_RULE(hth,th) = 
 HOL_MATCH_MP 
  IF1_T_THM 
 (CONJ hth (TRANS_THM th))
 ? failwith `IF1_T_RULE`;;

% Examples for testing:

   new_theory `MAX` ? extend_theory `MAX` ? ();;

   let MAX =
    new_definition
     (`MAX`, "MAX(m,n) = ((m>n) => m | n)") ? definition `MAX` `MAX` ;;

   let hth1 = ASSIGN_T_AX "{X = MAX(x,y)}" "X:=Y";;

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

   let hth2 = PRE_STRENGTH_T_RULE(MAX_LEMMA1,hth1);;

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

   let hth3 = IF1_T_RULE(hth2,MAX_LEMMA2);;

%


% Two-armed Conditional Rule. IF2_RULE:

       |- [P /\ B] C1 [Q]  ,  |- [P /\ ~B] C2 [Q]
       ------------------------------------------
             |- [P] if B then C1 else C2 [Q]

       |- T_SPEC({P/\B},{C1},{Q})   ,   |- T_SPEC({P/\~B},{C2},{Q})
       --------------------------------------------------------------
                  |- T_SPEC({P},MK_IF2({B},C1,C2),{Q})

%

let IF2_T_RULE (hth1,hth2) =
 HOL_MATCH_MP IF2_T_THM (CONJ hth1 hth2) ? failwith `IF2_T_RULE`;;


% Examples

   let MAX =
    new_definition
     (`MAX`, "MAX(m,n) = ((m>n) => m | n)") ? definition `MAX` `MAX`;;

   let hth1 = ASSIGN_T_AX "{R = MAX(x,y)}" "R := Y";;

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

   let hth2 = PRE_STRENGTH_T_RULE(MAX_LEMMA1,hth1);;

   let hth3 = ASSIGN_T_AX "{R = MAX(x,y)}" "R := X";;

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

   let hth4 = PRE_STRENGTH_T_RULE(MAX_LEMMA2,hth3);;

   let hth5 = IF2_T_RULE(hth2,hth4);;

%


% WHILE-Rule. WHILE_T_RULE:

          |- [P /\ B /\ X=n] C [P /\ X<n]
          -------------------------------
           |- [P] while B do C [P /\ ~B]


          |- T_SPEC({P /\ B /\ X=n},C,{P /\ X<n})
          ---------------------------------------
          |- T_SPEC({P},MK_WHILE({B},C),{P /\ ~B})

%

let WHILE_T_RULE hth =
 let p,(),() = dest_t_spec(concl(SPEC_ALL hth))
 in
 let (X,n) = dest_eq(snd(dest_conj(snd(dest_conj(snd(dest_abs p))))))
 in
 let hth1 = GEN "n:num" (INST["n:num",n]hth)
 in
 HOL_MATCH_MP WHILE_T_THM hth1 ? failwith `WHILE_T_RULE`;;

% Examples

 pretty_on();;

 let hth1 =
  ASSIGN_T_AX "{(0 < Y /\ (X = R + (Y * Q))) /\ R < r}" "Q := (Q + 1)";;

 let hth2 =
  ASSIGN_T_AX "{(0 < Y /\ (X = R + (Y * (Q + 1)))) /\ R < r}" "R := (R-Y)";;

 let hth3 = SEQ_T_RULE(hth2,hth1);;

 let lemma1 =
  TAC_PROOF
   (([], "!m. 0 < m ==> !n. 0 < n ==> (n - m) < n"),
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

 let lemma2 =
  TAC_PROOF
   (([], "!m n p. m < n /\ n <= p ==> m < p"),
    REWRITE_TAC[LESS_OR_EQ]
     THEN REPEAT STRIP_TAC
     THEN IMP_RES_TAC LESS_TRANS
     THEN ASSUM_LIST(\[th1;th2;th3]. REWRITE_TAC[SYM th2])
     THEN ASM_REWRITE_TAC[]);;

 let th1 =
  TAC_PROOF
   (([], "(0 < Y /\ (X = R + (Y * Q))) /\ (Y<=R) /\ (R = r)
          ==> (0 < Y /\ (X = (R - Y) + (Y * (Q + 1)))) /\ (R - Y) < r"),
    REPEAT STRIP_TAC
     THEN REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_CLAUSES]
     THEN ONCE_REWRITE_TAC[SPEC "Y*Q" ADD_SYM]
     THEN ONCE_REWRITE_TAC[ADD_ASSOC]
     THEN IMP_RES_TAC SUB_ADD
     THEN ASM_REWRITE_TAC[]
     THEN IMP_RES_TAC lemma2
     THEN ASSUM_LIST(\thl. REWRITE_TAC[SYM(el 4 thl)])
     THEN IMP_RES_TAC lemma1);;

  let hth4 = PRE_STRENGTH_T_RULE(th1,hth3);;

  let hth5 = WHILE_T_RULE hth4;;

  let hth6 =
   SEQL_T_RULE
    [ASSIGN_T_AX "{(0 < Y) /\ (X = R + (Y * 0))}" "R := X";
     ASSIGN_T_AX "{(0 < Y) /\ (X = R + (Y * Q))}" "Q := 0";
     hth5];;

  let th2 =
   TAC_PROOF
    (([],"~(Y <= R) = (R < Y)"),
     ONCE_REWRITE_TAC[SYM(SPEC "R<Y" (hd(CONJUNCTS NOT_CLAUSES)))]
     THEN PURE_REWRITE_TAC[NOT_LESS]
     THEN REFL_TAC);;

  let hth7 = REWRITE_RULE[th2;MULT_CLAUSES;ADD_CLAUSES]hth6;;

  let hth6 =
   SEQL_T_RULE
    [ASSIGN_T_AX "{(0 < Y) /\ (X = R + (Y * 0))}" "R := X";
     ASSIGN_T_AX "{(0 < Y) /\ (X = R + (Y * Q))}" "Q := 0";
     WHILE_T_RULE
      (PRE_STRENGTH_T_RULE
        (th1,SEQL_T_RULE
              [ASSIGN_T_AX "{((0 < Y) /\ (X = R + (Y * (Q + 1)))) /\ (R < r)}" 
                           "R := (R-Y)";
               ASSIGN_T_AX "{((0 < Y) /\ (X = R + (Y * Q))) /\ (R < r)}" 
                           "Q := (Q + 1)"]))];;

%