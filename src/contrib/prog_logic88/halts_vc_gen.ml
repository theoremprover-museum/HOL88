%
 This file defines tactics for generating verification conditions
 from annotated total correctness specifications. 
 The idea is that a goal 

    T_SPEC({P},C,{Q})

 is achieved by a theorem

    |- T_SPEC({P},{C},{Q})

 The validations of these tactics use the derived rules of Hoare logic from 
 the file halts_logic.ml (see also vc_gen.ml).
%

% loadx `halts_logic`;; %

% ASSIGN_T_TAC

    [P] X:=E [Q]
    ============
    P ==> Q[E/X]
%

let ASSIGN_T_TAC ((asl,t):goal) =
 (let p,c,q = dest_t_spec t
  in
  let x,e = dest_assign c
  in
  let p' = untrans_term p
  and q' = untrans_term q
  and e' = untrans_term e
  and x' = unprime x
  in
  ([asl,mk_imp(p', subst[e',x']q')],
   \[th]. PRE_STRENGTH_T_RULE(th, ASSIGN_T_AX q c))
 ) ? failwith `ASSIGN_T_TAC`;;

% Test examples:

 g "T_SPEC({X = x}, (X := X+1), {X = x+1})";;

 e ASSIGN_T_TAC;;

%

% SEQ_T_TAC

    [P] C1; ... ; Cn; X:=E [Q]          [P] C1; ... Cn; {R} C [Q]
    ==========================     ==================================
     [P] C1; ... ;Cn [Q[E/X]]      [P] C1; ... ; Cn [R]  ,  [R] C [Q]
%

let SEQ_T_TAC ((asl,t):goal) =
 (let p,c,q = dest_t_spec t 
  in
  let cl = dest_seql c
  in
  let cl',c = butlast cl, last cl
  in
  (let x,e = dest_assign c
   in
   let sq,q' = dest_abs q
   and se,e' = dest_abs e
   in
   if null(tl cl')
    then ([asl,"T_SPEC(^p, 
                        ^(hd cl'), 
                        ^(mk_abs(sq,subst[e',mk_comb(se,x)]q')))"], 
          \[th]. SEQ_T_RULE(th,ASSIGN_T_AX q c))
    else
     ([asl,"T_SPEC(^p,
                    ^(mk_seql cl'),
                    ^(mk_abs(sq,subst[e',mk_comb(se,x)]q')))"],
      \[th]. SEQ_T_RULE(th,ASSIGN_T_AX q c)))
  ?
  (let cl'',r = butlast cl',dest_assert(last cl')
   in
   if null(tl cl'')
    then
     ([(asl,"T_SPEC(^p, ^(hd cl''), ^r)");(asl,"T_SPEC(^r, ^c, ^q)")],
      \[th1;th2]. SEQ_T_RULE(th1,th2))
    else
     ([(asl,"T_SPEC(^p, ^(mk_seql cl''), ^r)");(asl,"T_SPEC(^r, ^c, ^q)")],
      \[th1;th2]. SEQ_T_RULE(th1,th2)))
 )
 ? failwith `SEQ_T_TAC`;;

% Test examples


 g "T_SPEC({(X=x) /\ (Y=y)}, (Z:=X;X:=Y;Y:=Z), {(X=y) /\ (Y=x)})";;

 e(REPEAT SEQ_T_TAC);;
 e(ASSIGN_T_TAC);;
 e(STRIP_TAC THEN ASM_REWRITE_TAC[]);;

 g"T_SPEC({(X=x) /\ (Y=y)},
             (Z:=X; X:=Y; assert{Z=Y}; if T then Y:=Z else Z:=Y),
             {(X=y) /\ (Y=x)})";
 e(SEQ_T_TAC);;
%


% IF1_T_TAC

           [P] if B then C [Q]
    ==================================
    [P /\ B] C [Q]   ,   P /\ ~B ==> Q
%

let IF1_T_TAC ((asl,t):goal) =
 (let p,c,q = dest_t_spec t 
  in
  let b,c1 = dest_if1 c
  in
  let p'     = untrans_term p
  and q'     = untrans_term q
  and b'     = untrans_term b
  and sp,p'' = dest_abs p
  and sq,g'' = dest_abs q
  and sb,b'' = dest_abs b
  in
  ([(asl,"T_SPEC((\^sp.^p'' /\ ^b''), ^c1, ^q)");(asl,"^p' /\ ~^b' ==> ^q'")],
   \[th1;th2]. IF1_T_RULE(th1,th2))
 )
 ? failwith `IF1_T_TAC`;;

%
   new_theory `MAX` ? extend_theory `MAX` ? ();;

   let MAX =
    new_definition
     (`MAX`, "MAX(m,n) = ((m>n) => m | n)") ? definition `MAX` `MAX` ;;

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

  let t = "T_SPEC({(X=x) /\ (Y=y)}, (if Y>X then X:=Y), {X = MAX(x,y)})";;

  TAC_PROOF
   (([], "T_SPEC({(X=x) /\ (Y=y)}, (if Y>X then X:=Y), {X = MAX(x,y)})"),
    IF1_T_TAC
     THEN (ASSIGN_T_TAC ORELSE ALL_TAC)
     THEN REWRITE_TAC[MAX_LEMMA1;MAX_LEMMA2]);;
%

% IF2_T_TAC

         [P] IF B then C1 else C2 [Q]
    ======================================
    [P /\ B] C1 [Q]   ,   [P /\ ~B] C2 [Q]
%

let IF2_T_TAC ((asl,t):goal) =
 (let p,c,q = dest_t_spec t 
  in
  let b,c1,c2 = dest_if2 c
  in
  let sp,p'' = dest_abs p
  and sq,g'' = dest_abs q
  and sb,b'' = dest_abs b
  in
  ([(asl,"T_SPEC((\^sp. ^p'' /\ ^b''), ^c1, ^q)");
    (asl,"T_SPEC((\^sp. ^p'' /\ ~^b''), ^c2, ^q)")],
   \[th1;th2]. IF2_T_RULE(th1,th2))
 )
 ? failwith `IF2_T_TAC`;;

%
  let t = 
   "T_SPEC({(X=x) /\ (Y=y)}, (if Y>X then X:=Y else X:=X), {X = MAX(x,y)})";;

  TAC_PROOF
   (([], "T_SPEC({(X=x)/\(Y=y)}, (if Y>X then X:=Y else X:=X), {X = MAX(x,y)})"),
    IF2_T_TAC
     THEN ASSIGN_T_TAC
     THEN REWRITE_TAC[MAX_LEMMA1;MAX_LEMMA2]);;
%

% WHILE_T_TAC

            [P] WHILE B SEQ[invariant R; variant X; C] [Q]
    ==============================================================
    P ==> R   ,   [R /\ B /\ X=n] C [R /\ X<n]   ,   R /\ ~B ==> Q
%

let var_name = fst o dest_var;;

let WHILE_T_TAC ((asl,t):goal) =
 (let p,c,q = dest_t_spec t 
  in
  let b,c1 = dest_while c
  in
  let cl = dest_seql c1
  in
  let r = dest_invariant(hd cl)
  and v = dest_variant(hd(tl cl))
  and c2 = 
   if null(tl(tl(tl cl)))
    then hd(tl(tl cl))
    else mk_seql(tl(tl cl))
  in
  let p'     = untrans_term p
  and q'     = untrans_term q
  and r'     = untrans_term r
  and v'     = untrans_term v
  and b'     = untrans_term b
  and sr,r'' = dest_abs r
  and sv,v'' = dest_abs v
  and sb,b'' = dest_abs b
  in
  let n = variant
           (freesl[p;c;q])(mk_var(ascii(32 + ascii_code(var_name v')),":num"))
  in
  ([(asl,"^p' ==> ^r'");
    (asl,"T_SPEC((\^sr. ^r'' /\ ^b'' /\ (^v''=^n)), 
                 ^c2, 
                 (\^sr. ^r'' /\ (^v''<^n)))");
    (asl,"^r' /\ ~^b' ==> ^q'")],
   \[th1;th2;th3]. 
     POST_WEAK_T_RULE(PRE_STRENGTH_T_RULE(th1, WHILE_T_RULE th2), th3))
 ) ? failwith `WHILE_T_TAC`;;

%

let t =
 "T_SPEC 
   ({(R=X) /\ (Q=0)},
    (while Y <= R
      do (invariant{X = R + (Y * Q)}; variant{R}; R := R-Y; Q := Q+1)),
    {(X = R + (Y * Q)) /\ R < Y})";;

let t =
 "T_SPEC 
   ({0 < Y},
    (R := X;
     Q := 0;
     assert{(R=X) /\ (Q=0)};
     while Y <= R
      do (invariant{X = R + (Y * Q)}; variant{R};
          R := R-Y; Q := Q+1)),
    {(X = R + (Y * Q)) /\ R < Y})";;

%

let VC_T_TAC =
 REPEAT(ASSIGN_T_TAC 
         ORELSE SEQ_T_TAC 
         ORELSE IF1_T_TAC 
         ORELSE IF2_T_TAC 
         ORELSE WHILE_T_TAC);;

% Examples:

pretty_on();;

g
 "T_SPEC 
   ({0 < Y},
    (R := X;
     Q := 0;
     assert{(0 < Y) /\ (R=X) /\ (Q=0)};
     while Y <= R
      do (invariant{(0 < Y) /\ (X = R + (Y * Q))}; variant{R};
          R := R-Y; Q := Q+1)),
    {(X = R + (Y * Q)) /\ R < Y})";;

e(VC_T_TAC);;

e(REWRITE_TAC[]);;

e(STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES]);;

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

e(ACCEPT_TAC th1);;

e(REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]);;
e(DISCH_TAC);;
e(ASM_REWRITE_TAC[]);;

let DIV_CORRECT =
 prove
  ("T_SPEC({0 < Y},
           (R:=X;
            Q:=0;
            assert{(0 < Y) /\ (R = X) /\ (Q = 0)};
            while Y<=R
             do (invariant{(0 < Y) /\ (X = (R + (Y * Q)))};
                 variant{R};
                 R:=R-Y; Q:=Q+1)),
           {(R < Y) /\ (X = (R + (Y * Q)))})",
   VC_T_TAC
    THENL
     [REWRITE_TAC[];
      STRIP_TAC
       THEN ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES];
      ACCEPT_TAC th1;
      REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]
       THEN DISCH_TAC
       THEN ASM_REWRITE_TAC[]
     ]);;

%
