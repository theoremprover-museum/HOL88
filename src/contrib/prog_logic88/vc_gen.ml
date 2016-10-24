%
 This file defines tactics for generating verification conditions
 from annotated partial correctness specifications. 
 The idea is that a goal (with annotations)

    MK_SPEC({P},C,{Q})

 is achieved by a theorem (without annotations)

    |- MK_SPEC({P},{C},{Q})

 The validations of these tactics use the derived rules of Hoare logic from 
 the file hoare_logic.ml. Note that since the theorems generated do not
 technically achieve the goal, since they do not contain the annotations.
 This means that expandf, instead of expand, must be used.
%

%<
loadx `hoare_logic`;;
>%

% ASSIGN_TAC

    {P} X:=E {Q}
    ============
    P ==> Q[E/X]
%

let ASSIGN_TAC ((asl,t):goal) =
 (let p,c,q = dest_spec t
  in
  let x,e = dest_assign c
  in
  let p' = untrans_term p
  and q' = untrans_term q
  and e' = untrans_term e
  and x' = unprime x
  in
  ([asl,mk_imp(p', subst[e',x']q')],
   \[th]. PRE_STRENGTH_RULE(th, ASSIGN_AX q c))
 ) ? failwith `ASSIGN_TAC`;;


% SEQ_TAC

    {P} C1; ... ; Cn; X:=E {Q}          {P} C1; ... Cn; {R} C {Q}
    ==========================     ==================================
     {P} C1; ... ;Cn {Q[E/X]}      {P} C1; ... ; Cn {R}  ,  {R} C {Q}
%

let SEQ_TAC ((asl,t):goal) =
 (let p,c,q = dest_spec t 
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
    then ([asl,"MK_SPEC(^p, 
                        ^(hd cl'), 
                        ^(mk_abs(sq,subst[e',mk_comb(se,x)]q')))"], 
          \[th]. SEQ_RULE(th,ASSIGN_AX q c))
    else
     ([asl,"MK_SPEC(^p,
                    ^(mk_seql cl'),
                    ^(mk_abs(sq,subst[e',mk_comb(se,x)]q')))"],
      \[th]. SEQ_RULE(th,ASSIGN_AX q c)))
  ?
  (let cl'',r = butlast cl',dest_assert(last cl')
   in
   if null(tl cl'')
    then
     ([(asl,"MK_SPEC(^p, ^(hd cl''), ^r)");(asl,"MK_SPEC(^r, ^c, ^q)")],
      \[th1;th2]. SEQ_RULE(th1,th2))
    else
     ([(asl,"MK_SPEC(^p, ^(mk_seql cl''), ^r)");(asl,"MK_SPEC(^r, ^c, ^q)")],
      \[th1;th2]. SEQ_RULE(th1,th2)))
 )
 ? failwith `SEQ_TAC`;;


% IF1_TAC

           {P} if B then C {Q}
    ==================================
    {P /\ B} C {Q}   ,   P /\ ~B ==> Q
%

let IF1_TAC ((asl,t):goal) =
 (let p,c,q = dest_spec t 
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
  ([(asl,"MK_SPEC((\^sp.^p'' /\ ^b''), ^c1, ^q)");(asl,"^p' /\ ~^b' ==> ^q'")],
   \[th1;th2]. IF1_RULE(th1,th2))
 )
 ? failwith `IF1_TAC`;;

% IF2_TAC

         {P} IF B then C1 else C2 {Q}
    ======================================
    {P /\ B} C1 {Q}   ,   {P /\ ~B} C2 {Q}
%

let IF2_TAC ((asl,t):goal) =
 (let p,c,q = dest_spec t 
  in
  let b,c1,c2 = dest_if2 c
  in
  let sp,p'' = dest_abs p
  and sq,g'' = dest_abs q
  and sb,b'' = dest_abs b
  in
  ([(asl,"MK_SPEC((\^sp. ^p'' /\ ^b''), ^c1, ^q)");
    (asl,"MK_SPEC((\^sp. ^p'' /\ ~^b''), ^c2, ^q)")],
   \[th1;th2]. IF2_RULE(th1,th2))
 )
 ? failwith `IF2_TAC`;;

% WHILE_TAC

            {P} WHILE B SEQ[ASSERT R; C] {Q}
    ================================================
    P ==> R   ,   {R /\ B} C {R}   ,   R /\ ~B ==> Q
%

let WHILE_TAC ((asl,t):goal) =
 (let p,c,q = dest_spec t 
  in
  let b,c1 = dest_while c
  in
  let cl = dest_seql c1
  in
  let r = dest_invariant(hd cl)
  and c2 = 
   if null(tl(tl cl))
    then hd(tl cl)  
    else mk_seql(tl cl)
  in
  let p'     = untrans_term p
  and q'     = untrans_term q
  and r'     = untrans_term r
  and b'     = untrans_term b
  and sr,r'' = dest_abs r
  and sb,b'' = dest_abs b
  in
  ([(asl,"^p' ==> ^r'");
    (asl,"MK_SPEC((\^sr. ^r'' /\ ^b''), ^c2, ^r)");
    (asl,"^r' /\ ~^b' ==> ^q'")],
   \[th1;th2;th3]. 
     POST_WEAK_RULE(PRE_STRENGTH_RULE(th1, WHILE_RULE th2), th3))
 ) ? failwith `WHILE_TAC`;;

let VC_TAC =
 REPEAT(ASSIGN_TAC 
         ORELSE SEQ_TAC 
         ORELSE IF1_TAC 
         ORELSE IF2_TAC 
         ORELSE WHILE_TAC);;

% Example:

pretty_on();;

let goal = g;;

let th1 =
 prove
  ("(X = R + (Y * Q)) /\ (Y<=R) ==> (X = (R - Y) + (Y * (Q + 1)))",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[LEFT_ADD_DISTRIB;MULT_CLAUSES]
    THEN ONCE_REWRITE_TAC[SPEC "Y*Q" ADD_SYM]
    THEN ONCE_REWRITE_TAC[ADD_ASSOC]
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]);;

goal "MK_SPEC
       ({T},
        (R:=X;
         Q:=0;
         assert{(R = X) /\ (Q = 0)};
         while Y<=R
          do (invariant{X = (R + (Y * Q))};
              R := R-Y; Q := Q+1)),
        {(R < Y) /\ (X = (R + (Y * Q)))})";;

expandf(SEQ_TAC);;

expandf(SEQ_TAC);;
expandf(ASSIGN_TAC);;
expandf(REWRITE_TAC[]);;

expandf(WHILE_TAC);;

expandf(STRIP_TAC);;
expandf(ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES]);;

expandf(SEQ_TAC);;
expandf(ASSIGN_TAC);;
expandf(ACCEPT_TAC th1);;

expandf(REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]);;
expandf(DISCH_TAC);;
expandf(ASM_REWRITE_TAC[]);;

goal "MK_SPEC
       ({T},
        (R:=X;
         Q:=0;
         assert{(R = X) /\ (Q = 0)};
         while Y<=R
          do (invariant{X = (R + (Y * Q))};
              R := R-Y; Q := Q+1)),
        {(R < Y) /\ (X = (R + (Y * Q)))})";;

expandf(VC_TAC);;

expandf(REWRITE_TAC[]);;

expandf(STRIP_TAC);;
expandf(ASM_REWRITE_TAC[ADD_CLAUSES;MULT_CLAUSES]);;

expandf(ACCEPT_TAC th1);;

expandf(REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]);;
expandf(DISCH_TAC);;
expandf(ASM_REWRITE_TAC[]);;
 
prove
 ("MK_SPEC({T},
           (R:=X;
            Q:=0;
            assert{(R = X) /\ (Q = 0)};
            while Y<=R
             do (invariant{X = (R + (Y * Q))};
                 R:=R-Y; Q:=Q+1)),
           {(R < Y) /\ (X = (R + (Y * Q)))})",
   VC_TAC
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
