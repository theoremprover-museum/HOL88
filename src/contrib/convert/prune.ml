%< 
---------------------------------

  new-unwind library
  
  prune.ml
  
  based on HOL88 unwind library   

  Rules for unwinding

  this file uses mk_thm !! 
---------------------------------
>%

%< useful conversions for getting things into a pruneable state >%

%< next bits subsidiary functions for EXISTS_AND >%

%<
   EXISTS_AND_LEFT: term     -> thm
                  "?x.t1/\t2"  

   | - ?x. t1 /\ t2 = t1 /\ (?x. t2)"  (If x not free in t1)
>%

let EXISTS_AND_LEFT t =
 (let x,t1,t2 = ((I # dest_conj) o dest_exists) t
  in
  let t1_frees, t2_frees = frees t1, frees t2
  in
  if (mem x t1_frees)
  then fail
  else
  (let th1 = ASSUME "^t1 /\ ^t2"
   and t' = "^t1 /\ (?^x.^t2)"
   in
   let th2 = ASSUME t'
   in
   let th3 = DISCH
              t
              (CHOOSE 
               (x, ASSUME t)
               (CONJ(CONJUNCT1 th1)(EXISTS("?^x.^t2",x)(CONJUNCT2 th1))))
     % th3 = |-"?x. t1  /\  t2  ==>  t1  /\  (?x. t2)" %
   and th4 = DISCH
              t'
              (CHOOSE
               (x, CONJUNCT2 th2)
               (EXISTS(t,x)(CONJ(CONJUNCT1 th2)(ASSUME t2))))
     % th4 = |-"t1  /\  (?x. t2)  ==>  ?x. t1  /\  t2" %
   in 
   IMP_ANTISYM_RULE th3 th4)
 ) ? failwith `EXISTS_AND_LEFT`;;
 
%<
   EXISTS_AND_RIGHT: term    -> thm
                   ?x.t1/\t2 

     |- ?x. t1 /\ t2 = (?x. t1) /\ t2"  (If x not free in t2)
>%

let EXISTS_AND_RIGHT t =
 (let x,t1,t2 = ((I # dest_conj) o dest_exists) t
  in
  let t1_frees, t2_frees = frees t1, frees t2
  and th1              = ASSUME "^t1 /\ ^t2"
  in
  if (mem x t2_frees)
  then fail
  else
  (let t' = "(?^x.^t1) /\ ^t2"
   in
   let th2 = ASSUME t'
   in
   let th3 = DISCH
              t
              (CHOOSE 
               (x, ASSUME t)
               (CONJ(EXISTS("?^x.^t1",x)(CONJUNCT1 th1))(CONJUNCT2 th1)))
     % th3 = |-"?x. t1  /\  t2  ==>  (?x.t1)  /\  t2" %
   and th4 = DISCH
              t'
              (CHOOSE
               (x, CONJUNCT1 th2)
               (EXISTS(t,x)(CONJ(ASSUME t1)(CONJUNCT2 th2))))
     % th4 = |-"(?x.t1)  /\  t2  ==>  ?x. t1  /\  t2" %
   in
   IMP_ANTISYM_RULE th3 th4)
 ) ? failwith `EXISTS_AND_RIGHT`;;

%<
   EXISTS_AND_BOTH: term     -> thm
                   ?x.t1/\t2

   |- ?x. t1 /\ t2 = t1 /\ t2"        (If x not free in t1 or t2)
>%

let EXISTS_AND_BOTH t =
 (let x,t1,t2 = ((I # dest_conj) o dest_exists) t
  in
  let t1_frees, t2_frees = frees t1, frees t2
  and th1              = ASSUME "^t1 /\ ^t2"
  in
  if (mem x t2_frees) or (mem x t1_frees)
  then fail
  else
  (let t' = "^t1 /\ ^t2"
   in
   let th3 = DISCH
              t
              (CHOOSE
               (x, ASSUME t)
               (ASSUME t'))
     % th3 = |-"?x. t1  /\  t2  ==>  t1  /\  t2" %
   and th4 = DISCH
              t'
              (EXISTS(t, x)(ASSUME t'))
     % th4 = |-"t1  /\ t2  ==>  ?x. t1 /\  t2" %
   in IMP_ANTISYM_RULE th3 th4)
 ) ? failwith `EXISTS_AND_BOTH`;;

%<
   EXISTS_AND: term -> thm
              ?x.t1/\t2

    |- ?x. t1 /\ t2 = t1 /\ t2"        (If x not free in t1 or t2)

    |- ?x. t1 /\ t2 = t1 /\ (?x. t2)"  (If x not free in t1)

    |- ?x. t1 /\ t2 = (?x. t1) /\ t2"  (If x not free in t2)
>%

let EXISTS_AND t =
 EXISTS_AND_BOTH  t ?  
 EXISTS_AND_LEFT  t ?  
 EXISTS_AND_RIGHT t ?
 failwith`EXISTS_AND`;;

%<
 EXISTS_EQN

   "?l. l x1 ... xn = t" --> |- (?l.l x1 ... xn = t) = T

  (if l not free in t)
>%

let EXISTS_EQN t =
 (let l,t1,t2 = ((I # dest_eq) o dest_exists) t
  in
  let l',xs = strip_comb t1
  in
  let t3 = list_mk_abs(xs,t2)
  in
  let th1 = RIGHT_CONV_RULE LIST_BETA_CONV (REFL(list_mk_comb(t3,xs)))
  in
  EQT_INTRO(EXISTS("?^l.^(list_mk_comb(l,xs))=^(rhs(concl th1))",t3)th1)
 ) ? failwith `EXISTS_EQN`;;

%<
 EXISTS_EQNF

   "?l. !x1 ... xn. l x1 ... xn = t" --> 
     |- (?l. !x1 ... xn. l x1 ... xn = t) = T

  (if l not free in t)
>%

let EXISTS_EQNF t =
 (let l,vars,t1,t2 =
  ((I # (I # dest_eq)) o (I # strip_forall) o dest_exists) t
  in
  let l',xs = strip_comb t1
  in
  let t3 = list_mk_abs(xs,t2)
  in
  let th1 =
   GENL vars (RIGHT_CONV_RULE LIST_BETA_CONV (REFL(list_mk_comb(t3,xs))))
  in
  EQT_INTRO
   (EXISTS
    ((mk_exists
      (l,
       list_mk_forall
        (xs,
         (mk_eq(list_mk_comb(l,xs), rhs(snd(strip_forall(concl th1)))))))),
     t3)
   th1)
 ) ? failwith `EXISTS_EQNF`;;


% |- (?x.t) = t    if x not free in t 

let EXISTS_DEL1 tm =
 (let x,t = dest_exists tm
  in
  let th1 = DISCH tm (CHOOSE (x, ASSUME tm) (ASSUME t))
  and th2 = DISCH t (EXISTS(tm,x)(ASSUME t))
  in
  IMP_ANTISYM_RULE th1 th2
 ) ? failwith `EXISTS_DEL`;;
%

% |- (?x1 ... xn.t) = t    if x1,...,xn not free in t 

letrec EXISTS_DEL tm =
 (if is_exists tm
  then
  (let th1 = EXISTS_DEL1 tm
   in
   let th2 = EXISTS_DEL(rhs(concl th1))
   in
   th1 TRANS th2)
  else REFL tm
 ) ? failwith`EXISTS_DEL`;;
%

let EXISTS_DEL1 tm =   % delete one ? %
 (let l,t = dest_exists tm
  in
  let l'  = frees t   % bug fix [DES] 24mar88 -- frees t NOT frees tm !! 
                        so need an extra let %
  in
  if not(mem l l') then mk_thm([], mk_eq(tm,t)) else fail
 ) ? failwith`EXISTS_DEL`;;

let EXISTS_DEL tm =
 (let l,t = strip_exists tm
  in
  let l'  = frees t   % bug fix [DES] 24mar88 -- frees t NOT frees tm !! 
                        so need an extra let %
  in
  if intersect l l' = [] then mk_thm([], mk_eq(tm,t)) else fail
 ) ? failwith`EXISTS_DEL`;;


%< [DES] 27apr89

   PRUNE_ONCE_CONV
   
   (? x . eqn1 /\ .... /\ x=t /\ ... /\ eqnn)
   ----------------------------------------------
   |- (? x . eqn1 /\ ... /\ x=t /\ ... /\ eqnn) =
      (? x . eqn1[t/x] /\ ... /\ eqnn[t/x])
>%

let AND_CLAUSE1 = GEN "t:bool" (CONJUNCT1 (SPEC "t:bool" AND_CLAUSES));;

let PRUNE_ONCE_CONV t =
   (let bv,bdy = dest_exists t in
    let conjs = conjuncts bdy in
    let bvas = filter (\t.lhs t=bv?false) conjs in
    if bvas=[] % case where no assignment to bv %
       then EXISTS_DEL1 t % can just attempt to delete it %
       else
    let bveq = rhs(hd bvas) in  % the value to equate it to %
    let nbdy = subst[bveq,bv]bdy in 
    let th1 = DISCH nbdy(EXISTS (t,bveq) (ASSUME nbdy)) in
    let lem = hd(filter(\th.lhs(concl th)=bv?false)(CONJUNCTS(ASSUME bdy))) in
    let lem1 = SUBST [lem,bv] bdy (ASSUME bdy) in
    let th2 = DISCH t(CHOOSE (bv,ASSUME t) (lem1)) in
    let th3 = IMP_ANTISYM_RULE th2 th1 in
    let nvar = genvar ":bool" in
    let th4 = SUBST[EQT_INTRO(REFL bveq),nvar](mk_eq(nbdy,subst[nvar,mk_eq(bveq,bveq)]nbdy))
            (REFL(nbdy)) in
    let nconjs = filter(\t.not t="T")(conjuncts(rhs(concl th4))) in
    let th5 =  CONJUNCTS_CONV(rhs(concl th4),list_mk_conj ("T".nconjs)) in
    if nconjs=[] then th3 TRANS th4 TRANS th5
    else
    let th6 = SUBST [SPEC(list_mk_conj nconjs)AND_CLAUSE1,nvar](mk_eq(lhs(concl th5),nvar))th5 in
    th3 TRANS th4 TRANS th6) ? failwith `PRUNE_ONCE_CONV`;;

letrec PRUNE_CONV t =
   letrec f t = % local function -- does ? x1 ... xn . b --> ? x2 .. xn x1 . b 
                  then PRUNES ? x1 . b %
             ((SWAP_EXISTS_CONV THENC (SUB_CONV(SUB_CONV f))) 
               ORELSEC PRUNE_ONCE_CONV)t
   in
   if (is_exists t)
      then ((SUB_CONV(SUB_CONV PRUNE_CONV))THENC(f ORELSEC ALL_CONV))t
      else (ALL_CONV t);;

let PRUNE_RULE th = RIGHT_CONV_RULE PRUNE_CONV th ? failwith `PRUNE_RULE`;;






