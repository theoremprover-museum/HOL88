%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        hol-drule.ml                                          %
%                                                                             %
%     DESCRIPTION:      Derived theorems and rules.  (Proper derivation are   %
%                       given as comments.)                                   %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-rule.ml                                           %
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

% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer     %
% This loads genfns.ml and hol-syn.ml too.                              %
% Also depends on hol-rule.ml                                           %
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`; loadf `ml/hol-rule`);;

% Add an assumption

      A |- t'
   -----------
    A,t |- t'

let ADD_ASSUM t th = MP (DISCH t th) (ASSUME t);;
%

let ADD_ASSUM t th =
 fst(mk_thm(union [t] (hyp th), concl th), RecordStep(AddAssumStep(t,th)));;

% Symmetry of =

       A |- t1 = t2
     ----------------
       A |- t2 = t1

let SYM th =
 (let t1,t2 = dest_eq(concl th)
  in
  let v = genvar(type_of t1)
  in
  SUBST [th,v] "^v=^t1" (REFL "^t1")
 ) ? failwith`SYM`;;
%

let SYM th =
   (let hyps,conc = dest_thm th in
    let x,y = dest_eq conc in
    fst(mk_thm (hyps, mk_eq (y,x)), RecordStep(SymStep th)))
   ? failwith `SYM`;;

% Transitivity of =

   A1 |- t1 = t2  ,  A2 |- t2 = t3
  ---------------------------------
        A1 u A2 |- t1=t3

let TRANS th1 th2 =
 (let t1 ,t2 = dest_eq(concl th1)
  and t2',t3 = dest_eq(concl th2)
  in
  let v = genvar(type_of t1)
  in
  SUBST [th2,v] "^t1=^v" th1
 ) ? failwith`TRANS`;;
%

ml_curried_infix `TRANS`;;

let th1 TRANS th2 =
   (let x,y  = dest_eq (concl th1)
    and y',z = dest_eq (concl th2)
    and hyps = union (hyp th1) (hyp th2)
    in
    if aconv y y'
    then
     fst(mk_thm (hyps, mk_eq(x,z)), RecordStep(TransStep(th1,th2)))
    else fail)
   ? failwith `TRANS`;;

% Transitivity of ==>

   A1 |- t1 ==> t2            A2 |- t2 ==> t3
 ---------------------------------------------
           A1 u A2 |- t1 ==> t3

let IMP_TRANS th1 th2 =
 (let t1,t2 = dest_imp(concl th1)
  in
  DISCH t1 (MP th2 (MP th1 (ASSUME t1)))
 ) ? failwith `IMP_TRANS`;;
%

% Modified: TFM 88.10.08 to use "union A1 A1" instead of A1 @ A2        %

let IMP_TRANS th1 th2 =
 (let A1, (t1,t2)  = ((I # dest_imp) o dest_thm) th1
  and A2, (t2',t3) = ((I # dest_imp) o dest_thm) th2
  in
  if aconv t2 t2'
   then
    fst(mk_thm(union A1 A2, mk_imp(t1,t3)), RecordStep(ImpTransStep(th1,th2)))
   else fail
 ) ? failwith `IMP_TRANS`;;

%<
 Application of a term to a theorem

    A |- t1 = t2
 ------------------
  A |- t t1 = t t2

let AP_TERM tm th =
 (let t1,t2 = dest_eq(concl th)
  in
  let th1 = REFL "^tm ^t1"
  %< th1 = |- t t1 = t t1 >%
  and v   = genvar(type_of t1)
  in
  SUBST [th,v] "^tm ^t1 = ^tm ^v" th1
 ) ? failwith `AP_TERM`;;
>%

let AP_TERM tm th =
 (let t1,t2 = dest_eq(concl th)
  in
  fst(mk_thm(hyp th, mk_eq(mk_comb(tm,t1), mk_comb(tm,t2))),
      RecordStep(ApTermStep(tm,th)))
 ) ? failwith `AP_TERM`;;

%< Application of a theorem to a term

    A |- t1 = t2
   ----------------
   A |- t1 t = t2 t

let AP_THM th tm =
 (let t1,t2 = dest_eq(concl th)
  in
  let th1 = REFL "^t1 ^tm"
  %< th1 = |- t1 t = t1 t >%
  and v   = genvar(type_of t1)
  in
  SUBST [th,v] "^t1 ^tm = ^v ^tm" th1
 ) ? failwith `AP_THM`;;
>%

let AP_THM th tm =
 (let t1,t2 = dest_eq(concl th)
  in
  fst(mk_thm(hyp th, mk_eq(mk_comb(t1,tm), mk_comb(t2,tm))),
      RecordStep(ApThmStep(th,tm)))
 ) ? failwith `AP_THM`;;

% Modus Ponens for =

   A1 |- t1 = t2  ,  A2 |- t1
  ----------------------------
        A1 u A2 |- t2

let EQ_MP th1 th2 =
 (let t1,t2 = dest_eq(concl th1)
  in
  let v = genvar(type_of t1)
  in
  SUBST [th1,v] v th2
 ) ? failwith `EQ_MP`;;
%

let EQ_MP th1 th2 =
 (let t1,t2 = dest_eq(concl th1)
  and t1'   = concl th2
  in
  if aconv t1 t1'
  then
   fst(mk_thm(union(hyp th1)(hyp th2), t2), RecordStep(EqMpStep(th1,th2)))
  else fail
 ) ? failwith `EQ_MP`;;


%
              A |- t1 = t2
    ------------------------------------
     A |- t1 ==> t2      A |- t2 ==> t1

let EQ_IMP_RULE th =
 (let t1,t2 = dest_eq(concl th)
  in
  (DISCH t1 (EQ_MP th (ASSUME t1)), DISCH t2 (EQ_MP(SYM th)(ASSUME t2)))
 ) ? failwith `EQ_IMP_RULE`;;
%

let EQ_IMP_RULE th =
 (let t1,t2 = dest_eq(concl th)
  and A     = hyp th
  in
  fst((mk_thm(A,mk_imp(t1,t2)), mk_thm(A,mk_imp(t2,t1))),
      RecordStep(EqImpRuleStep th))
 ) ? failwith `EQ_IMP_RULE`;;

% |- T (type of "x" set to ":bool" for HOL88) %

let TRUTH = EQ_MP (SYM T_DEF) (REFL "\x:bool.x");;

% =T elimination

   A |- t = T
  ------------
    A |- t
%

let EQT_ELIM th = EQ_MP (SYM th) TRUTH ? failwith `EQT_ELIM`;;

%< Specialization

    A |- !(\x.u)
  --------------------   (where t is free for x in u)
    A |- u[t/x]

let SPEC t th =
 (let F,body = dest_comb(concl th)
  in
  if not(fst(dest_const F)=`!`)
  then fail
  else
   let x,u = dest_abs body
   in
   let v1 = genvar(type_of F)
   and v2 = genvar(type_of body)
   in
   let th1 = SUBST [INST_TYPE[type_of x,":*"]FORALL_DEF,v1] "^v1 ^body" th
   %< th1 = |- (\P. P = (\x. T))(\x. t1 x) >%
   in
   let th2 = BETA_CONV(concl th1)
   %< th2 = |- (\P. P = (\x. T))(\x. t1 x) = ((\x. t1 x) = (\x. T)) >%
   in
   let th3 = EQ_MP th2 th1
   %< th3 = |- (\x. t1 x) = (\x. T) >%
   in
   let th4 = SUBST [th3, v2] "^body ^t = ^v2 ^t" (REFL "^body ^t")
   %< th4 = |- (\x. t1 x)t = (\x. T)t >%
   in
   let ls,rs = dest_eq(concl th4)
   in
   let th5 = TRANS(TRANS(SYM(BETA_CONV ls))th4)(BETA_CONV rs)
   %< th5 = |- t1 t = T >%
   in
   EQT_ELIM th5
 ) ? failwith `SPEC`;;
>%

let SPEC t th =
   (let x,w = dest_forall(concl th)
    in fst(mk_thm( hyp th , subst[t,x]w ), RecordStep(SpecStep(t,th))))
   ? failwith `SPEC`  ;;



%
      |- !x1 ... xn. t[xi]
    --------------------------  SPECL [t1; ...; tn]
          |-  t[ti]
%

let SPECL ts = \th. rev_itlist SPEC ts th ? failwith `SPECL`;;


% Introduce =T

     A |- t
   ------------
     A |- t=T

let EQT_INTRO th =
 let t = concl th
 in
 MP
  (MP(SPEC "T" (SPEC t IMP_ANTISYM_AX))(DISCH t TRUTH))
  (DISCH "T" th);;
%

let EQT_INTRO =
    let T = "T:bool" in
    \th. fst(mk_thm(hyp th, mk_eq(concl th,T)), RecordStep(EqtIntroStep th))
 ? failwith `EQT_INTRO`;;

%< Generalization

         A |- t
   -------------------   (where x not free in A)
       A |- !(\x.t)

let GEN x th =
 (let th1 = ABS x (EQT_INTRO th)
  %< th1 = |- (\x. t1 x) = (\x. T) >%
  in
  let abs = "\^x.^(concl th)"
  and v1 = genvar ":(^(type_of x)->bool)->bool"
  and v2 = genvar ":bool"
  in
  let th2 = SUBST
             [INST_TYPE[type_of x,":*"]FORALL_DEF,v1]
             "$! ^abs = ^v1 ^abs"
             (REFL "$! ^abs")
  %< th2 = |- (!x. t1 x) = (\P. P = (\x. T))(\x. t1 x) >%
  in
  let th3 = TRANS th2 (BETA_CONV(snd(dest_eq(concl th2))))
  %< th3 = |- (!x. t1 x) = ((\x. t1 x) = (\x. T)) >%
  in
  SUBST [SYM th3, v2] v2 th1
 ) ? failwith `GEN`;;
>%

let GEN x th =
   (if exists (free_in x) (hyp th) 
    then failwith `variable not free in assumption`
    else
     fst(mk_thm( hyp th , mk_forall(x, concl th)), RecordStep(GenStep(x,th)))
   ) ?\s failwith (`GEN: `^s);;

let GENL = itlist GEN;;

%< Simple version of alpha-conversion (needed for deriving ETA_CONV)

       "\x1. t x1"   "\x2. t x2"   --->   |- "(\x1.t x1)=(\x2.t x2)"

let SIMPLE_ALPHA(t1,t2) =
 let x1,body1 = dest_abs t1
 and x2,body2 = dest_abs t2
 in
 let th1 = BETA_CONV "^t1 (x:^(type_of x1))"
 %< th1 = |- (\x1. t x1)x = t x >%
 and th2 = BETA_CONV "^t2 (x:^(type_of x2))"
 %< th2 = |- (\x2. t x2)x = t x >%
 and th3 = SPEC t1 (INST_TYPE [type_of x1,":*"; type_of body1, ":**"] ETA_AX)
 %< th3 = |- (\x. (\x1. t x1)x) = (\x1. t x1) >%
 and th4 = SPEC t2 (INST_TYPE [type_of x2,":*"; type_of body2, ":**"] ETA_AX)
 %< th4 = |- (\x. (\x2. t x2)x) = (\x2. t x2) >%
 in
 (SYM th3) TRANS (ABS "x:^(type_of x1)" (th1 TRANS (SYM th2))) TRANS th4;;
>%

%< Eta-conversion

        "(\x.t x)"   --->    |- (\x.t x) = t  (if x not free in t)

let ETA_CONV tm =
 (let x,body = dest_abs tm
  in
  let t,() = dest_comb body
  in
  let th = SPEC t (INST_TYPE [type_of x,":*"; type_of body, ":**"] ETA_AX)
  %< th = |- (\x. t x) = t >%
  in
  SIMPLE_ALPHA(tm,lhs(concl th)) TRANS th
 ) ? failwith`ETA_CONV`;;
>%

let ETA_CONV tm =
 (let x,body = dest_abs tm
  in
  let t,x' = dest_comb body
  in
  if (x=x') & not(mem x (frees t))
  then fst(mk_thm([],mk_eq(tm,t)), RecordStep(EtaConvStep tm))
  else fail
 ) ? failwith `ETA_CONV`;;

%< Extensionality

     A |- !x. t1 x = t2 x
    ----------------------     (x not free in t1 or t2)
        A |- t1 = t2

        % Failure if x not free in A avoided    [JG 92.04.16]   %

let EXT th =
 (let x,() = dest_forall(concl th)
  in
  let x' = genvar (type_of x)
  in
  let th1 = SPEC x' th
  %< th1 = |- t1 x' = t2 x' >%
  in
  let t1x',t2x' = dest_eq(concl th1)
  in
  let th2 = ABS x' th1
  %< th2 = |- (\x'. t1 x') = (\x'. t2 x') >%
  in
  TRANS (TRANS(SYM(ETA_CONV "\^x'.^t1x'"))th2) (ETA_CONV "\^x'.^t2x'")
 ) ? failwith `EXT`;;
>%

let EXT th =
 (let x,eqn = dest_forall(concl th)
  in
  let (t1,x1),(t2,x2) = ((dest_comb # dest_comb) o dest_eq) eqn
  in
  if not(mem x (union(frees t1)(frees t2)))
     & (x=x1)
     & (x=x2)
  then fst(mk_thm(hyp th, mk_eq(t1,t2)), RecordStep(ExtStep th))
  else failwith `variable is free in function`
 ) ?\s failwith (`EXT: `^s);;

% SELECT introduction

    A |- P t
  -----------------
   A |- P($@ P)
%

let SELECT_INTRO th =
 (let P,t = dest_comb(concl th)
  in
  MP (SPEC t (SPEC P (INST_TYPE[type_of t,":*"]SELECT_AX))) th
 ) ? failwith `SELECT_INTRO`;;

% SELECT elimination (cases)

   A1 |- P($@ P)    ,    A2, "P v" |- t
  ------------------------------------------ (v occurs nowhere)
              A1 u A2 |- t
%

let SELECT_ELIM th1 (v,th2) =
 (let P, SP = dest_comb(concl th1)
  in
  let th3 = DISCH "^P ^v" th2
  %< th3 = |- P v ==> t >%
  in
  MP (SPEC SP (GEN v th3)) th1
 ) ? failwith `SELECT_ELIM`;;

%< Existential introduction

    A |- t[t']
  --------------
   A |- ?x.t[x]

  The parameters are: EXISTS("?x.t[x]", "t'") (|- t[t'])

let EXISTS (fm,tm) th =
 (let x,t = dest_exists fm
  in
  let th1 = BETA_CONV "(\^x.^t)^tm"
  %< th1 = |- (\x. t x)t' = t t' >%
  in
  let th2 = EQ_MP (SYM th1) th
  %< th2 = |- (\x. t x)t' >%
  in
  let th3 = SELECT_INTRO th2
  %< th3 = |- (\x. t x)(@x. t x) >%
  in
  let th4 = AP_THM(INST_TYPE[(type_of x),":*"]EXISTS_DEF)"\^x.^t"
  %< th4 = |- (?x. t x) = (\P. P($@ P))(\x. t x) >%
  in
  let th5 = TRANS th4 (BETA_CONV(snd(dest_eq(concl th4))))
  %< th5 = |- (?x. t x) = (\x. t x)(@x. t x) >%
  in
  EQ_MP (SYM th5) th3
 ) ? failwith `EXISTS`;;
>%

let EXISTS (w,t) th =
   (let x,body = dest_exists w in
    if aconv (subst [t,x] body) (concl th)
     then fst(mk_thm(hyp th, w), RecordStep(ExistsStep((w,t),th)))
    else fail)
   ? failwith `EXISTS`;;

%< Existential elimination

   A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
   ------------------------------------     (variable v occurs nowhere)
            A1 u A2 |- t'

let CHOOSE (v,th1) th2 =
 (let x,body = dest_exists(concl th1)
  and t'     = concl th2
  and v1     = genvar ":bool"
  in
  let th3 = AP_THM
             (INST_TYPE[type_of v,":*"]EXISTS_DEF)
             "\^x.^body"
  %< th3 = |- (?x. t x) = (\P. P($@ P))(\x. t x) >%
  in
  let th4 = EQ_MP th3 th1
  %< th4 = |- (\P. P($@ P))(\x. t x) >%
  in
  let th5 = EQ_MP (BETA_CONV(concl th4)) th4
  %< th5 = |- (\x. t x)(@x. t x) >%
  in
  let th6 = BETA_CONV "(\^x.^body)^v"
  %< th6 = |- (\x. t x)v = t v >%
  in
  let Pa = snd(dest_eq(concl th6))
  in
  let th7 = UNDISCH(SUBST [SYM th6,v1] "^v1==>^t'" (DISCH Pa th2))
  %< th7 = |- t' >%
  in
  SELECT_ELIM th5 (v,th7)
 ) ? failwith `CHOOSE`;;

WW 12 Jan 94
let CHOOSE (a,xth) bth =
   (let x,body = dest_exists (concl xth) in
    let bhyp = disch(subst [a,x]body, hyp bth) in
    if not(is_var a) or
       exists (free_in a)
              ((concl xth . hyp xth) @ (concl bth . bhyp))
    then fail
    else fst(mk_thm(union (hyp xth) bhyp , concl bth),
             RecordStep(ChooseStep((a,xth),bth)))
 ) ? failwith `CHOOSE`;;
>%
let CHOOSE (a,xth) bth =
   (let x,body = dest_exists (concl xth) in
    let s = subst [a,x]body and bhyp = hyp bth in
    if not(mem s bhyp) then failwith `theorems not in the correct form`
    else
      let bhyp' = disch(s, bhyp) in
      if not(is_var a) or
         exists (free_in a) ((concl xth) . (concl bth . bhyp'))
      then failwith `variable not free`
      else fst(mk_thm(union (hyp xth) bhyp' , concl bth),
               RecordStep(ChooseStep((a,xth),bth)))
 ) ?\s failwith (`CHOOSE: `^s);;


% SELECT introduction

    A |- ?x. t[x]
  -----------------
   A |- t[@x.t[x]]

%

%----------------------------------------------------------------------------%
% More efficient version added [JRH 93.06.29] -- old code:                   %
%                                                                            %
% let SELECT_RULE th =                                                       %
%  (let x,t = dest_exists(concl th)                                          %
%   in                                                                       %
%   let v = genvar(type_of x)                                                %
%   in                                                                       %
%   let P = mk_abs(x,t)                                                      %
%   in                                                                       %
%   let th1 = SPEC v (SPEC P (INST_TYPE[type_of x,":*"]SELECT_AX))           %
%   in                                                                       %
%   let th2,th3 = ((BETA_CONV # BETA_CONV) o dest_imp o concl) th1           %
%   in                                                                       %
%   let th4 = EQ_MP th3 (MP th1 ((EQ_MP(SYM th2)(ASSUME (rhs(concl th2)))))) %
%   in                                                                       %
%   CHOOSE(v, th)th4                                                         %
%  ) ? failwith `SELECT_RULE`;;                                              %
%----------------------------------------------------------------------------%

let SELECT_RULE =
  let ty = ":*" in
  let th1 = BETA_CONV "(\P:*->bool. P($@ P)) P" in
  let th2 = GEN "P:*->bool" ($TRANS (AP_THM EXISTS_DEF "P:*->bool") th1) in
  (\th. let rct = rand(concl th) in
       let ith = SPEC rct (INST_TYPE[type_of(bndvar rct),ty] th2) in
       let fth = EQ_MP ith th in
       EQ_MP (BETA_CONV(concl fth)) fth) ? failwith `SELECT_RULE`;;

%<

   A1 |- t1 ==> t2         A2 |- t2 ==> t1
  -----------------------------------------
            A1 u A2 |- t1 = t2

let IMP_ANTISYM_RULE th1 th2 =
 (let t1,t2 = dest_imp(concl th1)
  in
  MP (MP (SPEC t2 (SPEC t1 IMP_ANTISYM_AX)) th1) th2
 ) ? failwith `IMP_ANTISYM_RULE`;;
>%

% Modified: TFM 88.10.08 to use "union A1 A1" instead of A1 @ A2        %

let IMP_ANTISYM_RULE th1 th2 =
 (let A1,(t1 ,t2)   = ((I # dest_imp) o dest_thm) th1
  and A2,(t2',t1')  = ((I # dest_imp) o dest_thm) th2
  in
  if aconv t1 t1' & aconv t2 t2'
   then fst(mk_thm(union A1 A2, mk_eq(t1,t2)),
            RecordStep(ImpAntisymRuleStep(th1,th2)))
   else fail
 ) ? failwith`IMP_ANTISYM_RULE`;;

%
       A |-  (!x. t1 = t2)
   ---------------------------
    A |- (?x.t1)  =  (?x.t2)

let MK_EXISTS bodyth =
   (let x, sth = SPEC_VAR bodyth in
    let a,b = dest_eq (concl sth) in
    let abimp,baimp = EQ_IMP_RULE sth in
    let HALF (p,q) pqimp =
       (let xp = mk_exists(x,p)
        and xq = mk_exists(x,q)
        in
        DISCH xp
         (CHOOSE (x, ASSUME xp)
           (EXISTS (xq,x)
             (MP pqimp (ASSUME p)))))
    in
    IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
   ) ? failwith `MK_EXISTS`;;
%

let MK_EXISTS bodyth =
   (let x, body = dest_forall (concl bodyth) in
    let a,b = dest_eq body in
    fst(mk_thm (hyp bodyth, mk_eq (mk_exists(x,a), mk_exists(x,b))),
        RecordStep(MkExistsStep bodyth))
   ) ? failwith `MK_EXISTS`;;

%
               A |-  t1 = t2
   ------------------------------------------- (xi not free in A)
    A |- (?x1 ... xn. t1)  =  (?x1 ... xn. t2)
%

let LIST_MK_EXISTS l th = itlist (\x th. MK_EXISTS(GEN x th)) l th;;


% ! abstraction

          A |- t1 = t2
     -----------------------
      A |- (!x.t1) = (!x.t2)
%

% Optimized: [TFM 90.06.27]                                             %

let FORALL_EQ =
    let bool_ty = mk_type(`bool`,[]) in
    let pred_ty ty = mk_type(`fun`,[ty;bool_ty]) in
    \x. let all = AP_TERM (mk_const(`!`,pred_ty(pred_ty(type_of x)))) in
        \th. all (ABS x th) ? failwith `FORALL_EQ`;;

% ? abstraction

          A |- t1 = t2
     -----------------------
      A |- (?x.t1) = (?x.t2)

Optimized: [TFM 92.05.11]

let EXISTS_EQ x th =
 (let t1,t2 = dest_eq(concl th)
  in
  AP_TERM "$?:(^(type_of x)->bool)->bool" (ABS x th)
 ) ? failwith `EXISTS_EQ`;;
%

let EXISTS_EQ =
    let bool_ty = mk_type(`bool`,[]) in
    let pred_ty ty = mk_type(`fun`,[ty;bool_ty]) in
    \x. let ex = AP_TERM (mk_const(`?`,pred_ty(pred_ty(type_of x)))) in
        \th. ex (ABS x th) ? failwith `EXISTS_EQ`;;

% @ abstraction

          A |- t1 = t2
     -----------------------
      A |- (@x.t1) = (@x.t2)

      [Optimised by JG 92.04.24]
%

let SELECT_EQ =
    let bool_ty = mk_type(`bool`,[]) in
    (\x th.
                let ty = type_of x in
                        AP_TERM
                        (mk_const
                                (`@`, mk_type (`fun`, [mk_type (`fun`, [ty; bool_ty]); ty])))
                                (ABS x th)
    ) ? failwith `SELECT_EQ`;;

%
     A1 |- t1 == u1   ...   An |- tn = un       A |- t[ti]
    -------------------------------------------------------
               A1 u ... An u A |-  t[ui]

let GSUBS substfn ths th =
    let ls = map (lhs o concl) ths in
    let vars = map (genvar o type_of) ls in
    let w = substfn (combine(vars,ls)) (concl th)  in
    SUBST (combine(ths,vars)) w th;;
%

% --------------------------------------------------------------------- %
% GSUBS made local: [TFM 90.07.02]                                      %
% --------------------------------------------------------------------- %

let (SUBS,SUBS_OCCS) =

    let GSUBS substfn ths th =
        let instl = map (\th. let (x,y) = dest_eq (concl th) in (y,x)) ths
        and hyps = hyp_union (th . ths)
        in mk_thm (hyps, substfn instl (concl th)) in

   ((\ths th.   (fst((GSUBS subst ths th),
                     RecordStep(SubsStep(ths,th))) ? failwith `SUBS`)),
    (\nlths th. (let nll, ths = split nlths in
                fst((GSUBS (subst_occs nll) ths th),
                    RecordStep(SubsOccsStep(nlths,th)))
                ? failwith `SUBS_OCCS`)));;

%
       A |- ti == ui
    --------------------
     A |- t[ti] = t[ui]

let SUBST_CONV thvars template tm =
    SUBST thvars "^tm = ^template" (REFL tm) ? failwith `SUBST_CONV`;;
%

let SUBST_CONV thvars template tm =
 (let ths,vars = split thvars in
  let ls, rs = split (map (dest_eq o concl) ths) in
  if aconv (subst (combine(ls,vars)) template) tm
  then fst(mk_thm(hyp_union ths, mk_eq(tm,subst(combine(rs,vars))template)),
           RecordStep(SubstConvStep(thvars,template,tm)))
  else fail
 ) ? failwith `SUBST_CONV`;;

% Beta-conversion to the rhs of an equation

   A |- t1 = (\x.t2)t3
  --------------------
   A |- t1 = t2[t3/x]
%

let RIGHT_BETA th =
    TRANS th (BETA_CONV(snd(dest_eq(concl th)))) ? failwith `RIGHT_BETA`;;

%  "(\x1 ... xn.t)t1 ... tn" -->
    |- (\x1 ... xn.t)t1 ... tn = t[t1/x1] ... [tn/xn]
%

letrec LIST_BETA_CONV tm =
 (let rat,rnd = dest_comb tm
  in
  RIGHT_BETA(AP_THM(LIST_BETA_CONV rat)rnd)
 ) ? REFL tm;;

let RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(snd(dest_eq(concl th))));;

% |- !t1 t2. t1 ==> t2 ==> t1 /\ t2 %

let AND_INTRO_THM =
 let t,t1,t2 = "t:bool","t1:bool","t2:bool"
 in
 let t12 = "^t1 ==> ^t2 ==> ^t"
 in
 let th1 = GEN t (DISCH t12 (MP (MP (ASSUME t12) (ASSUME t1)) (ASSUME t2)))
 in
 let th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
 in
 GEN t1 (GEN t2 (DISCH t1 (DISCH t2 (EQ_MP (SYM th2) th1))));;

% Conjunction introduction rule

   A1 |- t1  ,  A2 |- t2
  -----------------------
    A1 u A2 |- t1 /\ t2

let CONJ th1 th2 =
 MP (MP (SPEC (concl th2) (SPEC (concl th1) AND_INTRO_THM)) th1) th2;;
%

let CONJ th1 th2 =
   fst(mk_thm(union(hyp th1) (hyp th2), mk_conj(concl th1, concl th2)),
       RecordStep(ConjStep(th1,th2)));;

% |- !t1 t2. t1 /\ t2 ==> t1 %

let AND1_THM =
  let t1,t2 = "t1:bool","t2:bool"
  in
  let th1 = ASSUME "^t1 /\ ^t2"
  in
  let th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
  in
  let th3 = SPEC t1 (EQ_MP th2 th1)
  in
  let th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t2 (ASSUME t1)))
  in
  GEN t1 (GEN t2 (DISCH "^t1 /\ ^t2" (MP th3 th4)));;

% Left conjunct extraction

   A |- t1 /\ t2
   -------------
      A |- t1

let CONJUNCT1 th =
 (let t1,t2 = dest_conj(concl th)
  in
  MP (SPEC t2 (SPEC t1 AND1_THM)) th
 ) ? failwith `CONJUNCT1`;;
%

let CONJUNCT1 th =
 fst(mk_thm(hyp th, fst(dest_conj(concl th))), RecordStep(Conjunct1Step th))
 ? failwith `CONJUNCT1`;;

% |- !t1 t2. t1 /\ t2 ==> t2 %

let AND2_THM =
  let t1,t2 = "t1:bool","t2:bool"
  in
  let th1 = ASSUME "^t1 /\ ^t2"
  in
  let th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
  in
  let th3 = SPEC t2 (EQ_MP th2 th1)
  in
  let th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t1 (ASSUME t2)))
  in
  GEN t1 (GEN t2 (DISCH "^t1 /\ ^t2" (MP th3 th4)));;

% Right conjunct extraction

   A |- t1 /\ t2
   -------------
      A |- t2

let CONJUNCT2 th =
 (let t1,t2 = dest_conj(concl th)
  in
  MP (SPEC t2 (SPEC t1 AND2_THM)) th
 ) ? failwith `CONJUNCT2`;;
%

let CONJUNCT2 th =
 fst(mk_thm(hyp th, snd(dest_conj(concl th))), RecordStep(Conjunct2Step th))
 ? failwith `CONJUNCT2`;;


% |- !t1 t2. (t1 /\ t2) = (t2 /\ t1) %

let CONJ_SYM =
 let t1,t2 = "t1:bool","t2:bool"
 in
 let th1 = ASSUME "^t1 /\ ^t2"
 and th2 = ASSUME "^t2 /\ ^t1"
 in
 GEN t1 (GEN t2 (IMP_ANTISYM_RULE
                 (DISCH "^t1 /\ ^t2" (CONJ(CONJUNCT2 th1)(CONJUNCT1 th1)))
                 (DISCH "^t2 /\ ^t1" (CONJ(CONJUNCT2 th2)(CONJUNCT1 th2)))));;

% |- !t1 t2 t3. t1 /\ (t2 /\ t3) = (t1 /\ t2) /\ t3 %

let CONJ_ASSOC =
 let t1,t2,t3 = "t1:bool","t2:bool","t3:bool"
 in
 let th1 = ASSUME "^t1 /\ (^t2 /\ ^t3)"
 and th2 = ASSUME "(^t1 /\ ^t2) /\ ^t3"
 in
 let th3 = DISCH
            "^t1 /\ (^t2 /\ ^t3)"
            (CONJ
             (CONJ(CONJUNCT1 th1)(CONJUNCT1(CONJUNCT2 th1)))
             (CONJUNCT2(CONJUNCT2 th1)))
 and th4 = DISCH
            "(^t1 /\ ^t2) /\ ^t3"
            (CONJ
             (CONJUNCT1(CONJUNCT1 th2))
             (CONJ(CONJUNCT2(CONJUNCT1 th2))(CONJUNCT2 th2)))
 in
 GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE th3 th4)));;

% |- t1 = t2  if t1 and t2 are equivalent using idempotence, symetry and
              associativity of /\. I have not (yet) coded a genuine
              derivation - it would be straightforward, but tedious.

  let CONJUNCTS_CONV(t1,t2) =
   if set_equal(conjuncts t1)(conjuncts t2)
   then mk_thm([],mk_eq(t1,t2))
   else failwith `CONJUNCTS_CONV`;;

  Genuine derivation added [RJB 15th August 1991]:
%

let CONJUNCTS_CONV (t1,t2) =
 letrec CONJUNCTS th =
  (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th)) ? [th]
 in
 letrec build_conj thl t =
  (let l,r = dest_conj t
   in  CONJ (build_conj thl l) (build_conj thl r)
  )
  ? find (\th. (concl th) = t) thl
 in
  (IMP_ANTISYM_RULE
    (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
    (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
  ) ? failwith `CONJUNCTS_CONV`;;

% |- (t1 /\ ... /\ tn) = (t1' /\ ... /\ tn') where {t1,...,tn}={t1',...,tn'}

  The genuine derived rule below only works if its argument
  lists are the same length.

  letrec CONJ_SET_CONV l1 l2 =
   (if l1 = l2
    then REFL(list_mk_conj l1)
    if hd l1 = hd l2
    then AP_TERM "$/\ ^(hd l1)" (CONJ_SET_CONV(tl l1)(tl l2))
    else
    (let th1 = SYM(FRONT_CONJ_CONV l2 (hd l1))
     in
     let l2' = conjuncts(lhs(concl th1))
     in
     let th2 = AP_TERM "$/\ ^(hd l1)" (CONJ_SET_CONV(tl l1)(tl l2'))
     in
     th2 TRANS th1)
   ) ? failwith`CONJ_SET_CONV`;;

  Unsafe version:

  let CONJ_SET_CONV l1 l2 =
   (if set_equal l1 l2
    then mk_thm([],mk_eq(list_mk_conj l1, list_mk_conj l2))
    else fail
   ) ? failwith `CONJ_SET_CONV`;;

  New implementation uses CONJUNCTS_CONV [RJB 15th August 1991]:
%

let CONJ_SET_CONV l1 l2 =
 CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
 ? failwith `CONJ_SET_CONV`;;

%
  |- (t1 /\ ... /\ t /\ ... /\ tn) = (t /\ t1 /\ ... /\ tn)

  Old implementation:

  letrec FRONT_CONJ_CONV tml t =
   (if t = hd tml
    then REFL(list_mk_conj tml)
    if null(tl(tl tml)) & t = hd(tl tml)
    then SPECL tml CONJ_SYM
    else
    (let th1 = AP_TERM "$/\ ^(hd tml)" (FRONT_CONJ_CONV (tl tml) t)
     in
     let t1,(t2,t3) = ((I # dest_conj) o dest_conj)(rhs(concl th1))
     in
     let th2 = AP_THM(AP_TERM "$/\"(SPECL[t1;t2]CONJ_SYM))t3
     in
     th1 TRANS (SPECL[t1;t2;t3]CONJ_ASSOC)
         TRANS th2
         TRANS (SYM(SPECL[t2;t1;t3]CONJ_ASSOC)))
   ) ? failwith `FRONT_CONJ_CONV`;;

  New implementation using CONJ_SET_CONV:
%

let FRONT_CONJ_CONV tml t =
 letrec remove x l =
    if ((hd l) = x)
    then tl l
    else (hd l).(remove x (tl l))
 in
 (CONJ_SET_CONV tml (t.(remove t tml)))
 ? failwith `FRONT_CONJ_CONV`;;

%
           A,t |- t1 = t2
    -----------------------------
      A |- (t /\ t1) = (t /\ t2)
%

let CONJ_DISCH t th =
 (let t1,t2 = dest_eq(concl th)
  and th1   = DISCH t th
  in
  let th2 = ASSUME "^t /\ ^t1"
  and th3 = ASSUME "^t /\ ^t2"
  in
  let th4 = DISCH
            "^t /\ ^t1"
            (CONJ
             (CONJUNCT1 th2)
             (EQ_MP(MP th1 (CONJUNCT1 th2))(CONJUNCT2 th2)))
  and th5 = DISCH
            "^t /\ ^t2"
            (CONJ
             (CONJUNCT1 th3)
             (EQ_MP(SYM(MP th1 (CONJUNCT1 th3)))(CONJUNCT2 th3)))
  in
  IMP_ANTISYM_RULE th4 th5) ? failwith `CONJ_DISCH`;;

%
                    A,t1,...,tn |- t = u
    --------------------------------------------------------
      A |- (t1 /\ ... /\ tn /\ t) = (t1 /\ ... /\ tn /\ u)
%

letrec CONJ_DISCHL l th =
 if null l
 then th
 else CONJ_DISCH (hd l) (CONJ_DISCHL (tl l) th);;

% |- !t1 t2. t1 ==> t1 \/ t2 %

let OR_INTRO_THM1 =
  let t,t1,t2 = "t:bool","t1:bool","t2:bool"
  in
  let th1 = ADD_ASSUM "^t2 ==> ^t" (MP (ASSUME "^t1 ==> ^t") (ASSUME t1))
  in
  let th2 = GEN t (DISCH "^t1 ==> ^t" (DISCH "^t2 ==> ^t" th1))
  in
  let th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
  in
  GEN t1 (GEN t2 (DISCH t1 (EQ_MP (SYM th3) th2)));;

% Left disjunction introduction

      A |- t1
  ---------------
   A |- t1 \/ t2

let DISJ1 th t2 =
 MP (SPEC t2 (SPEC (concl th) OR_INTRO_THM1)) th ? failwith `DISJ1`;;
%

let DISJ1 th w =
 fst(mk_thm(hyp th, mk_disj(concl th, w)), RecordStep(Disj1Step(th,w)))
 ? failwith `DISJ1`;;

% |- !t1 t2. t2 ==> t1 \/ t2 %

let OR_INTRO_THM2 =
  let t,t1,t2 = "t:bool","t1:bool","t2:bool"
  in
  let th1 = ADD_ASSUM "^t1 ==> ^t" (MP (ASSUME "^t2 ==> ^t") (ASSUME t2))
  in
  let th2 = GEN t (DISCH "^t1 ==> ^t" (DISCH "^t2 ==> ^t" th1))
  in
  let th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
  in
  GEN t1 (GEN t2 (DISCH t2 (EQ_MP (SYM th3) th2)));;

% Right disjunction introduction

      A |- t2
  ---------------
   A |- t1 \/ t2

let DISJ2 t1 th =
 MP (SPEC (concl th) (SPEC t1 OR_INTRO_THM2)) th ? failwith `DISJ2`;;
%

let DISJ2 w th =
 fst(mk_thm(hyp th, mk_disj(w, concl th)), RecordStep(Disj2Step(w,th)))
 ? failwith `DISJ2`;;

% |- !t t1 t2. (t1 \/ t2) ==> (t1 ==> t) ==> (t2 ==> t) ==> t %

let OR_ELIM_THM =
 let t,t1,t2 = "t:bool","t1:bool","t2:bool"
 in
 let th1 = ASSUME "^t1 \/ ^t2"
 and th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
 in
 let th3 = SPEC t (EQ_MP th2 th1)
 in
 let th4 = MP (MP th3 (ASSUME "^t1 ==> ^t")) (ASSUME "^t2  ==> ^t")
 in
 let th4 = DISCH "^t1 ==> ^t" (DISCH "^t2 ==> ^t" th4)
 in
 GEN t (GEN t1 (GEN t2 (DISCH "^t1 \/ ^t2" th4)));;

% Disjunction elimination

   A |- t1 \/ t2   ,   A1,t1 |- t   ,   A2,t2 |- t
   -----------------------------------------------
               A u A1 u A2 |- t

let DISJ_CASES th1 th2 th3 =
 (let t1,t2 = dest_disj(concl th1)
  and t     = concl th2
  in
  let th4 = SPEC t2 (SPEC t1 (SPEC t OR_ELIM_THM))
  in
  MP (MP (MP th4 th1) (DISCH t1 th2)) (DISCH t2 th3)
 ) ? failwith `DISJ_CASES`;;
%

let DISJ_CASES dth ath bth =
    if is_disj (concl dth)  &  aconv (concl ath) (concl bth) then
        let lw,rw = dest_disj (concl dth) in
        fst(mk_thm (union (hyp dth)
                 (union (disch(lw, hyp ath)) (disch(rw, hyp bth))),
               concl ath),
            RecordStep(DisjCasesStep(dth,ath,bth)))
    else failwith `DISJ_CASES`;;

% --------------------------------------------------------------------- %
% |- !t1 t2. (t1 <=> t2) ==> (t1=t2)             DELETED [TFM 91.01.20] %
%                                                                       %
% let IFF_EQ_THM1 =                                                     %
%  let t1,t2 = "t1:bool","t2:bool"                                      %
%  in                                                                   %
%  let th1 = ASSUME "$<=> ^t1 ^t2"                                      %
%  and th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM IFF_DEF t1)) t2)      %
%  and th3 = SPEC t2 (SPEC t1 IMP_ANTISYM_AX)                           %
%  in                                                                   %
%  let th4 = EQ_MP th2 th1                                              %
%  in                                                                   %
%  let th5 = MP (MP th3 (CONJUNCT1 th4)) (CONJUNCT2 th4)                %
%  in                                                                   %
%  GEN t1 (GEN t2 (DISCH "$<=> ^t1 ^t2" th5));;                         %
%                                                                       %
%                                                                       %
% |- !t1 t2. (t1=t2) ==> (t1<=>t2)               DELETED [TFM 91.01.20] %
%                                                                       %
% let IFF_EQ_THM2 =                                                     %
%  let t1,t2 = "t1:bool","t2:bool"                                      %
%  in                                                                   %
%  let th1 = DISCH t1 (EQ_MP (ASSUME "$= ^t1 ^t2") (ASSUME t1))         %
%  and th2 = DISCH t2 (EQ_MP (SYM(ASSUME "$= ^t1 ^t2")) (ASSUME t2))    %
%  and th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM IFF_DEF t1)) t2)      %
%  in                                                                   %
%  GEN t1 (GEN t2 (DISCH "$= ^t1 ^t2"                                   %
%         (EQ_MP (SYM th3) (CONJ th1 th2))));;                          %
%                                                                       %
% |- !t1 t2. (t1 <=> t2) = (t1=t2)               DELETED [TFM 91.01.20] %
%                                                                       %
% let IFF_EQ =                                                          %
%  let t1,t2 = "t1:bool","t2:bool"                                      %
%  in                                                                   %
%  let th1 = SPEC "$= ^t1 ^t2" (SPEC "$<=> ^t1 ^t2" IMP_ANTISYM_AX)     %
%  in                                                                   %
%  let th2 = MP th1 (SPEC t2 (SPEC t1 IFF_EQ_THM1))                     %
%  in                                                                   %
% GEN t1 (GEN t2 (MP th2 (SPEC t2 (SPEC t1 IFF_EQ_THM2))));;            %
%                                                                       %
% IFF to EQ                                      DELETED [TFM 91.01.20] %
%                                                                       %
%    A |- t1 <=> t2                                                     %
%   ----------------                                                    %
%     A |- t1 = t2                                                      %
%                                                                       %
% let IFF_EQ_RULE th =                                                  %
%  (let t1,t2 = dest_iff(concl th)                                      %
%   in                                                                  %
%   EQ_MP (SPEC t2 (SPEC t1 IFF_EQ)) th                                 %
%  ) ? failwith`IFF_EQ_RULE`;;                                          %
% --------------------------------------------------------------------- %

% |- !t. F ==> t %

let FALSITY =
 let t = "t:bool"
 in
 GEN t (DISCH "F" (SPEC t (EQ_MP F_DEF (ASSUME "F"))));;

% |- !t.(t ==> F) ==> ~t %

let IMP_F =
 let t = "t:bool"
 in
 let th1 = RIGHT_BETA(AP_THM NOT_DEF t)
 in
 GEN t (DISCH "^t ==> F" (EQ_MP (SYM th1) (ASSUME "^t ==> F")));;

% NOT introduction

     A |- t ==> F
     ------------
       A |- ~t

let NOT_INTRO th =
 (let t,() = dest_imp(concl th)
  in
  MP (SPEC t IMP_F) th
 ) ? failwith `NOT_INTRO`;;
%

let NOT_INTRO th =
 (let t,tf = dest_imp(concl th)
  in
  if tf=falsity
   then fst(mk_thm(hyp th,"~^t"), RecordStep(NotIntroStep th))
   else fail
 ) ? failwith `NOT_INTRO`;;

%
       A,t1 |- t2                A,t |- F
     --------------              --------
     A |- t1 ==> t2               A |- ~t
%

let NEG_DISCH t th =
 (if concl th = falsity then NOT_INTRO(DISCH t th) else DISCH t th)
 ? failwith`NEG_DISCH`;;

% |- !t. ~t ==>(t ==> F) %

let F_IMP =
 let t = "t:bool"
 in
 let th1 = RIGHT_BETA(AP_THM NOT_DEF t)
 in
 GEN t (DISCH "~ ^t" (EQ_MP th1 (ASSUME "~ t")));;

% ADDED by WW 24 Jan 1994. Implementing the old MP rule %
let NOT_MP =
    \thi th. (MP thi th) ?
     (let t = dest_neg (concl thi)  in
      MP(MP (SPEC t F_IMP) thi) th) ? failwith `NOT_MP`;;

% Undischarging

   A |- t1==> t2
   -------------
    A, t1 |- t2
%

let UNDISCH th =
 NOT_MP th (ASSUME(fst(dest_neg_imp(concl th)))) ? failwith `UNDISCH`;;


% Negation elimination

       A |- ~ t
     --------------
      A |- t ==> F

let NOT_ELIM th =
 (let (),t = dest_comb(concl th)
  in
  MP (SPEC t F_IMP) th
 ) ? failwith `NOT_ELIM`;;
%

let NOT_ELIM th =
 (let not_tm,t = dest_comb(concl th)
  in
  if fst(dest_const not_tm) = `~`
  then fst(mk_thm(hyp th, mk_imp(t,falsity)),RecordStep(NotElimStep th))
  else fail
 ) ? failwith `NOT_ELIM`;;

%
    A |- ~(t1 = t2)
   -----------------
    A |- ~(t2 = t1)

OLD_CODE: using special behavior of MP. CHANGED by WW 24 Jan 94
let NOT_EQ_SYM th =
 (let t = (mk_eq o (\(x,y).(y,x)) o dest_eq o dest_neg o concl) th
  in
  MP (SPEC t IMP_F) (DISCH t (MP th (SYM(ASSUME t)))))
  ? failwith `NOT_EQ_SYM`;;
%

let NOT_EQ_SYM th =
 (let t = (mk_eq o (\(x,y).(y,x)) o dest_eq o dest_neg o concl) th
  in
  MP (SPEC t IMP_F) (DISCH t (MP (NOT_ELIM th) (SYM(ASSUME t)))))
  ? failwith `NOT_EQ_SYM`;;



% --------------------------------------------------------------------- %
% AND_CLAUSES: proof rewritten to make clauses 1-5 local                %
%                                                                       %
% |- !t. (T /\ t) = t /\                                                %
%        (t /\ T) = t /\                                                %
%        (F /\ t) = F /\                                                %
%        (t /\ F) = F /\                                                %
%        (t /\ t) = t                                      TFM 90.04.18 %
% --------------------------------------------------------------------- %

let AND_CLAUSES =
 let t = "t:bool" in
 let cl1 =                                                  % (T /\ t) = t %
     let th1 = DISCH "T /\ ^t" (CONJUNCT2(ASSUME "T /\ ^t"))
     and th2 = DISCH t (CONJ TRUTH (ASSUME t)) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl2 =                                                  % (t /\ T) = t %
     let th1 = DISCH "^t /\ T" (CONJUNCT1(ASSUME "^t /\ T"))
     and th2 = DISCH t (CONJ (ASSUME t) TRUTH) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl3 =                                                  % (F /\ t) = F %
     let th1 = IMP_TRANS (SPEC t (SPEC "F" AND1_THM)) (SPEC "F" FALSITY)
     and th2 = SPEC "F /\ ^t" FALSITY in
     (IMP_ANTISYM_RULE th1 th2)
 and cl4 =                                                  % (t /\ F) = F %
     let th1 = IMP_TRANS (SPEC "F" (SPEC t AND2_THM)) (SPEC "F" FALSITY)
     and th2 = SPEC "^t /\ F" FALSITY in
     (IMP_ANTISYM_RULE th1 th2)
 and cl5 =                                                  % (t /\ t) = t %
     let th1 = DISCH "^t /\ ^t" (CONJUNCT1(ASSUME "^t /\ ^t"))
     and th2 = DISCH t (CONJ(ASSUME t)(ASSUME t)) in
     (IMP_ANTISYM_RULE th1 th2) in
 GEN t (end_itlist CONJ [cl1;cl2;cl3;cl4;cl5]);;


% --------------------------------------------------------------------- %
% OR_CLAUSES: proof rewritten to make clauses 1-5 local                 %
%                                                                       %
%  |- !t. (T \/ t) = T /\                                               %
%         (t \/ T) = T /\                                               %
%         (F \/ t) = t /\                                               %
%         (t \/ F) = t /\                                               %
%         (t \/ t) = t                                     TFM 90.04.20 %
% --------------------------------------------------------------------- %

let OR_CLAUSES =
 let t = "t:bool" in
 let cl1 =                                                  % (T \/ t) = T %
     let th1 = DISCH "T \/ ^t" TRUTH
     and th2 = DISCH "T" (DISJ1 TRUTH t) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl2 =                                                  % (t \/ T) = T %
     let th1 = DISCH "^t \/ T" TRUTH
     and th2 = DISCH "T" (DISJ2 t TRUTH) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl3 =                                                  % (F \/ t) = t %
     let th1 = DISCH
             "F \/ ^t"
             (DISJ_CASES
              (ASSUME "F \/ ^t")
              (UNDISCH (SPEC t FALSITY))
              (ASSUME t))
     and th2 = SPEC t (SPEC "F" OR_INTRO_THM2) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl4 =                                                  % (t \/ F) = t %
     let th1 = DISCH
                "^t \/ F"
                (DISJ_CASES
                 (ASSUME "^t \/ F")
                 (ASSUME t)
                 (UNDISCH (SPEC t FALSITY)))
     and th2 = SPEC "F" (SPEC t OR_INTRO_THM1) in
     (IMP_ANTISYM_RULE th1 th2)
 and cl5 =                                                  % (t \/ t) = t %
     let th1 = DISCH "^t \/ ^t"
                      (DISJ_CASES(ASSUME"^t\/^t")(ASSUME t)(ASSUME t))
     and th2 = DISCH t (DISJ1(ASSUME t)t) in
     (IMP_ANTISYM_RULE th1 th2) in
 GEN t (end_itlist CONJ [cl1;cl2;cl3;cl4;cl5]);;


% --------------------------------------------------------------------- %
% IMP_CLAUSES: proof rewritten to make clauses 1-5 local                %
%                                                                       %
% |- !t. (T ==> t) = t /\                                               %
%        (t ==> T) = T /\                                               %
%        (F ==> t) = T /\                                               %
%        (t ==> t) = T /\                                               %
%        (t ==> F) = ~t                                    TFM 90.04.20 %
% --------------------------------------------------------------------- %

let IMP_CLAUSES =
 let t = "t:bool" in
 let cl1 =                                              % (T ==> t) = t %
     let th1 = DISCH "T ==> ^t" (MP (ASSUME "T ==> ^t") TRUTH)
     and th2 = DISCH t (DISCH "T" (ADD_ASSUM "T" (ASSUME t)))
     and th3 = SPEC t (SPEC "T ==> ^t" IMP_ANTISYM_AX) in
     (MP (MP th3 th1) th2)
 and cl2 =                                              % (F ==> t) = T %
     (EQT_INTRO(SPEC t FALSITY))
 and cl3 =                                              % (t ==> T) = T %
     (EQT_INTRO(DISCH t (ADD_ASSUM t TRUTH)))
 and cl4 =                                              % (t ==> t) = T %
     (EQT_INTRO(DISCH t (ASSUME t)))
 and cl5 =                                             % (t ==> F) = ~t %
     let th1 = SPEC t IMP_F
     and th2 = SPEC t F_IMP in
     (IMP_ANTISYM_RULE th1 th2) in
 GEN t (end_itlist CONJ [cl1;cl3;cl2;cl4;cl5]);;


% Contradiction rule

   A |- F
   ------
   A |- t

let CONTR tm th =
 MP (SPEC tm FALSITY) th ? failwith `CONTR`;;
%

let CONTR w fth =
 if concl fth = falsity
 then fst(mk_thm(hyp fth, w), RecordStep(ContrStep(w,fth)))
 else failwith `CONTR`;;

% --------------------------------------------------------------------- %
% EQF_INTRO: inference rule for introducing equality with "F".          %
%                                                                       %
%                ~tm                                                    %
%            -----------    EQF_INTRO                                   %
%               tm = F                                                  %
%                                                                       %
% [TFM 90.05.08]                                                        %
% --------------------------------------------------------------------- %

let EQF_INTRO =
    let F = "F" and Fth = ASSUME "F" in
    \th. (let body = dest_neg(concl th) in
              IMP_ANTISYM_RULE (NOT_ELIM th) (DISCH F (CONTR body Fth)))
          ? failwith `EQF_INTRO: argument theorem not a negation`;;

% --------------------------------------------------------------------- %
% EQF_ELIM: inference rule for eliminating equality with "F".           %
%                                                                       %
%             |- tm = F                                                 %
%            -----------    EQF_ELIM                                    %
%              |- ~ tm                                                  %
%                                                                       %
% [TFM 90.08.23]                                                        %
% --------------------------------------------------------------------- %

let EQF_ELIM =
    let check = assert ((curry $= `F`) o fst o dest_const) in
    \th. (let body,_ = (I # check) (dest_eq(concl th)) in
          NOT_INTRO(DISCH body (EQ_MP th (ASSUME body))))
          ? failwith `EQF_ELIM: argument theorem not of the form |- tm = F`;;

% --------------------------------------------------------------------- %
% EXCLUDED_MIDDLE: |- !t. t \/ ~t                                       %
% --------------------------------------------------------------------- %

let EXCLUDED_MIDDLE =
 let t = "t:bool"
 in
 let th1 = RIGHT_BETA(AP_THM NOT_DEF t)
 in
 let th2 = DISJ1 (EQT_ELIM(ASSUME "^t = T")) "~^t"
 and th3 = DISJ2 t (EQ_MP(SYM th1)(DISCH t(EQ_MP(ASSUME "^t = F")(ASSUME t))))
 in
 GEN t (DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th3);;

% Classical contradiction rule

   A,"~t" |- F
   --------------
       A |- t

let CCONTR t th =
 (let th1 = RIGHT_BETA(AP_THM NOT_DEF t)
  and v   = genvar ":bool"
  in
  let th2 = EQT_ELIM(ASSUME "^t = T")
  in
  let th3 = SUBST [th1,v] "^v ==> F" (DISCH "~ ^t" th)
  in
  let th4 = SUBST [ASSUME "^t = F",v] "(^v ==> F)==>F" th3
  in
  let th5 = MP th4 (EQT_ELIM (el 3 (CONJUNCTS (SPEC "F" IMP_CLAUSES))))
  in
  let th6 = EQ_MP (SYM(ASSUME "^t = F")) th5
  in
  DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th6
 ) ? failwith `CCONTR`;;
 %

let CCONTR w fth =
 if concl fth = falsity
 then fst(mk_thm(disch(mk_neg w, hyp fth), w), RecordStep(CcontrStep(w,fth)))
 else failwith `CCONTR`;;

% Instantiate variables in a theorem                                    %
% var changed to v, for version 1.12                    [TFM 90.06.06]  %

let INST inst_list th =
  if null inst_list  then  th
  else
  (let asl,w = dest_thm th
   and vars = map (assert is_var o snd) inst_list in
     if  exists (\v. exists (free_in v) asl) vars then fail
     else
      fst(mk_thm(asl, subst inst_list w), RecordStep(InstStep(inst_list,th)))
  ) ? failwith `INST`;;


% New version that may be added later;
  code supplied by Elsa Gunter.

  letrec COUNT_UNDISCH n thm =
    if n = 0 then thm else COUNT_UNDISCH (n -1) (UNDISCH thm);;

  let INST inst_list th =
    let num_hyp = length (hyp th)
    and gen_list = map (GEN o snd) inst_list
    and spec_list = map (SPEC o fst) inst_list   in
      COUNT_UNDISCH num_hyp
         (itlist B (itlist B (DISCH_ALL th) gen_list) spec_list);;

let INST inst_list th =
  if null inst_list  then  th
  else
  let asl,w = dest_thm th in
   mk_thm((map (subst inst_list) asl), subst inst_list w);;
%


% --------------------------------------------------------------------- %
% Make a theorem that assumes falsity A legitimate way for the user to  %
% make a theorem of (almost) any form, for testing of derived inference %
% rules.  Most rules won't notice the extra assumption, strong though   %
% it is.                                                                %
%                                                                       %
% MJCG 17/1/89 for HOL88. mk_fthm not used; see comment in tacticals.ml %
%                                                                       %
% let mk_fthm (asl,w) = mk_thm(falsity . asl, w);;                      %
%                                                                       %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% IFF introduction                               DELETED [TFM 91.01.20] %
%                                                                       %
%       A |- (t1 ==> t2)  /\   (t2 ==> t1)                              %
%     --------------------------------------                            %
%            A |-  t1 <=> t2                                            %
%                                                                       %
%                                                                       %
% let CONJ_IFF th =                                                     %
%    (let lw, rw = dest_conj (concl th) in                              %
%     let la,lc = dest_imp lw                                           %
%     and ra,rc = dest_imp rw in                                        %
%     if aconv la rc  &  aconv lc ra                                    %
%     then mk_thm (hyp th, mk_iff(la,lc))                               %
%     else fail)                                                        %
%   ? failwith `CONJ_IFF`;;                                             %
%                                                                       %
% IFF elimination                                                       %
%                                                                       %
%               A |- t1 <=> t2                                          %
%      -----------------------------------                              %
%       A |- (t1 ==> t2)  /\  (t2 ==> t1)                               %
%                                                                       %
%                                                                       %
% let IFF_CONJ th =                                                     %
%    (let lw,rw = dest_iff (concl th) in                                %
%     mk_thm(hyp th, mk_conj(mk_imp(lw,rw), mk_imp(rw,lw))))            %
%   ? failwith `IFF_CONJ`;;                                             %
% --------------------------------------------------------------------- %

% |- !t. ~t ==> (t=F) %

let NOT_F =
 let t = "t:bool"
 in
 let th1 = MP (SPEC t F_IMP) (ASSUME "~ ^t")
 and th2 = SPEC t FALSITY
 and th3 = SPEC "F" (SPEC t IMP_ANTISYM_AX)
 in
 GEN t (DISCH "~ ^t" (MP (MP th3 th1) th2));;

% |- !t. ~(t /\ ~t) %

let NOT_AND =
 let th = ASSUME "t /\ ~t"
 in
 NOT_INTRO(DISCH "t /\ ~t" (NOT_MP(CONJUNCT2 th)(CONJUNCT1 th)));;


% --------------------------------------------------------------------- %
% EXPAND_TY_DEF : code deleted (TFM 90.04.10)                           %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% OR_IMP_THM = |- !t1 t2. (t1 = t2 \/ t1) = (t2 ==> t1)  [TFM 90.06.28] %
% --------------------------------------------------------------------- %

let OR_IMP_THM =
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let asm1 = ASSUME "^t1 = (^t2 \/ ^t1)" and
        asm2 = EQT_INTRO(ASSUME t2) in
    let th1 = SUBST [asm2,t2] (concl asm1) asm1 in
    let th2 = TRANS th1 (CONJUNCT1 (SPEC t1 OR_CLAUSES)) in
    let imp1 = DISCH (concl asm1) (DISCH t2 (EQT_ELIM th2)) in
    let asm3 = ASSUME "^t2 ==> ^t1" and
        asm4 = ASSUME "^t2 \/ ^t1" in
    let th3 = DISJ_CASES asm4 (MP asm3 (ASSUME t2)) (ASSUME t1) in
    let th4 = DISCH (concl asm4) th3 and
        th5 = DISCH t1 (DISJ2 t2 (ASSUME t1)) in
    let imp2 = DISCH "^t2 ==> ^t1" (IMP_ANTISYM_RULE th5 th4) in
        GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2));;

% --------------------------------------------------------------------- %
% NOT_IMP = |- !t1 t2. ~(t1 ==> t2) = t1 /\ ~t2          [TFM 90.07.09] %
% --------------------------------------------------------------------- %

let NOT_IMP =
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let asm1 = ASSUME "~ (^t1 ==> ^t2)" in
    let thm1 = SUBST [EQF_INTRO (ASSUME (mk_neg t1)),t1] (concl asm1) asm1 in
    let thm2 = CCONTR t1 (NOT_MP thm1 (DISCH "F" (CONTR t2 (ASSUME "F")))) in
    let thm3 = SUBST [EQT_INTRO (ASSUME t2),t2] (concl asm1) asm1 in
    let thm4 = NOT_INTRO(DISCH t2(NOT_MP thm3(DISCH t1(ADD_ASSUM t1 TRUTH))))in
    let imp1 = DISCH (concl asm1) (CONJ thm2 thm4) in
    let conj =  ASSUME "^t1 /\ ~ ^t2" in
    let asm2,asm3 = (CONJUNCT1 conj, CONJUNCT2 conj) in
    let asm4 = ASSUME "^t1 ==> ^t2" in
    let thm5 = MP (SUBST [EQF_INTRO asm3,t2] (concl asm4) asm4) asm2 in
    let imp2 = DISCH "^t1 /\ ~ ^t2" (NOT_INTRO(DISCH "^t1 ==> ^t2" thm5)) in
        GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2));;


% --------------------------------------------------------------------- %
% DISJ_ASSOC: |- !t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3           %
% --------------------------------------------------------------------- %

let DISJ_ASSOC =
    let t1 = "t1:bool" and t2 = "t2:bool" and t3 = "t3:bool" in
    let at1 = DISJ1 (DISJ1 (ASSUME t1) t2) t3 and
        at2 = DISJ1 (DISJ2 t1 (ASSUME t2)) t3 and
        at3 = DISJ2 (mk_disj(t1,t2)) (ASSUME t3) in
    let thm = DISJ_CASES (ASSUME (mk_disj(t2,t3))) at2 at3 in
    let thm1 = DISJ_CASES (ASSUME (mk_disj(t1,mk_disj(t2,t3)))) at1 thm in
    let at1 = DISJ1 (ASSUME t1) (mk_disj(t2,t3)) and
        at2 = DISJ2 t1 (DISJ1 (ASSUME t2) t3) and
        at3 = DISJ2 t1 (DISJ2 t2 (ASSUME t3)) in
    let thm = DISJ_CASES (ASSUME (mk_disj(t1,t2))) at1 at2 in
    let thm2 = DISJ_CASES (ASSUME (mk_disj(mk_disj(t1,t2),t3))) thm at3 in
    let imp1 = DISCH (mk_disj(t1,mk_disj(t2,t3))) thm1 and
        imp2 = DISCH (mk_disj(mk_disj(t1,t2),t3)) thm2 in
        GENL [t1;t2;t3] (IMP_ANTISYM_RULE imp1 imp2);;

% --------------------------------------------------------------------- %
% DISJ_SYM: |- !t1 t2. t1 \/ t2 = t2 \/ t1                              %
% --------------------------------------------------------------------- %

let DISJ_SYM =
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let th1 = DISJ1 (ASSUME t1) t2 and th2 = DISJ2 t1 (ASSUME t2) in
    let thm1 = DISJ_CASES (ASSUME(mk_disj(t2,t1))) th2 th1 in
    let th1 = DISJ1 (ASSUME t2) t1 and th2 = DISJ2 t2 (ASSUME t1) in
    let thm2 = DISJ_CASES (ASSUME(mk_disj(t1,t2))) th2 th1 in
    let imp1 = DISCH (mk_disj(t2,t1)) thm1 and
        imp2 = DISCH (mk_disj(t1,t2)) thm2 in
        GENL [t1;t2] (IMP_ANTISYM_RULE imp2 imp1);;

% --------------------------------------------------------------------- %
% DE_MORGAN_THM:                                                        %
%   |- !t1 t2.(~(t1 /\ t2) = ~t1 \/ ~t2) /\ (~(t1 \/ t2) = ~t1 /\ ~t2)  %
% --------------------------------------------------------------------- %

let DE_MORGAN_THM =
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let thm1 =
        let asm1 = ASSUME "~(^t1 /\ ^t2)" in
        let cnj = NOT_MP asm1 (CONJ (ASSUME t1) (ASSUME t2)) in
        let imp1 =
            let case1 = DISJ2 "~^t1" (NOT_INTRO(DISCH t2 cnj)) in
            let case2 = DISJ1 (ASSUME "~ ^t1") "~ ^t2" in
                DISJ_CASES (SPEC t1 EXCLUDED_MIDDLE) case1 case2 in
        let th1 = NOT_MP (ASSUME "~^t1") (CONJUNCT1 (ASSUME "^t1 /\ ^t2")) and
            th2 = NOT_MP (ASSUME "~^t2") (CONJUNCT2 (ASSUME "^t1 /\ ^t2")) in
        let imp2 =
            let fth = DISJ_CASES (ASSUME "~^t1 \/ ~^t2") th1 th2 in
                DISCH "~^t1 \/ ~^t2" (NOT_INTRO(DISCH "^t1 /\ ^t2" fth)) in
            IMP_ANTISYM_RULE (DISCH "~(^t1 /\ ^t2)" imp1) imp2 in
    let thm2 =
        let asm1 = ASSUME "~(^t1 \/ ^t2)" in
        let imp1 =
          let th1 = NOT_INTRO(DISCH t1 (NOT_MP asm1 (DISJ1 (ASSUME t1) t2))) in
          let th2 = NOT_INTRO(DISCH t2 (NOT_MP asm1 (DISJ2 t1 (ASSUME t2)))) in
                DISCH "~(^t1 \/ ^t2)" (CONJ th1 th2) in
        let imp2 =
            let asm = ASSUME "^t1 \/ ^t2" in
            let a1 = CONJUNCT1(ASSUME "~^t1 /\ ~^t2") and
                a2 = CONJUNCT2(ASSUME "~^t1 /\ ~^t2") in
            let fth = DISJ_CASES asm (UNDISCH a1) (UNDISCH a2) in
                DISCH "~^t1 /\ ~^t2" (NOT_INTRO(DISCH "^t1 \/ ^t2" fth)) in
            IMP_ANTISYM_RULE imp1 imp2 in
    GEN t1 (GEN t2 (CONJ thm1 thm2));;

% --------------------------------------------------------------------- %
% ISPEC: specialization, with type instantation if necessary.           %
%                                                                       %
%     A |- !x:ty.tm                                                     %
%  -----------------------   ISPEC "t:ty'"                              %
%      A |- tm[t/x]                                                     %
%                                                                       %
% (where t is free for x in tm, and ty' is an instance of ty)           %
% --------------------------------------------------------------------- %

let ISPEC t th =
    let x,tm = dest_forall(concl th) ?
               failwith `ISPEC: input theorem not universally quantified` in
    let _,inst = match x t ?
               failwith `ISPEC: can't type-instantiate input theorem` in
        (SPEC t (INST_TYPE inst th) ?
               failwith `ISPEC: type variable free in assumptions`);;

% --------------------------------------------------------------------- %
% ISPECL: iterated specialization, with type instantation if necessary. %
%                                                                       %
%        A |- !x1...xn.tm                                               %
%  ---------------------------------   ISPECL ["t1",...,"tn"]           %
%      A |- tm[t1/x1,...,tn/xn]                                         %
%                                                                       %
% (where ti is free for xi in tm)                                       %
% --------------------------------------------------------------------- %

let ISPECL =
    let tup = end_itlist (curry mk_pair) in
    letrec strip (ts:term list) =
       if (null ts) then \tm.[] else
       let fn = strip (tl ts) in \tm. let x,b = dest_forall tm in (x.fn b) in
    \ts. if (null ts) then \th.th else
         if (null (tl ts)) then ISPEC (hd ts) else
         let stripfn = strip ts and tst = tup ts in
         \th. let xs = stripfn (concl th) ?
                  failwith `ISPECL: list of terms too long for theorem` in
              let _,inst = match (tup xs) tst ?
                  failwith `ISPECL: can't type-instantiate input theorem` in
              (SPECL ts (INST_TYPE inst th) ?
                  failwith `ISPECL: type variable free in assumptions`);;

% --------------------------------------------------------------------- %
% SELECT_REFL = |- !x. (@y. y = x) = x                                  %
% --------------------------------------------------------------------- %

let SELECT_REFL =
  let th1 = ISPECL ["\y:*. y = x"; "x:*"] SELECT_AX in
  let ths = map BETA_CONV ["(\y:*. y = x) x"; "(\y:*. y = x)(@y. y = x)"] in
  let th2 = SUBST[(el 1 ths,"u:bool"); (el 2 ths,"v:bool")] "u ==> v" th1 in
  GEN "x:*" (MP th2 (REFL "x:*"));;

%----------------------------------------------------------------------------%
% SELECT_UNIQUE = |- !P x. (!y. P y = (y = x)) ==> ($@ P = x)                %
%----------------------------------------------------------------------------%

let SELECT_UNIQUE =
  let mksym tm = DISCH tm (SYM(ASSUME tm)) in
  let th0 = IMP_ANTISYM_RULE (mksym "y:* = x") (mksym "x:* = y") in
  let th1 = SPEC "y:*" (ASSUME "!y:*. P y = (y = x)") in
  let th2 = EXT(GEN "y:*" (TRANS th1 th0)) in
  let th3 = AP_TERM "$@:(*->bool)->*" th2 in
  let th4 = TRANS (BETA_CONV "(\y:*. y = x) y") th0 in
  let th5 = AP_TERM "$@:(*->bool)->*" (EXT(GEN "y:*" th4)) in
  let th6 = TRANS (TRANS th3 (SYM th5)) (SPEC "x:*" SELECT_REFL) in
  GENL ["P:*->bool"; "x:*"] (DISCH "!y:*. P y = (y = x)" th6);;
