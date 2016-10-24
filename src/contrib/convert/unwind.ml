%< 
---------------------------------

  new-unwind library
  
  unwind.ml
  
  based on HOL88 unwind library   

  Rules for unwinding

  this file uses mk_thm !! 
---------------------------------
>%

let REWRITES_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm;;

%< some useful conversions for getting things into right form for unwinding >% 

%<
   AND_FORALL_CONV -- move universal quantification out of a conjunction
   
 "(!x. t1) /\ ... /\ (!x. tn)" --->
   |- (!x. t1) /\ ... /\ (!x. tn) = !x. t1 /\ ... /\ tn 
>%

%< now we remove the mk_thm ones and use binary conversions for left, right and both
   conversions as in exists_and (?) ones >%

let AND_FORALL_LEFT_CONV t =
 (let xt1,xt2 = dest_conj t
  in
  let x = fst(dest_forall xt1)
  in
  let (th1,th2) = CONJ_PAIR(ASSUME t)
  in
  let th3 = DISCH_ALL(GEN x (CONJ(SPEC x th1)th2))
  in
  let (th4,th5) =
   CONJ_PAIR
    (SPEC x
     (ASSUME
      (mk_forall(x,(mk_conj((snd o dest_forall o concl)th1,
                            concl th2))))))
  in
  let th6 = DISCH_ALL(CONJ(GEN x th4)th5)
  in
  IMP_ANTISYM_RULE th3 th6
 ) ? failwith `AND_FORALL_LEFT_CONV`;;

%( test AND_FORALL_LEFT_CONV "(! (x:*). T) /\ T";;)%

let AND_FORALL_RIGHT_CONV t =
 (let xt1,xt2 = dest_conj t
  in
  let x = fst(dest_forall xt2)
  in
  let (th1,th2) = CONJ_PAIR(ASSUME t)
  in
  let th3 = DISCH_ALL(GEN x (CONJ th1(SPEC x th2)))
  in
  let (th4,th5) =
   CONJ_PAIR
    (SPEC x
     (ASSUME
      (mk_forall(x,(mk_conj(concl th1,
                            (snd o dest_forall o concl)th2))))))
  in
  let th6 = DISCH_ALL(CONJ th4(GEN x th5))
  in
  IMP_ANTISYM_RULE th3 th6
 ) ? failwith `AND_FORALL_RIGHT_CONV`;;

%( test AND_FORALL_RIGHT_CONV "T /\ (! (x:*). T)";;)%

let AND_FORALL_BOTH_CONV t =
 (let xt1,xt2 = dest_conj t
  in
  let x = fst(dest_forall xt2)
  in
  let (th1,th2) = CONJ_PAIR(ASSUME t)
  in
  let th3 = DISCH_ALL(GEN x (CONJ (SPEC x th1)(SPEC x th2)))
  in
  let (th4,th5) =
   CONJ_PAIR
    (SPEC x
     (ASSUME
      (mk_forall(x,(mk_conj((snd o dest_forall o concl)th1,
                            (snd o dest_forall o concl)th2))))))
  in
  let th6 = DISCH_ALL(CONJ (GEN x th4)(GEN x th5))
  in
  IMP_ANTISYM_RULE th3 th6
 ) ? failwith `AND_FORALL_BOTH_CONV`;;

%( test 

AND_FORALL_BOTH_CONV "(! (x:*). T) /\ (! (x:*). T)";;
)%

let AND_FORALL_CONV = AND_FORALL_BOTH_CONV ORELSEC
                      AND_FORALL_LEFT_CONV ORELSEC
                      AND_FORALL_RIGHT_CONV;;

%( test 
AND_FORALL_CONV "(! (x:*). T) /\ (! (x:*). T)";;
)%

%< mk_thm version eliminated [DES] 31jul90
%  "(!x. t1) /\ ... /\ (!x. tn)" ---> ("x", ["t1"; ... ;"tn"]) %

letrec dest_andl t =
 ((let x1,t1 = dest_forall t
   in
   (x1,[t1])
  )
  ?
  (let first,rest = dest_conj t
   in
   let x1,l1 = dest_andl first
   and x2,l2 = dest_andl rest
   in
   if x1=x2 then (x1, l1@l2) else fail)
 ) ? failwith `dest_andl`;;

% Version of AND_FORALL_CONV below will pull quantifiers out and flatten an
  arbitrary tree of /\s, not just a linear list. %
   
let AND_FORALL_CONV t =
 (let x,l = dest_andl t
  in
  mk_thm([], mk_eq(t,mk_forall(x,list_mk_conj l)))
 ) ? failwith `AND_FORALL_CONV`;;
>%

%<
    FORALL_AND_CONV -- inverse of above

 "!x. t1 /\ ... /\ tn" --->
   |- !x. t1 /\ ... /\ tn =  (!x. t1) /\ ... /\ (!x. tn)
>%
%< superceded by mk_thm version
let FORALL_AND_CONV t =
 (let x,l = ((I # conjuncts) o dest_forall) t
  in
  SYM(AND_FORALL_CONV(list_mk_conj(map(curry mk_forall x)l)))
 ) ? failwith `AND_FORALL_CONV`;;
>%

let FORALL_AND_CONV t =
 (let x,l = ((I # conjuncts) o dest_forall) t
  in
  mk_thm([],mk_eq(t, list_mk_conj(map(curry mk_forall x)l)))
 ) ? failwith `FORALL_AND_CONV`;;

%< [DES] 27apr89

   EXISTS_FORALL_CONV

   ? s . ! t . ....(s t)....  = ! t . ? st . ....st....

   used after unfolding to bring ! t's to outside

   s and t and unprimed then reprimed to be unique in body
   (avoids ?s'!t'.bdy ===> !t'?s't'.bdy problem as s't' not "legal" var name)
>%

let unprime s = implode(filter (\c.not(c=`'`)) (explode s));;

let EXISTS_FORALL_CONV t =
    let ex,t0 = dest_exists t
    in let un,t1 = dest_forall t0
    in let unty = snd(dest_var un)
    in let newname = mk_var(unprime(fst(dest_var ex))^unprime(fst(dest_var un)),type_of"^ex ^un")
    in let new = variant (frees t1) newname
    in let t2 = subst [new,"^ex ^un"] t1
    in let t3 = mk_forall (un,mk_exists (new,t2))
    in let t4 = mk_eq (t,t3)
    in TAC_PROOF(([],t4),
        EQ_TAC THEN REPEAT STRIP_TAC
        THENL [ EXISTS_TAC "^ex ^un" THEN 
                POP_ASSUM (ACCEPT_TAC o SPEC "^un")
               ;EXISTS_TAC "\ ^un . @ ^new . ^t2"
                THEN BETA_TAC
                THEN POP_ASSUM (ACCEPT_TAC o (GEN "^un") 
                                o SELECT_RULE o (SPEC "^un"))
              ]);;

% line_var "!v1 ... vn. f v1 ... vn = t"  ====> "f"                     %

let line_var tm = fst(strip_comb(lhs(snd(strip_forall tm))));;

% var_name "var" ====> `var`                                            %

let var_name = fst o dest_var;;

% line_name "!v1 ... vn. f v1 ... vn = t"  ====> `f`                    %

let line_name = var_name o line_var;;

% UNWIND CONVERSIONS -------------------------------------------------- %

% UNWIND_ONCE_CONV - Basic conversion for parallel unwinding of lines.  %
%                                                                       %
% DESCRIPTION: tm should be a conjunction, t1 /\ t2 ... /\ tn.          %
%              p:term->bool is a function which is used to partition the%
%              terms (ti) into two sets.  Those ti which p is true of   %
%              are then used as a set of rewrite rules (thus they must  %
%              be equations) to do a top-down one-step parallel rewrite %
%              of the conjunction of the remaining terms.  I.e.         %
%                                                                       %
%              t1 /\ ... /\ eqn1 /\ ... /\ eqni /\ ... /\ tn            %
%              ---------------------------------------------            %
%              |-  t1 /\ ... /\ eqn1 /\ ... /\ eqni /\ ... /\ tn        %
%                   =                                                   %
%                  eqn1 /\ ... /\ eqni /\ ... /\ t1' /\ ... /\ tn'      %
%                                                                       %
%                  where tj' is tj rewritten with the equations eqnx    %

let UNWIND_ONCE_CONV p tm =
    let eqns = conjuncts tm in
    let eq1,eq2 = partition (\tm. ((p tm) ? false)) eqns in
    if (null eq1) or (null eq2) 
       then REFL tm
       else let thm = CONJ_DISCHL eq1
                       (ONCE_DEPTH_CONV
                       (REWRITES_CONV (mk_conv_net (map ASSUME eq1)))
                       (list_mk_conj eq2)) in
            let re = CONJUNCTS_CONV(tm,(lhs(concl thm))) in
            re TRANS thm;;

% Unwind until no change using equations selected by p.                 %
% WARNING -- MAY LOOP!                                                  %

letrec UNWIND_CONV p tm =
       let th = UNWIND_ONCE_CONV p tm in
       if lhs(concl th)=rhs(concl th)
          then th
          else th TRANS (UNWIND_CONV p (rhs(concl th)));;

%< [DES] 27apr89

   UNWIND_EXISTS_ONCE_CONV and UNWIND_EXISTS_CONV
   
  
   ? l1 ... ln . eqn1 /\ ... /\ eqnm
   ----------------------------------------
   |- (? l1 ... ln . eqn1 /\ ... /\ eqnm) =
      (? l1 ... ln . eqn1'/\ ... /\ eqnm')

   where any eqs (li = ti) are used as rewrites
>%

let UNWIND_EXISTS_ONCE_CONV t =
   (let exs,bdy = strip_exists t in
    let th1 = UNWIND_ONCE_CONV (\t.mem (line_var t) exs ? false) bdy in
    LIST_MK_EXISTS exs th1) ? failwith `UNWIND_EXISTS_ONCE_CONV`;;

let UNWIND_EXISTS_CONV t =
   (let exs,bdy = strip_exists t in
    let th1 = UNWIND_CONV (\t.mem (line_var t) exs ? false) bdy in
    LIST_MK_EXISTS exs th1) ? failwith `UNWIND_EXISTS_ONCE_CONV`;;

% UNWIND CONVERSIONS -------------------------------------------------- %

% One-step unwinding of device behaviour with hidden lines using line   %
% equations selected by p.                                              %
let UNWIND_ONCE_RULE p th = 
    let rhs_conv = \rhs. (let lines,eqs = strip_exists rhs in
                          LIST_MK_EXISTS lines (UNWIND_ONCE_CONV p eqs)) in
    RIGHT_CONV_RULE rhs_conv th ?  failwith `UNWIND_ONCE_RULE`;;

% Unwind device behaviour using line equations selected by p until no   %
% change.  WARNING --- MAY LOOP!                                        %
let UNWIND_RULE p th = 
    let rhs_conv = \rhs. (let lines,eqs = strip_exists rhs in
                          LIST_MK_EXISTS lines (UNWIND_CONV p eqs)) in
    RIGHT_CONV_RULE rhs_conv th ?  failwith `UNWIND_RULE`;;

% Unwind all lines (except those in the list l) as much as possible.    %
let UNWIND_ALL_RULE l th = 
    let rhs_conv = 
           \rh. (let lines,eqs = strip_exists rh in
                 let eqns = filter (can line_name) (conjuncts eqs) in
                 let line_names = subtract (map line_name eqns) l in
             let p = \line. \tm. (line_name tm) = line in
             let itfn = \line. \th. th TRANS 
                                    UNWIND_CONV (p line) (rhs(concl th)) in
             LIST_MK_EXISTS lines (itlist itfn line_names (REFL eqs))) in
    RIGHT_CONV_RULE rhs_conv th ?  failwith `UNWIND_ALL_RULE`;; 







