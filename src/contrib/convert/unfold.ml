%< 
---------------------------------

  new-unwind library
  
  unfold.ml
  
  based on HOL88 unwind library   

  Rules for unfolding

  this file mk_thm free !! 
---------------------------------
>%

let REWRITES_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm;;

%
            A1 |- t1 = t1' , ... , An |- tn = tn'
   ---------------------------------------------------------
    A1 u ... u An |- (t1 /\ ... /\ tn) = (t1' /\ ... /\ tn')
%

letrec MK_CONJL thl =
 (if null thl 
  then fail
  if null(tl thl)
  then hd thl
  else
  (let th = MK_CONJL(tl thl)
   in
   let t1,()  = dest_eq(concl(hd thl))
   and (),t2' = dest_eq(concl th)
   in
   (AP_TERM "$/\ ^t1" th) TRANS (AP_THM (AP_TERM "$/\" (hd thl)) t2'))
 ) ? failwith `MK_CONJL`;;

%
            A1 |- t1 = t1' , ... , An |- tn = tn'
      --------------------------------------------------
       A1 u ... u An  |- ?l1 ... lm. t1  /\ ... /\ tn =
                         ?l1 ... lm. t1' /\ ... /\ tn'
%

let UNFOLD thl =
 let net = mk_conv_net thl
 in
 \t.
  ((let vars, eqs = strip_exists t
    and rewrite   = REWRITES_CONV net
    in
    LIST_MK_EXISTS vars (MK_CONJL(map rewrite (conjuncts eqs)))
   ) ? failwith `UNFOLD`);;

%

       A1 |- t1 = t1' , ... , An |- tn = tn'

        A |- t = (?l1 ... lm. t1 /\ ... /\ tn)
      ------------------------------------------
        A |- t = (?l1 ... lm. t1' /\ ... /\ tn')
%

let UNFOLD_RULE thl th =
 RIGHT_CONV_RULE (UNFOLD(map SPEC_ALL thl)) (SPEC_ALL th)
 ? failwith`UNFOLD_RULE`;;



