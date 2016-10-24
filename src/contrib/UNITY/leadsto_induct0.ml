%	-*- Emacs Mode: fundamental -*-                                       %

%-----------------------------------------------------------------------------%
%
   File:         leadsto_induct.ml
   Description:  

   This file defines the induction tactics for the  LEADSTO definition.
   
   Authors:      Copyright by Flemming Andersen 1990.
   Date:         December 19, 1990
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `unity_lemmas`;;
autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
autoload_defs_and_thms `leadsto_mod`;;
autoload_defs_and_thms `leadsto`;;
%

%
|- !X st Pr.
    (!p q.   (p ENSURES q)(CONS st Pr) ==> X p q(CONS st Pr)) /\
    (!p r q. (p ENSURES r)(CONS st Pr) /\
             (r LEADSTO q)(CONS st Pr) /\ X r q(CONS st Pr)
                                       ==> X p q(CONS st Pr)) /\
    (!P q.   (!p. p In P ==> (p LEADSTO q)(CONS st Pr)) /\
             (!p. p In P ==> X p q(CONS st Pr))
                                       ==> X (LUB P) q (CONS st Pr))

    ==> (!p q. (p LEADSTO q)(CONS st Pr) ==> X p q(CONS st Pr))
%
let LEADSTO_INDUCT0_TAC (hyp,conc) =
 (
  let (p, qstPrLX)  = dest_forall  conc in

  let (q,  stPrLX)  = dest_forall  qstPrLX in
  let (st,   PrLX)  = dest_forall   stPrLX in
  let (Pr,     LX)  = dest_forall     PrLX in
  let (L,       X)  = dest_imp          LX in

  let PrX           = mk_abs(Pr,         X) in
  let stPrX         = mk_abs(st,        PrX) in
  let qstPrX        = mk_abs(q,       stPrX) in
  let pqstPrX       = mk_abs(p,       qstPrX) in


  let RbX = "(^p ENSURES ^q)(CONS ^st ^Pr) ==> ^X" in

  let r     = variant (freesl (conc.hyp)) "r:*->bool" in
  let RtL1  = "(^p ENSURES ^r) (CONS ^st ^Pr)" in
  let RtL2  = "(^r LEADSTO ^q) (CONS ^st ^Pr)" in
  let RtX1  = subst[r,p] X in

  let P     = variant (freesl (conc.hyp)) "P:(*->bool)->bool" in
  let p'    = variant (freesl (conc.hyp)) "p:*->bool" in
  let RdX1  = subst[p',p] L in
  let RdX1' = "!^p'. ^p' In ^P ==> ^RdX1" in
  let RdX2  = subst[p',p] X in
  let RdX2' = "!^p'. ^p' In ^P ==> ^RdX2" in
  let RdX3  = subst["LUB ^P",p] X in

  let Xb    = "!^p ^q ^st ^Pr. ^RbX" in
  let Xt    = "!^p ^r ^q ^st ^Pr. (^RtL1 /\ ^RtL2 /\ ^RtX1) ==> ^X" in
  let Xd    = "!^P ^q ^st ^Pr. ^RdX1' /\ ^RdX2' ==> ^RdX3" in

  let Pr'   = variant (freesl (conc.hyp)) "Pr:(*->*)list" in
  let X' = subst[Pr',"CONS ^st ^Pr"] X in
  let PrX'         = mk_abs(Pr,         X') in
  let qPrX'        = mk_abs(q,        PrX') in
  let pqPrX'       = mk_abs(p,       qPrX') in
   ([(hyp, Xb);(hyp, Xt);(hyp, Xd)],
       \ [thmb;thmt;thmd].
           MP (BETA_RULE (SPEC pqPrX' LEADSTO_thm34b))
              (CONJ thmb (CONJ thmt thmd))))
 ? failwith `LEADSTO_INDUCTION_0`;;
