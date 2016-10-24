%----- -*- Emacs Mode: fundamental -*- -------------------------------

  File:		curry.ml

  Author:	(c) Kim Dam Petersen, 1991.
  Date:		8/8-1991.

  Description:
		Defines operations for manipulating curried abstraction

  Usage:
		loadt`curry`;;
---------------------------------------------------------------------%

%<
  mk_uncurry_abs "(x1,...,xn)" t
  --> "UNCURRY \x1. UNCURRY \x2. ... UNCURRY \xn-1 xn. t"
  == "\(x1, ... ,xn). t"
>%

letrec mk_uncurry_abs (x,tm) =
    if is_pair x then
      let
        (x1,xv) = dest_pair x
      in
        "UNCURRY ^(mk_abs(x1, mk_uncurry_abs (xv,tm)))"
    else
       mk_abs(x,tm);;

%<
  list_mk_uncurry_abs ["(x11,...,x1n1)";...;"(xm1,...,xmnm)"] t
  --> "\(x11,...,x1n1)...(xm1,...,xmnm). t"
>%
letrec list_mk_uncurry_abs (xv,tm) =
  (case xv of
    []. tm
   |(x.xv). mk_uncurry_abs (x,(list_mk_uncurry_abs(xv,tm))));;

%<
  dest_uncurry_abs "\(x1,...,xn). t"
  --> ("(x1,...,xn)",t)
>%
letrec dest_uncurry_abs tm =
  if is_abs tm then
    let (x,t) = dest_abs tm in (x,t)
  else
    let (unc,abs) = dest_comb tm in
    let (x,t)     = dest_abs  abs in
    let (xp,t)    = dest_uncurry_abs t in
      if (fst(dest_const(unc)) = `UNCURRY`) then
         (mk_pair(x,xp),t)
      else
         failwith `dest_uncurry_abs`;;
%<
  strip_uncurry_abs "\(x11,...,x1n1) ... (xm1,...,xmnm). t"
  --> ("[(x11,...,x1n1);...;(xm1,...,xmnm)]",t)
>%
letrec strip_uncurry_abs tm =
  (let
     (xp,t) = dest_uncurry_abs tm
   in let
     (xv,t) = strip_uncurry_abs t
   in
     ((xp.xv),t)) ? ([],tm);;

%<
  UNCURRY_BETA_CONV "(\(x1,...,xn). P)(y1,...,yn)" -->
     |- (\(x1,...,xn). P)(y1,...,yn) = P[x1,...,xn\y1,...,yn]
>%
let UNCURRY_BETA_CONV =
  set_fail_prefix `UNCURRY_BETA_CONV`
  (\tm.
    %< ucb "(\(x1,x2,...,xn). P)(y1,...,yn)" -->
         |-"(\(x1,x2,...,xn). P)(y1,...,yn) 
              = (\(x2,...,xn). P[x1\y1])(y2,...yn)  iff n>2
              = P[x1,x2\y1,y2]                      iff n=2
    >%
  let
    uncurry_beta_conv tm =
       let once_beta_rule = CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) in
       let (f,yp) = dest_comb tm in
       let fn     = snd(dest_comb f) and
           (xp,b) = dest_uncurry_abs f in
       let (x1,x2) = dest_pair xp and
           (y1,y2) = dest_pair yp in
       let thm1 = ISPECL [fn;y1;y2] UNCURRY_DEF in
       if (is_pair x2) then
            once_beta_rule thm1
       else
            once_beta_rule (once_beta_rule thm1) in
  let
    (x,yv) = dest_comb tm
  in let
    (xp,b) = dest_uncurry_abs x
  in
    if not (is_pair xp) then fail else
      letrec ubc tm =
        let eq1thm = uncurry_beta_conv tm in
        let eq2thm = ([ubc (snd(dest_eq(concl eq1thm)))] ? [])
        in
          if eq2thm = [] then eq1thm else TRANS eq1thm (hd eq2thm)
    in ubc tm);;

let UNCURRY_BETA_TAC = CONV_TAC (DEPTH_CONV UNCURRY_BETA_CONV);;

%< mk_fun_type (dtp,rtp) --> ":dtp -> rtp"
   dest_fun_type ":dtp -> rtp" --> (dt,prtp)
 >%
let mk_fun_type (dtp,rtp) = mk_type(`fun`,[dtp;rtp]);;

let dest_fun_type =
  set_fail `dest_fun_type`
  (\tp.
    let (f,[dtp;rtp]) = dest_type tp
    in
      if f = `fun` then (dtp,rtp) else fail);;

%< list_mk_fun_type [dt1;...;dtn] rt = ":dt1 -> ... -> dtn -> rt"
   strip_fun_type [dt1;...;dtn] rt = ":dt1 -> ... -> dtn -> rt"
 >%
let list_mk_fun_type (dtl,rt) = itlist (curry mk_fun_type) dtl rt;;
letrec strip_fun_type tp =
  (let (dt,rt) = dest_fun_type tp in
   let (dtl,rt') = strip_fun_type rt
   in ((dt.dtl),rt')) ? ([],tp);;

%<
    CURRY_EQUIV_RULE "f:(t1#...#tn)->t" ["x1";...;"xn"] |- P[f]
    --> |- P[\(x1,...,xn). f x1 ... xn]
>%

%<  Still has to be finished????
let CURRY_EQUIV_RULE =
  set_fail_prefix `CURRY_EQUIV_RULE`
  (\uf xl P.
    let xtl  = map type_of xl in
    let ufrt = snd(dest_fun_type(type_of uf)) in
    let cf   = mk_var(fst(dest_var uf), list_mk_fun_type(xtl,ufrt)) in
    let aucf = mk_uncurry_abs(list_mk_pair xtl, list_mk_comb(cf,xtl)) ;;
    let thm1 = SPEC ucf (GEN (f,f) P) in
$$$ ) ;;
>%
