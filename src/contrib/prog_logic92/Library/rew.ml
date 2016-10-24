%


Author:          R. A. Fleming

Affiliation:     Hewlett Packard Laboratories, Bristol

Address:         Hewlett Packard Laboratories,
                 Filton Road,
                 Stoke Gifford
                 Bristol BS12 6QZ
                 U.K.

Tel:             +44 272 799910

Fax:             +44 272 890554

Email:           ..!mcvax!ukc!hplb!raf
                 raf@hplb.lb.hp.co.uk

File:            Rewriting

Date:            28/11/90

This file provides an alternative set of rewriting tools.  It is faster
than the old rewriting tools (but marginally slower than the tools in the
Dec 1990 release of HOL).  The difference is in functionality.

* Laws are only instantiated by specialisation of universally quantified
  variables.  (The standard rewrite does an implicit generalisation of 
  all the laws.)  This gives an extra degree of control over how rewriting
  is done.

* Difficulties over clashes of bound variables in the term being rewritten
  with free variables in the laws are overcome.

To illustrate the first point:

Suppose we have the goal

  "x+(a+y)=0"

SEL_REWRITE_TAC [SPEC "a:num" ADD_SYM]
results in the goal

  "x+(y+a)=0"

(rather than diverging which REWRITE_TAC [SPEC "a:num" ADD_SYM] would do).

To illustrate the second point:

Suppose we have a goal

"!x. f x = 1+1"
    [ "1+1 = 2" ]
    [ "f x = x" ]

The ASM_REWRITE_TAC [] fails to do anything, because it rewrites "f x" to
"x" when dealing with the term "f x = 1 + 1".  This results in failure due
to a clash with the universal quantifier "x" which throws the baby out with
the bathwater, i.e. throwing away the legitimate rewrite of 1+1 to 2 as
well.

Also

"!x. f u = x+1"
    ["u = x+1"]

fails when rewriting with ASM_REWRITE_TAC [].  This is again due to clashes
of the free variable "x" in the law with the bound variable "x" of the term
when the rewrite is attempted.  The rewrites in this file rewrite this to:

"!x'. f (x+1) = x'+1"
    ["u = x+1"]

In the interests of speed, some compromise has been made on what the
results look like.  Some bound variables are rewritten to new variants,
even when no laws are used which forces this to happen.  E.g.

"!x y y. u"
   ["u = x"]

will rewrite (using a "PURE" rewrite) not to "!x' y y. x" but "!x' y y'. x"
with the second occurence of "y" being unexpectedly primed.  Also, in the
first example above, the result of the rewrite is "!x'. f x' = 2", even
though there is no occurence of "x" in the resultant term, rather than the
expected "!x. f x = 2".  (This is because rewriting of bound variables is
done if even the mere possibility of a clash with free variables in the
laws is detected.)

%

%PROBLEM WITH term_frees --- trying frees GT%

let term_frees = frees;;

%  Do a conversion c1 and then try doing a conversion c2.  It only fails  %
%  if c1 fails.                                                           %

ml_curried_infix `THENTRYC`;;

let c1 THENTRYC c2 = \t.
  let thm = c1 t
  in ((TRANS thm (c2 (rand (concl thm)))) ? thm);;

% The failing version of REPEATC. %

letrec TRYREPEATC c t =
  let thm = c t
  in ((TRANS thm (TRYREPEATC c (rand (concl thm))))?thm);;


%  Do a conversion as often as possible but at least once: %

let ONCE_OR_MOREC c = c THENTRYC (TRYREPEATC c);;

% let ONCE_OR_MOREC c = c THENC (REPEATC c);; %

%  Try doing conversion conv and then conversion conv'.  If one conversion  %
%  fails it just does the other.  It fails only when both conversions fail. %

let TRYBOTHC conv conv' = \t.
  (let thm1 = conv t
   in ((TRANS thm1 (conv' (rand (concl thm1)))) ? thm1))
  ? (conv' t);;

%

A new version of ALPHA_CONV is provided below.  This is because
ALPHA_CONV "x':num" "\x y y. x+y" = 
   |- (\x y y'. x + y') = (\x' y y'. x' + y')
rather than 
   |- (\x y y. x + y) = (\x' y y'. x' + y')
which, even though it does unnecessary priming on the rhs, at least keeps
the lhs the same as the argument term.

%

let SEL_ALPHA_CONV x t =
let thm = BETA_CONV (mk_comb(t,x)) in
let thm' = BETA_CONV (mk_comb((mk_abs(x,rhs (concl thm)),x))) in
EXT (GEN x (TRANS thm (SYM thm')));;

%

The fr parameter is the list of free variables in the laws used for
rewriting.

%

letrec SEL_ONCE_DEPTH_CONV fr conv = \t.
let SEL_SUBCONV t =
   if is_var t or is_const t then fail
   else if is_comb t then
     let f,a = dest_comb t in
       ((let f_thm = SEL_ONCE_DEPTH_CONV fr conv f
        in ((MK_COMB (f_thm, SEL_ONCE_DEPTH_CONV fr conv a))
            ? AP_THM f_thm a))
        ? AP_TERM f (SEL_ONCE_DEPTH_CONV fr conv a))
   else let x,b = dest_abs t in
        if mem x fr then
        let newvar = variant (fr@(term_frees b)) x in
        let thm = SEL_ALPHA_CONV newvar t in
        let b' = snd (dest_abs (rhs (concl thm))) in
        TRANS thm (ABS newvar (SEL_ONCE_DEPTH_CONV fr conv b'))
        else ABS x (SEL_ONCE_DEPTH_CONV fr conv b) in
(conv ORELSEC SEL_SUBCONV) t;;

letrec SEL_TOP_DEPTH_CONV fr conv = \t.
let SEL_SUBCONV t =
   if is_var t or is_const t then fail
   else if is_comb t then
     let f,a = dest_comb t in
       ((let f_thm = SEL_TOP_DEPTH_CONV fr conv f
        in ((MK_COMB (f_thm, SEL_TOP_DEPTH_CONV fr conv a))
            ? AP_THM f_thm a))
        ? AP_TERM f (SEL_TOP_DEPTH_CONV fr conv a))
   else let x,b = dest_abs t in
        if mem x fr then
        let newvar = variant (fr@(term_frees b)) x in
        let thm = SEL_ALPHA_CONV newvar t in
        let b' = snd (dest_abs (rhs (concl thm))) in
        TRANS thm (ABS newvar (SEL_TOP_DEPTH_CONV fr conv b'))
        else ABS x (SEL_TOP_DEPTH_CONV fr conv b) in
letrec aux t = (SEL_SUBCONV
                THENTRYC
                ((conv THENTRYC (TRYREPEATC conv))
                 THENTRYC
                 aux)) t
in (TRYBOTHC (conv THENTRYC (TRYREPEATC conv)) aux) t;;

%

The f parameter represents free variables in the original rewriting laws.
If a match is found, the substitution is checked to ensure that a
substitution of free variables does not occur.

%

let SEL_rewrite_CONV f th =
    let pat = fst (dest_eq(concl th)) in
    let matchfn = \t.
      let u = match pat t in
      if exists (\v.exists (\x. snd x = v) (fst u)) f then fail else u in
    \tm. INST_TY_TERM (matchfn tm) th;;

letrec SEL_mk_rewrites th =
 (let f = frees (concl th) in
  let th = GSPEC th in
  let t = concl th in
  if is_eq t
  then [f,th]
  if is_conj t
  then map (\x,y.f,y) (SEL_mk_rewrites(CONJUNCT1 th)
                       @SEL_mk_rewrites(CONJUNCT2 th))
  if is_iff t
  then [f, GSPEC (IFF_EQ_RULE th)]
  if is_neg t
  then [f, GSPEC (MP(SPEC(dest_neg t)NOT_F) th)]
  else [f, GSPEC (EQT_INTRO th)]
 ) ? failwith `SEL_mk_rewrites`;;

let SEL_mk_rewritesl thl = flat (map SEL_mk_rewrites thl);;

let SEL_mk_frees_conv_net thl =
 let f_th_pairs = SEL_mk_rewritesl thl in
 (flat (map fst f_th_pairs),
  (itlist
   enter_term
   (map (\f,th. (lhs(concl th),SEL_rewrite_CONV f th)) f_th_pairs)
   nil_term_net));;

let GEN_REWRITE_CONV rewrite_fun basic_rewrites = 
let f1,basic_net = SEL_mk_frees_conv_net basic_rewrites in
\thl.
let f2,thl_net = SEL_mk_frees_conv_net thl in
  rewrite_fun (f1@f2) (REWRITES_CONV(merge_term_nets thl_net basic_net));;

let SEL_PURE_REWRITE_CONV      = GEN_REWRITE_CONV SEL_TOP_DEPTH_CONV []
and SEL_REWRITE_CONV           = GEN_REWRITE_CONV SEL_TOP_DEPTH_CONV basic_rewrites
and SEL_PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV SEL_ONCE_DEPTH_CONV []
and SEL_ONCE_REWRITE_CONV      = GEN_REWRITE_CONV SEL_ONCE_DEPTH_CONV basic_rewrites;;

% A collection of go-faster versions of standard rewrites: %

let SEL_REWRITE_TAC thl = CONV_TAC (SEL_REWRITE_CONV thl)
and SEL_ONCE_REWRITE_TAC thl = CONV_TAC (SEL_ONCE_REWRITE_CONV thl)
and SEL_PURE_REWRITE_TAC thl = CONV_TAC (SEL_PURE_REWRITE_CONV thl)
and SEL_PURE_ONCE_REWRITE_TAC thl = CONV_TAC (SEL_PURE_ONCE_REWRITE_CONV thl);;

let SEL_PURE_ASM_REWRITE_TAC thl = 
 ASSUM_LIST (\asl. SEL_PURE_REWRITE_TAC (asl @ thl))
and SEL_ASM_REWRITE_TAC thl      = 
 ASSUM_LIST (\asl. SEL_REWRITE_TAC (asl @ thl))
and SEL_ONCE_ASM_REWRITE_TAC thl =
 ASSUM_LIST (\asl. SEL_ONCE_REWRITE_TAC (asl @ thl))
and SEL_PURE_ONCE_ASM_REWRITE_TAC thl =
 ASSUM_LIST (\asl. SEL_PURE_ONCE_REWRITE_TAC (asl @ thl))
and SEL_FILTER_PURE_ASM_REWRITE_TAC f thl =
 ASSUM_LIST (\asl. SEL_PURE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and SEL_FILTER_ASM_REWRITE_TAC f thl =
 ASSUM_LIST (\asl. SEL_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and SEL_FILTER_ONCE_ASM_REWRITE_TAC f thl =
 ASSUM_LIST (\asl. SEL_ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and SEL_FITLER_PURE_ONCE_ASM_REWRITE_TAC f thl =
 ASSUM_LIST (\asl. SEL_PURE_ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl));;

let SEL_REWRITE_RULE thml = CONV_RULE (SEL_REWRITE_CONV thml)
and SEL_PURE_REWRITE_RULE thml = CONV_RULE (SEL_PURE_REWRITE_CONV thml)
and SEL_ONCE_REWRITE_RULE thml = CONV_RULE (SEL_ONCE_REWRITE_CONV thml)
and SEL_PURE_ONCE_REWRITE_RULE thml = 
   CONV_RULE (SEL_PURE_ONCE_REWRITE_CONV thml);;


