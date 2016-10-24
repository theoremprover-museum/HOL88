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
                 raf@hplb.hpl.hp.com

File:            "Half rewriting" tactics for HOL

Date:            16/11/90
                 25/2/91   Modifications made to make compatible
                           with HOL version 12
                 14/5/91   Modified to abandon restrictions on what
                           variables can be rewritten, and adding
                           1/4 rewrites

This file contains the tactics for "half rewriting".  The idea is to be
able to do re-writing in some restricted form, when the rewriting laws are
implications rather than equations.

In the conversions, if C[...] is a monotonically increasing context, then
given a term C[A] and a rewrite law A==>B, the theorem C[A] ==> C[B]
results.  If C[...] is a decreasing context, given a term C[B], the theorem
C[A] ==> C[B] is returned.

Some contexts are neither monotonically increasing or decreasing.  No
rewriting can be done in these contexts.

The following describes the contexts that are encoded in these converions.
+ means an increasing context, - a decreasing one, and 0 means neither.

               + \/ +                     + /\ +
               
               ?x. +                      !x. +

               ~ -

               - ==> +

               0 => + | +

               0 = 0                      0 <=> 0

Considering just implications for the moment, theorems of the form A ==> B
are transformed into A' ==> B' where A' and B' are rewrites of A and B, and
where A' ==> A and B ==> B'.  (I.e. A' ==> A ==> B ==> B'.)  In other
words, "strengthening" of the theorem results.

Things happen conversely in backwards proof.  Goals of the form A ==> B are
transformed into A' ==> B' where A' and B' are rewrites of A and B, and
where A ==> A' and B' ==> B.  (I.e. A ==> A' ==> B' ==> B.)  This results
in the left hand and right hand sides becoming "closer together".  In other
words, "weakening" of the goal results.

Equalities are also handled as laws.  These are rewritten in a left to right
manner in all contexts.  (Thus the rules and tactics can perform the standard
simplifications.)

There is now the addition of two more classes of half rewriting conversions,
rules and tactics.

  LR_...

versions just do rewriting of implicational laws from left to right, and

  RL_...

versions write from right to left.

The basic rewrites in RL_... versions are retained, so simplification works
as usual.  However, all user-supplied equalities

  x = y

(where "x" and "y" are boolean) are written from right to left, as the name
implies.

%

% The analogy of THENC for half rewriting conversions. %

begin_section half;;

let THENHC thm h_cnv sng (tm:term) =
  if sng then IMP_TRANS thm (h_cnv sng (snd (dest_imp (concl thm))))
         else IMP_TRANS (h_cnv sng (fst (dest_imp (concl thm)))) thm;;

ml_curried_infix `HALF_THEN`;;

let h_cnv1 HALF_THEN h_cnv2 sng tm =
  THENHC (h_cnv1 sng tm) h_cnv2 sng tm;;

% h_cnv1 HALF_THENTRY h_cnv2 tries applying h_cnv1, and if that succeeds,
it tries applying h_cnv2. %

ml_curried_infix `HALF_THENTRY`;;

let h_cnv1 HALF_THENTRY h_cnv2 sng tm = 
  let thm = h_cnv1 sng tm in
  ((THENHC thm h_cnv2 sng tm) ? thm);;

% ALL_HCONV tm always works.  It just returns tm ==> tm. %

let ALL_HCONV sng tm = DISCH tm (ASSUME tm);;

let NO_HCONV sng tm = failwith `NO_HCONV`;;

% 

HALF_TRY_BOTH h_cnv1 h_cnv2 tries applying h_cnv1 and then h_cnv2.  If
the attempt to apply h_cnv1 fails, h_cnv2 is applied.  It only fails if
both h_cnv1 and h_cnv2 fail. 

%

let HALF_TRY_BOTH  h_cnv1 h_cnv2 sng tm =
  ((h_cnv1 HALF_THENTRY h_cnv2) sng tm) ? (h_cnv2 sng tm);;

% The analogy of REPEATC. %

letrec REPEATHC h_cnv sng t = 
  (h_cnv HALF_THENTRY (REPEATHC h_cnv)) sng t;;

% This deals with half-rewriting conversions on terms of the form ~t. %

let NEG_HCONV h_cnv sng tm = CONTRAPOS (h_cnv (not sng) (dest_neg tm));;

%

tm is assumed to have the form a/\b.  The half conversion h_cnv sng is
applied to a to produce a theorem x ==> y.  (Typically this theorem has
the form a ==> c or else c ==> a, but this is not required.)  The result is
a theorem x /\ b ==> y /\ b

%

let CONJ1_HCONV h_cnv sng tm =
  let a,b = dest_conj tm
  in let thm = h_cnv sng a
  in let ab = ASSUME (mk_conj (fst (dest_imp (concl thm)), b))
  in let a,b = CONJUNCT1 ab, CONJUNCT2 ab
  in DISCH (concl ab) (CONJ (MP thm a) b);;

% Below, CONJ2_HCONV is like CONJ1_HCONV but works on the second
conjunct. %

let CONJ2_HCONV h_cnv sng tm =
  let a,b = dest_conj tm
  in let thm = h_cnv sng b
  in let ab = ASSUME (mk_conj (a, fst (dest_imp (concl thm))))
  in let a,b = CONJUNCT1 ab, CONJUNCT2 ab
  in DISCH (concl ab) (CONJ a (MP thm b));;

%

tm is assumed to have the form a\/b.  The half conversion h_cnv sng is
applied to a to produce a theorem x ==> y.  (Typically this theorem has
the form a ==> c or else c ==> a, but this is not required.)  The result is
a theorem x \/ b ==> y \/ b

%

let DISJ1_HCONV h_cnv sng tm =
  let a,b = dest_disj tm
  in let thm = h_cnv sng a
  in let x,y = dest_imp (concl thm)
  in let ass = mk_disj (x,b)
  in DISCH ass 
           (DISJ_CASES (ASSUME ass) (DISJ1 (MP thm (ASSUME x)) b)
                                    (DISJ2 y (ASSUME b)));;

let DISJ2_HCONV h_cnv sng tm =
  let a,b = dest_disj tm
  in let thm = h_cnv sng b
  in let x,y = dest_imp (concl thm)
  in let ass = mk_disj (a,x)
  in DISCH ass 
           (DISJ_CASES (ASSUME ass) (DISJ1 (ASSUME a) y)
                                    (DISJ2 a (MP thm (ASSUME x))));;

let IMP1_HCONV h_cnv sng tm =
  let a,b = dest_imp tm
  in let thm = h_cnv (not sng) a
  in let x,y = dest_imp (concl thm)
  in let yb = mk_imp(y,b)
  in DISCH yb (IMP_TRANS thm (ASSUME yb));;

let IMP2_HCONV h_cnv sng tm =
  let a,b = dest_imp tm
  in let thm = h_cnv sng b
  in let x,y = dest_imp (concl thm)
  in let ax = mk_imp(a,x)
  in DISCH ax (IMP_TRANS (ASSUME ax) thm);;

let COND_THM1 = PROVE ("!a b b' c. (b ==> b') ==> (a => b | c) ==> (a => b' | c)",
REPEAT GEN_TAC THEN DISCH_TAC THEN
DISJ_CASES_THEN (\x. REWRITE_TAC [x]) (SPEC "a:bool" BOOL_CASES_AX) THEN
POP_ASSUM ACCEPT_TAC);;

let COND1_HCONV h_cnv sng tm =
  let a,b,c = dest_cond tm
  in if type_of b = ":bool"
  then let thm = h_cnv sng b
  in let b' = snd (dest_imp (concl thm))
  in MP (SPECL [a;b;b';c] COND_THM1) thm
  else failwith `COND1_HCONV`;;

let COND_THM2 = PROVE ("!a b c c'. (c ==> c') ==> (a => b | c) ==> (a => b | c')",
REPEAT GEN_TAC THEN DISCH_TAC THEN
DISJ_CASES_THEN (\x. REWRITE_TAC [x]) (SPEC "a:bool" BOOL_CASES_AX) THEN
POP_ASSUM ACCEPT_TAC);;

let COND2_HCONV h_cnv sng tm =
  let a,b,c = dest_cond tm
  in if type_of b = ":bool"
  then let thm = h_cnv sng b
  in let c' = snd (dest_imp (concl thm))
  in MP (SPECL [a;b;c;c'] COND_THM2) thm
  else failwith `COND2_HCONV`;;

let FORALL_HCONV h_cnv sng tm =
  let v,a = dest_forall tm
  in let thm = h_cnv sng a
  in let x,y = dest_imp (concl thm)
  in let h = mk_forall (v,x)
  in DISCH h (GEN v (MP thm (SPEC v (ASSUME h))));;

let EXISTS_HCONV h_cnv sng tm =
  let v,a = dest_exists tm
  in let thm = h_cnv sng a
  in let x,y = dest_imp (concl thm)
  in let h = mk_exists (v,x)
  in DISCH h (CHOOSE (v, ASSUME h)
                     (EXISTS (mk_exists(v,y), v)
                             (MP thm (ASSUME x))));;

let is_implies tm =  (rator (rator tm) = "==>")?false;;

%

Note that this conversion does not always yield rewrites when they are valid.
This is due to clashes of variables in hypotheses with bound variables in the
term being rewritten.  No attempt has been made to fix this, as this is in
line with the standard rewriting tactics.  (The alternative is also rather
inefficient.) 

%

let SUBTERMS_HCONV h_cnv sng tm =
  if is_neg tm
  then NEG_HCONV h_cnv sng tm
  else if is_conj tm 
  then (HALF_TRY_BOTH (CONJ1_HCONV h_cnv) 
                      (CONJ2_HCONV h_cnv)) sng tm
  else if is_disj tm
  then (HALF_TRY_BOTH (DISJ1_HCONV h_cnv)
                      (DISJ2_HCONV h_cnv)) sng tm
  else if is_implies tm
  then (HALF_TRY_BOTH (IMP1_HCONV h_cnv)
                      (IMP2_HCONV h_cnv)) sng tm
  else if is_cond tm
  then (HALF_TRY_BOTH (COND1_HCONV h_cnv)
                      (COND2_HCONV h_cnv)) sng tm
  else if is_forall tm
  then FORALL_HCONV h_cnv sng tm
  else if is_exists tm
  then EXISTS_HCONV h_cnv sng tm
  else failwith`SUBTERMS_HCONV`;;

% Does recursive rewriting in a single top-down pass through the term. %

letrec TOP_DOWN_HCONV h_cnv sng t =
  ((HALF_TRY_BOTH h_cnv
          (SUBTERMS_HCONV (TOP_DOWN_HCONV h_cnv))) sng t)
  ? failwith `TOP_DOWN_HCONV`;;

letrec BOTTOM_UP_HCONV h_cnv sng t =
  ((HALF_TRY_BOTH (SUBTERMS_HCONV (BOTTOM_UP_HCONV h_cnv))
                  h_cnv) sng t)
  ? failwith `BOTTOM_UP_HCONV`;;

letrec ONCE_DEPTH_HCONV h_cnv sng t =
  ((h_cnv sng) ORELSEC 
  (SUBTERMS_HCONV (ONCE_DEPTH_HCONV h_cnv) sng)) t;;

let HALF_ONCE_OR_MORE c s = (c HALF_THENTRY (REPEATHC c)) s;;

% The analogue of TOP_DEPTH_CONV for half rewriting. %

letrec TOP_DEPTH_HCONV h_cnv sng t =
  letrec aux1 sng = ((SUBTERMS_HCONV (TOP_DEPTH_HCONV h_cnv)) HALF_THENTRY aux2) sng 
     and aux2 sng = (HALF_ONCE_OR_MORE h_cnv HALF_THENTRY aux1) sng 
in ((HALF_TRY_BOTH (HALF_ONCE_OR_MORE h_cnv) aux1) sng t)?failwith `TOP_DEPTH_HCONV`;;

%

Laws which is not implicational are transformed to A = T.  (This is then
used to replace A by T in both +ve and -ve contexts.

%

let mk_HALF_imp_rewrite th =
letrec split_thm th = 
  let th = GSPEC th in
  let c = concl th in
  else if is_implies c then [th,th]
  else if is_conj c then flat (map split_thm (CONJUNCTS th))
  else if is_eq c then 
    ([EQ_IMP_RULE th]
     ?split_thm (EQT_INTRO th))
  else split_thm (EQT_INTRO th) in
split_thm th;;

let mk_LR_imp_rewrite th =
let th' = GSPEC th in 
letrec pos_split_thm th = 
  let c = concl th in
  else if is_implies c then [th]
  else if is_conj c then flat (map pos_split_thm (CONJUNCTS th))
  else if is_eq c then 
    ([fst (EQ_IMP_RULE th)]
     ?pos_split_thm (EQT_INTRO th))
  else pos_split_thm (EQT_INTRO th) 
and neg_split_thm th = 
  let c = concl th in
  else if is_implies c then []
  else if is_conj c then flat (map neg_split_thm (CONJUNCTS th))
  else if is_eq c then 
    ([snd (EQ_IMP_RULE th)]
     ?neg_split_thm (EQT_INTRO th))
  else neg_split_thm (EQT_INTRO th) 
in pos_split_thm th', neg_split_thm th';;

let mk_LR_imp_rewrites thl = (flat#flat) (split (map mk_LR_imp_rewrite thl));;

let mk_RL_imp_rewrite th =
let th' = GSPEC th in 
letrec pos_split_thm th = 
  let c = concl th in
  else if is_implies c then []
  else if is_conj c then flat (map pos_split_thm (CONJUNCTS th))
  else if is_eq c then 
    ([snd (EQ_IMP_RULE th)]
     ?pos_split_thm (EQT_INTRO th))
  else pos_split_thm (EQT_INTRO th) 
and neg_split_thm th = 
  let c = concl th in
  else if is_implies c then [th]
  else if is_conj c then flat (map neg_split_thm (CONJUNCTS th))
  else if is_eq c then 
    ([fst (EQ_IMP_RULE th)]
     ?neg_split_thm (EQT_INTRO th))
  else neg_split_thm (EQT_INTRO th) 
in pos_split_thm th', neg_split_thm th';;

let mk_RL_imp_rewrites thl = (flat#flat) (split (map mk_RL_imp_rewrite thl));;

let mk_HALF_imp_rewrite th =
letrec split_thm th = 
  let th = GSPEC th in
  let c = concl th in
  else if is_implies c then [th,th]
  else if is_conj c then flat (map split_thm (CONJUNCTS th))
  else if is_eq c then 
    ([EQ_IMP_RULE th]
     ?split_thm (EQT_INTRO th))
  else split_thm (EQT_INTRO th) in
split_thm th;;

let mk_HALF_imp_rewrites thml = split (flat (map mk_HALF_imp_rewrite thml));;

% The next set of stuff is just to generate new variables names.
  They are the first of
            newvar, newvar0, newvar1, ...
  which do not already appear amoungst the variables in the argument list.
%

let newvar = explode `newvar`;;

letrec strip_list l l' =
  if null l then l'
  else if null l' then fail
  else if hd l = hd l' then strip_list (tl l) (tl l') else fail;;

let newvar_numbers =
  mapfilter (\x. let n = strip_list newvar (explode (fst (dest_var x)))
                 in if n = [] then 0 else (int_of_string (implode n))+1);;

letrec get_num nl n =
  if mem n nl then get_num nl (n+1) else n;;

letrec get_new_numbered_vars nl l =
  if null l then []
  else let n = get_num nl 0 in
       (mk_var (implode (if n = 0 then newvar
                else newvar@(explode (string_of_int (n-1)))), type_of (hd l))).
       (get_new_numbered_vars (n.nl) (tl l));;

let get_new_vars l l' =
  get_new_numbered_vars (newvar_numbers l) l';;

%
let ALL_IMPLICANS_EXISTS_INTRO thm =
  let newvars = let a,b = dest_imp (concl thm) in 
                          subtract (frees a) (union (frees (concl thm)) (frees b)) in
  let replvars = get_new_vars newvars
%

letrec CHOOSEL (tm,l) thm =
  if null l then thm
  else let tm' = mk_exists (hd l,tm) in
       CHOOSEL (tm', tl l) (DISCH tm' (CHOOSE (hd l, ASSUME tm') (MP thm (ASSUME tm))));;

let IMPLICANS_EXISTS_INTRO thm =
  let a,b = dest_imp (concl thm) in
  let newvars = subtract (frees a) (union (frees b) (flat (map frees (hyp thm)))) in
  let replvars = get_new_vars (union (flat (map frees (hyp thm))) (frees (concl thm))) newvars in
  let s = combine (replvars,newvars) in
  CHOOSEL (subst s a, rev replvars) (INST s thm);;

let IMPLICAND_FORALL_INTRO thm =
  let a,b = dest_imp (concl thm) in
  let newvars = subtract (frees b) (union (frees a) (flat (map frees (hyp thm)))) in
  let replvars = get_new_vars (union (flat (map frees (hyp thm))) (frees (concl thm))) newvars in
  ((DISCH a (GENL replvars (INST (combine (replvars,newvars)) (MP thm (ASSUME a)))))?thm);;

let POS_REWRITE_HCONV th = 
    let mtch = match (rand (rator (concl th))) in
    ((\tm. let u = mtch tm in
           let instth = INST_TY_TERM u th in
           let l = rand (rator (concl instth)) in
           let thm' = if (l = tm) then instth 
                      else let B = genvar ":bool" in
                      SUBST [ALPHA l tm, B] (mk_imp (B,rand (concl instth))) instth
           in IMPLICAND_FORALL_INTRO thm'))
    ? failwith `POS_REWRITE_HCONV: bad theorem argument (not an implication)`
and NEG_REWRITE_HCONV th = 
    let mtch = match (rand (concl th)) in
    ((\tm. let u = mtch tm in
           let instth = INST_TY_TERM u th in
           let r = rand (concl instth) in
           let thm' = if (r = tm) then instth 
                      else let B = genvar ":bool" in
                      SUBST [ALPHA r tm, B] (mk_imp (rand (rator (concl instth)),B)) instth
           in IMPLICANS_EXISTS_INTRO thm'))
    ? failwith `NEG_REWRITE_HCONV: bad theorem argument (not an implication)`;;

let mk_LRCONV_nets thl =
let pos_rewrites,neg_rewrites = mk_LR_imp_rewrites thl in
 itlist
  enter_term
  (map (\th. (rand (rator (concl th)),POS_REWRITE_HCONV th)) pos_rewrites)
  nil_term_net,
 itlist
  enter_term
  (map (\th. (rand(concl th),NEG_REWRITE_HCONV th)) neg_rewrites)
  nil_term_net;;

let mk_RLCONV_nets thl =
let pos_rewrites,neg_rewrites = mk_RL_imp_rewrites thl in
 itlist
  enter_term
  (map (\th. (rand (rator (concl th)),POS_REWRITE_HCONV th)) pos_rewrites)
  nil_term_net,
 itlist
  enter_term
  (map (\th. (rand(concl th),NEG_REWRITE_HCONV th)) neg_rewrites)
  nil_term_net;;

let mk_HCONV_nets thl =
let pos_rewrites,neg_rewrites = mk_HALF_imp_rewrites thl in
 itlist
  enter_term
  (map (\th. (rand (rator (concl th)),POS_REWRITE_HCONV th)) pos_rewrites)
  nil_term_net,
 itlist
  enter_term
  (map (\th. (rand(concl th),NEG_REWRITE_HCONV th)) neg_rewrites)
  nil_term_net;;

let basic_SYM_rewrites = map (\x. CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) x) basic_rewrites;;

let basic_hconv_nets = mk_HCONV_nets basic_rewrites
and basic_LRconv_nets = mk_LRCONV_nets basic_rewrites
and basic_RLconv_nets = mk_RLCONV_nets basic_SYM_rewrites
and nil_term_nets = nil_term_net, nil_term_net;;

letrec FIRST_HCONV h_cnvl t = ((hd h_cnvl) t)?(FIRST_HCONV (tl h_cnvl) t);;

let REWRITES_HCONV (posnet,negnet) sng tm =
  if sng then FIRST_HCONV (lookup_term posnet tm) tm
  else FIRST_HCONV (lookup_term negnet tm) tm;;

let GEN_REWRITE_HCONV mk_nets TERM_WALK_HCONV (basic_pos_net,basic_neg_net) thml =
let a,b = mk_nets thml in
TERM_WALK_HCONV (REWRITES_HCONV (merge_term_nets a basic_pos_net,
                                 merge_term_nets b basic_neg_net));;

let REWRITE_HCONV = GEN_REWRITE_HCONV mk_HCONV_nets TOP_DEPTH_HCONV basic_hconv_nets 
and PURE_REWRITE_HCONV = GEN_REWRITE_HCONV mk_HCONV_nets TOP_DEPTH_HCONV nil_term_nets
and ONCE_REWRITE_HCONV = GEN_REWRITE_HCONV mk_HCONV_nets ONCE_DEPTH_HCONV basic_hconv_nets
and PURE_ONCE_REWRITE_HCONV = GEN_REWRITE_HCONV mk_HCONV_nets ONCE_DEPTH_HCONV nil_term_nets
and REWRITE_LRCONV = GEN_REWRITE_HCONV mk_LRCONV_nets TOP_DEPTH_HCONV basic_LRconv_nets 
and PURE_REWRITE_LRCONV = GEN_REWRITE_HCONV mk_LRCONV_nets TOP_DEPTH_HCONV nil_term_nets
and ONCE_REWRITE_LRCONV = GEN_REWRITE_HCONV mk_LRCONV_nets ONCE_DEPTH_HCONV basic_LRconv_nets
and PURE_ONCE_REWRITE_LRCONV = GEN_REWRITE_HCONV mk_LRCONV_nets ONCE_DEPTH_HCONV nil_term_nets
and REWRITE_RLCONV = GEN_REWRITE_HCONV mk_RLCONV_nets TOP_DEPTH_HCONV basic_RLconv_nets 
and PURE_REWRITE_RLCONV = GEN_REWRITE_HCONV mk_RLCONV_nets TOP_DEPTH_HCONV nil_term_nets
and ONCE_REWRITE_RLCONV = GEN_REWRITE_HCONV mk_RLCONV_nets ONCE_DEPTH_HCONV basic_RLconv_nets
and PURE_ONCE_REWRITE_RLCONV = GEN_REWRITE_HCONV mk_RLCONV_nets ONCE_DEPTH_HCONV nil_term_nets;;

let HCONV_TAC h_cnv (gl, g) = 
let thm = h_cnv false g in
if rand (rator (concl thm)) = "T"
then ([],\prf. MP thm TRUTH)
else MATCH_MP_TAC thm (gl, g);;

let HCONV_RULE h_cnv thm =
let thm' = h_cnv true (concl thm) in
MP thm' thm;;

%

These rewriting tactics all fail if no rewriting can be done.  This allows
easy failure-driven flow control.  If non-failing versions are required,
things like HALF_REWRITE_TAC [...] ORELSE ALL_TAC can be used.

%

let HALF_ONCE_REWRITE_TAC = HCONV_TAC o ONCE_REWRITE_HCONV
and HALF_REWRITE_TAC = HCONV_TAC o REWRITE_HCONV 
and HALF_PURE_ONCE_REWRITE_TAC = HCONV_TAC o PURE_ONCE_REWRITE_HCONV
and HALF_PURE_REWRITE_TAC = HCONV_TAC o PURE_REWRITE_HCONV
and HALF_ONCE_REWRITE_RULE = HCONV_RULE o ONCE_REWRITE_HCONV
and HALF_REWRITE_RULE =  HCONV_RULE o REWRITE_HCONV
and HALF_PURE_ONCE_REWRITE_RULE = HCONV_RULE o PURE_ONCE_REWRITE_HCONV
and HALF_PURE_REWRITE_RULE =  HCONV_RULE o PURE_REWRITE_HCONV
and LR_ONCE_REWRITE_TAC = HCONV_TAC o ONCE_REWRITE_LRCONV
and LR_REWRITE_TAC = HCONV_TAC o REWRITE_LRCONV 
and LR_PURE_ONCE_REWRITE_TAC = HCONV_TAC o PURE_ONCE_REWRITE_LRCONV
and LR_PURE_REWRITE_TAC = HCONV_TAC o PURE_REWRITE_LRCONV
and LR_ONCE_REWRITE_RULE = HCONV_RULE o ONCE_REWRITE_LRCONV
and LR_REWRITE_RULE =  HCONV_RULE o REWRITE_LRCONV
and LR_PURE_ONCE_REWRITE_RULE = HCONV_RULE o PURE_ONCE_REWRITE_LRCONV
and LR_PURE_REWRITE_RULE =  HCONV_RULE o PURE_REWRITE_LRCONV
and RL_ONCE_REWRITE_TAC = HCONV_TAC o ONCE_REWRITE_RLCONV
and RL_REWRITE_TAC = HCONV_TAC o REWRITE_RLCONV 
and RL_PURE_ONCE_REWRITE_TAC = HCONV_TAC o PURE_ONCE_REWRITE_RLCONV
and RL_PURE_REWRITE_TAC = HCONV_TAC o PURE_REWRITE_RLCONV
and RL_ONCE_REWRITE_RULE = HCONV_RULE o ONCE_REWRITE_RLCONV
and RL_REWRITE_RULE =  HCONV_RULE o REWRITE_RLCONV
and RL_PURE_ONCE_REWRITE_RULE = HCONV_RULE o PURE_ONCE_REWRITE_RLCONV
and RL_PURE_REWRITE_RULE =  HCONV_RULE o PURE_REWRITE_RLCONV;;

let HALF_ONCE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. HALF_ONCE_REWRITE_TAC (thml@asl))
and HALF_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. HALF_REWRITE_TAC (thml@asl))
and HALF_PURE_ONCE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. HALF_PURE_ONCE_REWRITE_TAC (thml@asl))
and HALF_PURE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. HALF_PURE_REWRITE_TAC (thml@asl))
and LR_ONCE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. LR_ONCE_REWRITE_TAC (thml@asl))
and LR_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. LR_REWRITE_TAC (thml@asl))
and LR_PURE_ONCE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. LR_PURE_ONCE_REWRITE_TAC (thml@asl))
and LR_PURE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. LR_PURE_REWRITE_TAC (thml@asl))
and RL_ONCE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. RL_ONCE_REWRITE_TAC (thml@asl))
and RL_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. RL_REWRITE_TAC (thml@asl))
and RL_PURE_ONCE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. RL_PURE_ONCE_REWRITE_TAC (thml@asl))
and RL_PURE_ASM_REWRITE_TAC thml = ASSUM_LIST (\asl. RL_PURE_REWRITE_TAC (thml@asl));;

(THENHC,
HALF_THEN,
HALF_THENTRY,
ALL_HCONV,
NO_HCONV,
HALF_TRY_BOTH,
REPEATHC,
CONJ1_HCONV,
CONJ2_HCONV,
DISJ1_HCONV,
DISJ2_HCONV,
IMP1_HCONV,
IMP2_HCONV,
COND1_HCONV,
COND2_HCONV,
FORALL_HCONV,
EXISTS_HCONV,
NEG_HCONV,
SUBTERMS_HCONV,
TOP_DOWN_HCONV,
BOTTOM_UP_HCONV,
ONCE_DEPTH_HCONV,
HALF_ONCE_OR_MORE,
TOP_DEPTH_HCONV,
REWRITE_HCONV,
PURE_REWRITE_HCONV,
ONCE_REWRITE_HCONV,
PURE_ONCE_REWRITE_HCONV,
REWRITE_LRCONV,
PURE_REWRITE_LRCONV,
ONCE_REWRITE_LRCONV,
PURE_ONCE_REWRITE_LRCONV,
REWRITE_RLCONV,
PURE_REWRITE_RLCONV,
ONCE_REWRITE_RLCONV,
PURE_ONCE_REWRITE_RLCONV,
HCONV_TAC,
HCONV_RULE,
HALF_ONCE_REWRITE_TAC,
HALF_REWRITE_TAC,
HALF_PURE_ONCE_REWRITE_TAC,
HALF_PURE_REWRITE_TAC,
HALF_ONCE_REWRITE_RULE,
HALF_REWRITE_RULE,
HALF_PURE_ONCE_REWRITE_RULE,
HALF_PURE_REWRITE_RULE,
LR_ONCE_REWRITE_TAC,
LR_REWRITE_TAC,
LR_PURE_ONCE_REWRITE_TAC,
LR_PURE_REWRITE_TAC,
LR_ONCE_REWRITE_RULE,
LR_REWRITE_RULE,
LR_PURE_ONCE_REWRITE_RULE,
LR_PURE_REWRITE_RULE,
RL_ONCE_REWRITE_TAC,
RL_REWRITE_TAC,
RL_PURE_ONCE_REWRITE_TAC,
RL_PURE_REWRITE_TAC,
RL_ONCE_REWRITE_RULE,
RL_REWRITE_RULE,
RL_PURE_ONCE_REWRITE_RULE,
RL_PURE_REWRITE_RULE,
HALF_ONCE_ASM_REWRITE_TAC,
HALF_ASM_REWRITE_TAC,
HALF_PURE_ONCE_ASM_REWRITE_TAC,
HALF_PURE_ASM_REWRITE_TAC,
LR_ONCE_ASM_REWRITE_TAC,
LR_ASM_REWRITE_TAC,
LR_PURE_ONCE_ASM_REWRITE_TAC,
LR_PURE_ASM_REWRITE_TAC,
RL_ONCE_ASM_REWRITE_TAC,
RL_ASM_REWRITE_TAC,
RL_PURE_ONCE_ASM_REWRITE_TAC,
RL_PURE_ASM_REWRITE_TAC);;

end_section half;;

let (THENHC,
HALF_THEN,
HALF_THENTRY,
ALL_HCONV,
NO_HCONV,
HALF_TRY_BOTH,
REPEATHC,
CONJ1_HCONV,
CONJ2_HCONV,
DISJ1_HCONV,
DISJ2_HCONV,
IMP1_HCONV,
IMP2_HCONV,
COND1_HCONV,
COND2_HCONV,
FORALL_HCONV,
EXISTS_HCONV,
NEG_HCONV,
SUBTERMS_HCONV,
TOP_DOWN_HCONV,
BOTTOM_UP_HCONV,
ONCE_DEPTH_HCONV,
HALF_ONCE_OR_MORE,
TOP_DEPTH_HCONV,
REWRITE_HCONV,
PURE_REWRITE_HCONV,
ONCE_REWRITE_HCONV,
PURE_ONCE_REWRITE_HCONV,
REWRITE_LRCONV,
PURE_REWRITE_LRCONV,
ONCE_REWRITE_LRCONV,
PURE_ONCE_REWRITE_LRCONV,
REWRITE_RLCONV,
PURE_REWRITE_RLCONV,
ONCE_REWRITE_RLCONV,
PURE_ONCE_REWRITE_RLCONV,
HCONV_TAC,
HCONV_RULE,
HALF_ONCE_REWRITE_TAC,
HALF_REWRITE_TAC,
HALF_PURE_ONCE_REWRITE_TAC,
HALF_PURE_REWRITE_TAC,
HALF_ONCE_REWRITE_RULE,
HALF_REWRITE_RULE,
HALF_PURE_ONCE_REWRITE_RULE,
HALF_PURE_REWRITE_RULE,
LR_ONCE_REWRITE_TAC,
LR_REWRITE_TAC,
LR_PURE_ONCE_REWRITE_TAC,
LR_PURE_REWRITE_TAC,
LR_ONCE_REWRITE_RULE,
LR_REWRITE_RULE,
LR_PURE_ONCE_REWRITE_RULE,
LR_PURE_REWRITE_RULE,
RL_ONCE_REWRITE_TAC,
RL_REWRITE_TAC,
RL_PURE_ONCE_REWRITE_TAC,
RL_PURE_REWRITE_TAC,
RL_ONCE_REWRITE_RULE,
RL_REWRITE_RULE,
RL_PURE_ONCE_REWRITE_RULE,
RL_PURE_REWRITE_RULE,
HALF_ONCE_ASM_REWRITE_TAC,
HALF_ASM_REWRITE_TAC,
HALF_PURE_ONCE_ASM_REWRITE_TAC,
HALF_PURE_ASM_REWRITE_TAC,
LR_ONCE_ASM_REWRITE_TAC,
LR_ASM_REWRITE_TAC,
LR_PURE_ONCE_ASM_REWRITE_TAC,
LR_PURE_ASM_REWRITE_TAC,
RL_ONCE_ASM_REWRITE_TAC,
RL_ASM_REWRITE_TAC,
RL_PURE_ONCE_ASM_REWRITE_TAC,
RL_PURE_ASM_REWRITE_TAC) = it;;


let DRAW_IMP_RULE thm =
  let thm' = SPEC_ALL thm in
  let a = rand (rator (concl thm')) in
  GEN_ALL (DISCH a (CONJ (ASSUME a) (MP thm' (ASSUME a))));;
