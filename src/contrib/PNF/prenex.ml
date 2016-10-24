%-------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------%
%------                                                                   ------%
%------                        PRENEX NORMAL FORMS                        ------%
%------                                                                   ------%
%------                                 by                                ------%
%------                                                                   ------%
%------                            Clive Jervis                           ------%
%------                             (SD-Scicon)                           ------%
%------                                                                   ------%
%------                              Jan. 1990                            ------%
%------                                                                   ------%
%-------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------%

%
This file contains a conversion, rule, and tactic for automatically generating
prenex normal form terms equivalent to given ones. In addition, it has other
conversions related to manipulating universal and existential quantifiers. Some
of these are new versions of existing conversions that have been reimplemented
because of bugs discovered in the originals.

The prenex normal form is defined on terms constructed from the propositional
connectives /\, \/, ~, and ==>, and the universal and existential quantifiers.
Terms built using <=> and unique existence (?!), &c., would first have to be
rewritten into symbols from the previous list for prenex normal forms to apply.

By choice, the conversions &c. only work at the outermost level of logical
connectives, by which we mean that sub-terms are not put into normal form if
they form part of an argument to a function not included in the above list. For
example, suppose we have the term t built from the logical connectives mentioned
above. Then the terms t and ~t can each be put into prenex normal form by our
conversions, &c., whereas the term f(t) will not. However, it is simple enough
to use REDEPTH_CONV family of conversions to achieve this if required.

The code should be fairly efficient - each basic conversion being made by
instantiating a template theorem - and robust, with traps (`fatal' error
messages) to signal when a conversion has failed because I've got the code
wrong! The template theorems are defined in the theory `quant.th', which is
automatically called when this file is loaded.

We list the more important definitions found below:

SWAP_FORALL_CONV
    A conversion for swapping the order of two universal quantifiers.

SWAP_EXISTS_CONV
    A reimplementation of the conversion for swapping the order of two
    existential quantifiers.

EXISTS_DISTRIB_CONV
    A conversion exploiting the disributiveness of existential quantification
    through disjunction.

FORALL_DISTRIB_CONV
    A conversion exploiting the disributiveness of universal quantification
    through conjunction.

NOT_EXISTS_CONV
    A reimplementation of the conversion for pushing a negation through
    an existential quantifier.
    
NOT_FORALL_CONV
    A reimplementation of the conversion for pushing a negation through
    a universal quantifier.

PRENEX_CONV
    A conversion for converting a term into prenex normal form.

PRENEX_TAC
    A tactic for converting a goal into prenex normal form.

PRENEX_RULE
    A rule for converting a theorem into prenex normal form.

This code was developed in part with my previous employers, ICL Defence Systems,
and in part with my current employers, SD-Scicon.
%

%--------------------------------------------------------------------------------

Load up the template theorems from the theory `quant', which is made into a new
parent if it is not already one. 
%

if draft_mode() & not( mem `quant` (parents `-`)) then
  new_parent `quant`
else
  load_theory `quant`;;

load_theorems `quant`;;

%--------------------------------------------------------------------------------

CASES_TAC: term -> tactic

Given a term t, the tactic CASES_TAC t splits the current goal into two
subgoals, one with t as an assumption and the other with ~t; it then rewrites
these subgoals with their new assumptions. This is useful when doing a case
analysis on the current goal in which one of the cases makes the goal true.
Hence, it effectively discharges this case to the assumption list.

A bit more delicate than ASM_CASES_TAC t THEN ASM_REWRITE_TAC[].
%

let CASES_TAC t =
    ASM_CASES_TAC t THENL[ REWRITE_TAC[ASSUME t]; REWRITE_TAC[ASSUME(mk_neg t)] ];;

%--------------------------------------------------------------------------------

back: num -> void

The function back is a generalised form of backup, in that it backs up the goal
stack the number of steps given by a numerical argument. Thus, back 1 is the
equivalent of backup(), and back 0 has no effect. As with back, the number of
backups that can be done is limited.
%

letrec back n = if n=0 then () else (backup();back(n-1));;

%--------------------------------------------------------------------------------

SWAP_FORALL_CONV: conv

The conversion SWAP_FORALL_CONV is used to reverse the order of two universally
quantified variables.

    SWAP_FORALL_CONV "!x y.t" ---->
    |- !x y.t = !y x.t
%

let SWAP_FORALL_CONV: conv = \ q .
  let x,t = (dest_forall q)?failwith `FORALL_SYM_CONV: term not universally quantified` in
  let y,r = (dest_forall t)?failwith `FORALL_SYM_CONV: term not universally quantified twice` in
  let p   = "! ^y ^x . ^r" in
    let t1 = (DISCH_ALL o GENL[y;x] o SPECL[x;y])(ASSUME q) in
    let t2 = (DISCH_ALL o GENL[x;y] o SPECL[y;x])(ASSUME p) in
  IMP_ANTISYM_RULE t1 t2;;

%-------------------------------------------------------------------------------

SWAP_EXISTS_CONV: conv

The conversion SWAP_EXISTS_CONV is used to reverse the order of two existentially
quantified variables. This is a reimplemented version of the provided
SWAP_EXISTS_CONV, which was found to fail if the supplied term had more than two 
existential quantifiers.

    SWAP_EXISTS_CONV "?x y.t" ---->
    |- ?x y.t = ?y x.t
%

let SWAP_EXISTS_CONV: conv = \ q .
  let x,t = (dest_exists q)?failwith `EXISTS_SYM_CONV: term not existentially quantified` in
  let y,r = (dest_exists t)?failwith `EXISTS_SYM_CONV: term not existentially quantified twice` in
  let p   = "? ^y ^x . ^r" in
    let thm1 = (SELECT_RULE o SELECT_RULE)(ASSUME q) in
    let t1 = mk_select(x,t) in
    let t2 = subst[ t1, x ] t in
    let t3 = mk_select(dest_exists t2) in
    let t4 = subst[ t3, y ] r in
    let thm2 = EXISTS( mk_exists(x,t4), t1 )thm1 in
    let thm3 = DISCH_ALL( EXISTS( p, t3 )thm2 ) in
    let thm4 = (SELECT_RULE o SELECT_RULE)(ASSUME p) in
    let s1 = mk_select(y,mk_exists(x,r)) in
    let s2 = subst[ s1, y ](mk_exists(x,r)) in
    let s3 = mk_select(dest_exists s2) in
    let s4 = subst[ s3, x ] r in
    let thm5 = EXISTS( mk_exists(y,s4), s1 )thm4 in
    let thm6 = DISCH_ALL( EXISTS( q, s3 )thm5 ) in
  IMP_ANTISYM_RULE thm3 thm6;;

%-------------------------------------------------------------------------------

is_true_imp: term -> bool

The function is_true_imp is true if the argument term is an implication, and
false otherwise. This is to be distinguished from the system function true_imp
that is also true of a negation (in which ~t is treated as F ==> t).
%

let is_true_imp t = (is_imp t)& not(is_neg t);;

%-------------------------------------------------------------------------------

is_true_imp: term -> (term # term)

The function true_dest_imp destructs an implication into its two terms, and
fails if it is not an implication. This is to be distinguished from the system
function true_dest_imp that will also destruct a negation (in which ~t is
treated as F ==> t).

%
let true_dest_imp t =
  if is_neg t then failwith `true_dest_imp: term is a negation`
  else dest_imp t;;

%-------------------------------------------------------------------------------

EXISTS_DISTRIB_CONV: term -> conv

The function EXISTS_DISTRIB_CONV is used to pull out an existential quantified
variable from the disjunction of two existentially quantified terms. The first
argument to the function is the variable (as a term) that will be the bound
variable in the result. The second argument is the term to be converted.

    EXISTS_DISTRIB_CONV "z" "(?x.p) \/ (?y.q)" ---->
    |- (?x.p) \/ (?y.q) = ?z. p \/ q

If the conversion fails due to an incorrect implementation, the function returns
a `fatal' error message.
%

let EXISTS_DISTRIB_CONV: term -> conv = \ z t .
  let id = `EXISTS_DISTRIB_CONV` in
  if not(is_var z) then
    failwith id^`: first term not a variable`
  else if mem z(frees t) then
    failwith id^`: variable is free in term`
  else
  let l,r  = (dest_disj t)?failwith id^`: term not a disjunction` in
  let x,p  = (dest_exists l)?failwith id^`: left sub-term not existentially quantified` in
  let y,q  = (dest_exists r)?failwith id^`: right sub-term not existentially quantified` in
  if not( type_of z = type_of x & type_of z = type_of y ) then
    failwith id^`: quantified variables not all of same type`
  else (
    let  xp  = mk_abs(x,p) in
    let  yq  = mk_abs(y,q) in
    let thm1 = SPECL[xp; yq](INST_TYPE[type_of z,":*"]EXISTS_DISTRIB) in
    let thml = BETA_CONV (mk_comb(xp,z)) in
    let thmr = BETA_CONV (mk_comb(yq,z)) in
     let p1,p2 = (dest_eq o concl)thml in
     let q1,q2 = (dest_eq o concl)thmr in
     let thm2 = SPECL[p2;q2;p1;q1]DISJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ z thm3 in
    TRANS thm1 thm4 ?
  failwith id^`: fatal`);;

%-------------------------------------------------------------------------------

FORALL_DISTRIB_CONV: term -> conv

The function FORALL_DISTRIB_CONV is used to pull out an universally quantified
variable from the conjunction of two existentially quantified terms. The first
argument to the function is the variable (as a term) that will be the bound
variable in the result. The second argument is the term to be converted.

    FORALL_DISTRIB_CONV "z" "(!x.p) /\ (!y.q)" ---->
    |- (!x.p) /\ (!y.q) = !z. p /\ q

If the conversion fails due to an incorrect implementation, the function returns
a `fatal' error message.
%

let FORALL_DISTRIB_CONV: term -> conv = \ z t .
  let id = `FORALL_DISTRIB_CONV` in
  if not(is_var z) then
    failwith id^`: first term not a variable`
  else if mem z(frees t) then
    failwith id^`: variable is free in term`
  else
  let l,r  = (dest_conj t)?failwith id^`: term not a conjunction` in
  let x,p  = (dest_forall l)?failwith id^`: left sub-term not universally quantified` in
  let y,q  = (dest_forall r)?failwith id^`: right sub-term not universally quantified` in
  if not( type_of z = type_of x & type_of z = type_of y ) then
    failwith id^`: quantified variables not all of same type`
  else (
    let  xp  = mk_abs(x,p) in
    let  yq  = mk_abs(y,q) in
    let thm1 = SPECL[xp; yq](INST_TYPE[type_of z,":*"]FORALL_DISTRIB) in
    let thml = BETA_CONV (mk_comb(xp,z)) in
    let thmr = BETA_CONV (mk_comb(yq,z)) in
     let p1,p2 = (dest_eq o concl)thml in
     let q1,q2 = (dest_eq o concl)thmr in
     let thm2 = SPECL[p2;q2;p1;q1]CONJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ z thm3 in
    TRANS thm1 thm4 ?
  failwith id^`: fatal`);;

%-------------------------------------------------------------------------------

NOT_EXISTS_CONV: conv

The conversion NOT_EXISTS_CONV is used to push a negation through an existential
quantifier. This is a reimplemented version of the system's NOT_EXISTS_CONV,
which was found to fail when the bound variable did not appear free in the scope of the quantifier

    NOT_EXISTS_CONV "~?x.p" ---->
    |- ~?x.p = !x.~p

If the conversion fails due to an incorrect implementation, the function returns
a `fatal' error message.
%

let NOT_EXISTS_CONV: conv = \ q .
  let id = `NOT_EXISTS_CONV` in
  let t  = (dest_neg q)?failwith id^`: term not negation` in
  let x,p  = (dest_exists t)?failwith id^`: sub-term not existentially quantified` in (
    let  xp  = mk_abs(x,p) in
    let thm1 = SPECL[xp](INST_TYPE[type_of x,":*"]NOT_EXISTS_THM) in
    let thm2 = BETA_CONV (mk_comb(xp,x)) in
    let thm3 = FORALL_EQ x(AP_TERM "$~" thm2) in
    TRANS thm1 thm3) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

NOT_FORALL_CONV: conv

The conversion NOT_FORALL_CONV is used to push a negation through an existential
quantifier. This is a reimplemented version of the system's NOT_FORALL_CONV,
which was found to fail when the bound variable did not appear free in the scope
of the quantifier.

    NOT_FORALL_CONV "~!x.p" ---->
    |- ~!x.p = ?x.~p

If the conversion fails due to an incorrect implementation, the function returns 
a `fatal' error message.
%

let NOT_FORALL_CONV: conv = \ q .
  let id = `NOT_FORALL_CONV` in
  let t  = (dest_neg q)?failwith id^`: term not negation` in
  let x,p  = (dest_forall t)?failwith id^`: sub-term not universally quantified` in (
    let  xp  = mk_abs(x,p) in
    let thm1 = SPECL[xp](INST_TYPE[type_of x,":*"]NOT_FORALL_THM) in
    let thm2 = BETA_CONV (mk_comb(xp,x)) in
    let thm3 = EXISTS_EQ x(AP_TERM "$~" thm2) in
    TRANS thm1 thm3) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

L_DISJ_EXISTS_CONV: conv
R_DISJ_EXISTS_CONV: conv

The conversions L_DISJ_EXISTS_CONV and R_DISJ_EXISTS_CONV are used to move an
existential quantifier from the left and right terms of a disjunction,
respectively, out to the whole term. The bound variable will be renamed if it
appears free in the other sub-term.

    L_DISJ_EXISTS_CONV "(?x.p) \/ q" ---->
    |- (?x.p) \/ q = ?x. p \/ q

    R_DISJ_EXISTS_CONV "p \/ (?x.q)" ---->
    |- p \/ (?x.q) = ?x. p \/ q

If the conversions fail due to incorrect implementation, the functions return
`fatal' error messages.
%

let L_DISJ_EXISTS_CONV: conv = \ q .
  let id = `L_DISJ_EXISTS_CONV` in
  let t,r  = (dest_disj q)?failwith id^`: term not disjunction` in
  let x,l  = (dest_exists t)?failwith id^`: left term not existentially quantified` in (
    let  x'  = variant(union(frees r)(subtract(frees l)[x]))x in
    let  xl  = mk_abs(x,l) in
    let thm1 = SPECL[r;xl](INST_TYPE[type_of x,":*"]L_DISJ_EXISTS_THM) in
    let thml = BETA_CONV (mk_comb(xl,x')) in
    let thmr = REFL r in
    let  l'  = (rhs o concl)thml in
    let thm2 = SPECL[l';r;mk_comb(xl,x');r]DISJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

let R_DISJ_EXISTS_CONV: conv = \ q .
  let id = `R_DISJ_EXISTS_CONV` in
  let l,t  = (dest_disj q)?failwith id^`: term not disjunction` in
  let x,r  = (dest_exists t)?failwith id^`: right term not existentially quantified` in (
    let  x'  = variant(union(frees l)(subtract(frees r)[x]))x in
    let  xr  = mk_abs(x,r) in
    let thm1 = SPECL[l;xr](INST_TYPE[type_of x,":*"]R_DISJ_EXISTS_THM) in
    let thml = REFL l in
    let thmr = BETA_CONV (mk_comb(xr,x')) in
    let  r'  = (rhs o concl)thmr in
    let thm2 = SPECL[l;r';l;mk_comb(xr,x')]DISJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

L_DISJ_FORALL_CONV: conv
R_DISJ_FORALL_CONV: conv

The conversions L_DISJ_FORALL_CONV and R_DISJ_FORALL_CONV are used to move a
universal quantifier from the left and right terms of a disjunction,
respectively, out to the whole term. The bound variable will be renamed if it
appears free in the other sub-term.

    L_DISJ_FORALL_CONV "(!x.p) \/ q" ---->
    |- (!x.p) \/ q = !x. p \/ q

    R_DISJ_FORALL_CONV "p \/ (!x.q)" ---->
    |- p \/ (!x.q) = !x. p \/ q

If the conversions fail due to incorrect implementation, the functions return
`fatal' error messages.
%

let L_DISJ_FORALL_CONV: conv = \ q .
  let id = `L_DISJ_FORALL_CONV` in
  let t,r  = (dest_disj q)?failwith id^`: term not disjunction` in
  let x,l  = (dest_forall t)?failwith id^`: left term not universally quantified` in (
    let  x'  = variant(union(frees r)(subtract(frees l)[x]))x in
    let  xl  = mk_abs(x,l) in
    let thm1 = SPECL[r;xl](INST_TYPE[type_of x,":*"]L_DISJ_FORALL_THM) in
    let thml = BETA_CONV (mk_comb(xl,x')) in
    let thmr = REFL r in
    let  l'  = (rhs o concl)thml in
    let thm2 = SPECL[l';r;mk_comb(xl,x');r](INST_TYPE[type_of x,":*"]DISJ_EQ) in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

let R_DISJ_FORALL_CONV: conv = \ q .
  let id = `R_DISJ_FORALL_CONV` in (
    let l,t  = (dest_disj q)?failwith id^`: term not disjunction` in
    let x,r  = (dest_forall t)?failwith id^`: right term not universally quantified` in
    let  x'  = variant(union(frees l)(subtract(frees r)[x]))x in
    let  xr  = mk_abs(x,r) in
    let thm1 = SPECL[l;xr](INST_TYPE[type_of x,":*"]R_DISJ_FORALL_THM) in
    let thml = REFL l in
    let thmr = BETA_CONV (mk_comb(xr,x')) in
    let  r'  = (rhs o concl)thmr in
    let thm2 = SPECL[l;r';l;mk_comb(xr,x');]DISJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

L_CONJ_EXISTS_CONV: conv
R_CONJ_EXISTS_CONV: conv

The conversions L_CONJ_EXISTS_CONV and R_CONJ_EXISTS_CONV are used to move an
existential quantifier from the left and right terms of a conjunction,
respectively, out to the whole term. The bound variable will be renamed if it
appears free in the other sub-term.

    L_CONJ_EXISTS_CONV "(?x.p) /\ q" ---->
    |- (?x.p) /\ q = ?x. p /\ q

    R_CONJ_EXISTS_CONV "p /\ (?x.q)" ---->
    |- p /\ (?x.q) = ?x. p /\ q

If the conversions fail due to incorrect implementation, the functions return
`fatal' error messages.
%

let L_CONJ_EXISTS_CONV: conv = \ q .
  let id = `L_DISJ_EXISTS_CONV` in
  let t,r  = (dest_conj q)?failwith id^`: term not conjunction` in
  let x,l  = (dest_exists t)?failwith id^`: left term not existentially quantified` in (
    let  x'  = variant(union(frees r)(subtract(frees l)[x]))x in
    let  xl  = mk_abs(x,l) in
    let thm1 = SPECL[r;xl](INST_TYPE[type_of x,":*"]L_CONJ_EXISTS_THM) in
    let thml = BETA_CONV (mk_comb(xl,x')) in
    let thmr = REFL r in
    let  l'  = (rhs o concl)thml in
    let thm2 = SPECL[l';r;mk_comb(xl,x');r]CONJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

let R_CONJ_EXISTS_CONV: conv = \ q .
  let id = `R_DISJ_EXISTS_CONV` in
  let l,t  = (dest_conj q)?failwith id^`: term not conjunction` in
  let x,r  = (dest_exists t)?failwith id^`: right term not existentially quantified` in (
    let  x'  = variant(union(frees l)(subtract(frees r)[x]))x in
    let  xr  = mk_abs(x,r) in
    let thm1 = SPECL[l;xr](INST_TYPE[type_of x,":*"]R_CONJ_EXISTS_THM) in
    let thml = REFL l in
    let thmr = BETA_CONV (mk_comb(xr,x')) in
    let  r'  = (rhs o concl)thmr in
    let thm2 = SPECL[l;r';l;mk_comb(xr,x')](INST_TYPE[type_of x,":*"]CONJ_EQ) in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

L_CONJ_FORALL_CONV: conv
R_CONJ_FORALL_CONV: conv

The conversions L_CONJ_FORALL_CONV and R_CONJ_FORALL_CONV are used to move an
universal quantifier from the left and right terms of a disjunction,
respectively, out to the whole term. The bound variable will be renamed if it
appears free in the other sub-term.

    L_CONJ_FORALL_CONV "(!x.p) /\ q" ---->
    |- (!x.p) /\ q = !x. p /\ q

    R_CONJ_FORALL_CONV "p /\ (!x.q)" ---->
    |- p /\ (!x.q) = !x. p /\ q

If the conversions fail due to incorrect implementation, the functions return
`fatal' error messages.
%

let L_CONJ_FORALL_CONV: conv = \ q .
  let id = `L_DISJ_FORALL_CONV` in
  let t,r  = (dest_conj q)?failwith id^`: term not conjunction` in
  let x,l  = (dest_forall t)?failwith id^`: left term not universally quantified` in (
    let  x'  = variant(union(frees r)(subtract(frees l)[x]))x in
    let  xl  = mk_abs(x,l) in
    let thm1 = SPECL[r;xl](INST_TYPE[type_of x,":*"]L_CONJ_FORALL_THM) in
    let thml = BETA_CONV (mk_comb(xl,x')) in
    let thmr = REFL r in
    let  l'  = (rhs o concl)thml in
    let thm2 = SPECL[l';r;mk_comb(xl,x');r]CONJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

let R_CONJ_FORALL_CONV: conv = \ q .
  let id = `R_DISJ_FORALL_CONV` in
  let l,t  = (dest_conj q)?failwith id^`: term not conjunction` in
  let x,r  = (dest_forall t)?failwith id^`: right term not universally quantified` in (
    let  x'  = variant(union(frees l)(subtract(frees r)[x]))x in
    let  xr  = mk_abs(x,r) in
    let thm1 = SPECL[l;xr](INST_TYPE[type_of x,":*"]R_CONJ_FORALL_THM) in
    let thml = REFL l in
    let thmr = BETA_CONV (mk_comb(xr,x')) in
    let  r'  = (rhs o concl)thmr in
    let thm2 = SPECL[l;r';l;mk_comb(xr,x')]CONJ_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

L_IMP_EXISTS_CONV: conv

The conversion L_IMP_EXISTS_CONV is used to move an existential quantifier on
the left hand side of an implication out into a universal quantifier whose
scope is the the whole implication. The bound variable will be renamed if it
appears free on the right hand side of the implication.

    L_IMP_EXISTS_CONV "(?x.p) ==> q" ---->
    |- !x. p ==> q

If the conversion fails due to an incorrect implementation, then a `fatal'
error message is given.
%

let L_IMP_EXISTS_CONV: conv = \ q .
  let id = `L_IMP_EXISTS_CONV` in
  let t,r  = (true_dest_imp q)?failwith id^`: term not implication` in
  let x,l  = (dest_exists t)?failwith id^`: left term not existentially quantified` in (
    let  x'  = variant(union(frees r)(subtract(frees l)[x]))x in
    let  xl  = mk_abs(x,l) in
    let thm1 = SPECL[r;xl](INST_TYPE[type_of x,":*"]L_IMP_EXISTS_THM) in
    let thml = BETA_CONV (mk_comb(xl,x')) in
    let thmr = REFL r in
    let  l'  = (rhs o concl)thml in
    let thm2 = SPECL[l';r;mk_comb(xl,x');r]IMP_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

R_IMP_EXISTS_CONV: conv

The conversion R_IMP_EXISTS_CONV is used to move an existential quantifier on
the right hand side of an implication out to cover the whole term. The bound
variable will be renamed if it appears free on the left hand side of the
implication.

   R_IMP_EXISTS_CONV "p ==> (?x.q)" ---->
    |- ?x. p ==> q

If the conversion fails due to an incorrect implementation, then a `fatal'
error message is given.
%

let R_IMP_EXISTS_CONV: conv = \ q .
  let id = `R_IMP_EXISTS_CONV` in
  let l,t  = (true_dest_imp q)?failwith id^`: term not implication` in
  let x,r  = (dest_exists t)?failwith id^`: right term not existentially quantified` in (
    let  x'  = variant(union(frees l)(subtract(frees r)[x]))x in
    let  xr  = mk_abs(x,r) in
    let thm1 = SPECL[l;xr](INST_TYPE[type_of x,":*"]R_IMP_EXISTS_THM) in
    let thml = REFL l in
    let thmr = BETA_CONV (mk_comb(xr,x')) in
    let  r'  = (rhs o concl)thmr in
    let thm2 = SPECL[l;r';l;mk_comb(xr,x')]IMP_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

L_IMP_FORALL_CONV: conv

The conversion L_IMP_FORALL_CONV is used to move a universal quantifier on the
left hand side of an implication out to an existential quantifier whose scope
is the whole term. The bound variable will be renamed if it appears free on the
right hand side of the implication.

    L_IMP_FORALL_CONV "(!x.p) ==> q" ---->
    |- ?x. p ==> q

If the conversion fails due to an incorrect implementation, then a `fatal'
error message is given.
%

let L_IMP_FORALL_CONV: conv = \ q .
  let id = `L_IMP_FORALL_CONV` in
  let t,r  = (true_dest_imp q)?failwith id^`: term not implication` in
  let x,l  = (dest_forall t)?failwith id^`: left term not universally quantified` in (
    let  x'  = variant(union(frees r)(subtract(frees l)[x]))x in
    let  xl  = mk_abs(x,l) in
    let thm1 = SPECL[r;xl](INST_TYPE[type_of x,":*"]L_IMP_FORALL_THM) in
    let thml = BETA_CONV (mk_comb(xl,x')) in
    let thmr = REFL r in
    let  l'  = (rhs o concl)thml in
    let thm2 = SPECL[l';r;mk_comb(xl,x');r]IMP_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = EXISTS_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

R_IMP_FORALL_CONV: conv

The conversion R_IMP_FORALL_CONV is used to move an universal quantifier on the
right hand side of an implication out to cover the whole term. The bound
variable will be renamed if it appears free on the left hand side of the
implication.

    R_IMP_FORALL_CONV "p ==> (!x.q)" ---->
    |- !x. p ==> "

If the conversion fails due to an incorrect implementation, then a `fatal'
error message is given.
%

let R_IMP_FORALL_CONV: conv = \ q .
  let id = `R_IMP_FORALL_CONV` in (
    let l,t  = (true_dest_imp q)?failwith id^`: term not implication` in
    let x,r  = (dest_forall t)?failwith id^`: right term not universally quantified` in
    let  x'  = variant(union(frees l)(subtract(frees r)[x]))x in
    let  xr  = mk_abs(x,r) in
    let thm1 = SPECL[l;xr](INST_TYPE[type_of x,":*"]R_IMP_FORALL_THM) in
    let thml = REFL l in
    let thmr = BETA_CONV (mk_comb(xr,x')) in
    let  r'  = (rhs o concl)thmr in
    let thm2 = SPECL[l;r';l;mk_comb(xr,x')]IMP_EQ in
    let thm3 = MP(MP thm2 thml)thmr in
    let thm4 = FORALL_EQ x' thm3 in
    TRANS thm1 thm4 ) ?
  failwith id^`: fatal`;;

%-------------------------------------------------------------------------------

NOT_PRENEX_CONV: conv

The conversion NOT_PRENEX_CONV is used to pull a series of quantifiers through
a negation (or equally push a negation through a series of quantifiers). If the
argument term is not a negation then the conversion fails, and if the sub-term
of the negation is not quantified then ALL_CONV is applied, otherwise
NOT_EXISTS_CONV or NOT_FORALL_CONV are recursively applied as appropriate.

    NOT_PRENEX_CONV "~ Q1 x1. Q2 x2. ... Qn xn. p" ---->
    |- ~ Q1 x1. Q2 x2. ... Qn xn. p = Q1' x1. Q2' x2. ... Qn' xn. ~ p

Where  Qi' is a universal quantifier if Qi is an existential quantifier, and
Qi' is an existential quantifier if Qi is universal quantifier, for each i=1...n.

Its use is in converting a negated prenex normal form formula back into prenex
normal form.
%

letrec NOT_PRENEX_CONV: conv = \ q .
  let id = `NOT_PRENEX_CONV` in
  if is_neg q then
    let p = dest_neg q in
    if is_exists p then
      let thm1 = NOT_EXISTS_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = NOT_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall p then
      let thm1 = NOT_FORALL_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = NOT_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else ALL_CONV q
  else failwith id^`:term not a negation`;;

%-------------------------------------------------------------------------------

CONJ_PRENEX_CONV: conv

The conversion CONJ_PRENEX_CONV is used to pull all quantifiers appearing on
either side of a conjunction back to cover the whole term. If the argument term
is not a conjunction then the conversion fails, and if the sub-terms of the
conjunction are not quantified then ALL_CONV is applied, otherwise
L_CONJ_EXISTS_CONV, L_CONJ_FORALL_CONV, R_CONJ_EXISTS_CONV, and
R_CONJ_FORALL_CONV, are recursively applied in that order as appropriate.

    CONJ_PRENEX_CONV "(Q1 x1. ... Qn xn. p) /\ (R1 y1. ... Rm ym. q)" ---->
    |- (Q1 x1. ... Qn xn. p) /\ (R1 y1. ... Rm ym. q)
       =
       Q1' x1. ... Qn' xn. R1'y1.  ... Rm' ym. p /\ q

Bound variables will be renamed when their new scope clashes with other free
variables.

Its use is in converting two conjuncted prenex normal form terms into prenex
normal form.
%

letrec CONJ_PRENEX_CONV: conv = \ q .
  let id = `CONJ_PRENEX_CONV` in
  if is_conj q then
    let l,r = dest_conj q in
    if is_exists l then
      let thm1 = L_CONJ_EXISTS_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = CONJ_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall l then
      let thm1 = L_CONJ_FORALL_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = CONJ_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else if is_exists r then
      let thm1 = R_CONJ_EXISTS_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = CONJ_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall r then
      let thm1 = R_CONJ_FORALL_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = CONJ_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else ALL_CONV q
  else failwith id^`:term not a conjunction`;;

%-------------------------------------------------------------------------------

DISJ_PRENEX_CONV: conv

The conversion DISJ_PRENEX_CONV is used to pull all quantifiers appearing on
either side of a disjunction back to cover the whole term. If the argument term
is not a disjunction then the conversion fails, and if the sub-terms of the
disjunction are not quantified then ALL_CONV is applied, otherwise
L_DISJ_EXISTS_CONV, L_DISJ_FORALL_CONV, R_DISJ_EXISTS_CONV, and
R_DISJ_FORALL_CONV, are recursively applied in that order as appropriate.

    DISJ_PRENEX_CONV "(Q1 x1. ... Qn xn. p) \/ (R1 y1. ... Rm ym. q)" ---->
    |- (Q1 x1. ... Qn xn. p) \/ (R1 y1. ... Rm ym. q)
       =
       Q1 x1. ... Qn xn. R1 y1.  ... Rm ym. p \/ q

Bound variables will be renamed when their new scope clashes with other free
variables.

Its use is in converting two disjuncted prenex normal form formulae into prenex
normal form.
%

letrec DISJ_PRENEX_CONV: conv = \ q .
  let id = `DISJ_PRENEX_CONV` in
  if is_disj q then
    let l,r = dest_disj q in
    if is_exists l then
      let thm1 = L_DISJ_EXISTS_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = DISJ_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall l then
      let thm1 = L_DISJ_FORALL_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = DISJ_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else if is_exists r then
      let thm1 = R_DISJ_EXISTS_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = DISJ_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall r then
      let thm1 = R_DISJ_FORALL_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = DISJ_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else ALL_CONV q
  else failwith id^`:term not a disjunction`;;

%-------------------------------------------------------------------------------

IMP_PRENEX_CONV: conv

The conversion IMP_PRENEX_CONV is used to pull all quantifiers appearing on
either side of an implication back to cover the whole term. If the argument
term is not an implication then the conversion fails, and if the sub-terms
of the implication are not quantified then ALL_CONV is applied, otherwise
L_IMP_EXISTS_CONV, L_IMP_FORALL_CONV, R_IMP_EXISTS_CONV, and
R_IMP_FORALL_CONV, are recursively applied in that order as appropriate.

    DISJ_PRENEX_CONV "(Q1 x1. ... Qn xn. p) ==> (R1 y1. ... Rm ym. q)" ---->
    |- (Q1 x1. ... Qn xn. p) ==> (R1 y1. ... Rm ym. q)
       =
       Q1' x1. ... Qn' xn. R1 y1.  ... Rm ym. p ==> q

Where  Qi' is a universal quantifier if Qi is an existential quantifier, and
Qi' is an existential quantifier if Qi is universal quantifier, for each
i=1...n.

Bound variables will be renamed when their new scope clashes with other free
variables.

Its use is in converting two prenex normal form formulae joined by an
implication back into prenex normal form.
%

letrec IMP_PRENEX_CONV: conv = \ q .
  let id = `IMP_PRENEX_CONV` in
  if is_true_imp q then
    let l,r = dest_imp q in
    if is_exists l then
      let thm1 = L_IMP_EXISTS_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = IMP_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall l then
      let thm1 = L_IMP_FORALL_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = IMP_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else if is_exists r then
      let thm1 = R_IMP_EXISTS_CONV q in
      let x,t  = (dest_exists o rhs o concl)thm1 in
      let thm2 = IMP_PRENEX_CONV t in
      let thm3 = EXISTS_EQ x thm2 in
      TRANS thm1 thm3
    else if is_forall r then
      let thm1 = R_IMP_FORALL_CONV q in
      let x,t  = (dest_forall o rhs o concl)thm1 in
      let thm2 = IMP_PRENEX_CONV t in
      let thm3 = FORALL_EQ x thm2 in
      TRANS thm1 thm3
    else ALL_CONV q
  else failwith id^`:term not an implication`;;

%-------------------------------------------------------------------------------

PRENEX_CONV: conv

The conversion PRENEX_CONV is used to convert a term into prenex normal form.
If the argument term is not of type ":bool" then the conversion fails.

The conversion recursively descends the term, and each time it encounters a
propositional connective applies the appropriate conversion from NOT_PRENEX_CONV,
CONJ_PRENEX_CONV, DISJ_PRENEX_CONV, and IMP_PRENEX_CONV, once its sub-terms have
been put into prenex normal form.


    PRENEX_CONV "p" ---->
    |- p = Q1 x1. ... Qn xn. q

Where each Qi for i=1...n, is a universal or existential quantifier and q is
constructed only from propositional connectives at the outermost level.

Bound variables will be renamed when their new scope clashes with other free
variables.

One bug in this implementation is that sometimes bound variables in the argument
term (in "p", above) will be renamed with primes for no good reason. This
happens in the instantiation of the theorems upon which the primitive
conversions of PRENEX_CONV are based.

If the conversion fails due to an incorrect implementation, then a `fatal'
error message is given.
%

letrec PRENEX_CONV: conv = \ q .
  let id = `PRENEX_CONV` in
  if not(type_of q = ":bool") then
    failwith id^`: type of term not boolean`
  else ( if is_exists q then
    let x,t  = dest_exists q in
    let thm1 = PRENEX_CONV t in
    EXISTS_EQ x thm1
  else if is_forall q then
    let x,t  = dest_forall q in
    let thm1 = PRENEX_CONV t in
    FORALL_EQ x thm1
  else if is_neg q then
    let    p = dest_neg q in
    let thm1 = PRENEX_CONV p in
    let thm2 = AP_TERM "$~" thm1 in
    let    t = (rhs o concl)thm2 in
    let thm3 = NOT_PRENEX_CONV t in
    TRANS thm2 thm3
  else if is_conj q then
    let  l,r = dest_conj q in
    let thml = PRENEX_CONV l in
    let thmr = PRENEX_CONV r in
    let   l' = (rhs o concl)thml in
    let   r' = (rhs o concl)thmr in
    let thm1 = MP(MP(SPECL[l';r';l;r]CONJ_EQ)thml)thmr in
    let    t = (rhs o concl)thm1 in
    let thm2 = CONJ_PRENEX_CONV t in
    TRANS thm1 thm2
  else if is_disj q then
    let  l,r = dest_disj q in
    let thml = PRENEX_CONV l in
    let thmr = PRENEX_CONV r in
    let   l' = (rhs o concl)thml in
    let   r' = (rhs o concl)thmr in
    let thm1 = MP(MP(SPECL[l';r';l;r]DISJ_EQ)thml)thmr in
    let    t = (rhs o concl)thm1 in
    let thm2 = DISJ_PRENEX_CONV t in
    TRANS thm1 thm2
  else if is_imp q then
    let  l,r = dest_imp q in
    let thml = PRENEX_CONV l in
    let thmr = PRENEX_CONV r in
    let   l' = (rhs o concl)thml in
    let   r' = (rhs o concl)thmr in
    let thm1 = MP(MP(SPECL[l';r';l;r]IMP_EQ)thml)thmr in
    let    t = (rhs o concl)thm1 in
    let thm2 = IMP_PRENEX_CONV t in
    TRANS thm1 thm2
  else ALL_CONV q
  ? failwith id^`: fatal` );;

%-------------------------------------------------------------------------------

PRENEX_TAC: tactic

The tactic PRENEX_TAC is used to rewrite a goal into prenex normal form. If the
current goal is already in prenex normal form, there should be no change.
However, due to a bug some of the bound variables may become primed. The tactic
is based on the conversion PRENEX_CONV.

              p
    =====================
     Q1 x1. ... Qn xn. q

Where each Qi for i=1...n, is a universal or existential quantifier and q is
constructed only from propositional connectives at the outermost level.

Bound variables will be renamed when their new scope clashes with other free
variables.
%

let PRENEX_TAC = CONV_TAC PRENEX_CONV;;


%-------------------------------------------------------------------------------

PRENEX_RULE: thm -> thm

The rule PRENEX_TAC is used to rewrite a theorem into prenex normal form.
However, due to a bug some of the bound variables may become primed. The rule
is based on the conversion PRENEX_CONV.

             p
    ---------------------
     Q1 x1. ... Qn xn. q

Where each Qi for i=1...n, is a universal or existential quantifier and q is
constructed only from propositional connectives at the outermost level.

Bound variables will be renamed when their new scope clashes with other free
variables.
%

let PRENEX_RULE = CONV_RULE PRENEX_CONV;;


%-------------------------------------------------------------------------------
%
