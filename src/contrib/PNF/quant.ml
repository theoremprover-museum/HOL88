%-------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------%
%-------------------------------------------------------------------------------%
%------                                                                   ------%
%------                        QUANTIFIER  THEOREMS                       ------%
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
This file contains a theory named `quant' that proves all sorts of ad-hoc
theorems involving the universal and existential quantifiers. Its main purpose
was to devise template theorems that are used in the formation of conversions
defined in the prenex normal form file `prenex.ml'. The theory requires no
parents.

Mostly, the theorems are simply equations stating the equivalence between a
term formed from a propositional connective /\, \/, ==>, or ~, in which one
of its sub-terms has a quantifier, and a term in which the quantifier has been
moved outermost (this may involve a change of quantifier). The list of such
theorems proved below is:
    NOT_EXISTS_THM		|- !p. ~($? p) = $! (\x. ~p x)
    NOT_FORALL_THM		|- !p. ~($! p) = $? (\x. ~p x)
    L_DISJ_EXISTS_THM		|- !q p. ($? p) \/ q = $? (\x. p x \/ q)
    R_DISJ_EXISTS_THM		|- !q p. q \/ ($? p) = $? (q \/ \x. p x)
    L_DISJ_FORALL_THM		|- !q p. ($! p) \/ q = $! (\x. p x \/ q)
    R_DISJ_FORALL_THM		|- !q p. q \/ ($! p) = $! (q \/ \x. p x)
    L_CONJ_EXISTS_THM		|- !q p. ($? p) /\ q = $? (\x. p x /\ q)
    R_CONJ_EXISTS_THM		|- !q p. q /\ ($? p) = $? (q /\ \x. p x)
    L_CONJ_FORALL_THM		|- !q p. ($! p) /\ q = $! (\x. p x /\ q)
    R_CONJ_FORALL_THM		|- !q p. q /\ ($! p) = $! (q /\ \x. p x)
    L_IMP_EXISTS_THM		|- !q p. ($? p) ==> q = $! (\x. p x ==> q)
    R_IMP_EXISTS_THM		|- !q p. q ==> ($? p) = $? (\x. q ==> p x)
    L_IMP_FORALL_THM		|- !q p. ($! p) ==> q = $? (\x. p x ==> q)
    R_IMP_FORALL_THM		|- !q p. q ==> ($! p) = $! (\x. q ==> p x)

We prove the following two distributive theorems:
    EXISTS_DISTRIB		|- !p q. ($? p) \/ ($? q) = $? (\x. p x \/ q x)
    FORALL_DISTRIB		|- !p q. ($! p) /\ ($! q) = $! (\x. p x /\ q x)

Finally, these really boring theorems are also proved:
    CONJ_EQ		|- !p'q'p q. (p=p') ==> (q=q') ==> ( p /\ q = p'/\ q')
    DISJ_EQ		|- !p'q'p q. (p=p') ==> (q=q') ==> ( p \/ q = p'\/ q')
    IMP_EQ		|- !p'q'p q. (p=p') ==> (q=q') ==> ( p ==> q = p'==> q')


This code was developed in part with my previous employers, ICL Defence Systems,
and in part with my current employers, SD-Scicon.
%

%--------------------------------------------------------------------------------

Open the theory `quant'. It does not require any parents.
%

new_theory `quant`;;

%--------------------------------------------------------------------------------

CASES_TAC: term -> tactic

This tactic is used within the proofs given in this file, however it is also
defined in the file `prenex.ml', from which it can be loaded. Full documentation
is also given there.
%

let CASES_TAC t =
    ASM_CASES_TAC t THENL[ REWRITE_TAC[ASSUME t]; REWRITE_TAC[ASSUME(mk_neg t)] ];;

%--------------------------------------------------------------------------------

CONJ_EQ: thm

    |- !p'q'p q. (p=p') ==> (q=q') ==> ( p /\ q = p'/\ q')
%

let CONJ_EQ = save_thm( `CONJ_EQ`,
  let gl = [], "! p' q' p q:bool. (p = p') ==> (q = q') ==> ( p /\ q = p'/\ q')" in
  TAC_PROOF(gl, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] ) );;

%--------------------------------------------------------------------------------

DISJ_EQ: thm

    |- !p'q'p q. (p=p') ==> (q=q') ==> ( p \/ q = p'\/ q')
%

let DISJ_EQ = save_thm( `DISJ_EQ`,
  let gl = [], "! p' q' p q:bool. (p = p') ==> (q = q') ==> ( p \/ q = p'\/ q')" in
  TAC_PROOF(gl, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] ) );;

%--------------------------------------------------------------------------------

IMP_EQ: thm

   |- !p'q'p q. (p=p') ==> (q=q') ==> ( p ==> q = p'==> q')
%

let IMP_EQ = save_thm( `IMP_EQ`,
  let gl = [], "! p' q' p q:bool. (p = p') ==> (q = q') ==> ( p ==> q = p'==> q')" in
  TAC_PROOF(gl, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] ) );;

%--------------------------------------------------------------------------------

EXISTS_DISTRIB: thm

    |- !p q. ($? p) \/ ($? q) = $? (\x. p x \/ q x)

The theorem EXISTS_DISTRIB expresses the distributivity of existential
quantification through disjunction. When p and q are appropriately specialised,
we would get a theorem of the form:
    |- (?x. f x) \/ (?y. g y) = ?z. (f z \/ g z).
%

set_goal([], "!(p q:* -> bool). (($? p) \/ ($? q)) = $? (\x. p x \/ q x)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
let thm3 = EXT(GEN"x:*"(BETA_CONV"(\z.(q:*->bool) z) x"));;
let thm4 = SYM(AP_TERM "$?:(*->bool)->bool" thm3);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2; thm4 ] );;
expand( CASES_TAC "?y:*. p y" );;
expand( UNDISCH_TAC "?y:*. p y" THEN STRIP_TAC );;
expand( EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] );;
expand( CASES_TAC "?z:*. q z");;
expand( UNDISCH_TAC "?z:*. q z" THEN STRIP_TAC );;
expand( EXISTS_TAC "z:*" THEN ASM_REWRITE_TAC[] );;
expand( STRIP_TAC );;
expand( UNDISCH_TAC "~(?y:*. p y)" THEN REWRITE_TAC[] );;
expand( EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] );;
expand( UNDISCH_TAC "~(?z:*. q z)" THEN REWRITE_TAC[] );;
expand( EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] );;
let EXISTS_DISTRIB = save_top_thm `EXISTS_DISTRIB`;;

%--------------------------------------------------------------------------------

FORALL_DISTRIB: thm

    |- !p q. ($! p) /\ ($! q) = $! (\x. p x /\ q x)

The theorem FORALL_DISTRIB expresses the distributivity of universal
quantification through conjunction. When p and q are appropriately specialised,
we would get a theorem of the form:
    |- (!x. s[x]) /\ (!y. t[y]) = !z. (s[z] /\ t[z]).
%

set_goal([], "!(p q:* -> bool). (($! p) /\ ($! q)) = $! (\x. p x /\ q x)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
let thm3 = EXT(GEN"x:*"(BETA_CONV"(\z.(q:*->bool) z) x"));;
let thm4 = SYM(AP_TERM "$!:(*->bool)->bool" thm3);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2; thm4 ] );;
expand( CASES_TAC "!x:*. p x /\ q x" );;
expand( REPEAT STRIP_TAC );;
expand( UNDISCH_TAC "~!x:*. p x /\ q x" THEN ASM_REWRITE_TAC[] );;
let FORALL_DISTRIB = save_top_thm `FORALL_DISTRIB`;;

%--------------------------------------------------------------------------------

NOT_EXISTS_THM: thm

    |- !p. ~($? p) = $! (\x. ~p x)

The theorem NOT_EXISTS_THM expresses the equivalence between `there does not
exist an x such that ...' and `for all x it is not the case that ...'. When p
is appropriately specialised, we would get a theorem of the form:
    |- (~?x. t[x]) = (!x. ~t[x]).
%

set_goal([], "!(p:* -> bool). ~($? p) = $! (\x. ~p x)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "!x:*. ~p x" );;
expand( UNDISCH_TAC "~(!x:*. ~p x)" );;
expand( CASES_TAC "?y:*. p y" THEN GEN_TAC );;
expand( CASES_TAC "(p:*->bool)x" );;
expand( UNDISCH_TAC "~(?y:*. p y)" THEN REWRITE_TAC[] );;
expand( EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] );;
let NOT_EXISTS_THM = save_top_thm `NOT_EXISTS_THM`;;

%--------------------------------------------------------------------------------

NOT_FORALL_THM: thm

    |- !p. ~($! p) = $? (\x. ~p x)

The theorem NOT_EXISTS_THM expresses the equivalence between `it is not the
case that for all x ...' and `there is an x such that it is not the case
that ...'. When p is appropriately specialised, we would get a theorem of the
form:
    |- (~!x. t[x]) = (?x. ~t[x]).
%

set_goal([], "!(p:* -> bool). ~($! p) = $? (\x. ~p x)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "!y:*. p y" );;
expand( UNDISCH_TAC "~(!y:*. p y)" );;
expand( CASES_TAC "?x:*. ~p x" THEN GEN_TAC );;
expand( CASES_TAC "(p:*->bool)y" );;
expand( UNDISCH_TAC "~(?x:*. ~p x)" THEN REWRITE_TAC[] );;
expand( EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] );;
let NOT_FORALL_THM = save_top_thm `NOT_FORALL_THM`;;

%--------------------------------------------------------------------------------

L_DISJ_EXISTS_THM: thm

    |- !q p. ($? p) \/ q = $? (\x. p x \/ q)

The theorem L_DISJ_EXISTS_THM is used to move an existential quantifier out
from the left hand disjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- (?x. s[x]) \/ t = ?x'. (s[x'] \/ t),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). ($? p) \/ q = $? (\x. p x \/ q)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let L_DISJ_EXISTS_THM = save_top_thm `L_DISJ_EXISTS_THM`;;

%--------------------------------------------------------------------------------

R_DISJ_EXISTS_THM: thm

    |- !q p. q \/ ($? p) = $? (q \/ \x. p x)

The theorem R_DISJ_EXISTS_THM is used to move an existential quantifier out
from the right hand disjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- t \/ (?x. s[x]) = ?x'. (t \/ s[x']),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). q \/ ($? p) = $? (\x. q \/ (p x))" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let R_DISJ_EXISTS_THM = save_top_thm `R_DISJ_EXISTS_THM`;;

%--------------------------------------------------------------------------------

L_DISJ_FORALL_THM: thm

    |- !q p. ($! p) \/ q = $! (\x. p x \/ q)

The theorem L_DISJ_FORALL_THM is used to move a universal quantifier out
from the left hand disjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- (!x. s[x]) \/ t = !x'. (s[x'] \/ t),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). ($! p) \/ q = $! (\x. p x \/ q)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let L_DISJ_FORALL_THM = save_top_thm `L_DISJ_FORALL_THM`;;

%--------------------------------------------------------------------------------

R_DISJ_FORALL_THM: thm

    |- !q p. q \/ ($! p) = $! (q \/ \x. p x)

The theorem R_DISJ_FORALL_THM is used to move a universal quantifier out
from the right hand disjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- t \/ (!x. s[x]) = !x'. (t \/ s[x']),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). q \/ ($! p) = $! (\x. q \/ (p x))" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let R_DISJ_FORALL_THM = save_top_thm `R_DISJ_FORALL_THM`;;

%--------------------------------------------------------------------------------

L_CONJ_EXISTS_THM: thm

    |- !q p. ($? p) /\ q = $? (\x. p x /\ q)

The theorem L_CONJ_EXISTS_THM is used to move an existential quantifier out
from the left hand conjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- (?x. s[x]) /\ t = ?x'. (s[x'] /\ t),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). ($? p) /\ q = $? (\x. p x /\ q)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let L_CONJ_EXISTS_THM = save_top_thm `L_CONJ_EXISTS_THM`;;

%--------------------------------------------------------------------------------

R_CONJ_EXISTS_THM: thm

    |- !q p. q /\ ($? p) = $? (q /\ \x. p x)

The theorem R_CONJ_EXISTS_THM is used to move an existential quantifier out
from the right hand conjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- t /\ (?x. s[x]) = ?x'. (t /\ s[x']),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). q /\ ($? p) = $? (\x. q /\ (p x))" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let R_CONJ_EXISTS_THM = save_top_thm `R_CONJ_EXISTS_THM`;;

%--------------------------------------------------------------------------------

L_CONJ_FORALL_THM: thm

    |- !q p. ($! p) /\ q = $! (\x. p x /\ q)

The theorem L_CONJ_FORALL_THM is used to move a universal quantifier out
from the left hand conjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- (!x. s[x]) /\ t = !x'. (s[x'] /\ t),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). ($! p) /\ q = $! (\x. p x /\ q)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let L_CONJ_FORALL_THM = save_top_thm `L_CONJ_FORALL_THM`;;

%--------------------------------------------------------------------------------

R_CONJ_FORALL_THM: thm

    |- !q p. q /\ ($! p) = $! (q /\ \x. p x)

The theorem R_CONJ_FORALL_THM is used to move a universal quantifier out
from the right hand conjunct. When p and q are appropriately specialised, we
would get a theorem of the form:
    |- t /\ (!x. s[x]) = !x'. (t /\ s[x']),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). q /\ ($! p) = $! (\x. q /\ (p x))" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let R_CONJ_FORALL_THM = save_top_thm `R_CONJ_FORALL_THM`;;

%--------------------------------------------------------------------------------

L_IMP_EXISTS_THM: thm

    |- !q p. ($? p) ==> q = $! (\x. p x ==> q)

The theorem L_IMP_EXISTS_THM is used to move an existential quantifier out from
the left hand side of an implication. When p and q are appropriately specialised,
we would get a theorem of the form:
    |- (?x. s[x]) ==> t = !x'. (s[x'] ==> t),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). ($? p) ==> q = $! (\x. (p x) ==> q)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" THEN REWRITE_TAC[ NOT_EXISTS_CONV "~(?y:*. p y)" ] );;
let L_IMP_EXISTS_THM = save_top_thm `L_IMP_EXISTS_THM`;;

%--------------------------------------------------------------------------------

R_IMP_EXISTS_THM: thm

    |- !q p. q ==> ($? p) = $? (\x. q ==> p x)

The theorem R_IMP_EXISTS_THM is used to move an existential quantifier out
from the right hand side of an implication. When p and q are appropriately
specialised, we would get a theorem of the form:
    |- t ==> (?x. s[x]) = ?x'. (t ==> s[x']),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). q ==> ($? p) = $? (\x. q ==> (p x))" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$?:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let R_IMP_EXISTS_THM = save_top_thm `R_IMP_EXISTS_THM`;;

%--------------------------------------------------------------------------------

L_IMP_FORALL_THM: thm

    |- !q p. ($! p) ==> q = $? (\x. p x ==> q)

The theorem L_IMP_FORALL_THM is used to move a universal quantifier out from
the left hand side of an implication. When p and q are appropriately specialised,
we would get a theorem of the form:
    |- (!x. s[x]) ==> t = ?x'. (s[x'] ==> t),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). ($! p) ==> q = $? (\x. (p x) ==> q)" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" THEN REWRITE_TAC[ NOT_FORALL_CONV "~(!y:*. p y)" ] );;
let L_IMP_FORALL_THM = save_top_thm `L_IMP_FORALL_THM`;;

%--------------------------------------------------------------------------------

R_IMP_FORALL_THM: thm

    |- !q p. q ==> ($! p) = $! (\x. q ==> p x)

The theorem R_IMP_FORALL_THM is used to move a universal quantifier out
from the right hand side of an implication. When p and q are appropriately
specialised, we would get a theorem of the form:
    |- t ==> (!x. s[x]) = !x'. (t ==> s[x']),
the bound variable being renamed to x' if it is free in s.
%

set_goal([], "!(q:bool)(p:* -> bool). q ==> ($! p) = $! (\x. q ==> (p x))" );;
let thm1 = EXT(GEN"x:*"(BETA_CONV"(\y.(p:*->bool) y) x"));;
let thm2 = SYM(AP_TERM "$!:(*->bool)->bool" thm1);;
expand( REPEAT GEN_TAC THEN SUBST_TAC[ thm2 ] );;
expand( CASES_TAC "q:bool" );;
let R_IMP_FORALL_THM = save_top_thm `R_IMP_FORALL_THM`;;

%--------------------------------------------------------------------------------
%
