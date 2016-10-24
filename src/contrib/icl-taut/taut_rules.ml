% ICL Defence Systems 1988 %

%
for arbitrary terms t2:

       X |- t1
===============================   expand (RMP_TAC t2);;
    X |- t2      X |- t2 ==> t1
%

let RMP_TAC term (al,t)	= [al,mk_imp(term,t); al,term], fun [f;s].MP f s;;

%
for theorems of the form "A ==> B":

	X |- B
====================== expand(TMP_TAC "|- A ==> B");;
      X |- A
%

let TMP_TAC thm (al,t)	= 
	let h,c = dest_imp (concl thm)
	in	if t=c
		then [al,h], fun [p]. MP thm p
		else failwith `TMP_TAC`;;

%
for an arbitrary term tm:
         al |- g
================================== expand(LEMMA tm);;
  al |- tm         tm', al |- g

where "tm', al |- g"  results from applying STRIP_TAC to "al |- tm ==> g"
%

let LEMMA t = RMP_TAC t THENL [STRIP_TAC; ALL_TAC];;

%
for any term, tm, together with a list of tactics, tacl:

	al |- g
====================================== expand (LEMMA_PROOF tm tacl);;
      tm, al |- g

if EVERY tacl proves tm. 
%

let LEMMA_PROOF term tacticl (asl,g) =
	(MP_TAC (TAC_PROOF ((asl,term), (EVERY tacticl))) THEN STRIP_TAC)  (asl,g);;

% oprotate_goals modified to use hd, tl, @, last and butlast	%
% instead of rotate_left and rotate_right [RJB 90.10.20].	%

let oprotate_goals (gl,pr) :subgoals = 
    (last gl).(butlast gl), pr o (\l. (tl l)@[hd l])
    ? failwith `oprotate_goals`;;

let lemma t = expand (oprotate_goals o (LEMMA t));;

let lemma_proof term tacticl = expand (LEMMA_PROOF term tacticl);;

%
ASSUMP is a crude modification of ASSUME to provide a check that
the term supplied is in the assumption list. 
It uses top_goal and therefore doesn't always get the right answer. 

The idea is to detect errors in the use of ASSUME
before reaching the end of the proof. 
%

let ASSUMP term =
	let	(al,g) = top_goal()
	in	letrec test ter =	fun	[].	failwith `ASSUMP - term not an assumption`
					|	(h.t).	if	h = term
								then	ASSUME term
								else	test ter t 
		in test term al;;

%
bool_subexpr is used in proving tautologies. 
It extracts the subexpressions of a list of terms so that
BOOL_CASES_TAC can be applied to them. 

case for handling iff (<=>) deleted [TFM 90.01.21]

%
letrec bool_subexpr =
	fun	[].		[]							|
		(h.t).
		if type_of h = ":bool"
		then
			if	is_const h
			then	bool_subexpr t
			else if is_var h
			then	h.(bool_subexpr t)
			else if is_neg h
			then	bool_subexpr ((dest_neg h).t)
			else if is_conj h
			then	let	l,r = dest_conj h
				in	bool_subexpr(l.r.t)
			else if is_disj h
			then	let	l,r = dest_disj h
				in	bool_subexpr(l.r.t)
			else if is_imp h
			then	let	l,r = dest_imp h
					in	bool_subexpr(l.r.t)
			else if is_eq h
			then	let	l,r = dest_eq h
				in	if	type_of l = ":bool"
					then	bool_subexpr(l.r.t)
					else	h.(bool_subexpr t)
			else if	is_cond h
			then	let c,f,s = dest_cond h
				in	bool_subexpr(c.f.s.t)
			else	h.(bool_subexpr t)
		else bool_subexpr t;;

%
TAUT_TAC proves tautologies,
If the current goal is a tautology then TAUT_TAC will prove it. 
Otherwise it will take longer and fail. 
The definition of tautology is fairly broad, including all substitution
instances of tautologies, allowing for an understanding of boolean equality
and conditionals, and coping with outer universal quantifiers. 
Similar rules apply to all the derivatives with TAUT in their names. 
%

let TAUT_TAC =
	let pTAUT_TAC f =
		let a,c = f
		in
		let (gl,p) = (EVERY (map (\x.BOOL_CASES_TAC x THEN REWRITE_TAC[])
				(bool_subexpr [c]))
				THEN REWRITE_TAC[]) f
		in if gl = [] then (gl,p) else failwith `TAUT_TAC - term not a tautology`
	in REPEAT GEN_TAC THEN pTAUT_TAC;;

% TAUT_RULE also proves tautologies, given a tautological term
it will return a tautological theorem %

let TAUT_RULE t = TAC_PROOF (([],t),TAUT_TAC);;

% TAUT_CONV, given a term t will return the theorem "t = T" if this is 
a tautology
%

let TAUT_CONV t =	if type_of t = ":bool"
			then (TAUT_RULE "^t = T")
			else failwith `TAUT_CONV - term not boolean`;;

%
PURE_TAUT_SIMP_TAC takes a long time,
replacing all tautological subexpressions by T. 
TAUT_SIMP_TAC follows this by a REWRITE_TAC[]. 
There must be a better way. 
%
let PURE_TAUT_SIMP_TAC
	 = CONV_TAC (REDEPTH_CONV (CHANGED_CONV TAUT_CONV));;

let TAUT_SIMP_TAC = PURE_TAUT_SIMP_TAC THEN REWRITE_TAC[];;

% 
In the following t must be a tautological term. 
A tactic or rule is obtained which rewrites using the tautology
%
let TAUT_REWRITE_TAC t = ONCE_REWRITE_TAC [TAUT_RULE t];;

let PURE_TAUT_REWRITE_TAC t = PURE_ONCE_REWRITE_TAC [TAUT_RULE t];;

let TAUT_REWRITE_RULE t = ONCE_REWRITE_RULE [TAUT_RULE t];;

let PURE_TAUT_REWRITE_RULE t = PURE_ONCE_REWRITE_RULE [TAUT_RULE t];;

%
      A |- (!x. f) ==> (!x. g)
=============================== expand (FORALL_OUT_TAC);;
      A |- (!x. f ==> g)
%
let  FORALL_OUT_TAC (al,g) = 
	let (h,c) = dest_imp g
? failwith `FORALL_OUT_TAC - goal not an implication`
in	let [v1,b1;v2,b2] = map dest_forall [h;c]
? failwith `FORALL_OUT_TAC - missing quantifier`
in	if not(v1 = v2)
	then failwith `FORALL_OUT_TAC - quantified variables not same`
	else
	let a = mk_forall(v1,"^b1==>^b2")
in	let l1 = GEN v1 (MP	(SPEC v1 (ASSUME a))
					(SPEC v1 (ASSUME h)))
in	let l2 = DISCH a (DISCH h l1)
in    (RMP_TAC a THENL [ACCEPT_TAC l2; ALL_TAC])
	(al,g);;

%
if B is boolean:
        MATCH_EQ_MP (A |- B = C) B = (A |- C)
%

let MATCH_EQ_MP eqth = 
     let match = PART_MATCH (fst o dest_eq) eqth ? failwith `MATCH_MP` 
     in
     \th. EQ_MP (match (concl th)) th;;

%
if B is boolean:
        DEF_IMP (A |- B = C) = (A |- B ==> C)
%
let DEF_IMP def = 
	let term = (fst o dest_eq o concl) (SPEC_ALL def)
	in (GEN_ALL	(DISCH term (MATCH_EQ_MP def (ASSUME term))));;

% DEF_RES_TAC is like IMP_RES_TAC except that it takes boolean equations
instead of implications
%

let DEF_RES_TAC = IMP_RES_TAC o DEF_IMP;;

let OREWRITE_TAC thm = REWRITE_TAC [thm];;
