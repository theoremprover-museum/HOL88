% --------------------------------------------------------------------- %
%									%
% FILE		: upper_bound.ml 					%
%									%
% A theory for upper bounds, complete partial orders, and fixed points.	%
% Defines orderings on types instead of sets by using type variables.   %
% For example, the standard notation for representing a partial order   %
% is a pair (D,<=), where D denotes some set of values, and <= is some  %
% binary relation defined over elements in D. In this theory we do not	%
% refer to D explicitly, but refer to it implicitly in the type of <=,	%
% e.g. for <= : *->*->bool, D is implicitly represented as :*.		%
% The final result in this theory is the proof of the fixed point       %
% theorem which allows the definition of recursive operators.           %
% 									%
% LOADS LIBRARY	: all_sets			          		%
% READS FILES	: NONE				          		%
% WRITES FILES  : upper_bound.th					%
%									%
% AUTHOR	: Albert J Camilleri					%
% AFFILIATION   : Hewlett-Packard Laboratories, Bristol			%
% DATE		: 90.04.01						%
% LAST MODIFIED	: 90.05.10						%


new_theory `upper_bound`;;


% --------------------------------------------------------------------- %
% 									%
% Load files and set up preliminaries.					%
% 									%

load_library `all_sets`;;


% A conversion, tactic, and inference rule for handling sets:           %
% They can be used to abbreviate "x IN ABS_set (\y. P y)" to "P x"      %

let ELEM_ELIM_CONV ty tm =
     let opr,[opd1;opd2] = strip_comb tm
     in
     ((rator opd2) = "ABS_set:^(inst_type [ty, ":*"] ":(*->bool)->(* set)")") &
     (opr = "$IN:^(inst_type [ty, ":*"] ":*->((* set)->bool)")") =>
         TRANS
	  (SPECL [(rand opd2); opd1]
		 (INST_TYPE [ty, ":*"] (theorem `all_sets` `IN_SET_LEMMA`)))
          (BETA_CONV (mk_comb ((rand opd2), opd1))) |
         failwith `ELEM_ELIM_CONV`;;

let ELEM_ELIM_TAC ty = CONV_TAC (DEPTH_CONV (ELEM_ELIM_CONV ty));;

let ELEM_ELIM_RULE ty = CONV_RULE (DEPTH_CONV (ELEM_ELIM_CONV ty));;

% --------------------------------------------------------------------- %


map (load_theorem `all_sets`) [`IN`; `SET_EQ`];;


% --------------------------------------------------------------------- %



% --------------------------------------------------------------------- %

% A relation is a partial order iff it is reflexive, transitive and	%
% antisymmetric.							%

% Definition of Reflexive.						%

let REF =
    new_definition (`REF`, "REF (r:*->*->bool) = ! x:*. r x x");;


% Definition of Transitive.						%

let TRANS =
    new_definition
       (`TRANS`,
	"TRANS (r:*->*->bool) = ! x y z:*. ((r x y) /\ (r y z)) ==> (r x z)");;


% Definition of Antisymmetric.						%

let ANTISYM =
    new_definition
       (`ANTISYM`,
	"ANTISYM (r:*->*->bool) = ! x y:*. ((r x y) /\ (r y x)) ==> (x = y)");;


% Definition of Partial Order.						%

let PO =
    new_definition
       (`PO`, "PO (r:*->*->bool) = (REF r) /\ (TRANS r) /\ (ANTISYM r)");;

% --------------------------------------------------------------------- %



% --------------------------------------------------------------------- %

% For any binary relation r, b is an upper bound of a set X iff		%
% r is a partial order, and all members of X are ordered before b.	%

let IS_UB =
    new_definition
       (`IS_UB`,
	"IS_UB b X r = (PO r) /\ (!a:*. (a IN X) ==> r a b)");;


% For any binary relation r, b is a least upper bound of a set X iff	%
% b is an upper bound of X for r, and all other upper bounds of X are   %
% ordered after b.							%

let IS_LUB =
    new_definition
       (`IS_LUB`,
	"IS_LUB b X r =  (IS_UB b X r) /\ (!c:*. (IS_UB c X r) ==> r b c)");;


% We use epsilon to define the least upper bound.			%

let LUB = new_definition (`LUB`, "LUB X r = @b:*. IS_LUB b X r");;


% When a least upper bound exists, it is unique.			%

let UNIQUE_LUB =
    prove_thm
       (`UNIQUE_LUB`,
	"!r X x. IS_LUB x X r ==> !y:*. IS_LUB y X r ==> (y = x)",
	REWRITE_TAC [IS_LUB; IS_UB] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC THEN
	ASSUM_LIST
	 (\thl.
	  (ACCEPT_TAC
	   (MATCH_MP
	    (CONJUNCT2 (CONJUNCT2 (REWRITE_RULE [PO; ANTISYM] (el 11 thl))))
	    (CONJ (el 4 thl) (el 2 thl))))));;


% An example (used in a proof later).					%
% For any partial order, saying that some element a is ordered below	%
% some element b, is equivalent to saying that b is the least upper	%
% bound of the set {a, b}.						%

let LUB_ORDER =
    prove_thm
       (`LUB_ORDER`,
	"!r.
	  (PO r) ==>
	  !a b:*. (r a b) = (IS_LUB b (ABS_set (\x. (x = a) \/ (x = b))) r)",
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [IS_LUB; IS_UB] THEN
	ELEM_ELIM_TAC ":*" THEN
	POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [PO; REF])) THEN
	EQ_TAC THENL
	[REPEAT STRIP_TAC THEN
	 ASM_REWRITE_TAC [] THEN
	 POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE []) o (SPEC "b:*"));
	 DISCH_THEN
	  (ACCEPT_TAC o (REWRITE_RULE []) o (SPEC "a:*") o CONJUNCT1)]);;


% Theorem above, but rephrased as LUB{a,b} = b. Useful to eliminate LUB.%

let LUB_ORDER' =
    let th1 =
        UNDISCH (fst(EQ_IMP_RULE (SPEC_ALL (UNDISCH (SPEC_ALL LUB_ORDER))))) in
    let th2 =
        REWRITE_RULE
	 [SYM (SPEC_ALL LUB)]
	 (SELECT_RULE
	  (EXISTS
	   ("?z:*. IS_LUB z(ABS_set(\x. (x = a) \/ (x = b)))r","b:*") th1)) in
    (GEN_ALL o DISCH_ALL o GEN_ALL o (DISCH "(r (a:*) (b:*)):bool") o
     (REWRITE_RULE [th2]) o (SPEC "LUB(ABS_set(\x:*. (x = a) \/ (x = b)))r") o
     (REWRITE_RULE [th1]) o
     (SPECL ["r:*->*->bool"; "ABS_set (\x:*. (x = a) \/ (x = b))"; "b:*"]))
    UNIQUE_LUB;;


% This lemma just proves that |- IS_LUB b X r ==> (LUB X r = b)		%
% Comes in handy later.							%

let LUB_EQ =
    let th1 =
        REWRITE_RULE
	 [SYM (SPEC_ALL LUB)]
	 (SELECT_RULE
	  (EXISTS ("?z:*. IS_LUB z X r", "b:*") (ASSUME "IS_LUB (b:*) X r")))
    and th2 = ASSUME "IS_LUB (b:*) X r"
    in
    DISCH_ALL (MATCH_MP (MATCH_MP UNIQUE_LUB th2) th1);;


% --------------------------------------------------------------------- %



% --------------------------------------------------------------------- %

% For any partial order, a non-empty set X is directed iff for any two  %
% elements in X, there exists another which is ordered above the two.   %

let DIRECTED =
    new_definition
       (`DIRECTED`,
	"DIRECTED (X:(*)set) r =
	 ((PO r) /\
	  ~(X = EMPTY) /\
	  !a b. ((a IN X) /\ (b IN X)) ==>
	        (?c. (c IN X) /\ (r a c) /\ (r b c)))");;


% Lemma which proves that if (PO r) and (r a b) then {a,b} is directed	%

let DIRECTED_TUPLE =
    TAC_PROOF
       (([],
	 "!r. (PO r) ==>
 	      !a b:*.
	       (r a b) ==> (DIRECTED (ABS_set (\x. (x = a) \/ (x = b))) r)"),
	REWRITE_TAC [PO; REF; DIRECTED; SET_EQ; IN] THEN
	ELEM_ELIM_TAC ":*" THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [] THENL
	[POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE []) o (SPEC "a:*"));
	 EXISTS_TAC "a:*"; EXISTS_TAC "b:*";
	 EXISTS_TAC "b:*"; EXISTS_TAC "b:*"] THEN
	 ASM_REWRITE_TAC []);;


% A relation is a complete partial order iff:				%
%   it is a partial order, and						%
%   there exists a bottom element, and					%
%   all sets directed by the ordering has a least upper bound.		% 

let CPO =
    new_definition
       (`CPO`,
	"CPO (r:*->*->bool) =
	 ((PO r) /\
	  (? bot. !x. r bot x) /\
	  (! (X:(*)set). (DIRECTED X r) ==> ?b. IS_LUB b X r))");;

% --------------------------------------------------------------------- %



% --------------------------------------------------------------------- %

% Some definitions:							%

% Least fixed point.							%

let IS_FIX =
    new_definition
       (`IS_FIX`,
	"IS_FIX (x:*) fun r = (fun x = x) /\ !y. (fun y = y) ==> (r x y)");;

let FIX = new_definition (`FIX`, "FIX fun r = @x:*. IS_FIX x fun r");;


% When a least fixed point exists, it is unique.			%

let UNIQUE_FIX =
    prove_thm
       (`UNIQUE_FIX`,
	"!r. (PO r) ==> !f x. IS_FIX x f r ==> !y:*. IS_FIX y f r ==> (y = x)",
	REWRITE_TAC [IS_FIX; PO; ANTISYM] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC);;

% Iteration.								%

let ITER =
    new_prim_rec_definition
       (`ITER`,
        "(ITER 0       f x = (x:*)) /\
         (ITER (SUC n) f x = f(ITER n f x))");;


% Union of indexed sets.						%

let IT_UNION =
    new_definition
      (`IT_UNION`,
       "IT_UNION c = ABS_set (\x:*. ?n:num. x IN (c n))");;


% Intersection of indexed sets.						%

let IT_INTER =
    new_definition
      (`IT_INTER`,
       "IT_INTER c = ABS_set (\x:*. !n:num. x IN (c n))");;


% The set {f x | x IN X}						%

let SET_APPLY =
    new_definition
       (`SET_APPLY`,
	 "SET_APPLY f X = ABS_set (\y:**. ?x:*. (x IN X) /\ (y = (f x)))");;


% --------------------------------------------------------------------- %



% --------------------------------------------------------------------- %

% Definition of monotonicity.						%

let EXISTS_MONO =
    TAC_PROOF
       (([],
         "?f:(*->**)->(*->*->bool)->(**->**->bool)->bool.
           !r1 r2. ((CPO r1) /\ (CPO r2)) ==>
                   !fun. (f fun r1 r2) =
			 (!p1 p2. (r1 p1 p2) ==> (r2 (fun p1) (fun p2)))"),
	EXISTS_TAC "\x y z. !p1 p2:*. y p1 p2 ==> z ((x p1):**) (x p2)" THEN
 	BETA_TAC THEN
	REWRITE_TAC []);;

let MONOTONIC =
    new_specification `MONOTONIC` [(`constant`,`MONOTONIC`)] EXISTS_MONO;;


% Definition of continuity.						%

let EXISTS_CONT =
    TAC_PROOF
       (([],
         "?f:(*->**)->(*->*->bool)->(**->**->bool)->bool.
           !r1 r2. ((CPO r1) /\ (CPO r2)) ==>
               !fun. (f fun r1 r2) =
		     (!X. (DIRECTED X r1) ==>
			  ((DIRECTED (SET_APPLY fun X) r2) /\
			   (fun (LUB X r1) = (LUB (SET_APPLY fun X) r2))))"),
	EXISTS_TAC
	 "\x y z. !X:(*)set.
	     (DIRECTED X y) ==>
	     ((DIRECTED (SET_APPLY x X) z) /\
	      (x (LUB X y) = ((LUB (SET_APPLY x X) z):**)))" THEN
 	BETA_TAC THEN
	REWRITE_TAC []);;

let CONTINUOUS =
    new_specification `CONTINUOUS` [(`constant`,`CONTINUOUS`)] EXISTS_CONT;;

% --------------------------------------------------------------------- %



% --------------------------------------------------------------------- %

% Proof that all continuous functions are monotonic.			%

% First a lemma which states that applying a function fun to the	%
% elements of a set {a,b} results in the set {(fun a), (fun b)}.	%

let lemma =
    TAC_PROOF
       (([], "!fun (a b:*).
	      (SET_APPLY fun (ABS_set (\x. (x = a) \/ (x = b)))) =
	      (ABS_set (\x:**. (x = (fun a)) \/ (x = (fun b))))"),
	REWRITE_TAC [SET_APPLY; SET_EQ] THEN
	ELEM_ELIM_TAC ":*" THEN
	ELEM_ELIM_TAC ":**" THEN
	REPEAT GEN_TAC THEN
	EQ_TAC THEN
	REPEAT STRIP_TAC THENL
	[ALL_TAC; ALL_TAC; EXISTS_TAC "a:*"; EXISTS_TAC "b:*"] THEN
	ASM_REWRITE_TAC []);;

let CONT_IMP_MONO =
    prove_thm
       (`CONT_IMP_MONO`,
	"! (fun:*->**) r1 r2.
	   ((CPO r1) /\ (CPO r2)) ==>
	   (CONTINUOUS fun r1 r2) ==> (MONOTONIC fun r1 r2)",
	REPEAT GEN_TAC THEN
	DISCH_THEN STRIP_ASSUME_TAC THEN
	ASSUM_LIST
	 (\thl.
	   REWRITE_TAC
	    [MP (DISCH_ALL
		 (LIST_CONJ
		  (map (UNDISCH o SPEC_ALL) [MONOTONIC; CONTINUOUS])))
		(CONJ (el 2 thl) (el 1 thl))]) THEN
	POP_ASSUM_LIST
	 (\thl.
	   STRIP_ASSUME_TAC (LIST_CONJ (map (REWRITE_RULE [CPO]) thl))) THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC DIRECTED_TUPLE THEN
	RES_TAC THEN
	POP_ASSUM
	 (ASSUME_TAC o (REWRITE_RULE [SYM (SPEC_ALL LUB)]) o SELECT_RULE) THEN
	IMP_RES_TAC LUB_ORDER' THEN
	IMP_RES_THEN (\x. ASM_REWRITE_TAC [x]) LUB_ORDER THEN
	POP_ASSUM_LIST
	 (\thl.
	   ACCEPT_TAC
	    (REWRITE_RULE [lemma]
	     (SUBS [el 1 thl] (SUBS [SYM (el 6 thl)] (el 4 thl))))));;

%-----------------------------------------------------------------------%



%-----------------------------------------------------------------------%

% Here begins the proof of the KNASTER-TARSKY fixed point theorem.      %
% Several intermediate lemmas are proved.				%

let KNASTER_lemma_1 =
    TAC_PROOF
       (([],
	"((!p1 p2:*. r p1 p2 ==> r(f p1)(f p2)) /\
	  (f x' = (x':*)) /\
	  (!x:*. r bot x)) ==>
	 !n:num. r (ITER n f bot) x'"),
	DISCH_THEN STRIP_ASSUME_TAC THEN
	INDUCT_TAC THEN
	ASM_REWRITE_TAC [ITER] THEN
	POP_ASSUM_LIST
	 (\thl.
	   ACCEPT_TAC (SUBS [el 3 thl] (MATCH_MP (el 4 thl) (el 1 thl)))));;

let lemma1 =
    TAC_PROOF
       (([],
	 "(!a:*. (a IN X \/ a IN Y) ==> r a (c:*)) ==>
	  (!a:*. (a IN Y) ==> r a c)"),
        REPEAT STRIP_TAC THEN RES_TAC);;

let lemma2 =
    TAC_PROOF
       (([], "?x:*. x IN (SET_APPLY f (ABS_set (\x. ?n. x = ITER n f bot)))"),
	EXISTS_TAC "(f (bot:*)):*" THEN
	REWRITE_TAC [SET_APPLY] THEN
	ELEM_ELIM_TAC ":*" THEN
	EXISTS_TAC "bot:*" THEN
	REWRITE_TAC [] THEN
	EXISTS_TAC "0" THEN
	REWRITE_TAC [ITER]);;

let KNASTER_lemma_2 =
    TAC_PROOF
       (([],
	 "!X Y r. ((?y:*. y IN Y) /\ (?b:*. IS_LUB b Y r) /\ (PO r)) ==>
		  (!x y:*. ((x IN X) /\ (y IN Y)) ==> r x y) ==>
		  (IS_LUB (LUB Y r) (X UNION Y) r)"),
	REPEAT GEN_TAC THEN
	DISCH_THEN STRIP_ASSUME_TAC THEN
	IMP_RES_THEN SUBST1_TAC LUB_EQ THEN
	ASM_REWRITE_TAC [IS_LUB; IS_UB; IN_UNION] THEN
	POP_ASSUM
	 (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o (REWRITE_RULE [PO; TRANS])) THEN
	REPEAT STRIP_TAC THEN
	UNDISCH_TAC "IS_LUB (b:*) Y r" THEN
	DISCH_THEN
	 (STRIP_ASSUME_TAC o (REWRITE_RULE [IS_LUB; IS_UB])) THEN
	RES_TAC THEN
	IMP_RES_TAC lemma1 THEN
	RES_TAC);;



let KNASTER_lemma_3 =
    TAC_PROOF
       (([],
	 "(ABS_set (\x:*. ?n. x = ITER n f bot)) =
	  ((ABS_set (\x:*. x = bot)) UNION
	   (SET_APPLY f(ABS_set(\x. ?n. x = ITER n f bot))))"),
	REWRITE_TAC [SET_EQ; SET_APPLY; IN_UNION] THEN
	ELEM_ELIM_TAC ":*" THEN
	GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
	[DISJ_CASES_THEN STRIP_ASSUME_TAC (SPEC "n:num" num_CASES) THEN
	 ASM_REWRITE_TAC [ITER] THEN
	 DISJ2_TAC THEN
	 EXISTS_TAC "ITER n' f (bot:*)" THEN
	 REWRITE_TAC [] THEN
	 EXISTS_TAC "n':num";
	 EXISTS_TAC "0";
	 EXISTS_TAC "SUC n"] THEN
	ASM_REWRITE_TAC [ITER]);;

let lemma3 =
    ((ELEM_ELIM_RULE ":*") o
     (REWRITE_RULE [lemma2]) o
     (SPECL ["ABS_set (\x:*. x = bot)";
	     "SET_APPLY f (ABS_set (\x:*. ?n. x = ITER n f bot))";
	     "r:*->*->bool"]))
    KNASTER_lemma_2;;

let lemma4 =
    TAC_PROOF
       (([],
	 "(!x:*. r bot x) ==>
	  (!x y:*.
            (x = bot) /\
	    y IN (SET_APPLY f(ABS_set(\x. ?n. x = ITER n f bot))) ==>
            r x y)"),
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);;

let lemma5 =
    TAC_PROOF
       (([],
	 "!r f (bot:*).
	   ((!a b:*. r a b ==> r (f a) (f b)) /\ (!x:*. r bot x)) ==>
	   !n n'. r (ITER n f bot) (ITER (n + n') f bot)"),
	REPEAT GEN_TAC THEN
	DISCH_THEN STRIP_ASSUME_TAC THEN
	INDUCT_TAC THEN
	ASM_REWRITE_TAC [ADD; ITER] THEN
	GEN_TAC THEN
	POP_ASSUM (ASSUME_TAC o (SPEC "n':num")) THEN
	RES_TAC);;



let lemma6 =
    TAC_PROOF
       (([],
	 "!r f (bot:*).
	   ((!a b:*. r a b ==> r (f a) (f b)) /\ (!x:*. r bot x)) ==>
	   (PO r) ==>
	   DIRECTED ((ABS_set(\x:*. ?n. x = ITER n f bot))) r"),
	REPEAT GEN_TAC THEN
	DISCH_THEN (ASSUME_TAC o (MATCH_MP lemma5)) THEN
	REWRITE_TAC [DIRECTED; SET_EQ; IN] THEN
	ELEM_ELIM_TAC ":*" THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [] THENL
	[POP_ASSUM
	 (ACCEPT_TAC o (REWRITE_RULE [ITER]) o (SPEC "0") o
	  (CONV_RULE NOT_EXISTS_CONV) o (SPEC "bot:*"));
	 EXISTS_TAC "ITER (n + n') f (bot:*)" THEN
	 ASM_REWRITE_TAC [] THEN
	 SUBST1_TAC (SPECL ["n:num"; "n':num"] ADD_SYM) THEN
	 ASM_REWRITE_TAC [] THEN
	 EXISTS_TAC "n' + n" THEN
	 REWRITE_TAC []]);;

let KNASTER_lemma_4 =
    TAC_PROOF
       (([],
	 "!(f:*->*) r.
	  (CPO r /\ CONTINUOUS f r r) ==>
	  !bot. (!x. r bot x) ==>
		((f (LUB (ABS_set \x. ?n. x = ITER n f bot) r)) =
	         (LUB (ABS_set \x. ?n. x = ITER n f bot) r))"),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC CONT_IMP_MONO THEN
	POP_ASSUM_LIST
	 (\thl.
	  STRIP_ASSUME_TAC
	   (LIST_CONJ
	    [(\x. LIST_CONJ [hd x; el 4 thl; el 3 x])
	     (CONJUNCTS (REWRITE_RULE [CPO] (el 6 thl)));
	     REWRITE_RULE
	      [MATCH_MP CONTINUOUS (CONJ (el 6 thl) (el 6 thl))] (el 5 thl);
             REWRITE_RULE
	      [MATCH_MP MONOTONIC (CONJ (el 6 thl) (el 6 thl))] (el 1 thl)]))
	 THEN
	IMP_RES_TAC lemma6 THEN
	RES_TAC THEN
	IMP_RES_THEN (ASSUME_TAC o (SPEC "f:*->*")) lemma4 THEN
	ASM_REWRITE_TAC
	 [AP_TERM "LUB:(*)set->(*->*->bool)->*" KNASTER_lemma_3] THEN
	POP_ASSUM_LIST
	 (\thl.
	  REWRITE_TAC
	   [MATCH_MP
	     LUB_EQ
	     (MP (MP lemma3 (CONJ (el 3 thl) (el 13 thl))) (el 1 thl))]));;

let KNASTER_lemma_5 =
    TAC_PROOF
       (([],
	 "(!n. r (ITER n f bot) (y:*)) ==>
	  (!d:*. (d IN (ABS_set \x. ?n. x = ITER n f bot)) ==> r d y)"),
	ELEM_ELIM_TAC ":*" THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC []);;



let KNASTER_lemma_6 =
    TAC_PROOF
       (([],
	 "!(f:*->*) r.
	  (CPO r /\ CONTINUOUS f r r) ==>
	  !bot. (!x:*. r bot x) ==>
	        !y:*. (f y = y) ==>
	              r (LUB (ABS_set \x. ?n. x = ITER n f bot) r) y"),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC CONT_IMP_MONO THEN
	POP_ASSUM_LIST
	 (\thl.
	  STRIP_ASSUME_TAC
	   (LIST_CONJ
	    [(\x. LIST_CONJ [hd x; el 5 thl; el 3 x])
	     (CONJUNCTS (REWRITE_RULE [CPO] (el 7 thl)));
             REWRITE_RULE
	      [MATCH_MP MONOTONIC (CONJ (el 7 thl) (el 7 thl))] (el 1 thl);
	     el 4 thl])) THEN
	ASSUM_LIST
	 (\thl.
	  STRIP_ASSUME_TAC
	   (MATCH_MP (el 3 thl)
		     (MATCH_MP (MATCH_MP lemma6 (CONJ (el 2 thl) (el 4 thl)))
			       (el 5 thl)))) THEN
	IMP_RES_THEN SUBST1_TAC LUB_EQ THEN
	POP_ASSUM
	 (ASSUME_TAC o (SPEC "y:*") o CONJUNCT2 o
	  (REWRITE_RULE [IS_LUB; IS_UB])) THEN
	IMP_RES_TAC KNASTER_lemma_1 THEN
	IMP_RES_TAC KNASTER_lemma_5 THEN
	RES_TAC);;

let IS_FIX_LUB =
    TAC_PROOF
       (([],
	 "!(f:*->*) r.
	  (CPO r /\ CONTINUOUS f r r) ==>
	  !bot. (!x:*. r bot x) ==>
	        IS_FIX (LUB(ABS_set(\x. ?n. x = ITER n f bot))r) f r"),
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC KNASTER_lemma_4 THEN
	IMP_RES_TAC KNASTER_lemma_6 THEN
	ASM_REWRITE_TAC [IS_FIX]);;

let UNIQUE_FIX' =
    let th1 =
        DISCH_ALL (CONJUNCT1 (UNDISCH (fst (EQ_IMP_RULE (SPEC_ALL CPO))))) in
    GEN_ALL (DISCH_ALL (IMP_TRANS th1 (SPEC_ALL UNIQUE_FIX)));;



%-----------------------------------------------------------------------%
%									%
% The actual theorem:							%
% "!f r. (CPO r /\ CONTINUOUS f r r) ==>				%
%	 !bot:*. (!x. r bot x) ==>					%
%	         FIX f r = LUB (ABS_set \x. ?n. x = ITER n f bot) r"	%

let KNASTER_TARSKY =
    save_thm
       (`KNASTER_TARSKY`,
    let th1 = UNDISCH (SPEC_ALL (UNDISCH (SPEC_ALL IS_FIX_LUB)))
    in
    let th2 =
        REWRITE_RULE
	 [SYM (SPEC_ALL FIX)]
	 (SELECT_RULE
	  (EXISTS ("?z:*. IS_FIX z f r",
		   "LUB(ABS_set(\x:*. ?n. x = ITER n f bot))r") th1))
    in
    GEN_ALL
     (DISCH_ALL
      (ASM_REWRITE_RULE []
       (DISCH "CPO (r:*->*->bool)"
	(MATCH_MP (MATCH_MP (UNDISCH (SPEC_ALL UNIQUE_FIX')) th1) th2)))));;

close_theory ();;


