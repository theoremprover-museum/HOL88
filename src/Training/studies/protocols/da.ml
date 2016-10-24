
% PROOF		: Division Algorithm for natural numbers.		%
% FILE		: da.ml							%
% DESCRIPTION   : Proof of the Division Algorithm for natural numbers.	%
%									%
%		      |- !k n. (n>0) ==> ?q r. k=qn+r /\ 0<=r<n		%
%									%
%		  The proof follows MacLane & Birkhoff, p29.		%
%		 							%
% READS FILES   : NONE 					%
% WRITES FILES  : da.th							%
%									%
% AUTHOR	: T.F. Melham						%
% DATE		: 86.02.01						%
% REVISED	: 86.05.11						%
%									% 
% REFERENCES	: MacLane, S. & Birkhoff, G.				%
%	      	  "Algebra"						%
%		  2nd Edition, MacMillan, New York, 1979.		%

% Create the new theory "da.th"						%
new_theory `da`;;

% We first show that ?r q. k=qn+r.  This is easy, with r=k and q=0.	%
let exists_lemma = 
    TAC_PROOF(([], "?r q. (k=(q*n)+r)"),
	      MAP_EVERY EXISTS_TAC ["k:num";"0"] THEN
	      REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES]);;

% We now show, using the well ordering property, that there is a	%
% SMALLEST n' such that ?q. k=qn+n'.  This is the correct remainder.	%
%									%
% The theorem is: |- ?n'. (?q. k = q*n+n') /\	 			%
%			  (!y. y<n' ==> (!q. ~(k=q*n+y)))		%
let smallest_lemma = 
    CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV)
	      (MATCH_MP (CONV_RULE (DEPTH_CONV BETA_CONV) 
				   (SPEC "\r.?q.k=(q*n)+r" WOP))
	      	  	exists_lemma);;

% We will need the lemma  |- !m n. n <= m ==> (?p. m = n + p)		%
let leq_add_lemma =
    TAC_PROOF(([],"!m n. (n<=m) ==> ?p.m=n+p"),
	      REWRITE_TAC [LESS_OR_EQ] THEN
	      REPEAT STRIP_TAC THENL
	      [FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1) THEN
	       EXISTS_TAC "p+1" THEN
	       FIRST_ASSUM ACCEPT_TAC;
	       EXISTS_TAC "0" THEN
	       ASM_REWRITE_TAC [ADD_CLAUSES]]);;
% We will need the lemma:  |- k=qn+n+p ==> k=(q+1)*n+p			%
let k_expr_lemma = 
    TAC_PROOF(([], "(k=(q*n)+n+p) ==> (k=((q+1)*n)+p)"),
	      REWRITE_TAC [RIGHT_ADD_DISTRIB;MULT_CLAUSES;ADD_ASSOC]);;

% We will need the lemma: [~n=0] |- p < (n + p)				%
let less_add = UNDISCH(SUBS [SPECL ["p:num";"n:num"] ADD_SYM]
		            (SPECL ["p:num";"n:num"] LESS_ADD_NONZERO));;

% Now prove the theorem stating the Division Algorithm Theorem.		%
let da = 
    prove_thm(`Da`,
              "!k n. ~(n=0) ==> ?r q. (k=(q*n)+r) /\ r<n",
	      REPEAT STRIP_TAC THEN
	      STRIP_ASSUME_TAC smallest_lemma THEN
	      MAP_EVERY EXISTS_TAC ["n':num";"q:num"] THEN
	      ASM_REWRITE_TAC [] THEN
	      DISJ_CASES_THEN CHECK_ASSUME_TAC
			      (SPECL ["n':num";"n:num"] LESS_CASES) THEN
	      IMP_RES_THEN (STRIP_THM_THEN SUBST_ALL_TAC) leq_add_lemma THEN
	      IMP_RES_TAC k_expr_lemma THEN
	      ANTE_RES_THEN IMP_RES_TAC less_add);;

let LESS_EQUAL_ANTISYM = 
    TAC_PROOF(
    ([], "!n m. n <= m /\ m <= n ==> (n = m)"),
     REWRITE_TAC [LESS_OR_EQ] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC LESS_ANTISYM;
      ASM_REWRITE_TAC[]]);;

let LESS_ADD_SUC = 
    TAC_PROOF(([], "!m n. m < m + SUC n"),
     INDUCT_TAC THENL
     [REWRITE_TAC [LESS_0;ADD_CLAUSES];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [ADD_CLAUSES]) THEN
      ASM_REWRITE_TAC [LESS_MONO_EQ;ADD_CLAUSES]]);;

% Now show that the quotient is unique.					%
let Quotient_Unique = 
    prove_thm
    (`Quotient_Unique`,
     "!n r1 r2. ((r1 < n /\ r2 < n)) ==>
      !q1 q2 k. ((k = (q1 * n) + r1) /\ (k = (q2 * n) + r2)) ==>
	    	 (q1 = q2)",
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     POP_ASSUM (STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
     REWRITE_TAC [SYM (SPEC_ALL NOT_LESS)] THEN
     POP_ASSUM SUBST_ALL_TAC THEN
     REPEAT STRIP_TAC THEN POP_ASSUM_LIST (MAP_EVERY MP_TAC o rev) THEN
     DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [LEFT_ADD_DISTRIB;RIGHT_ADD_DISTRIB] THEN
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);MULT_CLAUSES] THEN
     REWRITE_TAC [PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ] THENL
     [PURE_ONCE_REWRITE_TAC [SPECL ["n:num";"m + (1 + p)"] ADD_SYM] THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
      REWRITE_TAC [ADD_CLAUSES] THEN
      DISCH_THEN (MP_TAC o MATCH_MP NOT_LESS_EQ) THEN
      REWRITE_TAC [REWRITE_RULE [ADD_CLAUSES] LESS_ADD_SUC];
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
      REWRITE_TAC [ADD_CLAUSES;LESS_MONO_EQ;ADD_ASSOC] THEN
      SUBST1_TAC (SPECL ["r2:num";"p:num"] ADD_SYM) THEN
      REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
      REWRITE_TAC [NOT_LESS] THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN 
      MATCH_ACCEPT_TAC LESS_EQ_ADD]);;

% Now show that the remainder is unique.				%
let Remainder_Unique = 
    prove_thm
    (`Remainder_Unique`,
     "!n r1 r2. ((r1 < n /\ r2 < n)) ==>
     	 (?q1 q2. ((q1 * n) + r1) = (q2 * n) + r2) ==> (r1 = r2)",
     REPEAT STRIP_TAC THEN (MP_TAC (SPEC_ALL Quotient_Unique)) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MP_TAC o SPECL ["q1:num";"q2:num";"(q1 * n) + r1"]) THEN
     ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN
     POP_ASSUM MP_TAC THEN
     PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
     REWRITE_TAC [EQ_MONO_ADD_EQ]);;

% Close the theory "da.th".						%
close_theory();;

quit();;
