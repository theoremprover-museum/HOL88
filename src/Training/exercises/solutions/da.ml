% ===================================================================== %
% HOL TRAINING COURSE: proof of the division algorithm.			%
% ===================================================================== %

% ===================================================================== %
% The exercise is to prove the division algorithm for the natural	%
% numbers, expressed in HOL by the following theorem:			%
%									%
%   |- !k n. (n>0) ==> ?q r. k = q n + r /\ 0 <= r < n			%
%									%
% This theorem is actually built into HOL (as `DA'), as are a number of %
% consequences of it.  For the purposes of this exercise, the built-in  %
% theorem DA should not be used (or it would be too easy!). Neither	%
% should any built-in theorems about the functions MOD and DIV be used  %
% in the exercise (these are consequences of DA).			%
%									%
% The theorem WOP:							%
%									%
%  |- !P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))		%
%									%
% is most likely to be helpful, and may be used in the proof.		%
% ===================================================================== %



% ===================================================================== %
% The proof given below follows MacLane & Birkhoff, p29. Several tricky %
% tactics are used; see the REFERENCE manual for these.			%
%									% 
% * MacLane & Birkhoff, "Algebra" 2nd Ed, MacMillan, New York, 1979.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% We first show that:							%
%									%
%    |- ?r q. k = q n + r. 						%
%									%
% This is easy, with r=k and q=0.					%
% --------------------------------------------------------------------- %
let exists_lemma = 
    TAC_PROOF(([], "?r q. (k=(q*n)+r)"),
	      MAP_EVERY EXISTS_TAC ["k:num";"0"] THEN
	      REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES]);;

% --------------------------------------------------------------------- %
% We now show, using the well ordering property WOP, that there is a	%
% smallest n' such that ?q. k=qn+n'.  This is the correct remainder.	%
%									%
% The theorem is: 							%
%									%
% |- ?r. (?q. k = (q*n) + r) /\ (!r'. r' < r ==> ~(?q. k = (q*n) + r')) %
%									%
% --------------------------------------------------------------------- %
let smallest_lemma = CONV_RULE EXISTS_LEAST_CONV exists_lemma;; 

% --------------------------------------------------------------------- %
% For the following proof, we will need the lemma:			%
%									%
%    |- !m n. n <= m ==> (?p. m = n + p)				%
% --------------------------------------------------------------------- %
let leq_add_lemma =
    TAC_PROOF(([],"!m n. (n<=m) ==> ?p.m=n+p"),
	      REWRITE_TAC [LESS_OR_EQ] THEN
	      REPEAT STRIP_TAC THENL
	      [FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1) THEN
	       EXISTS_TAC "p+1" THEN
	       FIRST_ASSUM ACCEPT_TAC;
	       EXISTS_TAC "0" THEN
	       ASM_REWRITE_TAC [ADD_CLAUSES]]);;

% --------------------------------------------------------------------- %
% We will also need the lemma:  |- k=qn+n+p ==> k=(q+1)*n+p		%
% --------------------------------------------------------------------- %
let k_expr_lemma = 
    TAC_PROOF(([], "(k=(q*n)+n+p) ==> (k=((q+1)*n)+p)"),
	      REWRITE_TAC [RIGHT_ADD_DISTRIB;MULT_CLAUSES;ADD_ASSOC]);;

% --------------------------------------------------------------------- %
% We will also need the lemma: [~n=0] |- p < (n + p)			%
% --------------------------------------------------------------------- % 
let less_add = UNDISCH(SUBS [SPECL ["p:num";"n:num"] ADD_SYM]
		            (SPECL ["p:num";"n:num"] LESS_ADD_NONZERO));;

% --------------------------------------------------------------------- %
% Now prove the theorem stating the Division Algorithm Theorem.		%
% --------------------------------------------------------------------- %
let thm =
    PROVE("!k n. ~(n=0) ==> ?r q. (k=(q*n)+r) /\ r<n",
          REPEAT STRIP_TAC THEN
	  STRIP_ASSUME_TAC smallest_lemma THEN
	  MAP_EVERY EXISTS_TAC ["r:num";"q:num"] THEN
	  ASM_REWRITE_TAC [] THEN
	  DISJ_CASES_THEN CHECK_ASSUME_TAC
	      (SPECL ["r:num";"n:num"] LESS_CASES) THEN
	  IMP_RES_THEN (STRIP_THM_THEN SUBST_ALL_TAC) leq_add_lemma THEN
	  IMP_RES_TAC k_expr_lemma THEN
	  ANTE_RES_THEN IMP_RES_TAC less_add);;

