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

% --------------------------------------------------------------------- %
% HINT: first show that:						%
%									%
%    |- ?r q. k = q n + r. 						%
%									%
% This is easy, with r=k and q=0.					%
% --------------------------------------------------------------------- %
let exists_lemma = 
    TAC_PROOF(([], "?r q. (k=(q*n)+r)"), <*** put your tactic here ***>);;


% --------------------------------------------------------------------- %
% Then show, using the well ordering property WOP, that there is a	%
% smallest n' such that ?q. k=qn+n'.  This is the correct remainder.	%
%									%
% The required theorem is: 						%
%									%
% |- ?r. (?q. k = (q*n) + r) /\ (!r'. r' < r ==> ~(?q. k = (q*n) + r')) %
%									%
% HINT: see EXISTS_LEAST_CONV.						%
% --------------------------------------------------------------------- %
let smallest_lemma = <*** put your proof here ***>;;

% --------------------------------------------------------------------- %
% Now prove the theorem stating the Division Algorithm Theorem.		%
%									%
% You may have to prove several lemmas, which you will find are needed	%
% as you are developing the main proof. Prove these lemmas separately.	%
% --------------------------------------------------------------------- %
let thm =
    PROVE("!k n. ~(n=0) ==> ?r q. (k=(q*n)+r) /\ r<n",
          <*** put your proof here ***>);;

