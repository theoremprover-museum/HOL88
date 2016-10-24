% ===================================================================== %
% HOL TRAINING COURSE: exercises on forward proof.			%
% ===================================================================== %

% ===================================================================== %
% Prove the following theorem using the HOL derived inference rules.	%
%									%
%   |- (t1 /\ (t1 ==> t2) /\ (t3:bool = t2)) ==> t3			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The required theorem is an implication, so we begin by assuming the 	%
% antecedent, from which we shal then to prove the consequent. The 	%
% derived rule for making this assumption is ASSUME.  			%
% --------------------------------------------------------------------- %
let th1 = ASSUME "t1 /\ (t1 ==> t2) /\ (t3 = t2)";;

% --------------------------------------------------------------------- %
% We now break th1 into its three conjuncts using the CONJUCTS rule.    %
% The resulting three theorems are bound to th2, th3 and th4.		%
% --------------------------------------------------------------------- %
let [th2;th3;th4] = CONJUNCTS th1;;

% --------------------------------------------------------------------- %
% It is now straightforward to prove A |- t3, where A is the assumption %
% of theorem th1.  The proof is:					%
%									%
%   1)  |- t1			[theorem th2]				%
%   2)  |- t1 ==> t2	        [theorem th3]				%
%   3)  |- t2 			[modus ponens: 1 and 2]			%
%   4)  |- t2 = t3		[symmetric form of th4]			%
%   5)  |- t3			[substituting t3 for t2 in 3 using 4]	%
%									%
% This final theorem inherits the original assumption of th1.		%
% --------------------------------------------------------------------- %
let th5 = SUBS [SYM th4] (MP th3 th2);;

% --------------------------------------------------------------------- %
% Finally, discharge the assumption to get the required result.		%
% --------------------------------------------------------------------- %
let thm0 = DISCH  "t1 /\ (t1 ==> t2) /\ (t3 = t2)" th5;;

% ===================================================================== %
% Prove the following theorem using derived inference rules:		%
%									%
%    |- (b1 ==> (b2 /\ b3)) = ((b1 ==> b2) /\ (b1 ==> b3))		%
%									%
% HINT: Prove implication in each direction, then use IMP_ANTISYM_RULE.	%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using derived inference rules:		%
% 									%
%    |- ((b1 /\ b2) ==> b3) = (b1 ==> (b2 ==> b3))			%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem by forward proof:				%
%									%
%   |- ((!x. P x ==> R x) \/ (!x. P x ==> Q x))		    	        %
%       ==>								%
%      (!x:*. P x ==> R x \/ Q x)					%
%									%
% HINT: Consider the two cases of the antecedent separately, then use   %
% the rule DISJ_CASES to put the two results together.			%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem by forward inference.			%
%									%
%   |- ?x. x ==> ~x 							%
% 									%
% HINT: first prove that |- F ==> ~F using CONTR and then use EXISTS.	%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem: 						%
%									%
%   |- (!x:*.f(x)=x) ==> (f = \x:*.x)					%
%									%
% HINTS: you may find SUBST_OCCS, RIGHT_BETA and EXT useful.		%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using derived inference rules:		%
% 									%
%    |- !P:(*#**)->bool. (!x y. P(x,y)) = (!y x. P(x,y))		%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove that every irreflexive and transitive binary relation 		%
% is asymmetric. I.e. use forward proof to deduce the theorem:		%
%									%
%   |- !R:(*#*)->bool.							%
%      (!x. ~R(x,x)) /\ (!x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==>	%
%      (!x y. R(x,y) ==> ~R(y,x))					%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using derived inference rules:		%
% 									%
%   |- ((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)			%
%									%
% HINT: you'll have to use EXISTS and CHOOSE.  Prove it by proving 	%
% implication in both directions, using EXISTS for one direction and	%
% CHOOSE for the other.							%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem:						%
%									%
%    |- (?x y. t(x,y)) ==> (?y x. t(x,y))				%
%									%
% HINT: use SELECT_RULE first and then EXISTS --- be careful.		%
% ===================================================================== %

<*** put your proof here ***>

quit();;
