% ===================================================================== %
% HOL TRAINING COURSE: exercises on backward (tactic) proof.		%
% ===================================================================== %

% ===================================================================== %
% Prove the following theorem using tactics:				%
%									%
%   |- (t1 /\ (t1 ==> t2) /\ (t3:bool = t2)) ==> t3			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The first proof is done for you.					%
% --------------------------------------------------------------------- %

set_goal([], "(t1 /\ (t1 ==> t2) /\ (t3 = t2)) ==> t3");;

% --------------------------------------------------------------------- %
% First, put the antecedent on the assumption list, breaking up the	%
% conjunction into three separate assumptions.				%
% --------------------------------------------------------------------- %

expand(REPEAT STRIP_TAC);;

% --------------------------------------------------------------------- %
% We can now rewrite the conclusion of the goal "t3" with the		%
% assumption that "t3 = t2".						%
% --------------------------------------------------------------------- %

expand(PURE_ONCE_ASM_REWRITE_TAC []);;

% --------------------------------------------------------------------- %
% RES_TAC will now infer "t2" from the assumptions "t1" and "t1==>t2".  %
% This will solve the goal, as RES_TAC recognizes that "t2" is just the %
% conclusion of the goal itself.					%
% --------------------------------------------------------------------- %

expand RES_TAC;;

% --------------------------------------------------------------------- %
% Having found our proof using the subgoal package, we can now write a	%
% composite tactic that does the whole proof, and use PROVE to get the  %
% theorem that is proved.						%
% --------------------------------------------------------------------- %

let thm0 =
    PROVE ("(t1 /\ (t1 ==> t2) /\ (t3 = t2)) ==> t3",
           REPEAT STRIP_TAC THEN
           PURE_ONCE_ASM_REWRITE_TAC [] THEN
           RES_TAC);;

% ===================================================================== %
% Prove the following theorem using tactics.				%
%									%
%    |- (b1 ==> (b2 /\ b3)) = ((b1 ==> b2) /\ (b1 ==> b3))		%
%									%
% HINT: Prove implication in each direction, using EQ_TAC.		%
% ===================================================================== %

set_goal([],"(b1 ==> (b2 /\ b3)) = ((b1 ==> b2) /\ (b1 ==> b3))");;


% --------------------------------------------------------------------- %
% First, split the equivalence, reducing it to two implications.	%
% --------------------------------------------------------------------- %
expand EQ_TAC;;

<*** put your proof here ***>

% --------------------------------------------------------------------- %
% Having found the proof, write the appropriate composite tactic and	%
% prove the theorem using PROVE.					%
% --------------------------------------------------------------------- %

let thm1 =
    PROVE("b1 ==> b2 /\ b3 = (b1 ==> b2) /\ (b1 ==> b3)",
          EQ_TAC THEN <*** put your tactuic here ***>);;

% ===================================================================== %
% Prove the following theorem using tactics:				%
% 									%
%    |- ((b1 /\ b2) ==> b3) = (b1 ==> (b2 ==> b3))			%
% ===================================================================== %

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using tactics.				%
%									%
%   |- ((!x. P x ==> R x) \/ (!x. P x ==> Q x))		    	        %
%       ==>								%
%      (!x:*. P x ==> R x \/ Q x)					%
% ===================================================================== %

set_goal([], "((!x. P x ==> R x) \/ (!x. P x ==> Q x))
                ==>
              (!x:*. P x ==> R x \/ Q x)");;

<*** put your proof here ***>

% --------------------------------------------------------------------- %
% Having found the proof, write the appropriate composite tactic and	%
% prove the theorem using PROVE.					%
% --------------------------------------------------------------------- %

let thm3 =
    PROVE("((!x. P x ==> R x) \/ (!x. P x ==> Q x))
             ==>
           (!x:*. P x ==> R x \/ Q x)",
          <*** put your tactic here ***>);;

% ===================================================================== %
% Prove the following theorem using tactics.				%
%									%
%   |- ?x. x ==> ~x 							%
% 									%
% HINT: you need to start with EXISTS_TAC.				%
% ===================================================================== %

set_goal([], "?x. x ==> ~x");;


<*** put your proof here ***>


% ===================================================================== %
% Prove the following theorem: 						%
%									%
%   |- (!x:*.f(x)=x) ==> (f = \x:*.x)					%
%									%
% HINT: use the tactic FUN_EQ_TAC defined below. This has the following %
% specification as a tactic:						%
%									%
%	                 f = g  					%
%                 ====================   FUN_EQ_TAC 			%
%		     !x. f x = g x					%
%									%
% Note that f and g must be functions for this to work.			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, define the tactic.						%
% --------------------------------------------------------------------- %
let FUN_EQ_TAC = CONV_TAC FUN_EQ_CONV;;

% --------------------------------------------------------------------- %
% Now, the proof.							%
% --------------------------------------------------------------------- %
 
<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using tactics.				%
% 									%
%    |- !P:(*#**)->bool. (!x y. P(x,y)) = (!y x. P(x,y))		%
% ===================================================================== %

set_goal ([], "!P:(*#**)->bool. (!x y. P(x,y)) = (!y x. P(x,y))");;

<*** put your proof here ***>


% ===================================================================== %
% Prove that every irreflexive and transitive binary relation 		%
% is asymmetric. I.e. use tactics to prove the theorem:			%
%									%
%   |- !R:(*#*)->bool.							%
%      (!x. ~R(x,x)) /\ (!x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==>	%
%      (!x y. R(x,y) ==> ~R(y,x))					%
% ===================================================================== %

set_goal([], "!R. (!x:*. ~R(x,x)) /\ (!x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==>
                  (!x y. R(x,y) ==> ~R(y,x))");;

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using tactics:				%
% 									%
%   |- ((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)			%
%									%
% ===================================================================== %

set_goal([],"((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)");;

<*** put your proof here ***>

% ===================================================================== %
% Prove the following theorem using tactics:				%
%									%
%    |- (?x y. t(x,y)) ==> (?y x. t(x,y))				%
%									%
% HINT: use EXISTS_TAC.							%
% ===================================================================== %

<*** put your proof here ***>

quit();; 
