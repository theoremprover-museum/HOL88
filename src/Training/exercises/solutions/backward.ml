% ===================================================================== %
% HOL TRAINING COURSE: solutions to the exercises on backward proof.	%
% ===================================================================== %

% ===================================================================== %
% Prove the following theorem using tactics:				%
%									%
%   |- (t1 /\ (t1 ==> t2) /\ (t3:bool = t2)) ==> t3			%
% ===================================================================== %

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

% --------------------------------------------------------------------- %
% Each subgoal can be solveed just be breaking up the conjunctions, 	%
% putting antecedents on the assumption list and the using RES_TAC.	%
% --------------------------------------------------------------------- %
expand (REPEAT STRIP_TAC THEN RES_TAC);;	% For first subgoal	%
expand (REPEAT STRIP_TAC THEN RES_TAC);;        % For second subgoal	%

% --------------------------------------------------------------------- %
% Having found the proof, write the appropriate composite tactic and	%
% prove the theorem using PROVE.					%
% --------------------------------------------------------------------- %

let thm1 =
    PROVE("b1 ==> b2 /\ b3 = (b1 ==> b2) /\ (b1 ==> b3)",
          EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

% ===================================================================== %
% Prove the following theorem using tactics:				%
% 									%
%    |- ((b1 /\ b2) ==> b3) = (b1 ==> (b2 ==> b3))			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The tactic proof is exactly the same as for the previous theorem.	%
% Use the subgoal package to apply the tactics one at a time, if you	%
% wish to see how the proof goes.					%
% --------------------------------------------------------------------- %

let thm2 =
    PROVE("((b1 /\ b2) ==> b3) = (b1 ==> (b2 ==> b3))",
          EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

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

% --------------------------------------------------------------------- %
% The proof starts by moving the antecedent into the assumptions. This	%
% splits the goal into two subgoals, since the antecedent is a		%
% disjunction of two cases.						%
% --------------------------------------------------------------------- %

expand (REPEAT STRIP_TAC);;

% --------------------------------------------------------------------- %
% Both subgoals can be proved using the same tactic: use RES_TAC to get	%
% as a consequence of the two assumptions one of the two disjuncts in	%
% the conclusion of the goal.  Then rewrite with the assumptions to 	%
% solve the goal.							%
% --------------------------------------------------------------------- %

expand (RES_TAC THEN ASM_REWRITE_TAC[]);;
expand (RES_TAC THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------- %
% Having found the proof, write the appropriate composite tactic and	%
% prove the theorem using PROVE.					%
% --------------------------------------------------------------------- %

let thm3 =
    PROVE("((!x. P x ==> R x) \/ (!x. P x ==> Q x))
             ==>
           (!x:*. P x ==> R x \/ Q x)",
          REPEAT STRIP_TAC THEN
          RES_TAC THEN ASM_REWRITE_TAC[]);;
      

% ===================================================================== %
% Prove the following theorem using tactics.				%
%									%
%   |- ?x. x ==> ~x 							%
% 									%
% HINT: you need to start with EXISTS_TAC.				%
% ===================================================================== %

set_goal([], "?x. x ==> ~x");;

% --------------------------------------------------------------------- %
% A thing that satisfies x ==> ~x is "F", since "F" implies anything.   %
% We therefore suggest "F" as a witness for the existential assertion	%
% we are trying to prove.						%
% --------------------------------------------------------------------- %

expand (EXISTS_TAC "F");;

% --------------------------------------------------------------------- %
% When STRIP_TAC moves an antecedent "F" into the assumptions, it is 	%
% recognized as the assumption of falsity, and so the goal is solved.	%
% --------------------------------------------------------------------- %

expand STRIP_TAC;;

% --------------------------------------------------------------------- %
% The composite tactic and proof.					%
% --------------------------------------------------------------------- %

let thm4 = PROVE ("?x. x ==> ~x", EXISTS_TAC "F" THEN STRIP_TAC);;

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
set_goal([],"(!x:*.f(x)=x) ==> (f = \x:*.x)");;

% --------------------------------------------------------------------- %
% Put the antecedent on the assumption list.				%
% --------------------------------------------------------------------- %
expand STRIP_TAC;;

% --------------------------------------------------------------------- %
% We now need to prove equality of two functions, so use FUN_EQ_TAC.	%
% --------------------------------------------------------------------- %
expand FUN_EQ_TAC;;

% --------------------------------------------------------------------- %
% Simplify "(\x. x)x" by beta-reduction (BETA_TAC).			%
% --------------------------------------------------------------------- %
expand BETA_TAC;;

% --------------------------------------------------------------------- %
% Rewriting with the assumption now solves the goal.			%
% --------------------------------------------------------------------- %
expand (ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------- %
% Put the tactics together, and do the proof.				%
% --------------------------------------------------------------------- %
let thm5 =
    PROVE("(!x:*. f x = x) ==> (f = (\x. x))",
	  STRIP_TAC THEN
          FUN_EQ_TAC THEN
          BETA_TAC THEN
          ASM_REWRITE_TAC[]);;

% ===================================================================== %
% Prove the following theorem using tactics.				%
% 									%
%    |- !P:(*#**)->bool. (!x y. P(x,y)) = (!y x. P(x,y))		%
% ===================================================================== %

set_goal ([], "!P:(*#**)->bool. (!x y. P(x,y)) = (!y x. P(x,y))");;

% --------------------------------------------------------------------- %
% Strip the quantifier and reduce to two implicative sub-goals 		%
% --------------------------------------------------------------------- %
expand (GEN_TAC THEN EQ_TAC);;

% --------------------------------------------------------------------- %
% Solve each subgoal by rewriting the conclusion with the antecedent.	%
% --------------------------------------------------------------------- %
expand (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
expand (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------- %
% The complete proof: a slight reorganization has been done here, with	%
% the recognition that 							%
%									%
%   GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC				%
%									%
% can be replaced by REPEAT (STRIP_TAC ORELSE EQ_TAC).			%
% --------------------------------------------------------------------- %

let thm6 =
    PROVE("!P:(*#**)->bool. (!x y. P(x,y)) = (!y x. P(x,y))",
          REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC []);;

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

% --------------------------------------------------------------------- %
% The proof is completely trivial, but note that RES_TAC is used twice.	%
% --------------------------------------------------------------------- %
expand (REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;

let thm7 =
    PROVE("!R. (!x:*. ~R(x,x)) /\ (!x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==>
                  (!x y. R(x,y) ==> ~R(y,x))",
          REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;

% ===================================================================== %
% Prove the following theorem using tactics:				%
% 									%
%   |- ((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)			%
%									%
% ===================================================================== %

set_goal([],"((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)");;

% --------------------------------------------------------------------- %
% Reduce to two implications						%
% --------------------------------------------------------------------- %
expand EQ_TAC;;

% --------------------------------------------------------------------- %
% Solve the first sub-goal using STRIP_TAC and RES_TAC.			%
% --------------------------------------------------------------------- %
expand (REPEAT STRIP_TAC THEN RES_TAC);;

% --------------------------------------------------------------------- %
% Use RES_TAC and rewriting to solve the other subgoal. 		%
% --------------------------------------------------------------------- %
expand (REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

% --------------------------------------------------------------------- %
% The whole proof, transcribed exactly from the above.			%
% --------------------------------------------------------------------- %

let thm8 = 
    PROVE("((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)",
          EQ_TAC THENL
           [REPEAT STRIP_TAC THEN RES_TAC;
            REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []]);;

% --------------------------------------------------------------------- %
% The whole proof, merging the proofs of the two cases.			%
% --------------------------------------------------------------------- %

let thm8 = 
    PROVE("((?x:*.t1(x)) ==> t2) = (!x. t1(x) ==> t2)",
          REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
          RES_TAC THEN ASM_REWRITE_TAC []);;


% ===================================================================== %
% Prove the following theorem using tactics:				%
%									%
%    |- (?x y. t(x,y)) ==> (?y x. t(x,y))				%
%									%
% HINT: use EXISTS_TAC.							%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The proof is trivial. Investigate using the subgoal package.		%
% --------------------------------------------------------------------- %

let thm9 =
    PROVE("(?x y. t(x:*,y:**)) ==> (?y x. t(x,y))",
          STRIP_TAC THEN
          EXISTS_TAC "y:**" THEN 
          EXISTS_TAC "x:*" THEN
          ASM_REWRITE_TAC[]);;

quit();; 




