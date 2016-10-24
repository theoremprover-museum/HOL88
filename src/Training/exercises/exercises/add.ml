% ===================================================================== %
% HOL TRAINING COURSE: an "induction" exercise.				%
% ===================================================================== %

% ===================================================================== %
% It is an elementry theorem of arithmetic that:			%
%									%
%     1 + 3 + ... + 2n+1 = (n+1)**2					%
%									%
% The exercise is to  prove the above theorem for all n.  This will	%
% involve:								%
%  	    								%
%    1) defining a function which will represent the sum on 		%
%	the left hand side, "add" say.  You want:			%
%									%
%	    add 0 = 1							%
%	    add 1 = 1 + 3						%
%	    add 2 = 1 + 3 + 5 				 		%
%	 	... etc							%
%									%
%       You'll have to define add:num->num by primitive recursion.	%
%									%
%   2) using induction to prove that:					%
%									%
%	    |- !n. add n = (n+1) EXP 2.					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The solution begins by creating a new theory.				%
% --------------------------------------------------------------------- %
new_theory `add`;;

% --------------------------------------------------------------------- %
% Now, define the function "add" by primitive recursion.		%
% --------------------------------------------------------------------- %
let add = <*** put your definition here ***>;;

% --------------------------------------------------------------------- %
% Finished making definitions, so close the theory.			%
% --------------------------------------------------------------------- %
close_theory();;

% --------------------------------------------------------------------- %
% Now do the proof.  Note the ML identifier EXP gives the definition of %
% the logic function "EXP:num->num->num".				%
% --------------------------------------------------------------------- %
let ADD_THM = 
    prove_thm
    (`ADD_THM`,
     "!n. add n = (n+1) EXP 2",
     <*** put an appropriate tactic here ***>);;


quit();;
