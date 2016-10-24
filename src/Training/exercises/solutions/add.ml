% ===================================================================== %
% HOL TRAINING COURSE: solution to the "induction" exercise.		%
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
let add = 
    new_prim_rec_definition
       (`add`,
	"(add 0 = 1) /\
	 (add (SUC n) = (2*(SUC n)) + 1 + (add n))");;

% --------------------------------------------------------------------- %
% Finished making definitions, so close the theory.			%
% --------------------------------------------------------------------- %
close_theory();;

% --------------------------------------------------------------------- %
% Now, here's the proof. Try stepping through it one tactic at a time	%
% using the subgoal package to see what's going on.			%
% --------------------------------------------------------------------- %
let ADD_THM = 
    prove_thm
    (`ADD_THM`,
     "!n. add n = (n+1) EXP 2",
     let numths = (map num_CONV ["1";"2"]) in
     PURE_REWRITE_TAC (numths @ [ADD_CLAUSES;EXP;MULT_CLAUSES]) THEN
     INDUCT_TAC THENL
     [REWRITE_TAC (numths @ [add;ADD_CLAUSES;MULT_CLAUSES]);
      ASM_REWRITE_TAC (numths @ [add;ADD_CLAUSES;MULT_CLAUSES]) THEN
      let thm = SPECL ["m:num";"(n * n)"] ADD_SYM in
      REWRITE_TAC [ADD_ASSOC;thm]]);;

quit();;
