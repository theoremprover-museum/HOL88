% ===================================================================== %
% HOL TRAINING COURSE: exercise in writing a derived inference rule.	%
% ===================================================================== %

% ===================================================================== %
% The following code shows how one might go about deriving the		% 
% following inference rule for swapping the order of two universally	%
% quantified variables.							%
%									%
%	SWAP_FORALL		A |- !x y. t[x,y]			%
%			     ----------------------			%
%				A |- !y x. t[x,y]			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% As a start in writing SWAP_FORALL, we first try to do the proof for	%
% a specific case. The following theorem is representative of what we   %
% wish to prove in general:						%
%									%
%   |- (!x y. t(x,y)) ==> !y x. t(y,x)					%
%									%
% so we begin by finding a proof of this theorem.			%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Begin by assuming the antecedant of the theorem to be proved.  This   %
% gives th1, which has the form of the kind of theorem that will be 	%
% expected as input to our derived rule.				%
% --------------------------------------------------------------------- %
let th1 = ASSUME "!x y. t(x:*,y:**)";;

% --------------------------------------------------------------------- %
% Now, just specialize the two variables and then generalize them in 	%
% the reverse order.  The result, th3, is what we want our derived 	%
% inference rule to return.						%
% --------------------------------------------------------------------- %
let th2 = SPEC "y:**" (SPEC "x:*" th1);;
let th3 = GEN "y:**" (GEN "x:*" th2);;

% --------------------------------------------------------------------- %
% This looks really easy. Let's try and make a rule that does the same  %
% proof in general, for any input theorem th. The proof is identical,	%
% except that we need to extract from the input theorem the names of 	%
% the two variables.							%
% --------------------------------------------------------------------- %
let SWAP_FORALL th =
    let x,y_body = (dest_forall (concl th)) in    % get first variable  %
    let y,body = dest_forall y_body in		  % get second variable %
    GEN y (GEN x (SPEC y (SPEC x th)));;	  % do the swap		%

% --------------------------------------------------------------------- %
% Now, let's try it out on the theorem th1.				%
% --------------------------------------------------------------------- %
SWAP_FORALL th1;;

% --------------------------------------------------------------------- %
% It seems to work! But suppose the variable x and/or y occurs free in	%
% the assumptions of the input theorem.  To provide a concrete example, %
% let's make a theorem for which this is the case:			%
% --------------------------------------------------------------------- %
let thm = ADD_ASSUM "x:*=x" th1;;

% --------------------------------------------------------------------- %
% Now, if we try our rule on thm, it will fail.				%
% --------------------------------------------------------------------- %
SWAP_FORALL thm;;

% ===================================================================== %
% EXERCISE: Fix SWAP_FORALL to get around this problem.			%
%                                                                       %
% HINTS: 								%
%                                                                       %
%	1)  If theorem is a thm, evaluating:				%
%									%
%		freesl (hyp theorem) 					%
%									%
%	    will give you a list of the free variables in the 		%
%	    assumptions of theorem.					%
%									%
%	 2) if l is a list of variables (a term list), and x is a 	%
%	    variable (term), executing:					%
%									%
%		variant l x						%
%									%
%	    will give you a primed variant of x which does not occur in %
%	    the list l.							%
% 									%
%	 3) the rule ALPHA_RULE (defined below) will rename a bound	%
%	    variable:							%
%									%
%				!x. t[x]				%
%			    ================    ALPHA_RULE "y"		%
%				!y. t[y]				%
% ===================================================================== %

let ALPHA_RULE t = CONV_RULE (GEN_ALPHA_CONV t);;

% --------------------------------------------------------------------- %
% To get an idea of what freesl, variant, and ALPHA_RULE do, try:	%
% --------------------------------------------------------------------- %
freesl(hyp thm);;
variant (freesl(hyp thm)) "x:*";;
ALPHA_RULE "foo:*" thm;;


% --------------------------------------------------------------------- %
% Now, write the rule. It starts the in same way as the old version.	%
% --------------------------------------------------------------------- %
let SWAP_FORALL th =
    let x,y_body = (dest_forall (concl th)) in	       % get first var  %
    let y,body = dest_forall y_body in		       % get 2nd var	%
	< *** put your code here *** >;;


% --------------------------------------------------------------------- %
% Try your rule out on the following theorems.				%
% --------------------------------------------------------------------- %
let th1 = ASSUME "!x y. t(x:*, y:*)";;
let th2 = ADD_ASSUM "x:*=x" th1;;
let th3 = ADD_ASSUM "y:*=y" th2;;
let th4 = ASSUME 
          (list_mk_forall 
	    (["x:*";"x:**"],
	     (mk_comb ("t:* # ** -> bool", mk_pair("x:*","x:**")))));;

% --------------------------------------------------------------------- %
% Does your rule also work on the following theorem? (mine doesn't)	%
% --------------------------------------------------------------------- %
let th5 = ASSUME "!x x. t(x:*, x:*)";;

quit();;
