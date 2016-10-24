% ===================================================================== %
% HOL TRAINING COURSE: solutions to the "swap" exercise.		%
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
% For thm, the problem was that we first specialized:			%
%									%
%   x = x |- !x y. t(x,y)	 [the given theorem thm]		%
%   x = x |- t(x,y)		 [SPEC x and y applied to thm]		%
% 									%
% But when we later try to generalize, we find we can't, because of the %
% side condition on the inference rule GEN:				%
% 									%
%     A |- t(x)								%
%   ------------ where the variable "x" is not free in A		%
%   A |- !x.t(x)							%
%									%
% We have to get around this by specializing to some variables not free	%
% in the assumptions, instead of using just x and y. The following code %
% shows how to do this.							%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% First of all, we can find out exactly which variables are free in the %
% assumptions of the input theorem using freesl and hyp.  Try executing %
% the following example.						%
% --------------------------------------------------------------------- %  
freesl(hyp thm);;

% --------------------------------------------------------------------- %
% We'll need to pick variables not free in the assumptions, that is     %
% different from all variables in the list given by freesl(hyp thm).    %
% The variant function will do this for us.				%
% --------------------------------------------------------------------- %  
variant (freesl(hyp thm)) "x:*";;

% --------------------------------------------------------------------- %
% Finally, we'll need to do alpha-conversion to get the theorem back	%
% into the desired form.  For this, we can use ALPHA_RULE.		%
% --------------------------------------------------------------------- %
ALPHA_RULE "foo:*" thm;;

% --------------------------------------------------------------------- %
% Here's the corrected rule.  Step through it for an example theorem.	%
% --------------------------------------------------------------------- %
let SWAP_FORALL th =
    let x,y_body = (dest_forall (concl th)) in	       % get first var  %
    let y,body = dest_forall y_body in		       % get 2nd var	%
    let xvar = variant (freesl (hyp th)) x in	       % pick a variant %
    let yvar = variant (xvar.(freesl (hyp th))) y in   % and another    %
    let spec_thm = SPEC yvar (SPEC xvar th) in	       % spec to THESE  %
    let x_forall = ALPHA_RULE x (GEN xvar spec_thm) in % GEN and alpha  %
	ALPHA_RULE y (GEN yvar x_forall);;	       % likewise for y %

% --------------------------------------------------------------------- %
% Here are a few test cases.						%
% --------------------------------------------------------------------- %
let th1 = ASSUME "!x y. t(x:*, y:*)";;
let th2 = ADD_ASSUM "x:*=x" th1;;
let th3 = ADD_ASSUM "y:*=y" th2;;
let th4 = ASSUME 
          (list_mk_forall 
	    (["x:*";"x:**"],
	     (mk_comb ("t:* # ** -> bool", mk_pair("x:*","x:**")))));;


% --------------------------------------------------------------------- %
% The following example for which SWAP_FORALL don't work illustrates	%
% the problem of thinking of everything when trying to get a derived	%
% inference rule to be 100% correct.					%
% --------------------------------------------------------------------- %
let th5 = ASSUME "!x x. t(x:*, x:*)";;

quit();;
