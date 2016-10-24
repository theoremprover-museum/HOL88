% ===================================================================== %
% HOL TRAINING COURSE: exercise in defining a "conv".			%
% ===================================================================== %

% ===================================================================== %
% A conversion is a particular kind of inference rule in HOL that maps	%
% terms to equations.  A typical example is BETA_CONV, which in the 	%
% standard notation used for inference rules looks like:		%
%									%
%  									%
%      ---------------------  BETA_CONV "(\x.u) v"			%
%       |- (\x.u)v = u[v/x]						%
%									%
% In general, a conversion c:term->thm is a function that maps a term	%
% "t" to a theorem |- t = t', where t' is some useful transformation 	%
% of t (in the case of BETA_CONV, the beta-reduction of t).		%
%									%
% The exercise if to define a conversion FUN_EQ_CONV with the following %
% inference-rule specification:						%
%									%
%        								%
%      -----------------------------  FUN_EQ_CONV "f = g"		%
%       |- (f = g) = !x. f x = g x					%
%		 							%
% Note that f and g must be functions and that FUN_EQ_CONV must choose	%
% an "x" not free in f or g.     					%
% ===================================================================== %

let FUN_EQ_CONV tm = 
    < *** put your code here ***>;;

quit();;
