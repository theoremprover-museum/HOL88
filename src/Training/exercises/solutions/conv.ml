% ===================================================================== %
% HOL TRAINING COURSE: solution to the "conv" exercise.			%
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

% --------------------------------------------------------------------- %
% Here is one possible implementation.					%
% --------------------------------------------------------------------- %

let FUN_EQ_CONV tm = 
    let vs = frees tm in			% get free vars in tm   %
    let ty = type_of(lhs tm) in			% get type of lhs	%
    let op,xty = (I # hd)(dest_type ty) in	% type that x must have %
    if op = `fun` 				% is type operator -> ? %
       then let x = (variant vars "x:^xty") in
            let imp1 = DISCH tm (GEN x (AP_THM (ASSUME tm) x)) in
            let asm = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x))) in
            IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))
       else failwith `FUN_EQ_CONV`;;

quit();;
