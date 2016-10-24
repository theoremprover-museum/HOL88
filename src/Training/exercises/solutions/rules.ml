% ===================================================================== %
% HOL TRAINING COURSE: solutions to the "rules" exercise.		%
% ===================================================================== %

% ===================================================================== %
% The following code shows how one might go about deriving the		% 
% following two inference rules:					%
%									%
%	NOT_EXISTS :		|- ~ ?x. tm[x]				%
%			     --------------------			%
%				|- !x. ~tm[x]				%
%									%
%									%
%	FORALL_NOT :		|- !x. ~tm[x]				%
%			     --------------------			%
%				|- ~ ?x. tm[x]				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The definition of NOT_EXISTS is as follows:				%
% --------------------------------------------------------------------- %

let NOT_EXISTS th = 
    let x,tm = dest_exists (dest_neg (concl th)) in
    let asm = EXISTS (rand (concl th), x) (ASSUME tm) in
        GEN x (NOT_INTRO (DISCH tm (MP th asm)));;

% --------------------------------------------------------------------- %
% Let's have a look at how NOT_EXISTS works by going step by step	%
% through an example. We begin by constructing a theorem of the 	%
% appropriate form for input to the rule.				%
% --------------------------------------------------------------------- %
let th = ASSUME "~?x:bool. tm(x)";;

% --------------------------------------------------------------------- %
% First take the theorem th apart to get the variable and body.		%
% --------------------------------------------------------------------- %
let x,tm = dest_exists (dest_neg (concl th));;

% --------------------------------------------------------------------- %
% Now, if we assume tm[x] then we can prove that ?x.tm[x].		%
% --------------------------------------------------------------------- %
let asm = EXISTS (rand (concl th), x) (ASSUME tm);;

% --------------------------------------------------------------------- %
% Have a look at the assumption of asm.					%
% --------------------------------------------------------------------- %
hyp asm;;

% --------------------------------------------------------------------- %
% Now, asm and th form a contradiction. Modus ponens works on negations %
% so we can just do the following to derive falsity:			%
% --------------------------------------------------------------------- %
let th1 = MP th asm;;

% --------------------------------------------------------------------- %
% Our aim is to get ~tm(x), which we can do by discharging the relevant %
% assumption and then using NOT_INTRO.					%
% --------------------------------------------------------------------- %
let th2 = DISCH tm th1;;
let th3 = NOT_INTRO th2;;

% --------------------------------------------------------------------- %
% Finally, we just generalize the variable x.				%
% --------------------------------------------------------------------- %
let result = GEN x th3;;

% ===================================================================== %
% Now write the reverse inference rule: FORALL_NOT.			%
% 									%
% HINT: assume that ?x.tm[x] and then derive a contradiction. You may   %
% have to use SELECT_RULE or CHOOSE.					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Here is one possible solution (using SELECT_RULE).			%
% --------------------------------------------------------------------- %
let FORALL_NOT th = 
    let x,tm = (I # dest_neg) (dest_forall (concl th)) in
    let asm = ASSUME (mk_exists (x,tm)) in
    let sthm = SELECT_RULE asm in
    let fthm = MP (SPEC (rand (concl sthm)) th) sthm in
        NOT_INTRO (DISCH (mk_exists (x,tm)) fthm);;

% --------------------------------------------------------------------- %
% And here is another (using CHOOSE).  This one is better.		%
% --------------------------------------------------------------------- %
let FORALL_NOT th = 
    let x,tm = (I # dest_neg) (dest_forall (concl th)) in
    let asm = MP (SPEC x th) (ASSUME tm) in
    let cth = CHOOSE (x,ASSUME (mk_exists(x,tm))) asm in
        NOT_INTRO (DISCH (mk_exists(x,tm)) cth);;

quit();;
