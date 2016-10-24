% ===================================================================== %
% HOL TRAINING COURSE: exercises in the HOL syntax functions.		%
%									%
% The aim of these exercises to get you acquainted with the HOL syntax 	%
% functions, which are used to manipulate terms of higher order logic   %
% in ml.								%
% ===================================================================== %

% --------------------------------------------------------------------- %
% First, an example:							%
%									%
% Construct the following term using only the primitive syntax 		%
% for higher order logic.						%
%									%
% "!b a. (b ==> a) = (~a ==> ~b)"					%
%									%
% I.e. don't type anything in between double quotes --- "....".		%
% --------------------------------------------------------------------- %

let term = 
    let bool = mk_type (`bool`,[]) in
    let a = mk_var (`a`, bool) and
        b = mk_var (`b`, bool) in
    let imp1 = mk_imp(a,b) and
        imp2 = mk_imp(mk_neg b, mk_neg a) in
        list_mk_forall ([b;a], mk_eq (imp1,imp2));;

% --------------------------------------------------------------------- %
% See if the term is correct...						%
% --------------------------------------------------------------------- %
term = "!b a. (a ==> b) = (~b ==> ~a)";;

% --------------------------------------------------------------------- %
% Construct the following term using only the HOL syntax functions.     %
%									%
%     "!P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))"		%
%									%
% Hint: first construct the types you'll need, then construct the 	%
% the variables, then construct the term by constructing appropriate    %
% sub-terms and putting them together.					%
% --------------------------------------------------------------------- %

let wop =  < *** put your code here *** > ;;

% --------------------------------------------------------------------- %
% See if the term is correct...						%
% --------------------------------------------------------------------- %
wop = "!P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))";;


% --------------------------------------------------------------------- %
% Write an ml program that will universally quantify all free variables %
% in a term.								%
% --------------------------------------------------------------------- %

let quant tm =  < *** put your code here *** > ;;

% --------------------------------------------------------------------- %
% Try it out....							%
% --------------------------------------------------------------------- %
quant "(a+b=c) /\ (!a.a+b=a)";;


% --------------------------------------------------------------------- %
% Write an ml program that will take a term of the form !n. tm[n] where %
% n is of type :num and return two terms corresponding to the base and  %
% step cases of an induction that would prove |- !n. tm[n].  		%
%									%
% I.e. induct "!n. n > 0" would return "0 > 0" and "n>0 ==> SUC n>0"    % 
%									%
% If the term is NOT of the form !n. tm[n], fail with the message: 	%
% 	"induct --- bad term"						%
%									%
% Hint: use subst.							%
% --------------------------------------------------------------------- %

let induct tm =  < *** put your code here *** > ;;

% --------------------------------------------------------------------- %
% Try your program out on the following terms:				%
% --------------------------------------------------------------------- %
induct "!n. n>0";;
induct "!n m. ((n+m=n) = (!n.n-m=n))";;

% --------------------------------------------------------------------- %
% Write an ml program that takes a term and changes all subterms of the %
% form "~!x.tm" to "?x.~tm".						%
% --------------------------------------------------------------------- %

letrec chng tm =
       if ((is_neg tm) & (is_forall (snd(dest_comb tm))))
          then < *** do something *** >
          else < *** do something else *** >;;

% --------------------------------------------------------------------- %
% Test your program as follows:						%
% --------------------------------------------------------------------- %
let x = chng "~!a b c d. a /\ b /\ c /\ d";;
x = chng x;;

% ---------------------------------------------------------------------	%
% Write an ML program:							%
%									%
% find_terms: (term -> bool) -> term -> term list			%
%									%
% that takes a predicate p:term->bool and a term t:term and returns a	%
% list of ALL the subterms in t that satisfy p.				%
% --------------------------------------------------------------------- %

let find_terms p tm =
    letrec accum tl p tm = < *** body of defn of accum *** > in
           accum [] p tm;;

% --------------------------------------------------------------------- %
% Test your program on the following:					%
% (should return: ["2"; "1"; "$+"; "$+ 1"; "1 + 2"] : term list)	%
% --------------------------------------------------------------------- %
find_terms (\tm.true) "1+2";;

% --------------------------------------------------------------------- %
% Test your program on the following:					%
% (should return: ["$+ 1"; "1 + 2"] : term list)			%
% --------------------------------------------------------------------- %
find_terms is_comb "1+2";;

% --------------------------------------------------------------------- %
% Test your program on the following:					%
% (should return: ["$+ x"; "$+ 1"] : term list)				%
% --------------------------------------------------------------------- %
find_terms (\tm. is_comb tm & (rator tm = "$+")) "!x. ?y. 1+x+y=2";;

% ---------------------------------------------------------------------	%
% Use find_terms, defined above, to convert terms of the form:		%
%									%
%	P [@x.P[x]]   (i.e. P with a subterm "@x.P[x]")			%
%									%
% to terms of the form:							%
%									%
%	?x.P[x]								%
%									%
% E.g. sel "(@x.x=y)=y" should return "?x.x=y".				%
%									%
% Hint:  1) use find_terms to find all @-subterms			%
%	 2) look in the resulting list of subterms for one that gives	%
%	    the original term back when it is substituted in itself in	%
%	    an appropriate way.						%
% ---------------------------------------------------------------------	%

let sel tm = 
    let epsl = find_terms is_select tm in
        < *** put your code here *** >;;

% ---------------------------------------------------------------------	%
% Test your program as follows:						%
% (should return : "?x. x = y" : term					%
%		   "?p. m = n + (p + 1)" : term				%
%		   "?y. (@x. ?y. x = y) = y" : term			%
% ---------------------------------------------------------------------	%
sel "(@x.x=y)=(y:*)";;
sel "m = n + ((@p. m = n + (p + 1)) + 1)";;
sel "(@x:*. ?y. x = y) = (@y. (@x. ?y. x = y) = y)";;

% ---------------------------------------------------------------------	%
% The following exercises illustrate two features of the representation %
% of higher order logic in ML --- namely:				%
%									%
%	1) two variables with the same name but different types		%
%	   ARE allowed in the same term, but have to be constructed	%
%	   with the syntax functions and can't be entered between	%
%	   quotes ---- "....".						%
%									%
%	2) is_imp, dest_imp, etc work on ~tm --- being equivalent	%
%	   to tm ==> F.							%
% ---------------------------------------------------------------------	%

% --------------------------------------------------------------------- %
% Construct the following term, use syntax functions if you have to.	%
% "!x:*. !x:**. f(x:*) = (x:**)"					%
% ---------------------------------------------------------------------	%

let term =   < *** put your code here *** > ;;

% ---------------------------------------------------------------------	%
% Print out your term to show the types...				%
% ---------------------------------------------------------------------	%
show_types true;;
term;;
show_types false;;

% --------------------------------------------------------------------- %
% Write an ml program that takes a term and changes all subterms of the %
% form "A ==> B" to "~A \/ B".	 Exception: do not change terms of the  %
% form ~X (which behave like terms of the form X ==> F).		%
% ---------------------------------------------------------------------	%

letrec change tm =  < *** put your code here *** > ;;

% ---------------------------------------------------------------------	%
% Test your program as follows:						%
% ---------------------------------------------------------------------	%
let x = change "!P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))";;
x = change x;;

