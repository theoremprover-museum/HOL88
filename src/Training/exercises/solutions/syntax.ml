% ===================================================================== %
% HOL TRAINING COURSE: solutions to the syntax functions exercises.	%
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
% --------------------------------------------------------------------- %

let wop = 
    let num = mk_type (`num`,[]) and
        bool = mk_type (`bool`,[]) in
    let pred = mk_type (`fun`, [num;bool]) in
    let less_ty = mk_type (`fun`, [num;pred]) in
    let n = mk_var (`n`,num) and
        m = mk_var (`m`,num) and
        P = mk_var (`P`,pred) in
    let Pn = mk_comb(P,n) and
        less = list_mk_comb (mk_const(`<`,less_ty),[m;n]) and
        notPm = mk_neg(mk_comb(P,m)) in
    let ante = mk_exists(n, Pn) and
        conseq = mk_exists(n,mk_conj(Pn, mk_forall(m,mk_imp(less,notPm)))) in
        mk_forall(P, mk_imp(ante, conseq));;

% --------------------------------------------------------------------- %
% See if the term is correct...						%
% --------------------------------------------------------------------- %
wop = "!P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))";;


% --------------------------------------------------------------------- %
% Write an ml program that will universally quantify all free variables %
% in a term.								%
% --------------------------------------------------------------------- %

let quant tm = list_mk_forall(frees tm, tm);;

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

let induct tm = 
    (let n, body = dest_forall tm in
     (subst ["0",n] body, mk_imp(body,subst ["SUC ^n", n] body)))?
    failwith `induct --- bad term`;;

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
          then let var,tm = dest_forall(snd(dest_comb tm)) in
		   mk_exists(var,chng(mk_neg tm))
          else if is_comb tm 
	          then mk_comb(chng(rator tm), chng(rand tm))
	          else if is_abs tm 
			  then (mk_abs o (I # chng) o dest_abs) tm
		          else tm;;

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
    letrec accum tl p tm =
           let tl' = if p tm then tm.tl else tl in
	       if is_abs tm then 
	          accum tl' p (snd (dest_abs tm)) else
	       if is_comb tm then
	          accum (accum tl' p (rator tm)) p (rand tm) else
	          tl' in
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
    let findfn t = 
	subst [t, fst (dest_select t)] (snd (dest_select t)) = tm in
    let select = find findfn epsl in
    mk_exists(dest_select select);;

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

let term = 
    let eqn = mk_eq("f(x:*):**","x:**") in
              list_mk_forall (["x:*";"x:**"],eqn);;

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

letrec change tm =
       if (is_imp tm & not(is_neg tm))
          then let (A,B) = dest_imp tm in
               mk_disj(mk_neg (change A), (change B))
          else if is_comb tm 
	          then mk_comb(change(rator tm), change(rand tm))
	          else if is_abs tm 
			  then (mk_abs o (I # change) o dest_abs) tm
		          else tm;;

% ---------------------------------------------------------------------	%
% Test your program as follows:						%
% ---------------------------------------------------------------------	%
let x = change "!P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))";;
x = change x;;

