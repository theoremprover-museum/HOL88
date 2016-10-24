% sidecond.ml                                           (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Function to create a `result_of_match' of all the ways of matching a %
% termpattern within a term.                                           %

% The function tries to match the termpattern against the term. If this is %
% successful the resulting matching is made the first item of the          %
% `result_of_match'. The rest of the `result_of_match' will be null if `t' %
% is a variable or a constant, since `t' cannot be split in such cases.    %

% If `t' is an abstraction, a match is tried against the body. If `t' is a %
% combination, matches are tried against both the rator and the rand. Both %
% these return `result_of_matches' which have to be appended using the     %
% function `approms'.                                                      %

% Note that the function requires a null argument before it actually does  %
% any evaluation. This is to keep the computation as lazy as possible.     %

letrec containsfn p t () =

   % : (termpattern -> term -> void -> result_of_match) %

   let rest () =
      if (is_const t) then Nomatch
      if (is_var t) then Nomatch
      if (is_abs t) then (containsfn p ((snd o dest_abs) t) () )
      if (is_comb t) then (approms
                             (containsfn p (rator t))
                             (containsfn p (rand t))
                             ()
                          )
      else fail
   in (Match (make_matching p t,rest)) ??[`no match`] (rest ());;


% Functions which make theorem patterns which are side-conditions %

% `Contains' looks up its first argument in the matching given as argument  %
% to the side-condition. A `result_of_match' is formed from the termpattern %
% and the term bound to `w', by testing the termpattern for containment     %
% within the term.                                                          %

ml_curried_infix `Contains`;;

let w Contains p =

   % : (wildvar -> termpattern -> thmpattern) %

   Side (\m . containsfn p (match_of_var m w) () );;


% `contains' behaves as for `Contains' except that its arguments are given %
% as terms rather than as a wildvar and a termpattern. The terms are made  %
% into a wildvar and a termpattern using default wildcards.                %

ml_curried_infix `contains`;;

let t contains t' =

   % : (term -> term -> thmpattern) %

   (make_wildvar t) Contains (autotermpattern t');;


% `Matches' looks up its first argument in the matching given as argument     %
% to the side-condition. A `result_of_match' is formed from the termpattern   %
% and the term bound to `w', by testing the termpattern against the term. If  %
% the match is successful, the matching becomes the first and only element of %
% the `result_of_match'. If not the `result_of_match' is `Nomatch'.           %

ml_curried_infix `Matches`;;

let w Matches p =

   % : (wildvar -> termpattern -> thmpattern) %

   Side (\m . (  Match (make_matching p (match_of_var m w), (\().Nomatch))
              ?? [`no match`] Nomatch
              )
        );;


% `matches' behaves as for `Matches' except that its arguments are given as   %
% terms rather than as a wildvar and a termpattern. The terms are made into a %
% wildvar and a termpattern using default wildcards.                          %

ml_curried_infix `matches`;;

let t matches t' =

   % : (term -> term -> thmpattern) %

   (make_wildvar t) Matches (autotermpattern t');;


% Function to split a bound term into the bound variable and the body %

% The bindings are represented by applications of function constants to     %
% lambda-abstractions. Hence the need to destroy a combination, followed by %
% (if the operator is a binder) destruction of an abstraction.              %

let dest_binder t =

   % : (term -> (term # term)) %

   (let (t1,t2) = dest_comb t
    in  if (is_binder (fst (dest_const t1)))
        then dest_abs t2
        else fail
   ) ? failwith `dest_binder`;;


% Function to strip all binders from the beginning of a term %

% The function repeatedly strips one binder until the process fails. %

letrec strip_binders t =

   % : (term -> term) %

   ((strip_binders o snd o dest_binder) t) ? t;;


% `Has_body' looks up its first argument in the matching given as argument    %
% to the side-condition. The bound term then has any binders stripped from    %
% the front of it. A `result_of_match' is formed from the termpattern and the %
% processed term by testing the termpattern against the term. If the match is %
% successful, the matching becomes the first and only element of the          %
% `result_of_match'. If not the `result_of_match' is `Nomatch'.               %

ml_curried_infix `Has_body`;;

let w Has_body p =

   % : (wildvar -> termpattern -> thmpattern) %

   Side (\m . (  Match (make_matching p (strip_binders (match_of_var m w)),
                    (\().Nomatch))
              ?? [`no match`] Nomatch
              )
        );;


% `has_body' behaves as for `Has_body' except that its arguments are given %
% as terms rather than as a wildvar and a termpattern. The terms are made  %
% into a wildvar and a termpattern using default wildcards.                %

ml_curried_infix `has_body`;;

let t has_body t' =

   % : (term -> term -> thmpattern) %

   (make_wildvar t) Has_body (autotermpattern t');;


%----------------------------------------------------------------------------%


% Functions which construct a side-condition as a theorem pattern %


% This one builds a side-condition which looks up the binding of `w' in the %
% matching given as argument to the side-condition. It then applies `f' to  %
% the bound `term', and converts the resulting Boolean value to a value of  %
% type `result_of_match'. The latter becomes the result of the              %
% side-condition test.                                                      %

let Test1term f w =

   % : ((term -> bool) -> wildvar -> thmpattern) %

   Side (\m . (bool_to_rom o f) (match_of_var m w));;


% `test1term' behaves as for `Test1term' except that its second argument is %
% given as a `term'. The `term' is automatically converted to a `wildvar'.  %

let test1term f t =

   % : ((term -> bool) -> term -> thmpattern) %

   Test1term f (make_wildvar t);;


% This one builds a side-condition which looks up the binding of `w' in the %
% matching given as argument to the side-condition. It then applies `f' to  %
% the bound `type', and converts the resulting Boolean value to a value of  %
% type `result_of_match'. The latter becomes the result of the              %
% side-condition test.                                                      %

let Test1type f w =

   % : ((type -> bool) -> wildtype -> thmpattern) %

   Side (\m . (bool_to_rom o f) (match_of_type m w));;


% `test1type' behaves as for `Test1type' except that its second argument is %
% given as a `type'. The `type' is automatically converted to a `wildtype'. %

let test1type f t =

   % : ((type -> bool) -> type -> thmpattern) %

   Test1type f (make_wildtype t);;


% This one builds a side-condition which looks up the bindings of `w1' and  %
% `w2' in the matching given as argument to the side-condition. It then     %
% applies `f' to the two bound `terms', and converts the resulting Boolean  %
% value to a value of type `result_of_match'. The latter becomes the result %
% of the side-condition test.                                               %

let Test2terms f w1 w2 =

   % : ((term -> term -> bool) -> wildvar -> wildvar -> thmpattern) %

   Side (\m . bool_to_rom (f (match_of_var m w1) (match_of_var m w2)));;


% `test2terms' behaves as for `Test2terms' except that its second and third %
% arguments are given as `terms'. The `terms' are automatically converted   %
% to `wildvars'.                                                            %

let test2terms f t1 t2 =

   % : ((term -> term -> bool) -> term -> term -> thmpattern) %

   Test2terms f (make_wildvar t1) (make_wildvar t2);;


% This one builds a side-condition which looks up the bindings of `w1' and  %
% `w2' in the matching given as argument to the side-condition. It then     %
% applies `f' to the two bound `types', and converts the resulting Boolean  %
% value to a value of type `result_of_match'. The latter becomes the result %
% of the side-condition test.                                               %

let Test2types f w1 w2 =

   % : ((type -> type -> bool) -> wildtype -> wildtype -> thmpattern) %

   Side (\m . bool_to_rom (f (match_of_type m w1) (match_of_type m w2)));;


% `test2types' behaves as for `Test2types' except that its second and third %
% arguments are given as `types'. The `types' are automatically converted   %
% to `wildtypes'.                                                           %

let test2types f t1 t2 =

   % : ((type -> type -> bool) -> type -> type -> thmpattern) %

   Test2types f (make_wildtype t1) (make_wildtype t2);;


%----------------------------------------------------------------------------%
