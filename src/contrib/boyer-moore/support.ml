%****************************************************************************%
% FILE          : support.ml                                                 %
% DESCRIPTION   : Miscellaneous supporting definitions for Boyer-Moore       %
%                 style prover in HOL.                                       %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 6th June 1991                                              %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 21st June 1991                                             %
%****************************************************************************%

%----------------------------------------------------------------------------%
% Discriminator functions for T (true) and F (false)                         %
%----------------------------------------------------------------------------%

let is_T = let T = "T" in \tm. tm = T
and is_F = let F = "F" in \tm. tm = F;;

%----------------------------------------------------------------------------%
% number_list : * list -> (* # int) list                                     %
%                                                                            %
% Numbers a list of elements,                                                %
% e.g. [`a`;`b`;`c`] ---> [(`a`,1);(`b`,2);(`c`,3)].                         %
%----------------------------------------------------------------------------%

let number_list l =
   letrec number_list' n l =
      if (null l)
      then []
      else (hd l,n).(number_list' (n + 1) (tl l))
   in number_list' 1 l;;

%----------------------------------------------------------------------------%
% insert_on_snd : (* # int) -> (* # int) list -> (* # int) list              %
%                                                                            %
% Insert a numbered element into an ordered list,                            %
% e.g. insert_on_snd (`c`,3) [(`a`,1);(`b`,2);(`d`,4)] --->                  %
%      [(`a`,1); (`b`,2); (`c`,3); (`d`,4)]                                  %
%----------------------------------------------------------------------------%

letrec insert_on_snd (x,n) l =
   if (null l)
   then [(x,n)]
   else let h = hd l
        in  if (n < snd h)
            then (x,n).l
            else h.(insert_on_snd (x,n) (tl l));;

%----------------------------------------------------------------------------%
% sort_on_snd : (* # int) list -> (* # int) list                             %
%                                                                            %
% Sort a list of pairs, of which the second component is an integer,         %
% e.g. sort_on_snd [(`c`,3);(`d`,4);(`a`,1);(`b`,2)] --->                    %
%      [(`a`,1); (`b`,2); (`c`,3); (`d`,4)]                                  %
%----------------------------------------------------------------------------%

letrec sort_on_snd l =
   if (null l)
   then []
   else insert_on_snd (hd l) (sort_on_snd (tl l));;

%----------------------------------------------------------------------------%
% conj_list : term -> term list                                              %
%                                                                            %
% Splits a conjunction into conjuncts. Only recursively splits the right     %
% conjunct.                                                                  %
%----------------------------------------------------------------------------%

letrec conj_list tm =
   (let (tm1,tm2) = dest_conj tm
    in  tm1.(conj_list tm2))
   ? [tm];;

%----------------------------------------------------------------------------%
% disj_list : term -> term list                                              %
%                                                                            %
% Splits a disjunction into disjuncts. Only recursively splits the right     %
% disjunct.                                                                  %
%----------------------------------------------------------------------------%

letrec disj_list tm =
   (let (tm1,tm2) = dest_disj tm
    in  tm1.(disj_list tm2))
   ? [tm];;

%----------------------------------------------------------------------------%
% find_bm_terms : (term -> bool) -> term -> term list                        %
%                                                                            %
% Function to find all subterms in a term that satisfy a given predicate p,  %
% breaking down terms as if they were Boyer-Moore logic expressions.         %
% In particular, the operator of a function application is only processed if %
% it is of zero arity, i.e. there are no arguments.                          %
%----------------------------------------------------------------------------%

let find_bm_terms p tm =
 (letrec accum tml p tm =
     let tml' = if (p tm) then (tm.tml) else tml
     in  ( (let args = snd (strip_comb tm)
            in  rev_itlist (\tm tml. accum tml p tm) args tml')
         ? tml'
         )
  in accum [] p tm
 ) ? failwith `find_bm_terms`;;
