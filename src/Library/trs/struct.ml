% struct.ml                                             (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Function to merge two association lists, failing if the lists are %
% inconsistent.                                                     %

% The first element of the pair at the head of l2 is looked-up in l1. If the %
% second element of the pair obtained is equal to the second element of the  %
% pair at the head of l2, then the head of l2 is discarded. Otherwise, the   %
% merge fails. If the look-up in l1 fails, the head of l2 is retained.       %

letrec merge l1 l2 =

   % : ((* # **) list -> (* # **) list -> (* # **) list) %

   if (null l2)
   then l1
   else ((let p = assoc (fst (hd l2)) l1
          in  if (snd p = snd (hd l2))
              then (merge l1 (tl l2))
              else failwith `merge`)

        ??[`assoc`] (hd l2).(merge l1 (tl l2))

        );;


% Function to merge two `match' lists. %

let join (avtl,attl) ((bvtl,bttl) : (term # term) list # (type # type) list) =

   % : ((term # term) list # (type # type) list ->   %
   %    (term # term) list # (type # type) list ->   %
   %    (term # term) list # (type # type) list    ) %

   (merge avtl bvtl,merge attl bttl) ??[`merge`] failwith `no match`;;


% Function to remove a bound-variable from a `match' list. %

% Any pairs in the variable-term association list which have the %
% bound-variable as their first element are filtered out.        %

let remove_bv bv ((vtl,ttl) : (term # term) list # (type # type) list) =

   % : (term -> (term # term) list # (type # type) list ->    %
   %                 (term # term) list # (type # type) list) %

   (filter (\x.not ((fst x) = bv)) vtl,ttl);;


% Function for matching two types. %

% The first type given, p, must be the more general.                         %

% If p is a simple polymorphic type (i.e. one containing no constructors)    %
% then it can match any type. A single item association list is constructed  %
% from the two types in such a case.                                         %

% If p is not a simple type, it is split up into a constructor and a list of %
% simpler types. An attempt is made to split t, also. If this fails, then no %
% match can be made. If the constructors obtained from p and t are different %
% then the match must fail. The lists of simpler types obtained from         %
% decomposing p and t are converted to a list of pairs, the match failing if %
% the original lists were not of the same length. The function is then       %
% applied recursively to each pair of the new list, and the results are      %
% merged. If merging fails, the whole match fails.                           %

letrec match_type p t =

   % : (type -> type -> (type # type) list) %

   if (is_vartype p)
   then [(p,t)]
   else let (pc,ptypl) = dest_type p
        and (tc,ttypl) = ((dest_type t) ? failwith `no match`)
        in  if (pc = tc)
            then ((itlist merge (map (\(x,y).match_type x y)
                                        (combine (ptypl,ttypl))) [])
                 ??[`merge`;`combine`] failwith `no match`
                 )
            else failwith `no match`;;


% Function for matching two terms. %

% The first term given, p, must be the more general.                        %

% The function consists of four cases.                                      %

% p is a constant. If t is not a constant, the match fails. If the names of %
% p and t are different, the match fails. Constants cannot be wildcards, so %
% only the types need adding to the `match' list. One might think the match %
% should fail if the types are different, but this is not the case.         %
% Consider the `=' function, for instance. The types must match, however.   %

% p is a variable. A variable can match any term, provided its type can be  %
% matched to that of the term.                                              %

% p is an abstraction. An abstraction can only match another abstraction.   %
% p and t are decomposed into their bound-variables and bodies. The bound-  %
% variables are matched to obtain the type matchings. The bodies are also   %
% matched. The resultant matchings are then merged, and the bound-variable  %
% is then removed from the variable-term list to allow for renaming of      %
% bound-variables. Note that the merge has to be done before the bound-var. %
% is removed to ensure the bound-variables correspond in the body.          %

% p is a combination. A combination can only match another combination.     %
% p and t are decomposed into their rators and rands. The two rators are    %
% matched against each other. The two rands are matched. Then the resulting %
% `match' lists are merged.                                                 %

letrec match_term p t =

   % : (term -> term -> (term # term) list # (type # type) list) %

   if (is_const p) then if (is_const t)
                        then if (fst (dest_const p) = fst (dest_const t))
                             then ([],match_type (type_of p) (type_of t))
                             else failwith `no match`
                        else failwith `no match`
   if (is_var p) then ([(p,t)],match_type (type_of p) (type_of t))
   if (is_abs p) then
     (let (pbv,pbody) = dest_abs p
      and (tbv,tbody) = ((dest_abs t) ? failwith `no match`)
      in  remove_bv pbv (join (match_term pbv tbv) (match_term pbody tbody)))
   if (is_comb p) then
     (let (prator,prand) = dest_comb p
      and (trator,trand) = ((dest_comb t) ? failwith `no match`)
      in  join (match_term prator trator) (match_term prand trand))
   else fail;;


% Function to match a term pattern inside a term %

% The function applies match_term to the pattern and the term. If this fails %
% the function is called recursively on any possible sub-terms of the term.  %
% If all these attempts to match fail, the whole evaluation fails.           %

letrec match_internal_term p t =

   % : (term -> term -> (term # term) list # (type # type) list) %

   match_term p t
   ??[`no match`]             (match_internal_term p (rator t))
   ??[`no match`;`dest_comb`] (match_internal_term p (rand t))
   ??[`no match`;`dest_comb`] (match_internal_term p (snd (dest_abs t)))
   ??[`no match`;`dest_abs`]  failwith `no match`;;


%----------------------------------------------------------------------------%


% Abstract datatype for wildcard variables to be used in pattern matching %

abstype wildvar = term

   % Function to convert a wildvar into a term %

   with show_wildvar w = rep_wildvar w

       % : (wildvar -> term) %

   % Function to make a wildvar from a term. The term must be a variable %

   and  make_wildvar t =

       % : (term -> wildvar) %

       if (is_var t)
       then (abs_wildvar t)
       else failwith `make_wildvar -- term is not a variable`;;


% Function to make a list of wildvars out of a list of terms %

let wildvarlist varl = map make_wildvar varl;;

   % : (term list -> wildvar list) %


%----------------------------------------------------------------------------%


% Abstract datatype for wildcard types to be used in pattern matching %

abstype wildtype = type

   % Function to convert a wildtype into a type %

   with show_wildtype w = rep_wildtype w

       % : (wildtype -> type) %

   % Function to make a wildtype from a type.         %
   % The type must be a `primitive' polymorphic type. %

   and  make_wildtype t =

       % : (type -> wildtype) %

       if (is_vartype t)
       then (abs_wildtype t)
       else failwith `make_wildtype -- type is not polymorphic`;;


% Function to make a list of wildtypes out of a list of types %

let wildtypelist typl = map make_wildtype typl;;

   % : (type list -> wildtype list) %


%----------------------------------------------------------------------------%


% Abstract datatype for patterns used to match terms %

abstype termpattern = term # wildvar list # wildtype list

   % Function to convert a termpattern to its representing type %

   with show_termpattern p = rep_termpattern p

       % : (termpattern -> (term # wildvar list # wildtype list)) %

   % Function to make a termpattern from a term, a list of wildcard variables %
   % and a list of wildcard types.                                            %

   and  make_termpattern (tm,wvl,wtl) =

       % : ((term # wildvar list # wildtype list) -> termpattern) %

       % Convert wildcard variables to their representing variables %

       let varl = map show_wildvar wvl

       % Convert wildcard types to their representing type %

       and typl = map show_wildtype wtl

       % Form a termpattern if and only if the lists of wildcard variables %
       % and wildcard types are sets (i.e. contain no repetitions) and all %
       % the wildcard variables specified are free variables in tm and all %
       % the wildcard types specified are `primitive' polymorphic types    %
       % occurring in tm.                                                  %

       in  if (no_rep varl) then
              if (no_rep typl) then
                 if (is_subset (get_freevars tm) varl) then
                    if (is_subset (get_primvartypes tm) typl) then

                       (abs_termpattern (tm,wvl,wtl))

                    else failwith `make_termpattern -- wildtype not in term`
                 else failwith `make_termpattern -- wildvar not in term`
              else failwith `make_termpattern -- duplicate wildtype`
           else failwith `make_termpattern -- duplicate wildvar`;;


% Function to convert a termpattern into its representing type, and the %
% wildvars and wildtypes within that to their representing types.       %
% So, function makes all of a termpattern visible.                      %

let show_full_termpattern p =

   % : (termpattern -> (term # term list # type list)) %

   let (tm,wvl,wtl) = show_termpattern p
   in  (tm,(map show_wildvar wvl),(map show_wildtype wtl));;


% Function to make a termpattern from a term, a list of terms, and a list of %
% types. The term represents the pattern. The list of terms represents the   %
% variables which are to be taken as wildcards, and the list of types        %
% represents the `primitive' polymorphic types which are to be taken as      %
% wildcards.                                                                 %

let make_full_termpattern (tm,terml,typel) =

   % : ((term # term list # type list) -> termpattern) %

   make_termpattern (tm,wildvarlist terml,wildtypelist typel);;


% Function to make a termpattern out of a term by using the free variables in %
% the term as wildvars and the `primitive' polymorphic types as wildtypes.    %

let autotermpattern t =

   % : (term -> termpattern) %

   make_full_termpattern (t,get_freevars t,get_primvartypes t);;


%----------------------------------------------------------------------------%


% Abstract datatype for the result of matching a termpattern against a term %

abstype matching = ((wildvar # term) list # (wildtype # type) list)

   % Function to convert a matching to its representing type %

   with show_matching m = rep_matching m

       % : (matching -> ((wildvar # term) list # (wildtype # type) list)) %

   % A matching with no bindings %

   and  null_matching = abs_matching ([],[])

       % : (matching) %

   % Function to form a matching from a termpattern and a term %

   and  make_matching p t =

       % : (termpattern -> term -> matching) %

           % Extract low-level components of termpattern %

           let (tm,varl,typl) = show_full_termpattern p

               % Use `match_term' to attempt a matching of the template tm  %
               % against the term t. If this fails, `make_matching' fails.  %
               % If it succeeds the (term # term) list # (type # type) list %
               % returned by `match_term' is bound to the pair (vpl,tpl)    %
               % for further analysis/processing.                           %

           in  let (vpl,tpl) = match_term tm t

               % The (term # term) list component returned by `match_term'   %
               % is a list of pairs such that the first element of the pair  %
               % is a variable in tm, and the second element of the pair is  %
               % the term in t that the variable has been matched to.        %

               % Bound-variables in tm do not appear in the result of        %
               % `match_term'. Some of the variables which do appear may not %
               % have been specified as wildvars. The match must fail if     %
               % such a variable does not (when its type has been            %
               % instantiated) match itself in the list returned by          %
               % `match_term'. The (type # type) list, returned by           %
               % `match_term' is used to perform the instantiation.          %

               % Types are dealt with similarly, except that there is no     %
               % equivalent action to instantiation.                         %

               % The matching we are trying to construct should look like    %
               % the result of `match_term' except that the variables and    %
               % types from tm should be converted to wildcards, and only    %
               % those of them that appear as wildcards in the termpattern   %
               % should be included.                                         %

               % Now we know what we are trying to achieve, let us define    %
               % some functions to help us.                                  %

               % f is used to convert the term or type which is representing %
               % a wildcard into the appropriate wildcard type.              %

               and f w (a,b) = ((w a),b)

                  % : ((* -> **) -> (* # ***) -> (** # ***)) %

               % `instant_type' instantiates the type of a variable using a  %
               % (type # type) list in which the first element of each pair  %
               % is a `primitive' type. The embedded function `change_type'  %
               % does the real work. `instant_type' splits the variable into %
               % its name and type, applies `change_type' to the type, and   %
               % then reconstructs the variable using the new type.          %

               and instant_type ttl v =

                  % : ((type # type) list -> term -> term) %

                  % `change_type' instantiates a type. If the type is        %
                  % `primitive', it is looked-up in the instantiation list.  %
                  % If found, the corresponding instance is returned. If not %
                  % the type itself is returned. If the type is              %
                  % not `primitive', it is decomposed into a constructor and %
                  % a list of simpler types. Each of the latter are then     %
                  % instantiated, and the type is reconstructed.             %

                 (letrec change_type ttl typ =

                     % : ((type # type) list -> type -> type) %

                     if (is_primtype typ)
                     then ((snd (assoc typ ttl)) ? typ)
                     else (let (s,l) = dest_type typ
                           in  mk_type (s,(map (change_type ttl) l)))
                  in (let (s,t) = dest_var v
                      in  mk_var (s,(change_type ttl t)))
                 )

                   % `build' filters xxl removing any pairs whose first  %
                   % element is not in xl. If lf applied to the first    %
                   % element of such a pair is not equal to the second   %
                   % element of the pair, then the match being performed %
                   % is failed.                                          %

                   % `build' is used to build a matching from a `match'  %
                   % list and a wildcard list. Any variable or type in   %
                   % the `match' list but not in the wildcard list must  %
                   % match itself (allowing for type instantiation -     %
                   % hence the need for lf), and will not be included in %
                   % the result.                                         %

               in (letrec build lf xl xxl =

                      % : ((* -> **) -> * list -> (* # **) list ->          %
                      %                                      (* # **) list) %

                      if (null xxl)
                      then []
                      else if (mem ((fst o hd) xxl) xl)
                           then (hd xxl).(build lf xl (tl xxl))
                           else if ((lf o fst o hd) xxl = (snd o hd) xxl)
                                then (build lf xl (tl xxl))
                                else failwith `no match`

                   % Note : assumes all variables which could be wildvars   %
                   %        appear in the matching returned by `match_term' %

                   in abs_matching (
                        (map (f make_wildvar)
                                (build (instant_type tpl) varl vpl)),
                        (map (f make_wildtype) (build (\x.x) typl tpl)))
                  )

   % Function to combine two (consistent) matchings into a single matching %

   % Split the two matchings into wildvar and wildtype `match' lists. Merge %
   % the two resulting wildvar lists and the two resulting wildtype lists.  %
   % If either merge fails, the match fails.                                %

   and  join_matchings m n =

       % : (matching -> matching -> matching) %

           let mwvl,mwtl = rep_matching m
           and nwvl,nwtl = rep_matching n
           in  abs_matching ((merge mwvl nwvl),(merge mwtl nwtl))
                  ?? [`merge`] failwith `no match`;;


% Function to convert a matching into its representing type, and the %
% wildvars and wildtypes within that to their representing types.    %
% So, function makes all of a matching visible.                      %

let show_full_matching m =

   % : (matching -> ((term # term) list # (type # type) list)) %

       let wvl,wtl = show_matching m
       and f (w,t) = ((show_wildvar w),t)
       and g (w,t) = ((show_wildtype w),t)
       in  ((map f wvl),(map g wtl));;


% Function to lookup a wildvar in a matching, and return the term to %
% which it is bound.                                                 %

let match_of_var m wv =

   % : (matching -> wildvar -> term) %

   (snd o (assoc wv) o fst o show_matching) m
   ?? [`assoc`]
      failwith `match_of_var -- unknown wildvar (variable)`;;


% Function to lookup a wildtype in a matching, and return the type to %
% which it is bound.                                                  %

let match_of_type m wt =

   % : (matching -> wildtype -> type) %

   (snd o (assoc wt) o snd o show_matching) m
   ?? [`assoc`]
      failwith `match_of_type -- unknown wildtype (polymorphic type)`;;


%----------------------------------------------------------------------------%


% Datatype for lazy evaluation of alternate matchings %

% Nomatch means there is no way to match.                                    %
% Match means there is at least one way to match, and specifies the matching %
% (which may be null). The second element of the pair is a function to       %
% generate any other matchings if they exist.                                %

rectype result_of_match = Nomatch
                        | Match of matching # (void -> result_of_match);;


% Abbreviation for a result_of_match which is a match with no bindings %

let Match_null = Match(null_matching,(\().Nomatch));;


% Function to append two lazy lists (`result_of_matches') %

% `approms' appends two `result_of_matches' which are essentially just lazy %
% lists of matchings. The result must be kept as lazy as possible. This     %
% function is also used to OR two `result_of_matches', since this operation %
% corresponds exactly to appending them.                                    %

% The arguments to `approms' are actually functions from void to a          %
% `result_of_match', so that as little evaluation as necessary is done.     %

% The function is defined in an analogous way to `append' on lists.         %

letrec approms rom1fn rom2fn () =

   % : ((void -> result_of_match) -> (void -> result_of_match) ->           %
   %                                             (void -> result_of_match)) %

   case (rom1fn ())
   of (Nomatch) . (rom2fn ())
    | (Match (m,romfn)) . (Match (m,approms romfn rom2fn));;


% Function to convert a Boolean value to a result_of_match %

let bool_to_rom b =

   % : (bool -> result_of_match) %

   if b
   then Match_null
   else Nomatch;;


% Function to convert a result_of_match to a Boolean value %

% Note that information may be thrown away in this process. %

let rom_to_bool r =

   % : (result_of_match -> bool) %

   not (r = Nomatch);;


% Abbreviation for the datatype representing side-conditions %

% When applied to a matching, a side-condition performs tests on the        %
% bindings in the matching, and returns a `lazy list' of any successful new %
% bindings.                                                                 %

lettype side_condition = matching -> result_of_match;;


%----------------------------------------------------------------------------%
