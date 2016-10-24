% matching.ml                                           (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Datatype for a full representation of a theorem %

% The first string is for the theory name. The second is for the theorem %
% name.                                                                  %

lettype foundthm = thmkind # string # string # thm;;


% Datatype for representing theorem patterns %

% The first seven constructors generate representations for theorem patterns. %
% The rest combine or modify such representations.                            %

rectype thmpattern_rep = Kind' of thmkind
                       | Thryname' of namepattern
                       | Thmname' of namepattern
                       | Conc' of termpattern
                       | HypP' of termpattern list
                       | HypF' of termpattern list
                       | Side' of side_condition
                       | Andalso' of thmpattern_rep # thmpattern_rep
                       | Orelse' of thmpattern_rep # thmpattern_rep
                       | Not' of thmpattern_rep
                       | Where' of thmpattern_rep # thmpattern_rep;;


% Abstract datatype for theorem patterns %

% There are two types of theorem pattern clause.                             %

% There are main clauses, in which tests are performed on a foundthm. All of %
% the constructors are allowed in this type of clause, though in principle,  %
% side-condition tests should not be. Side-condition tests within main       %
% clauses are re-interpreted as follows:                                     %
%                                                                            %
%    Side <side-condition>                                                   %
%                                                                            %
% is interpreted as                                                          %
%                                                                            %
%    (Conc (autotermpattern "conc:bool")) Where (Side <side-condition>)      %
%                                                                            %
% This only makes sense if <side-condition> tests "conc".                    %

% Only `Side', `Andalso', `Orelse', and `Not' constructors are permitted     %
% within a side-condition clause.                                            %

% `Where' is used to link these two types of clause. Its first argument is a %
% main clause. Its second argument is a side-condition clause. Note that     %
% `Where' cannot occur within a side-condition clause.                       %

% All of these constraints are imposed by the abstract datatype, which uses  %
% the type `thmpattern_rep' as its representing type.                        %

abstype thmpattern = thmpattern_rep

   with show_thmpattern thmp = rep_thmpattern thmp

       % : (thmpattern -> thmpattern_rep) %

   and  Kind knd = abs_thmpattern (Kind' knd)

       % : (thmkind -> thmpattern) %

   and  Thryname nmp = abs_thmpattern (Thryname' nmp)

       % : (namepattern -> thmpattern) %

   and  Thmname nmp = abs_thmpattern (Thmname' nmp)

       % : (namepattern -> thmpattern) %

   and  Conc patt = abs_thmpattern (Conc' patt)

       % : (termpattern -> thmpattern) %

   and  HypP pattl = abs_thmpattern (HypP' pattl)

       % : (termpattern list -> thmpattern) %

   and  HypF pattl = abs_thmpattern (HypF' pattl)

       % : (termpattern list -> thmpattern) %

   and  Side x = abs_thmpattern (Side' x)

       % : (side_condition -> thmpattern) %

   and  Andalso (thmp1,thmp2) =

       % : ((thmpattern # thmpattern) -> thmpattern) %

       abs_thmpattern (Andalso' (rep_thmpattern thmp1,rep_thmpattern thmp2))

   and  Orelse (thmp1,thmp2) =

       % : ((thmpattern # thmpattern) -> thmpattern) %

       abs_thmpattern (Orelse' (rep_thmpattern thmp1,rep_thmpattern thmp2))

   and  Not thmp = abs_thmpattern (Not' (rep_thmpattern thmp))

       % : (thmpattern -> thmpattern) %

   and  Where (thmp1,thmp2) =

       % : ((thmpattern # thmpattern) -> thmpattern) %

       % Function to check that a side-condition clause is legal %

       % The function either returns `true' or fails. The failure which     %
       % occurs in the body of `Where' if `is_legal_sidecond' returns false %
       % is therefore unnecessary.                                          %

       letrec is_legal_sidecond thmp_rep =

          % : (thmpattern_rep -> bool) %

          case thmp_rep
          of (Kind' _) . failwith `Where -- \`Kind' used in side-condition`
           | (Thryname' _) .
                failwith `Where -- \`Thryname' used in side-condition`
           | (Thmname' _) .
                failwith `Where -- \`Thmname' used in side-condition`
           | (Conc' _) . failwith `Where -- \`Conc' used in side-condition`
           | (HypP' _) . failwith `Where -- \`HypP' used in side-condition`
           | (HypF' _) . failwith `Where -- \`HypF' used in side-condition`
           | (Side' _) . true
           | (Andalso' (thmp_rep1,thmp_rep2)) .
                ((is_legal_sidecond thmp_rep1) & (is_legal_sidecond thmp_rep2))
           | (Orelse' (thmp_rep1,thmp_rep2)) .
                ((is_legal_sidecond thmp_rep1) & (is_legal_sidecond thmp_rep2))
           | (Not' thmp_rep1) . (is_legal_sidecond thmp_rep1)
           | (Where' _) . failwith `Where -- \`Where' used in side-condition`

       in if (is_legal_sidecond (rep_thmpattern thmp2))
          then abs_thmpattern
                  (Where' (rep_thmpattern thmp1,rep_thmpattern thmp2))
          else failwith `Where -- illegal side-condition`

   % Function to test a theorem pattern against a foundthm %

   % It calls `mainmatch' to attempt the matching. `mainmatch' returns a %
   % `result_of_match', which `thmmatch' converts to a Boolean value.    %

   and  thmmatch thmp fthm =

       % : (thmpattern -> foundthm -> bool) %

       rom_to_bool (mainmatch (rep_thmpattern thmp) fthm ())

% The following auxiliary matching functions are local to the abstract type %
% definition. Hence, they are hidden from the user.                         %

% `mainmatch' is used for processing main clauses of theorem patterns, given %
% a foundthm to match against. For the first six cases of clause type,       %
% auxiliary functions are called. Note that these and `mainmatch' itself are %
% lazy. That is they require a null argument before they actually perform    %
% any computation.                                                           %

% Side-condition clauses are re-interpreted when they occur within a main    %
% clause, as described at the beginning of this abstract type definition.    %

% `Andalso' and `Orelse' call `mainmatch' recursively on their two arguments %
% and use subsidiary functions to combine the results. `Not' calls           %
% `mainmatch' on its argument and then calls a subsidiary function to        %
% process the result. `Where' calls `mainmatch' on its first argument, and   %
% then passes the result along with its second argument to a function which  %
% deals with the side-condition clause.                                      %

whererec mainmatch thmp_rep fthm () =

   % : (thmpattern_rep -> foundthm -> void -> result_of_match) %

   case thmp_rep
   of (Kind' x) . (kindfn x fthm ())
    | (Thryname' x) . (thrynamefn x fthm ())
    | (Thmname' x) . (thmnamefn x fthm ())
    | (Conc' x) . (concfn x fthm ())
    | (HypP' x) . (hypPfn x fthm ())
    | (HypF' x) . (hypFfn x fthm ())
    | (Side' _) . (mainmatch
                     (Where' ((Conc' o autotermpattern) "conc:bool",thmp_rep))
                     fthm
                     ()
                  )
    | (Andalso' (x,y)) . (andalsofn
                            (mainmatch x fthm)
                            (mainmatch y fthm)
                            ()
                         )
    | (Orelse' (x,y)) . (approms
                           (mainmatch x fthm)
                           (mainmatch y fthm)
                           ()
                        )
    | (Not' x) . (notfn (mainmatch x fthm) ())
    | (Where' (x,y)) . (wherefn y (mainmatch x fthm) ())

% `sidematch' is used for processing side-condition clauses, given an       %
% environment which consists of a single matching. All side-condition tests %
% within the clause are applied to this matching.                           %

% Tests on the foundthm itself are prohibited (there is no foundthm         %
% available to test). This means that the first six cases for theorem       %
% patterns all cause failures.                                              %

% If the side-condition clause is simply a side-condition, the side-        %
% condition is applied to the environment. If the test succeeds, the        %
% result is passed back up. If not, `Nomatch' is passed back up.            %

% `Andalso', `Orelse' and `Not' cause `sidematch' to be called recursively, %
% and the results of these calls are processed further by subsidiary        %
% functions. `Where' is prohibited within side-condition clauses.           %

% The failures due to illegal constructor use should never occur because    %
% the abstract datatype will prevent such constructions.                    %

and sidematch thmp_rep env () =

   % : (thmpattern_rep -> matching -> void -> result_of_match) %

   case thmp_rep
   of (Kind' _) . (failwith `sidematch -- illegal use of Kind`)
    | (Thryname' _) . (failwith `sidematch -- illegal use of Thryname`)
    | (Thmname' _) . (failwith `sidematch -- illegal use of Thmname`)
    | (Conc' _) . (failwith `sidematch -- illegal use of Conc`)
    | (HypP' _) . (failwith `sidematch -- illegal use of HypP`)
    | (HypF' _) . (failwith `sidematch -- illegal use of HypF`)
    | (Side' x) . ((x env) ??[`no match`] (Nomatch))
    | (Andalso' (x,y)) . (andalsofn
                            (sidematch x env)
                            (sidematch y env)
                            ()
                         )
    | (Orelse' (x,y)) . (approms
                           (sidematch x env)
                           (sidematch y env)
                           ()
                        )
    | (Not' x) . (notfn (sidematch x env) ())
    | (Where' _) . (failwith `sidematch -- illegal use of Where`)

% `andalsofn' is used for ANDing two `result_of_matches' together.          %

% The first argument is applied to (). If the result is `Nomatch', then the %
% result of the whole evaluation is `Nomatch'. If not, the second argument  %
% is treated similarly. If both the arguments contain matchings, the        %
% function attempts to join the two `heads'. If this succeeds, the result   %
% becomes the `head' of the combined `result_of_match'. If not, the result  %
% is discarded.                                                             %

% The rest of the `result_of_match' is (when required) obtained by calling  %
% `andalsofn' recursively, firstly on the original first argument and the   %
% `tail' of the second, and then on the tail of the first and the original  %
% second argument. The two resulting `result_of_matches' are appended using %
% `approms'.                                                                %

% The overall effect of this is to combine a `list' of n matchings with a   %
% `list' of m matchings to form a `list' of all the possible combinations   %
% of matchings which can be joined successfully (maximum length n * m).     %

and andalsofn rom1fn rom2fn () =

   % : ((void -> result_of_match) -> (void -> result_of_match) ->           %
   %                                             (void -> result_of_match)) %

   case (rom1fn ())
   of (Nomatch) . (Nomatch)
    | (Match (m1,romfn1)) .
         (case (rom2fn ())
          of (Nomatch) . (Nomatch)
           | (Match (m2,romfn2)) .
                (let rest = (approms
                               (andalsofn rom1fn romfn2)
                               (andalsofn romfn1 rom2fn)
                            )
                 in ( (Match (join_matchings m1 m2,rest))
                    ??[`no match`] (rest ())
                    )
                )
         )

% `notfn' simply negates a `result_of_match', discarding any matchings, %
% since they make no sense when negated. `Not' can therefore be very    %
% destructive.                                                          %

and notfn rom1fn () =

   % : ((void -> result_of_match) -> (void -> result_of_match)) %

   case (rom1fn ())
   of (Nomatch) . (Match_null)
    | (Match _) . (Nomatch)

% `wherefn' is used for handling side-condition clauses.               %

% It passes each matching in the `result_of_match' it is given to the  %
% theorem pattern. The matchings are passed in turn as environments.   %
% The evaluation proceeds only as far as is necessary, but the         %
% potential to continue it is retained.                                %

% `sidematch' is used to test the theorem pattern under each of the    %
% environments. It returns a `result_of_match'. Only those matchings   %
% consistent with the environment should be retained. That is, any     %
% wildcard which appears in the environment as well as in the matching %
% should match to the same object in both cases. `andalsofn' is used   %
% to perform this checking.                                            %

% The `result_of_matches' generated for each environment are appended  %
% using `approms'.                                                     %

and wherefn thmp_rep rom1fn () =

   % : (thmpattern_rep -> (void -> result_of_match) ->                 %
   %                                        (void -> result_of_match)) %

   case (rom1fn ())
   of (Nomatch) . (Nomatch)
    | (Match (m,romfn)) . (approms
                             (andalsofn
                                (\().Match (m,(\().Nomatch)))
                                (sidematch thmp_rep m))
                             (wherefn thmp_rep romfn)
                             ()
                          )


% `kindfn' tests the kind of a found theorem. %

and kindfn knd fthm () =

   % : (thmkind -> foundthm -> (void -> result_of_match)) %

   bool_to_rom (knd = (fst fthm))


% `thrynamefn' uses a `namepattern' to test the name of the theory to which %
% a found theorem belongs.                                                  %

and thrynamefn nmp fthm () =

   % : (namepattern -> foundthm -> (void -> result_of_match)) %

   bool_to_rom (namematch nmp ((fst o snd) fthm))


% `thmnamefn' uses a `namepattern' to test the name of a found theorem. %

and thmnamefn nmp fthm () =

   % : (namepattern -> foundthm -> (void -> result_of_match)) %

   bool_to_rom (namematch nmp ((fst o snd o snd) fthm))


% `concfn' tests the conclusion of a found theorem against a termpattern. %

% The conclusion is extracted and then matched against the termpattern. %
% If the match succeeds, the matching is made into a `result_of_match'. %
% Otherwise, `Nomatch' is returned as the `result_of_match'.            %

and concfn patt fthm () =

   % : (termpattern -> foundthm -> (void -> result_of_match)) %

   (Match (make_matching patt ((concl o snd o snd o snd) fthm),(\().Nomatch)))
   ??[`no match`] Nomatch


% `hypPfn' tests the hypotheses of a found theorem against a list of          %
% termpatterns. Not all of the hypotheses need to be matched for the match to %
% succeed.                                                                    %

% The list of hypotheses is extracted from the found theorem. If there are %
% more termpatterns than hypotheses, `Nomatch' is returned. Otherwise,     %
% `hypfn' is used to test the termpatterns against the hypotheses.         %

and hypPfn pattl fthm () =

   % : (termpattern list -> foundthm -> (void -> result_of_match)) %

   let hypl = (hyp o snd o snd o snd) fthm
   in if ((length pattl) > (length hypl))
      then Nomatch
      else hypfn pattl hypl ()

% `hypFfn' tests the hypotheses of a found theorem against a list of      %
% termpatterns. All of the hypotheses need to be matched for the match to %
% succeed.                                                                %

% The list of hypotheses is extracted from the found theorem. If there are    %
% the same number of termpatterns as there are hypotheses, `hypfn' is used to %
% test the termpatterns against the hypotheses. Otherwise, `Nomatch' is       %
% returned.                                                                   %

and hypFfn pattl fthm () =

   % : (termpattern list -> foundthm -> (void -> result_of_match)) %

   let hypl = (hyp o snd o snd o snd) fthm
   in if ((length pattl) = (length hypl))
      then hypfn pattl hypl ()
      else Nomatch

% `hypfn' tests a list of termpatterns against a list of hypotheses %

% The result is a `result_of_match'. A subsidiary function is used to allow %
% backtracking.                                                             %

% `hypmatch' takes four arguments plus a null argument to provide `lazy'    %
% evaluation. The first argument is an accumulated matching for the         %
% wildcards bound so far. The second argument is a list of hypotheses left  %
% unmatched. This has to be remembered while the various ways of matching   %
% them are attempted. The third argument is the list of patterns not yet    %
% matched. The fourth argument is the list of hypotheses which have not yet %
% been tried against the head of the pattern list.                          %

% When the pattern list is empty, the accumulated matching is made into a   %
% `result_of_match', and returned as result. If the list of hypotheses runs %
% out before the patterns, `Nomatch' is returned.                           %

% If the head of the pattern list matches the head of the hypothesis list,  %
% and the resulting matching is consistent with the accumulated matching,   %
% the head of the hypothesis list is removed from the previous level's list %
% and `hypmatch' is called recursively to attempt a new level of match. Any %
% other ways of matching are found as described below, and are appended to  %
% the result of this call.                                                  %

% Any other ways of matching are found by a recursive call to `hypmatch'    %
% with all of the original arguments except that the fourth argument is the %
% tail of the original list. The result of this call becomes the result of  %
% the original call if the head of the pattern list did not match the head  %
% of the hypothesis list.                                                   %

and hypfn pattl hypl () =

   % : (termpattern list -> term list -> (void -> result_of_match)) %

   letrec hypmatch m prevtl pl terml () =

      % : (matching -> term list -> termpattern list -> term list ->        %
      %                                          (void -> result_of_match)) %

      if (null pl)
      then Match(m,(\().Nomatch))
      else if (null terml)
           then Nomatch
           else (let rest = hypmatch m prevtl pl (tl terml)
                 in ((let newm = join_matchings m
                                    (make_matching (hd pl) (hd terml))
                      in (let newtl = filter (\x. not (x = (hd terml))) prevtl
                          in approms
                                (hypmatch newm newtl (tl pl) newtl)
                                rest
                                ()
                         )
                     )
                    ??[`no match`] rest ()
                    )
                )
   in hypmatch null_matching hypl pattl hypl ();;


% Infix declarations to make construction of theorem patterns nicer %

ml_paired_infix `Andalso`;;

ml_paired_infix `Orelse`;;

ml_paired_infix `Where`;;


% Function to filter a list of theorems using a theorem pattern %

let thmfilter thmp fthml = filter (thmmatch thmp) fthml;;

   % : (thmpattern -> foundthm list -> foundthm list) %


%----------------------------------------------------------------------------%
