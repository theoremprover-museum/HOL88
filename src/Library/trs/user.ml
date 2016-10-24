% user.ml                                               (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Abbreviation for `find_theorems' %

let FT = find_theorems;;

   % : (thmpattern -> source -> searchstep) %


% Abbreviation for `continue_search' %

let CS = continue_search;;

   % : (searchstep -> searchstep) %


% Function to complete a stepwise search in one step %

% This function repeatedly attempts to continue a search, until this fails  %
% because there are no more theories to search. When this happens, the list %
% of theorems found during the search is extracted and returned as result.  %

letrec run_search srchstp =

   % : (searchstep -> foundthm list) %

   (  (run_search (continue_search srchstp))
   ?? [`continue_search`] (show_step srchstp)
   );;


% Function to perform a search in a single step %

% Given a pattern and a source, this function searches the source in one %
% step, and returns a list of theorems which match the pattern.          %

let full_search thmp src = run_search (find_theorems thmp src);;

   % : (thmpattern -> source -> foundthm list) %


% Function to continue a search until a match is found %

% If the found theorem list of the searchstep given is empty, the search is %
% continued. The evaluation will fail if no theorems are found before the   %
% list of theories to search is exhausted.                                  %

letrec search_until_find srchstp =

   % : (searchstep -> searchstep) %

   if (null o show_step) srchstp
   then (search_until_find o continue_search) srchstp
   else srchstp;;


% Function to continue with a search for a number of steps %

% If n is greater than zero, and the end of the search has not been reached, %
% the search is continued.                                                   %

letrec search_n_theories n srchstp =

   % : (int -> searchstep -> searchstep) %

   if (n < 1)
   then srchstp
   else case srchstp
        of (Endofsearch _) . srchstp
         | (Step _) . (search_n_theories (n-1) (continue_search srchstp));;


% Function to continue with a search for a number of steps, or until a %
% theorem is found.                                                    %

% If n is greater than zero, and the searchstep given does not contain any %
% theorems, the search is continued.                                       %

letrec search_n_until_find n srchstp =

   % : (int -> searchstep -> searchstep) %

   if (n > 0) & ((null o show_step) srchstp)
   then (search_n_until_find (n-1) (continue_search srchstp))
   else srchstp;;


%----------------------------------------------------------------------------%


% Function to allow a user to set up a constructor equivalent to `Ancestors' %
% but with the a default value for the exclusion list.                       %

let ancestors_excluding exclusions ancestors =

   % : (string list -> string list -> searchpath) %

   Ancestors (ancestors,exclusions);;


% `Ancestry' is an example of the use of `ancestors_excluding' and is likely %
% to be the most useful default exclusion.                                   %

let Ancestry = ancestors_excluding [`HOL`];;


% Function to make a `source' of the form `List ...' from a `searchstep' %

% The `foundthm list' is extracted from the `searchstep', and then `List' is %
% applied to it.                                                             %

let List_from srchstp =

   % : (searchstep -> source) %

   (List o show_step) srchstp;;


%----------------------------------------------------------------------------%


% Functions which can be used in place of certain `thmpattern' constructors, %
% so that the arguments can be given as the representing types of abstract   %
% types rather than as the abstract types themselves.                        %

% `kind' and `side' are only included for consistency. %

let kind = Kind

   % : (thmkind -> thmpattern) %

and thryname = Thryname o autonamepattern

   % : (string -> thmpattern) %

and thmname = Thmname o autonamepattern

   % : (string -> thmpattern) %

and conc = Conc o autotermpattern

   % : (term -> thmpattern) %

and hypP = HypP o (map autotermpattern)

   % : (term list -> thmpattern) %

and hypF = HypF o (map autotermpattern)

   % : (term list -> thmpattern) %

and side = Side;;

   % : (side_condition -> thmpattern) %


%----------------------------------------------------------------------------%


% `BigAnd' is an additional thmpattern constructor, useful when large %
% numbers of thmpatterns are to be ANDed together.                    %

letrec BigAnd thmpl =

   % : (thmpattern list -> thmpattern) %

   if (null thmpl)
   then failwith `BigAnd -- null list prohibited`
   else if (null (tl thmpl))
        then (hd thmpl)
        else ((hd thmpl) Andalso (BigAnd (tl thmpl)));;


% `BigOr' is an additional thmpattern constructor, useful when large %
% numbers of thmpatterns are to be ORed together.                    %

letrec BigOr thmpl =

   % : (thmpattern list -> thmpattern) %

   if (null thmpl)
   then failwith `BigOr -- null list prohibited`
   else if (null (tl thmpl))
        then (hd thmpl)
        else ((hd thmpl) Orelse (BigOr (tl thmpl)));;


%----------------------------------------------------------------------------%
