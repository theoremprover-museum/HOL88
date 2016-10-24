% search.ml                                             (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


% Function to extract the theorems from a theory %

% The theorems are obtained from the theory as pairs of %
% (theorem name, structure). A 4-tuple is constructed   %
% by making this pair the third element of a 3-tuple    %
% where the first element is the kind of theorem and    %
% the second is the theory name.                        %

let get_theorems thry =

   % : (string -> foundthm list) %

   (map (\x.(Axiom,thry,x)) (axioms thry)) @
   (map (\x.(Definition,thry,x)) (definitions thry)) @
   (map (\x.(Theorem,thry,x)) (theorems thry));;


%----------------------------------------------------------------------------%


% Datatype for ways in which to search a theory file hierarchy %

% `Theory' means `search this theory only'.                                 %
% `Ancestors' means `search the first list of theories and their ancestors, %
% doing these theories first, then all of their parents, and so on'.        %
% If any theories are specified in the second list, they are removed from   %
% the list given at the first search level, and from any list of parents at %
% subsequent levels.                                                        %

type searchpath = Theory of string
                | Ancestors of string list # string list;;


% Datatype for possible sources of theorems for a search %

% `List' means `search this list of theorems'. %
% `Paths' means `search these paths in sequence'. %

% Note that to search the ancestry of the theories `theory1' and `theory2' %
% in `parallel', one would use the source:                                 %
%                                                                          %
% Paths [Ancestors ([`theory1`;`theory2`],[])]                             %
%                                                                          %
% To search them in sequence, one would use:                               %
%                                                                          %
% Paths [Ancestors ([`theory1`],[]); Ancestors ([`theory2`],[])]           %

type source = List of foundthm list
            | Paths of searchpath list;;


% Function to remove repetitions in a list, keeping the first duplicate %

% A new list is built from the original. Each element of the original list %
% is only added to the new list if it isn't already in it. Elements are    %
% added to the front of the new list, so the order is reversed. This is    %
% dealt with by reversing the new list before returning it as the result.  %

% `do_once_only' is defined and used here, rather than using `remove_rep', %
% because the lists it is processing have a special order.                 %

let do_once_only l =

   % : (* list -> * list) %

   letrec do_once_only' newl oldl =

      % : (* list -> * list -> * list) %

      if (null oldl)
      then rev newl
      else if (mem (hd oldl) newl)
           then do_once_only' newl (tl oldl)
           else do_once_only' ((hd oldl).newl) (tl oldl)
   in do_once_only' [] l;;


% Function to expand a list of theories into a list of them and all their %
% ancestors. The new list contains no repetitions, and it is in the       %
% correct order for searching the ancestry in a breath-first manner.      %
% In addition, any theories specified in the second list, and any of      %
% their ancestors, will not be included in the result. If, however, a     %
% theory is both an ancestor of a theory in the exclusion list, and also  %
% an ancestor of a theory in the source list, which is not in the list of %
% exclusions, it will be included in the result.                          %

% The new list is built up by concatenating levels of ancestry. The first %
% level of ancestry consists of the theories given in the original list,  %
% less any in the exclusion list. The second level of ancestry consists   %
% of the parents of the original theories less the original theories and  %
% any in the exclusion list (the ancestry may be an acyclic directed      %
% graph rather than just a tree). The third level is taken to be the      %
% parents of those included at the second level, less any theories        %
% previously included and less any theories which occur in the exclusion  %
% list. Further levels are constructed in a similar way. The process      %
% terminates when all the new parents have already been dealt with.       %

% The function `searchseq'' takes a list of exclusions, a list of         %
% theories already included, and a list of parents of the previous        %
% level's theories. If the list of parents is not empty, any theory in    %
% either the `done' list, or the exclusion list is removed from it.       %
% The result becomes the new level of theories. Each theory in the new    %
% list is converted to a list of parents. The resulting list of lists is  %
% then flattened, and any repetitions are removed in a way which          %
% preserves the search order. This list becomes the new list of parents.  %

% `searchseq'' is now called recursively with this list and a new `done'  %
% list consisting of the union of the old `done' list and the new level   %
% of theories. The exclusion list remains the same.                       %

% Due to the large amount of interdependence between theories, the lists  %
% will grow exponentially if duplicates are not removed at every          %
% opportunity. So, for this reason, duplicates are removed from the lists %
% of theories given by the user, before they are passed to the main part  %
% of the function. Similarly, duplicates are removed from the list of     %
% parents before passing it to `searchseq''. One also has to be careful   %
% not to introduce duplicates into the `done' list.                       %

let searchseq exclusions ancestors =

   % : (string list -> string list -> string list) %

   letrec searchseq' exclusions' done ancestors' =

      % : (string list -> string list -> string list -> string list) %

      if (null ancestors')
      then done
      else (let new = subtract ancestors' (done @ exclusions')

            % Note that maintaining the correct search order relies on %
            % `subtract' filtering its first argument based on the     %
            % contents of its second argument.                         %

            in  ((searchseq' exclusions' (done @ new)) o do_once_only o
                                                   flat o (map parents)) new)

   in searchseq' (do_once_only exclusions) [] (do_once_only ancestors);;


% Function to form an ordered list of theories from a list of searchpaths. %

% The sub-function `flatten_path' converts a single path to an ordered list %
% of theories. If the path is simply a theory, then a single-element list   %
% consisting of that theory is returned by `flatten_path'. If not,          %
% `searchseq' is used to find the ancestors of the theories given.          %

% Any duplicate paths in the path list are removed in a manner which does   %
% not affect the search order. `flatten_path' is then used to convert each  %
% path to a list of theories. This list of lists is flattened, and any      %
% duplicates are removed from the resulting list of theories.               %

let flatten_paths paths =

   % : (searchpath list -> string list) %

   let flatten_path path =

      % : (searchpath -> string list) %

      case path
      of (Theory x) . [x]
       | (Ancestors (xl,yl)) . searchseq yl xl
   in  (do_once_only o flat o (map flatten_path) o do_once_only) paths;;


% Datatype to allow a search to be `paused' after each theory has been %
% searched.                                                            %

% If there are no more theories to search, a list of theorems is returned %
% as an `Endofsearch'. Otherwise, a `Step' is returned, consisting of a   %
% list of theorems matched so far, and a function which given a null      %
% argument will perform the next step of the search.                      %

rectype searchstep = Endofsearch of foundthm list
                   | Step of foundthm list # (void -> searchstep);;


% Function to do a stepwise search for theorems matching a given pattern %

% If the source is just a list of theorems, it is filtered using the        %
% pattern. If the source is a list of paths, it is converted into a list of %
% theories to search, using `flatten_paths'. This is then passed to         %
% `make_step'.                                                              %

% `make_step' searches the theory at the head of its list, and forms a      %
% searchstep from the results. If the theory list is empty, the list of     %
% theorems found is returned. A theory is searched by extracting a list of  %
% theorems from it, and then filtering this list using the theorem pattern. %
% These new theorems are added to the existing list. Note that there can be %
% no duplication of theorems, since part of a `theorem' as represented here %
% is the name of the theory to which it belongs.                            %

% The name of the theory being searched is written to the terminal.         %

% See also the comments for the datatype `searchstep'.                      %

let find_theorems thmp src =

   % : (thmpattern -> source -> searchstep) %

   letrec make_step thmp ftl thryl =

      % : (thmpattern -> foundthm list -> string list -> searchstep) %

      if (null thryl)
      then (Endofsearch ftl)
      else (let output1 = print_string (`Searching theory `^(hd thryl))
            and output2 = print_newline()
            and newftl =
                   ftl @ (((thmfilter thmp) o get_theorems) (hd thryl))
            in  Step (newftl,(\().make_step thmp newftl (tl thryl))))

   in case src

      of (List ftl)    . (Endofsearch (thmfilter thmp ftl))

       | (Paths pathl) . (make_step thmp [] (flatten_paths pathl));;


% Function to extract the list of found theorems from a searchstep %

let show_step srchstp =

   % : (searchstep -> foundthm list) %

   case srchstp
   of (Endofsearch ftl) . ftl
    | (Step (ftl,_))    . ftl;;


% Function to continue a stepwise search %

% If the search has come to an end, this function fails. If not, the next  %
% step of the search is performed, by use of the function contained within %
% the searchstep. The result of the function is another searchstep.        %

let continue_search srchstp =

   % : (searchstep -> searchstep) %

   case srchstp
   of (Endofsearch _) . (failwith `continue_search`)
    | (Step (_,next)) . next ();;


%----------------------------------------------------------------------------%
