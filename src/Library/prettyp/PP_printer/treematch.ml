% treematch.ml                                                                %
%-----------------------------------------------------------------------------%


%  Matching patterns to parse-trees.  %


%  Datatype for sub-tree addresses.  %

type address = No_address | Address of int list;;


%  Datatype for different kinds of object which can be bound during a match.  %

type metavar_binding = Bound_name of string # address
                     | Bound_names of (string # address) list
                     | Bound_child of print_tree # address
                     | Bound_children of (print_tree # address) list;;


%  Abbreviation for datatype of bindings of metavariables to objects.  %

lettype print_binding = (string # metavar_binding) list;;


%  Abbreviation for datatype of tests on pretty-printing environment.  %

lettype print_test = (string # int) list -> print_binding -> bool;;


%  Datatype for bound on number of times a looping match should be attempted  %

%  The bound is either a natural number or the default value.  %

type loop_limit = Default
                | Val of nat;;


%  Datatype of patterns for matching trees.  %

rectype print_patt_tree = Const_name of string # child_metavar list
                        | Var_name of string # child_metavar list
                        | Wild_name of child_metavar list
                        | Var_child of string
                        | Wild_child
                        | Link_child of (loop_limit # loop_limit) # string list
                        | Print_label of string # print_patt_tree
                        | Print_link of ((loop_limit # loop_limit) #
                                                            string list)
                                      # print_patt_tree
                        | Print_loop of print_patt_tree # print_patt_tree

and child_metavar = Var_children of string
                  | Wild_children
                  | Patt_child of print_patt_tree;;


%  Abbreviation for datatype of pretty-printing language patterns.  %

lettype print_pattern = string # print_patt_tree # print_test;;


%  Datatype for `loop-link' information.  %

%  A looping pattern should contain a link which marks the sub-tree to be     %
%  tested on the next time round the loop. It also specifies the number of    %
%  times the loop should go round, and any metavariables which should match   %
%  to the same object on each time round the loop. This datatype represents   %
%  the alternatives of having this information, and not having found a link.  %

type print_loop_link = No_link
                     | Link of ((loop_limit # loop_limit) # string list)
                             # (print_tree # int list);;


%  Function to extract the object bound to a specified metavariable from a  %
%  binding. The function fails if the metavariable is not found in the      %
%  binding.                                                                 %

let lookup_metavar pbind mvar =

   % : (print_binding -> string -> metavar_binding) %

   ((snd (assoc mvar pbind)):metavar_binding)
      ? failwith
          (`lookup_metavar -- Metavariable \``^mvar^`' not found in binding`);;

begin_section treematch;;

%  Function to test whether the values of two metavar bindings are equal.  %

let eq_metavar_bind mbind1 mbind2 =
   case (mbind1,mbind2)
   of (Bound_name (s1,_),Bound_name (s2,_)) . (s1 = s2)
    | (Bound_names sl1,Bound_names sl2) . (map fst sl1 = map fst sl2)
    | (Bound_child (pt1,_),Bound_child (pt2,_)) . (pt1 = pt2)
    | (Bound_children ptl1,Bound_children ptl2) . (map fst ptl1 = map fst ptl2)
    | (_) . false;;


%  Function to replace the addresses in a metavar binding with No_address.  %

let no_address_meta mbind =
   case mbind
   of (Bound_name (s,_)) . (Bound_name (s,No_address))
    | (Bound_names sl) . (Bound_names (map (\(s,_). (s,No_address)) sl))
    | (Bound_child (pt,_)) . (Bound_child (pt,No_address))
    | (Bound_children ptl) .
         (Bound_children (map (\(pt,_). (pt,No_address)) ptl));;


%  Function to replace the value associated with a given key in an        %
%  association list. If the key is not present, no change is made to the  %
%  association list. If the key occurs more than once, only the first     %
%  occurrence is changed.                                                 %

letrec replace assocl (key,new) =

   % : ((* # **) list -> (* # **) -> (* # **) list) %

   if (null assocl)
   then []
   else if (key = (fst (hd assocl)))
        then (key,new).(tl assocl)
        else (hd assocl).(replace (tl assocl) (key,new));;


%  Function to replace the values associated with a list of keys in an    %
%  association list. The replacement is done in the manner of `replace'.  %

letrec replacel assocl changes =

   % : ((* # **) list -> (* # **) list -> (* # **) list) %

   if (null changes)
   then assocl
   else replacel (replace assocl (hd changes)) (tl changes);;


%  Function to merge two bindings.  %

%  Fails if a metavariable occurs in both bindings, but bound to different  %
%  objects. If objects are the same, only one copy is retained and the      %
%  sub-term addresses are thrown away because they are no longer valid.     %

let print_merge pb1 (pb2:print_binding) =

   % : (print_binding -> print_binding -> print_binding) %

   letrec print_merge' l pb1 pb2 =
      if (null pb1)
      then if (null l) then pb2 else filter (\(s,_). not (mem s l)) pb2
      else ((let (s,meta) = hd pb1
             in  let p = assoc s pb2
             in  if (eq_metavar_bind (snd p) meta)
                 then (s,no_address_meta meta).
                         (print_merge' (s.l) (tl pb1) pb2)
                 else failwith `print_merge`)
           ??[`assoc`] (hd pb1).(print_merge' l (tl pb1) pb2)
           )
   in print_merge' [] pb1 pb2;;


%  Function to merge a binding from a looping match with another binding.  %

%  Assumes that all bound items in looppb are lists. If a metavariable        %
%  occurs in both bindings, the single item or list obtained from the second  %
%  binding is appended to the end of the list from the loop binding. Any      %
%  metavariable occurring in only one of the bindings is included in the new  %
%  binding unchanged. The function fails if the bound items have              %
%  inconsistent types.                                                        %

letrec print_loop_merge looppb (pb:print_binding) =

   % : (print_binding -> print_binding -> print_binding) %

   if (null looppb)
   then pb
   else ((let (loopm,loopb) = hd looppb
          in  let newb =
                 case (loopb,snd (assoc loopm pb))
                 of (Bound_names sl1,Bound_name s2) .
                       (Bound_names (sl1 @ [s2]))
                  | (Bound_names sl1,Bound_names sl2) .
                       (Bound_names (sl1 @ sl2))
                  | (Bound_children ptl1,Bound_child pt2) .
                       (Bound_children (ptl1 @ [pt2]))
                  | (Bound_children ptl1,Bound_children ptl2) .
                       (Bound_children (ptl1 @ ptl2))
                  | (_) . failwith `print_loop_merge -- inconsistent bindings`
              in  print_loop_merge (tl looppb) (replace pb (loopm,newb)))

        ??[`assoc`] (hd looppb).(print_loop_merge (tl looppb) pb)

        );;


%  Function to convert all single bound items in a binding to lists of one   %
%  element. This is used to make the bound items from a looping match which  %
%  only matched once into lists.                                             %

letrec raise_binding (pb:print_binding) =

   % : (print_binding -> print_binding) %

   if (null pb)
   then []
   else let (m,b) = hd pb
        in  (m,case b
               of (Bound_name s) . (Bound_names [s])
                | (Bound_names _) . b
                | (Bound_child pt) . (Bound_children [pt])
                | (Bound_children _) . b
            ).(raise_binding (tl pb));;


%  Function to merge two bindings generated by the same looping match.  %

%  One binding should be the result from previous times round the loop, and   %
%  the other should be from the current time round the loop.  The number and  %
%  ordering of the metavariables should thus be the same in both bindings,    %
%  so for efficiency, this is assumed. If this is not the case, the function  %
%  fails. The bound lists or single items from the two bindings are appended  %
%  into a single list. The types of the items must be consistent. If not the  %
%  function fails.                                                            %

letrec raise_bindings pb1 (pb2:print_binding) =

   % : (print_binding -> print_binding -> print_binding) %

   if (null pb1)
   then if (null pb2)
        then []
        else failwith `raise_bindings -- inconsistent bindings`
   else if (null pb2)
        then failwith `raise_bindings -- inconsistent bindings`
        else let (m1,b1) = (hd pb1)
             and (m2,b2) = (hd pb2)
             in  if (m1 = m2)
                 then (m1,case (b1,b2)
                          of (Bound_name s1,Bound_name s2) .
                                (Bound_names (s1.[s2]))
                           | (Bound_name s1,Bound_names sl2) .
                                (Bound_names (s1.sl2))
                           | (Bound_names sl1,Bound_name s2) .
                                (Bound_names (sl1 @ [s2]))
                           | (Bound_names sl1,Bound_names sl2) .
                                (Bound_names (sl1 @ sl2))
                           | (Bound_child pt1,Bound_child pt2) .
                                (Bound_children (pt1.[pt2]))
                           | (Bound_child pt1,Bound_children ptl2) .
                                (Bound_children (pt1.ptl2))
                           | (Bound_children ptl1,Bound_child pt2) .
                                (Bound_children (ptl1 @ [pt2]))
                           | (Bound_children ptl1,Bound_children ptl2) .
                                (Bound_children (ptl1 @ ptl2))
                           | (_) . failwith `raise_bindings -- ` ^
                                               `inconsistent bindings`
                      ).(raise_bindings (tl pb1) (tl pb2))
                 else failwith `raise_bindings -- inconsistent bindings`;;


%  Function to re-order two bindings of the same length and with the same     %
%  bound metavariables so that the metavariables appear in the same order in  %
%  both. The function fails if the number or names of the metavariables from  %
%  the two bindings are not the same. The second binding is re-ordered and    %
%  returned as result.                                                        %

letrec correspond_bindings (right:print_binding) (wrong:print_binding) =

   % : (print_binding -> print_binding -> print_binding) %

   if (null right)
   then if (null wrong)
        then []
        else failwith `correspond_bindings -- inconsistent bindings`
   else (  ((assoc (fst (hd right)) wrong).
               (correspond_bindings (tl right)
                   (filter (\x. not ((fst x) = (fst (hd right)))) wrong)))
        ?? [`assoc`] failwith `correspond_bindings -- inconsistent bindings`
        );;


%  This function is a safe but less efficient version of `raise_bindings'.  %

%  `raise_bindings' is tried first for efficiency, but if it fails, the  %
%  first binding is re-ordered, then `raise_bindings' is tried again.    %

let raise_bindings_safe wrong right =

   % : (print_binding -> print_binding -> print_binding) %

   (  (raise_bindings wrong right)
   ?? [`raise_bindings -- inconsistent bindings`]
      (raise_bindings (correspond_bindings right wrong) right)
   );;


%  Function to extract names of metavariables and loop-link occurring within  %
%  a tree pattern. The pair of string lists returned as part of the result    %
%  are the names of the metavariables. The first list is of metavariables     %
%  which match to node-names. The second is of metavariables which match to   %
%  sub-trees. The sub-tree in the link information is a null tree, because    %
%  since we are not doing matching, no real tree can be obtained.             %

letrec extract_info_from_patt ptpatt =

   % : (print_patt_tree -> ((string list # string list) # print_loop_link)) %

   let merge_links link1 link2 =

      % : (print_loop_link -> print_loop_link -> print_loop_link) %

      case (link1,link2)
      of (No_link,_) . link2
       | (_,No_link) . link1
       | (_) . failwith (`extract_info_from_patt -- ` ^
                            `more than one \`link' for loop`)

   in  case ptpatt
       of (Const_name (_,cml)) .
             (let (vars,linkl) = split (map extract_info_from_child cml)
              in  let (nmsl,cmsl) = split vars
                  in  ((itlist union nmsl [], itlist union cmsl []),
                       itlist merge_links linkl No_link))
        | (Var_name (s,cml)) .
             (let (vars,linkl) = split (map extract_info_from_child cml)
              in  let (nmsl,cmsl) = split vars
                  in  ((itlist union nmsl [s], itlist union cmsl []),
                       itlist merge_links linkl No_link))
        | (Wild_name cml) .
             (let (vars,linkl) = split (map extract_info_from_child cml)
              in  let (nmsl,cmsl) = split vars
                  in  ((itlist union nmsl [], itlist union cmsl []),
                       itlist merge_links linkl No_link))
        | (Var_child s) . (([],[s]),No_link)
        | (Wild_child) . (([],[]),No_link)
        | (Link_child link) . (([],[]),Link (link,(Print_node (``,[]),[])))
        | (Print_label (s,ptpatt1)) .
             (let ((nms,cms),link) = extract_info_from_patt ptpatt1
              in  ((nms,union [s] cms),link))
        | (Print_link (link1,ptpatt1)) .
             (let ((nms,cms),link2) = extract_info_from_patt ptpatt1
              in  ((nms,cms),
                   merge_links (Link (link1,(Print_node (``,[]),[]))) link2))
        | (Print_loop (ptpatt1,ptpatt2)) .
             (let ((nms1,cms1),_) = extract_info_from_patt ptpatt1
              and ((nms2,cms2),link) = extract_info_from_patt ptpatt2
              in  ((union nms1 nms2, union cms1 cms2),link))

%  Function to extract names of metavariables and loop-link occurring within  %
%  a child (sub-tree).                                                        %

and extract_info_from_child cm =

   % : (child_metavar -> ((string list # string list) # print_loop_link)) %

   case cm
   of (Var_children s) . (([],[s]),No_link)
    | (Wild_children) . (([],[]),No_link)
    | (Patt_child ptpatt) . (extract_info_from_patt ptpatt);;


%  Function to obtain a dummy binding and the minimum number of times a loop  %
%  should go round from a tree pattern. Fails if pattern does not contain a   %
%  loop-link. This function is for use when a loop matches zero times.        %

let zero_loop_info ptpatt =

   % : (print_patt_tree -> (print_binding # loop_limit)) %

   let ((nms,cms),link) = extract_info_from_patt ptpatt
   in  case link
       of (No_link) . failwith `zero_loop_info -- no \`link' for loop`
        | (Link (((min,_),_),_)) .
             (((map (\s. (s,Bound_names [])) nms) @
                  (map (\s. (s,Bound_children [])) cms)),min);;


%  Function to add sub-tree addresses to a list of trees.  %

let new_addresses address (ptl:print_tree list) =

   % : (int list -> print_tree list -> (print_tree # int list) list) %

   letrec new_addresses' n ptl =
      if (null ptl)
      then []
      else (hd ptl,n.address).(new_addresses' (n + 1) (tl ptl))
   in new_addresses' 1 ptl;;


%  Function to split a list into three parts.  %

%  The list l is broken so that the first of the three lists contains nh  %
%  elements, the third list contains nt elements, and the second list     %
%  contains the elements in between. The function fails if there are      %
%  insufficient elements to do this.                                      %

let split_list (nh,nt) l =

   % : ((int # int) -> * list -> (* list # * list # * list)) %

   letrec get_head n lh lt =

      % : (int -> * list -> * list -> (* list # * list)) %

      if ((n < 0) or (n = 0))
      then (lh,lt)
      else if (null lt)
           then failwith `split_list -- insufficient elements in list`
           else get_head (n - 1) (lh @ [hd lt]) (tl lt)

   in let (h,r) = get_head nh [] l
      and nm = (length l) - (nh + nt)
      in  if (nm < 0)
          then failwith `split_list -- insufficient elements in list`
          else (h,get_head nm [] r);;


%  Function to match a tree pattern to a tree.  %

letrec print_tree_match' ptpatt (pt,address) =

   % : (print_patt_tree -> (print_tree # int list) ->    %
   %                  (print_binding # print_loop_link)) %

   %  Function to match a looping pattern to a tree.  %

   %  The arguments to the sub-function are as follows:                       %
   %                                                                          %
   %     ptpatt:   looping pattern                                            %
   %     min:      minimum number of times to loop                            %
   %     n:        number of successful loops                                 %
   %     fixedpb:  binding of `fixed' metavariables on first time round loop  %
   %     pbind:    binding obtained so far                                    %
   %     ptadd':   parse-tree to be matched on this time round loop           %
   %               and its address relative to root                           %

   %  On the first call to the sub-function, the minimum number of times to   %
   %  loop is not known, so it is set to the default value. The number of     %
   %  successful loops is zero. The bindings are both empty, and the tree to  %
   %  be matched is the whole tree to be matched by the looping pattern.      %

   %  `traps' is set to the specific exceptions which correspond to failures  %
   %  to match rather than errors. A match is attempted between the pattern   %
   %  and the tree. If successful, a binding and a loop-link is obtained.     %
   %  The loop-link is examined. If there was no link found, an error is      %
   %  raised. If the maximum number of times to loop is the default (which    %
   %  is any number of times), the minimum number of times to loop, the list  %
   %  of variables to be `fixed', and the new sub-tree to be matched are      %
   %  extracted. The minimum number of loops and the fix list are the same    %
   %  every time round the loop, so they are only really required on the      %
   %  first. The same information is extracted if the maximum number of       %
   %  times to loop is not the default, unless the number of successful       %
   %  loops so far is greater than or equal to the maximum, when a match      %
   %  failure is raised.                                                      %

   %  Assuming no match failure has occurred so far, the binding obtained     %
   %  from the match and the binding of fixed values are merged. If the       %
   %  objects bound to the fixed variables on this time around the loop are   %
   %  not the same as those for the first time, a match failure is raised.    %
   %  On the first time round the loop, `fixedpb' is null, so the merge       %
   %  succeeds trivially.                                                     %

   %  If still without a match failure, the function now behaves differently  %
   %  on the first time round the loop than on subsequent times. On the       %
   %  first time, the minimum number of times to loop is updated. The         %
   %  number of successful matches is incremented. The binding obtained is    %
   %  filtered for variables in the `fix' list and is used as the new         %
   %  `fixedpb'. The binding obtained is `raised' so that the bound items     %
   %  are all lists. On subsequent times round the loop, the minimum looping  %
   %  value and `fixedpb' are not updated (except that on the second time     %
   %  round, sub-tree addresses are thrown away because they are no longer    %
   %  valid.), and the new binding is merged with the previous binding in     %
   %  such a way that bound lists are appended.                               %

   %  If any match failure is raised, it is trapped. If it is the first time  %
   %  round the loop, a special function is used to obtain a dummy binding    %
   %  and the minimum number of times to loop. The loop has matched zero      %
   %  times, so all metavariables are bound to empty lists. Whatever the      %
   %  value of n, the function checks to see if the minimum number of times   %
   %  to loop has been attained. This is trivially so if the minimum number   %
   %  is the default of zero. If the minimum number has not been attained a   %
   %  match failure is raised (which is not in `traps', so will not be        %
   %  trapped by previous function calls).                                    %

   let loop_match ptpatt ptadd =

      % : (print_patt_tree -> (print_tree # int list) ->    %
      %       (print_binding # print_binding # print_tree)) %

      letrec loop_match' ptpatt min n fixedpb pbind ptadd' =

         % : (print_patt_tree -> loop_limit -> nat -> print_binding -> %
         %       print_binding -> (print_tree # int list) ->           %
         %          (print_binding # print_binding # print_tree))      %

         let traps = [`print_tree_match`;`print_merge`]
         in  (let (mainpb,link) = print_tree_match' ptpatt ptadd'
              in  let (min',fixl,newptadd) =
                     case link
                     of (No_link) . failwith (`print_tree_match -- ` ^
                                                 `no \`link' for loop`)
                      | (Link (((min,Default),fixl),newptadd)) .
                                                   (min,fixl,newptadd)
                      | (Link (((min,Val max),fixl),newptadd)) .
                           (if ((Int n) < (Int max))
                            then (min,fixl,newptadd)
                            else failwith `print_tree_match`)
                  and newpb = print_merge mainpb fixedpb
                  in  if ((Int n) = 0)
                      then loop_match' ptpatt min' (Nat ((Int n) + 1))
                              (filter (\p. mem (fst p) fixl) mainpb)
                                 (raise_binding newpb) newptadd
                      if ((Int n) = 1)
                      then loop_match' ptpatt min (Nat ((Int n) + 1))
                              (map (I # no_address_meta) fixedpb)
                                 (raise_bindings_safe pbind newpb) newptadd
                      else loop_match' ptpatt min (Nat ((Int n) + 1)) fixedpb
                              (raise_bindings_safe pbind newpb) newptadd
             ) ?? traps (let (pb,min') =
                            if ((Int n) = 0)
                            then zero_loop_info ptpatt
                            else (pbind,min)
                         in  case min'
                             of (Default) . (pb,fixedpb,ptadd')
                              | (Val m) . (if ((Int m) > (Int n))
                                           then failwith `print_loop_match`
                                           else (pb,fixedpb,ptadd')))

      in loop_match' ptpatt Default (Nat 0) [] [] ptadd

   in case ptpatt

      %  Constant node-name with children.  %

      of (Const_name (s,cml)) .
            (if (s = (print_tree_name pt))
             then children_match cml
                     (new_addresses address (print_tree_children pt))
             else failwith `print_tree_match`)

      %  Variable node-name with children (node-name to be bound).  %

      %  Sub-tree addresses are built up backwards, so have to be reversed  %
      %  before being stored.                                               %

       | (Var_name (s,cml)) .
            (let (pbind,link) =
                children_match cml
                   (new_addresses address (print_tree_children pt))
             in  (print_merge
                     [s,Bound_name (print_tree_name pt,Address (rev address))]
                        pbind,
                  link))

      %  Variable node-name with children (no binding of node-name).  %

       | (Wild_name cml) .
            (children_match cml
                (new_addresses address (print_tree_children pt)))

      %  Variable child (to be bound).  %

       | (Var_child s) . ([s,Bound_child (pt,Address (rev address))],No_link)

      %  Variable child (not to be bound).  %

       | (Wild_child) . ([],No_link)

      %  Loop-link on leaf of pattern tree.  %

       | (Link_child x) . ([],Link (x,(pt,address)))

      %  Labelling of sub-tree of pattern tree.  %
      %  Metavariable named is bound to tree matched by sub-tree of pattern.  %

       | (Print_label (label,ptpatt1)) .
            (let (pbind,link) = print_tree_match' ptpatt1 (pt,address)
             in  (print_merge
                     [label,Bound_child (pt,Address (rev address))] pbind,
                  link))

      %  Loop-link not on leaf of pattern tree.  %
      %  Any loop-link from the sub-tree of the pattern is discarded.  %

       | (Print_link (x,ptpatt1)) .
            (let (pbind,_) = print_tree_match' ptpatt1 (pt,address)
             in  (pbind,Link (x,(pt,address))))

      %  Looping pattern.  %
      %  First sub-pattern is the looping part. No link is obtained from      %
      %  this. The sub-tree produced is used for the second part of the       %
      %  match. Any `fixed' variables are removed from the binding obtained   %
      %  from the loop. The `fixed' binding is merged with the binding from   %
      %  the non-looping part in such a way that the match fails if `fixed'   %
      %  variables are not bound to the same object in both. The bindings     %
      %  resulting from these two operations are merged so that non-fixed     %
      %  variables from the looping part which also occur in the non-looping  %
      %  part become bound to a list formed by appending the bound objects    %
      %  from the two bindings. Note that if a loop matches zero times,       %
      %  `fixedpb' is a null list. This means that any metavariable `fixed'   %
      %  in the loop will cease to be treated as `fixed'.                     %

       | (Print_loop (ptpatt1,ptpatt2)) .
            (let (pbind1,fixedpb,ptadd1) = loop_match ptpatt1 (pt,address)
             in  let (pbind2,link) = print_tree_match' ptpatt2 ptadd1
                 in  (print_loop_merge
                        (filter (\x. not (can (assoc (fst x)) fixedpb)) pbind1)
                           (print_merge fixedpb pbind2), link))

%  Function to match patterns for children to a list of sub-trees.  %

and children_match ml ptaddl =

   % : (child_metavar list -> (print_tree # int list) list ->       %
   %                             (print_binding # print_loop_link)) %

   %  Function to associate each `child_metavar' to a list of trees.  %

   %  Each `Patt_child' has to be associated with exactly one tree.           %
   %  `Var_children' and `Wild_children' can be associated with zero or more  %
   %  trees. The first `Var_children' or `Wild_children' encountered becomes  %
   %  associated with all the `slack' in the list of trees, leaving one tree  %
   %  for each remaining `child_metavar'. So, having more than one            %
   %  `Var_children' or `Wild_children' is pointless, as all but the first    %
   %  will behave like a `Patt_child'.                                        %

   %  If there are insufficient trees to associate one with each              %
   %  `Patt_child', the match fails. If there are no `Var_children' or        %
   %  `Wild_children' to take up the `slack', then the number of              %
   %  `Patt_child's must be the same as the number of trees, or else the      %
   %   match fails.                                                           %

   letrec correspond ml' ptaddl' =

      % : (child_metavar list -> (print_tree # int list) list ->         %
      %                        (child_metavar # (print_tree list)) list) %

      if (null ml')
      then if (null ptaddl')
           then []
           else failwith `print_tree_match`
      else case (hd ml')
           of (Var_children _) .
                 ( (let (_,l,r) = split_list (0,length (tl ml')) ptaddl'
                    in  ((hd ml'),l).(correspond (tl ml') r))
                 ? failwith `print_tree_match`
                 )
            | (Wild_children) .
                 ( (let (_,l,r) = split_list (0,length (tl ml')) ptaddl'
                    in  ((hd ml'),l).(correspond (tl ml') r))
                 ? failwith `print_tree_match`
                 )
            | (Patt_child _) .
                 (if (null ptaddl')
                  then failwith `print_tree_match`
                  else ((hd ml'),[hd ptaddl']).
                          (correspond (tl ml') (tl ptaddl'))
                 )

   %  Function to match a `child_metavar' to a list of trees.  %

   and child_match m ptaddl' =

      % : (child_metavar -> (print_tree # int list) list ->    %
      %                     (print_binding # print_loop_link)) %

      case (m,ptaddl')
      of (Var_children s,_) .
            ([s,Bound_children (map (I # (Address o rev)) ptaddl')],No_link)
       | (Wild_children,_) . ([],No_link)
       | (Patt_child ptpatt',[ptadd']) . (print_tree_match' ptpatt' ptadd')
       | (_) . failwith (`print_tree_match -- ` ^
                            `inconsistent arguments to child_match`)

   %  Function to match a list of (`child_metavar'/tree list) pairs.  %

   %  The bindings are merged so that metavariables occurring in more than  %
   %  one have to match to the same object in each of those bindings. If    %
   %  more than one loop-link is present, an error occurs.                  %

   and merge l =

      % : ((child_metavar # ((print_tree # int list) list)) list ->    %
      %                             (print_binding # print_loop_link)) %

      if (null l)
      then ([],No_link)
      else let (pbind1,link1) = uncurry child_match (hd l)
           and (pbind2,link2) = merge (tl l)
           in  (print_merge pbind1 pbind2,
                case (link1,link2)
                of (No_link,_) . link2
                 | (_,No_link) . link1
                 | (_) . failwith (`print_tree_match -- ` ^
                                      `more than one \`link' for loop`))

   in merge (correspond ml ptaddl);;

%  Address of root of tree is an empty list.  %

let print_tree_match ptpatt pt = print_tree_match' ptpatt (pt,[]);;


%  Function to make context available in parameter list.  %

let add_context context params =

   % : (string -> (string # int) list -> (string # int) list) %

   ((`CONTEXT_` ^ context),0).params;;


%  Function to match a pretty-printing pattern to a tree under a  %
%  pretty-printing environment.                                   %

%  If the context of the pattern is the null string or matches the context    %
%  of the environment, then an attempt is made to match the tree. If a        %
%  loop-link appears at top-level, it is not used within a loop, so an error  %
%  occurs. A test is applied to the result of the match.                      %

let print_pattern_match (ppatt:print_pattern) context params pt =

   % : (print_pattern -> string -> (string # int) list -> print_tree ->     %
   %                                                         print_binding) %

   if (((fst ppatt) = ``) or ((fst ppatt) = context))
   then let (result,link) = print_tree_match (fst (snd ppatt)) pt
        in  if (link = No_link)
            then if ((snd (snd ppatt)) (add_context context params) result)
                 then result
                 else failwith `print_pattern_match`
            else failwith (`print_pattern_match -- ` ^
                              `\`link' used outside a loop`)
   else failwith `print_pattern_match`;;

(add_context,print_pattern_match);;
end_section treematch;;
let (add_context,print_pattern_match) = it;;


%-----------------------------------------------------------------------------%
