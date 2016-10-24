% treetobox.ml                                                                %
%-----------------------------------------------------------------------------%


%  Abbreviation for datatype of special metavariable assignments.  %

lettype print_special = string
                      # ((string # int) list -> print_binding ->
                                                    metavar_binding);;


%  Abbreviation for datatype of pretty-printer integer expressions.  %

lettype print_int_exp = (string # int) list -> print_binding -> int;;


%  Datatypes for formats, objects, and box specifications.  %

rectype print_box_spec = H_box of (nat # print_object) list
                       | V_box of ((print_indent # nat) # print_object) list
                       | HV_box of ((nat # print_indent # nat) # print_object)
                                                                           list
                       | HoV_box of ((nat # print_indent # nat) # print_object)
                                                                           list

and print_format = PF_empty
                 | PF of print_box_spec
                 | PF_branch of print_test # print_format # print_format

and print_object = PO_constant of string
                 | PO_leaf of string # (string -> string)
                 | PO_subcall of (string #
                                  ((print_tree # address) list ->
                                   (print_tree # address) list))
                               # (string # print_int_exp) list
                 | PO_context_subcall of string
                                       # (string #
                                          ((print_tree # address) list ->
                                           (print_tree # address) list))
                                       # (string # print_int_exp) list
                 | PO_format of print_format
                 | PO_expand of print_box_spec;;


%  Useful abbreviations for composite type constructors.  %

let PF_H = PF o H_box
and PF_V = PF o V_box
and PF_HV = PF o HV_box
and PF_HoV = PF o HoV_box;;


%  Abbreviation for type of pretty-printing rules.  %

lettype print_rule = print_pattern # print_special list # print_format;;


%  Abbreviation for type of pretty-printing rules as functions.  %

lettype print_rule_function = string -> (string # int) list -> print_tree ->
                                               (print_binding # print_format);;


%  Function to create extra bindings from special assignments using  %
%  pretty-printing environment supplied.                             %

let print_special_fun context params pbind (pspecials:print_special list) =

   % : (string -> (string # int) list -> print_binding ->     %
   %                     print_special list -> print_binding) %

   map (\(s,f). s,(f (add_context context params) pbind)) pspecials;;


%  Function to convert a list of pretty-printing rules into a function.  %

%  The function tries each rule in turn until one matches the tree. Special  %
%  assignments are then computed and used as replacements or additions to    %
%  the binding. The new binding is returned along with the format from the   %
%  rule.                                                                     %

letrec print_rule_fun (prl:print_rule list) context params pt =

   % : (print_rule list -> string -> (string # int) list -> print_tree ->    %
   %                                         (print_binding # print_format)) %

   % : (print_rule list -> print_rule_function) %

   if (null prl)
   then failwith `print_rule_fun`
   else let traps = [`print_pattern_match`;`print_tree_match`;
                     `print_merge`;`print_loop_match`]
        in  (  (let pbind =
                   print_pattern_match (fst (hd prl)) context params pt
                in  (change_assocl pbind
                        (print_special_fun context params pbind
                                              (fst (snd (hd prl)))),
                     snd (snd (hd prl))))
            ?? traps (print_rule_fun (tl prl) context params pt)
            );;


%  Infix function for composing two print-rule functions so that first the  %
%  rules of one function are tried, and if none match, rules of the second  %
%  function are tried.                                                      %

ml_curried_infix `then_try`;;

let then_try prf1 prf2 =

   % : (print_rule_function -> print_rule_function -> print_rule_function) %

   (\context params pt. (  (prf1 context params pt)
                        ?? [`print_rule_fun`] (prf2 context params pt)
                        )) : print_rule_function;;


%  Print-rules for pretty-printing the structure of a tree.  %

%  These rules are used by default if no other rules match.  %

let raw_tree_rules =

   % : (print_rule list) %

   [(``,Var_name (`n`,[Var_children `cl`;Patt_child (Var_child `c`)]),
                                                            (\x y. true)),[],
       (PF_HV [(Nat 0,Abs 0,Nat 0),
               PO_leaf (`n`,(\s.s));
               (Nat 0,Abs 3,Nat 0),
               PO_format
                  (PF_H [Nat 0,
                         PO_constant `(`;
                         Nat 0,
                         PO_format
                            (PF_HoV [(Nat 0,Abs 0,Nat 0),
                                     PO_expand (H_box [Nat 0,
                                                       PO_subcall
                                                          ((`cl`,(\l.l)),[]);
                                                       Nat 0,
                                                       PO_constant `,`]);
                                     (Nat 0,Abs 0,Nat 0),
                                     PO_subcall ((`c`,(\l.l)),[])]);
                         Nat 0,
                         PO_constant `)`])]);
    (``,Var_name (`n`,[]),(\x y. true)),[],
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))])
   ] : print_rule list;;


let raw_tree_rules_fun =

   % : (print_rule_function) %

   print_rule_fun raw_tree_rules;;


begin_section treetobox;;

%  Function to expand a binding into a list of bindings so that a        %
%  metavariable bound to a list in the original binding is bound to one  %
%  element of the list in each of the resulting bindings.                %

%  The number of bindings produced is equal to the length of the longest      %
%  list bound to a metavariable in the original binding. Items other than     %
%  lists become duplicated, one copy going in each list. If a metavariable    %
%  is bound to a list shorter than the longest list, the bindings for which   %
%  there are no values left get the metavariable bound to an empty list.      %
%  When an attempt is made to print such a metavariable, the result is an     %
%  empty box (i.e. no output).                                                %

%  The sub-function `split_binding' takes a binding and a Boolean value       %
%  initialised to false. The binding is duplicated. For any bound list in     %
%  the original, the first binding gets the head of the list, and the second  %
%  binding gets the tail. If the list is empty, both copies get the empty     %
%  list. If a list is split, the Boolean passed back is true, otherwise the   %
%  value from the recursive call is passed back. The result is that if any    %
%  list is split into head and tail, the final Boolean returned is true.      %

%  The first binding produced by `split_binding' is put into the list of      %
%  bindings to be returned by `expand_binding'. The other is either split     %
%  again or discarded. It is split again if the Boolean returned from the     %
%  call to `split_binding' is true. Note that when there is no more to do,    %
%  `newpb' is discarded as well as `restpb' because in such a case `newpb'    %
%  is an unwanted binding in which all bound lists are empty.                 %

letrec expand_binding pb =

   % : (print_binding -> print_binding list) %

   letrec split_binding b pb' =

      % : (bool -> print_binding -> (print_binding # print_binding # bool)) %

      if (null pb')
      then ([],[],b)
      else let (pbhead,pbtail,flag) = split_binding b (tl pb')
           and (m,mb) = hd pb'
           in  let (h,t,f) =
                  case mb
                  of (Bound_name _) . ((m,mb),(m,mb),flag)
                   | (Bound_names sl) .
                        (if (null sl)
                         then ((m,mb),(m,mb),flag)
                         else ((m,Bound_name (hd sl)),
                                  (m,Bound_names (tl sl)),true))
                   | (Bound_child _) . ((m,mb),(m,mb),flag)
                   | (Bound_children ptl) .
                        (if (null ptl)
                         then ((m,mb),(m,mb),flag)
                         else ((m,Bound_child (hd ptl)),
                                  (m,Bound_children (tl ptl)),true))
               in  ((h.pbhead),(t.pbtail),f)

   in let (newpb,restpb,more_to_do) = split_binding false pb
      in  if more_to_do
          then newpb.(expand_binding restpb)
          else [];;


%  Functions to obtain list of metavariables which are in scope within an  %
%  expansion box.                                                          %

letrec extract_expanded_from_spec pbs =

   % : (print_box_spec -> string list) %

   let pol =
      case pbs
      of (H_box x) .   (map snd x)
       | (V_box x) .   (map snd x)
       | (HV_box x) .  (map snd x)
       | (HoV_box x) . (map snd x)
   in  itlist union (map extract_expanded_from_object pol) []

and extract_expanded_from_object po =

   % : (print_object ->  string list) %

   case po
   of (PO_constant _) . []
    | (PO_leaf (metavar,_)) . [metavar]
    | (PO_subcall ((metavar,_),_)) . [metavar]
    | (PO_context_subcall (_,(metavar,_),_)) . [metavar]
    | (PO_format _) . []
    | (PO_expand pbs) . (extract_expanded_from_spec pbs);;


%  Functions for converting a parse-tree into a box of text.  %

%  If the rules supplied fail to match, default rules are used. If the     %
%  debugging option is specified in the parameters, errors are allowed to  %
%  pass up to top-level. Otherwise `*error*' is placed in the text if an   %
%  error occurs.                                                           %

letrec print_tree_to_box m i prf context params pt =

   % : (int -> int -> print_rule_function -> string -> (string # int) list -> %
   %                                         print_tree -> address print_box) %

   let print_tree_to_box' m i prf context params pt =

      % : (int -> int -> print_rule_function -> string ->            %
      %      (string # int) list -> print_tree -> address print_box) %

      let (pbind,pf) =
         (  (prf context params pt)
         ?? [`print_rule_fun`] (raw_tree_rules_fun context params pt)
         )
      in  print_format_fun m i prf context params pbind pf

   in  if (can (assoc `DEBUG`) params)
       then print_tree_to_box' m i prf context params pt
       else ( (print_tree_to_box' m i prf context params pt)
            ? (A_box ((Nat 7,`*error*`),No_address))
            )

%  The result of a call to `print_object_fun' is a list of functions which    %
%  given available space information produce boxes. One object may yield      %
%  several such functions. The sub-function `f' below pairs each function     %
%  with the box parameters of the object from which it was obtained. This is  %
%  done for all objects in the box, and the list of lists is flattened. If    %
%  the resulting list is empty, an exception is raised to be trapped later.   %
%  Otherwise the box parameters for the first item in the list are discarded  %
%  because the first item in a box of text has a fixed position at the        %
%  beginning of the box.                                                      %

and print_box_spec_fun m i prf context params pbind pbind' expanded pbs =

   % : (int -> int -> print_rule_function -> string ->                        %
   %     (string # int) list -> print_binding -> print_binding -> bool ->     %
   %                                     print_box_spec -> address print_box) %

   let f pof xpol =

      % : ((print_object -> (int -> int -> address print_box) list) -> %
      %    (* # print_object) list ->                                  %
      %    (int -> int -> address print_box) #                         %
      %       (* # (int -> int -> address print_box)) list)            %

      let xpbfnl = flat (map (\(x,po). map (\pbfn. (x,pbfn)) (pof po)) xpol)
      in  if (null xpbfnl)
          then failwith `print_box_spec_fun`
          else (snd (hd xpbfnl),tl xpbfnl)

   and pof = print_object_fun prf context params pbind pbind' expanded

   %  Empty sub-tree addresses (Address []) are inserted as the `labels' of   %
   %  each sub-box. The `label' at the root of the generated box will later   %
   %  be replaced by a relative address. This technique is a bit wasteful,    %
   %  since unnecessary garbage is generated. However, it greatly simplifies  %
   %  the box-building programs.                                              %

   in  build_print_box m i (Address [])
          (case pbs
           of (H_box xpol) . (UB_H (f pof xpol))
            | (V_box xpol) . (UB_V (f pof xpol))
            | (HV_box xpol) . (UB_HV (f pof xpol))
            | (HoV_box xpol) . (UB_HoV (f pof xpol)))

%  Expansion does not continue into nested formats. It only continues into    %
%  nested expansion-boxes. So `print_box_spec_fun' is called below with the   %
%  `expanded' argument set to false, and the binding-to-use reset to the      %
%  original binding. If the call fails, an empty box of text is returned.     %

%  For the branching case, the current context is made available in the list  %
%  of parameters to the test which determines the format to use.              %

and print_format_fun m i prf context params pbind pf =

   % : (int -> int -> print_rule_function -> string -> (string # int) list -> %
   %                      print_binding -> print_format -> address print_box) %

   case pf
   of (PF_empty) . N_box
    | (PF pbs) . (  (print_box_spec_fun m i prf
                        context params pbind pbind false pbs)
                 ?? [`print_box_spec_fun`] N_box
                 )
    | (PF_branch (ptest,pf1,pf2)) .
         (if (ptest (add_context context params) pbind)
          then (print_format_fun m i prf context params pbind pf1)
          else (print_format_fun m i prf context params pbind pf2))

%  For the object given, `print_object_fun' produces a list of partially      %
%  processed objects. This allows for expansion of objects. `pbind' is the    %
%  original binding. `pbind'' is the subset of that binding currently in      %
%  use. `expanded' is a Boolean indicating whether processing is occurring    %
%  within an expansion box.                                                   %

%  For `subcalls', a list of names/functions are provided as changes to the   %
%  parameter list. Each function is applied to the pretty-printing            %
%  environment to yield an integer. The resulting list of pairs are then      %
%  used as parameter replacements. Note that the binding supplied to the      %
%  functions is the original binding, not the subset currently in use. Note   %
%  also that when the context is being changed, the functions receive the     %
%  current context, not the new one.                                          %

%  When an expansion-box is encountered, expansion only takes place if it is  %
%  not already. Expansion takes place by obtaining a list of bindings from    %
%  a subset of the original binding. The subset is chosen by finding the      %
%  names of the metavariables which are used within the expansion-box and     %
%  nested expansion-boxes.                                                    %

and print_object_fun prf context params pbind pbind' expanded po =

   % : (print_rule_function -> string -> (string # int) list ->          %
   %       print_binding -> print_binding -> bool -> print_object ->     %
   %                             (int -> int -> address print_box) list) %

   case po

      %  Constants do not have a sub-tree address associated with them.  %

   of (PO_constant s) . [\m i. A_box ((Nat (strlen s),s),No_address)]

      %  The address of a leaf-node (name) comes directly from the binding.  %

    | (PO_leaf (metavar,string_fun)) .
         (case (lookup_metavar pbind' metavar)
          of (Bound_name (s,add)) .
                [\m i. let s' = string_fun s
                       in  A_box ((Nat (strlen s'),s'),add)]
           | (Bound_names sl) .
                (map (\(s,add) m i. let s' = string_fun s
                                    in  A_box ((Nat (strlen s'),s'),add)) sl)
           | (_) . failwith (`print_tree_to_box -- ` ^
                             `type of metavariable \`` ^ metavar ^
                             `' in pattern does n't match type in format`))

      %  The address for a subcall comes from the binding. It is an address   %
      %  relative to the root of the tree given to the parent call. The       %
      %  address is inserted at the root of the box to be returned. This box  %
      %  is obtained from the recursive call and contains addresses relative  %
      %  to the root of the tree bound to the metavar. So, only the           %
      %  outermost boxes of a format of a print rule have a non-empty         %
      %  address. The intermediate boxes have empty addresses. Thus, in the   %
      %  resulting box structure, the relative addressing takes place in      %
      %  jumps corresponding to calls to the pretty-printer.                  %

    | (PO_subcall ((metavar,list_fun),param_changes)) .
         (let ptaddl = case (lookup_metavar pbind' metavar)
                       of (Bound_child ptadd) . [ptadd]
                        | (Bound_children ptaddl) . ptaddl
                        | (_) . failwith (`print_tree_to_box -- ` ^
                                          `type of metavariable \`` ^ metavar ^
                                          `' in pattern ` ^
                                          `does n't match type in format`)
          in  map (\(pt,address) m i.
                      replace_box_label address
                         (print_tree_to_box m i prf context
                             (change_assocl params
                                 (map
                                   (\(s,f).
                                      s,(f (add_context context params) pbind))
                                   param_changes)) pt))
                  (list_fun ptaddl))
    | (PO_context_subcall (new_context,(metavar,list_fun),param_changes)) .
         (let ptaddl = case (lookup_metavar pbind' metavar)
                       of (Bound_child ptadd) . [ptadd]
                        | (Bound_children ptaddl) . ptaddl
                        | (_) . failwith (`print_tree_to_box -- ` ^
                                          `type of metavariable \`` ^ metavar ^
                                          `' in pattern ` ^
                                          `does n't match type in format`)
          in  map (\(pt,address) m i.
                      replace_box_label address
                         (print_tree_to_box m i prf new_context
                             (change_assocl params
                                 (map
                                   (\(s,f).
                                      s,(f (add_context context params) pbind))
                                   param_changes)) pt))
                  (list_fun ptaddl))
    | (PO_format pf) .
         [\m i. print_format_fun m i prf context params pbind pf]
    | (PO_expand pbs) .
         (if expanded
          then [\m i. print_box_spec_fun
                         m i prf context params pbind pbind' true pbs]
          else map (\pb m i. print_box_spec_fun
                                m i prf context params pbind pb true pbs)
                      (expand_binding
                          (filter (\x. mem (fst x)
                                          (extract_expanded_from_spec pbs))
                                     pbind)));;

print_tree_to_box;;
end_section treetobox;;
let print_tree_to_box = it;;


%-----------------------------------------------------------------------------%
