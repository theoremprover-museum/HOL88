% utils.ml                                                                    %
%-----------------------------------------------------------------------------%


%  Function to test for the containment of the binding of a metavariable  %
%  in a list of strings. Function is an infix.                            %

%  Fails if metavariable not found in binding, or is not bound to a name.  %

ml_curried_infix `is_a_member_of`;;

let is_a_member_of metavar sl =

   % : (string -> string list -> print_test) %

   (\params pbind.
       mem (case (lookup_metavar pbind metavar)
            of (Bound_name (s,_)) . s
             | (_) . failwith
                        (`is_a_member_of -- used on metavar \`` ^ metavar ^
                         `' which is not bound to a name`)) sl) : print_test;;


%  Function to obtain the value of a parameter from a pretty-printing  %
%  environment. Fails if named parameter does not exist.               %

let bound_number s =

   % : (string -> ((string # int) list -> print_binding -> int)) %

   (\params (pbind:print_binding).
       ((snd (assoc s params)):int)
          ? failwith (`bound_number -- \``^s^`' not in parameters`));;


%  Functions to obtain the values bound to metavariables from a  %
%  pretty-printing environment.                                  %

%  The functions fail if the specified metavariable does not exist, or if it  %
%  is bound to an object of the wrong type.                                   %

%  The functions throw away sub-tree address information.  %

let bound_name meta =

   % : (string -> ((string # int) list -> print_binding -> string)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith (`bound_name -- \``^meta^`' not a metavariable`))
       of (Bound_name (s,_)) . s
        | (_) . failwith
                   (`bound_name -- metavar \``^meta^`' not bound to a name`));;


let bound_names meta =

   % : (string -> ((string # int) list -> print_binding -> string list)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith (`bound_names -- \``^meta^`' not a metavariable`))
       of (Bound_names sl) . (map fst sl)
        | (_) . failwith
                   (`bound_names -- metavar \``^meta^`' not bound to names`));;


let bound_child meta =

   % : (string -> ((string # int) list -> print_binding -> print_tree)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith (`bound_child -- \``^meta^`' not a metavariable`))
       of (Bound_child (pt,_)) . pt
        | (_) . failwith (`bound_child -- metavar \`` ^ meta ^
                          `' not bound to a child`));;


let bound_children meta =

   % : (string -> ((string # int) list -> print_binding -> print_tree list)) %

   (\(params:(string # int) list) pbind.
       case ((lookup_metavar pbind meta)
                ? failwith
                     (`bound_children -- \``^meta^`' not a metavariable`))
       of (Bound_children ptl) . (map fst ptl)
        | (_) . failwith (`bound_children -- metavar \`` ^ meta ^
                          `' not bound to children`));;


%  Function to obtain the `context' from a pretty-printing environment.  %

%  The <context> is held as a parameter called `CONTEXT_<context>', bound to  %
%  any integer. If such a parameter does not exist, the function fails.       %

let bound_context =

   % : ((string # int) list -> print_binding -> string) %

   (\(params:(string # int) list) (pbind:print_binding).
       ( ((\s. substr 8 ((strlen s) - 8) s)
             (fst (find (\p. (substr 0 8 (fst p)) = `CONTEXT_`) params)))
       ? failwith `bound_context`
       ));;


%  Functions for constructing new functions which access the pretty-printing  %
%  environment.                                                               %

let apply0 f =

   % : (* -> ((string # int) list -> print_binding -> *)) %

   (\(params:(string # int) list) (pbind:print_binding). f);;


let apply1 f val =

   % : ((* -> **) -> ((string # int) list -> print_binding -> *) ->   %
   %                    ((string # int) list -> print_binding -> **)) %

   (\(params:(string # int) list) (pbind:print_binding).
       f (val params pbind));;


let apply2 f val1 val2 =

   % : ((* -> ** -> **) ->                                %
   %    ((string # int) list -> print_binding -> *) ->    %
   %    ((string # int) list -> print_binding -> **) ->   %
   %       ((string # int) list -> print_binding -> ***)) %

   (\(params:(string # int) list) (pbind:print_binding).
       f (val1 params pbind) (val2 params pbind));;


%  Functions for making new values suitable for binding to metavariables,  %
%  from existing bound metavariables and transformation functions.         %

%  The functions fail if the specified metavariable does not exist or is  %
%  bound to an object of the wrong type.                                  %


%  new_name retains sub-tree address information.  %

let new_name f meta =

   % : ((string -> string) -> string ->                               %
   %       ((string # int) list -> print_binding -> metavar_binding)) %

   let bound_name_add meta =
      (\(params:(string # int) list) pbind.
          case ((lookup_metavar pbind meta)
                   ? failwith (`new_name -- \``^meta^`' not a metavariable`))
          of (Bound_name x) . x
           | (_) . failwith
                      (`new_name -- metavar \``^meta^`' not bound to a name`))
   in  apply1 (Bound_name o (f # I)) (bound_name_add meta);;


%  In new_names, sub-tree address information has to be kept with the names  %
%  because the manipulation function might re-order the names.               %

let new_names f meta =

   % : (((string # address) list -> (string # address) list) -> string ->    %
   %              ((string # int) list -> print_binding -> metavar_binding)) %

   let bound_names_add meta =
      (\(params:(string # int) list) pbind.
          case ((lookup_metavar pbind meta)
                   ? failwith (`new_names -- \``^meta^`' not a metavariable`))
          of (Bound_names xl) . xl
           | (_) . failwith
                      (`new_names -- metavar \``^meta^`' not bound to names`))
   in  apply1 (Bound_names o f) (bound_names_add meta);;


%  new_child retains sub-tree address information.  %

let new_child f meta =

   % : ((print_tree -> print_tree) -> string ->                       %
   %       ((string # int) list -> print_binding -> metavar_binding)) %

   let bound_child_add meta =
      (\(params:(string # int) list) pbind.
          case ((lookup_metavar pbind meta)
                   ? failwith (`new_child -- \``^meta^`' not a metavariable`))
          of (Bound_child x) . x
           | (_) . failwith (`new_child -- metavar \`` ^ meta ^
                             `' not bound to a child`))
   in  apply1 (Bound_child o (f # I)) (bound_child_add meta);;


%  In new_children, sub-tree address information has to be kept with the  %
%  trees because the manipulation function might re-order the trees.      %

let new_children f meta =

   % : (((print_tree # address) list -> (print_tree # address) list) ->      %
   %    string -> ((string # int) list -> print_binding -> metavar_binding)) %

   let bound_children_add meta =
      (\(params:(string # int) list) pbind.
          case ((lookup_metavar pbind meta)
                   ? failwith
                        (`new_children -- \``^meta^`' not a metavariable`))
          of (Bound_children xl) . xl
           | (_) . failwith (`new_children -- metavar \`` ^ meta ^
                             `' not bound to children`))
   in  apply1 (Bound_children o f) (bound_children_add meta);;


%-----------------------------------------------------------------------------%
