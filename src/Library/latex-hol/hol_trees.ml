% hol_trees.ml                                                                %
%-----------------------------------------------------------------------------%


%  Datatype for specifying amount of type information to be included in  %
%  parse-trees obtained from terms.                                      %

type type_selection = No_types
                    | Hidden_types
                    | Useful_types
                    | All_types;;


%  Function to convert HOL type into the corresponding parse-tree.  %

%  The sub-function does the conversion. The tree it produces is labelled as  %
%  having been derived from a type. The type is either a variable type or a   %
%  compound type.                                                             %

let type_to_print_tree t =

   % : (type -> print_tree) %

   letrec type_to_print_tree' t =

      % : (type -> print_tree) %

      if (is_vartype t)
      then Print_node (`VAR`,[Print_node (dest_vartype t,[])])
      else let (name,args) = dest_type t
           in  Print_node (`OP`,((Print_node (name,[])).
                                    (map type_to_print_tree' args)))

   in Print_node (`type`,[type_to_print_tree' t]);;


%  Function to convert HOL term into the corresponding parse-tree.  %

%  The first argument determines whether or not occurrences of the constant   %
%  UNCURRY are to be converted into abstractions with tuples in place of      %
%  bound variables. The conversion is attempted as soon as a sub-tree has     %
%  been built. This causes the conversion to be applied upwards from deep     %
%  within the tree, which means that if the conversion generates any new      %
%  instances of sub-trees that should be converted, they will not be missed.  %

%  The second argument controls the amount of type information included in    %
%  the tree.                                                                  %

%  Type information is included with constants if all type info is required   %
%  or if useful type info is required and the constant is a function which    %
%  is not fully applied.                                                      %

%  There are two cases for variables. If a variable of the same name has      %
%  already been encountered, type info is included if all type info is        %
%  required. If no type info is required, no type is included. In any other   %
%  case, type info is included if the variable has a different type to that   %
%  of the variable already encountered. If no variable of the same name has   %
%  been encountered, type info is included if required, and in any case the   %
%  variable is added to the list of those already encountered.                %

%  For abstractions, the bound variable is converted first so that it is      %
%  adorned with type information in preference to occurrences of the same     %
%  variable within the body. Any variables of the same name already in the    %
%  list of variables encountered are removed because they are not visible     %
%  within the body.                                                           %

%  At an application, the rator may be told that it is fully applied. This    %
%  is the case if the application has an overall type which is not a          %
%  function type, and it is also the case if there is a fully applied parent  %
%  application (i.e. one higher up the tree).                                 %

%  Finally, the tree is labelled as having been generated from a term.        %

let term_to_print_tree transform type_info t =

   % : (bool -> type_selection -> term -> print_tree) %

   letrec term_to_print_tree' transform type_info fully_applied_fun stl t =

      % : (bool -> type_selection -> bool -> (string # type) list -> term ->  %
      %                                  (print_tree # (string # type) list)) %

      let (hidden_types,useful_types,all_types) =
         case type_info
         of No_types . (false,false,false)
          | Hidden_types . (true,false,false)
          | Useful_types . (true,true,false)
          | All_types . (true,true,true)

      and is_fun_type ty =

         % : (type -> bool) %

         (((fst (dest_type ty)) = `fun`) ? false)

      in let (pt,stl') =
            if (is_const t) then
               (let (name,typ) = dest_const t
                in  (Print_node
                       (`CONST`,((Print_node (name,[])).
                                 (if (((not fully_applied_fun) &
                                       (is_fun_type typ) &
                                       useful_types) or all_types)
                                  then [type_to_print_tree typ]
                                  else []))), stl))
            if (is_var t) then
               (let (name,typ) = dest_var t
                in  (  (let ty = snd (assoc name stl)
                        in  (Print_node
                               (`VAR`,((Print_node (name,[])).
                                       (if (((not (ty = typ)) & hidden_types)
                                               or all_types)
                                        then [type_to_print_tree typ]
                                        else []))), stl))
                    ?? [`assoc`]
                       (Print_node
                          (`VAR`,((Print_node (name,[])).
                                  (if (useful_types or all_types)
                                   then [type_to_print_tree typ]
                                   else []))), ((name,typ).stl))
                    ))
            if (is_abs t) then
               (let (bv,body) = dest_abs t
                in  let (pt1,stl1) =
                       term_to_print_tree' transform type_info false [] bv
                    in  let (pt2,stl2) =
                           term_to_print_tree' transform type_info false
                              ((hd stl1).
                                  (filter (\x. not ((fst x) = (fst (hd stl1))))
                                             stl)) body
                        in  (Print_node (`ABS`,[pt1;pt2]), stl2))
            if (is_comb t) then
               (let (rator,rand) = dest_comb t
                and fully_applied_fun' = fully_applied_fun or
                                            (not (is_fun_type (type_of t)))
                in  let (pt1,stl1) = term_to_print_tree' transform type_info
                                        fully_applied_fun' stl rator
                    in  let (pt2,stl2) =
                           term_to_print_tree' transform type_info false stl1
                                                                           rand
                        in  (Print_node (`COMB`,[pt1;pt2]),stl2))
            else failwith `term_to_print_tree`

         in  case (pt,transform)
             of (Print_node
                   (`COMB`,[Print_node
                              (`CONST`,((Print_node (`UNCURRY`,[]))._));
                            Print_node
                              (`ABS`,[pt1;Print_node (`ABS`,[pt2;pt3])])
                           ]), true) .
                   (Print_node
                      (`ABS`,
                       [Print_node
                          (`COMB`,
                           [Print_node
                              (`COMB`,
                               [Print_node (`CONST`,[Print_node (`,`,[])]);
                                pt1]);pt2]);pt3]), stl')
              | (_) . (pt,stl')

   in Print_node
         (`term`,[fst (term_to_print_tree' transform type_info false [] t)]);;


%  Function to convert HOL theorem into the corresponding parse-tree.  %

%  The first argument controls whether or not hypotheses are abbreviated.  %

let thm_to_print_tree show_assumps transform type_info t =

   % : (bool -> bool -> type_selection -> thm -> print_tree) %

   Print_node
      (`thm`,[term_to_print_tree transform type_info (concl t);
              (if show_assumps
               then Print_node
                      (`hyp`,
                          map (term_to_print_tree transform type_info) (hyp t))
               else Print_node
                      (`dots`,map (\x. Print_node (`dot`,[])) (hyp t)))
             ]);;


%-----------------------------------------------------------------------------%
