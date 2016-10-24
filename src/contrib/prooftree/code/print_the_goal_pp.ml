% print_the_goal_pp.ml                                                        %
%-----------------------------------------------------------------------------%


let printgoal_rules =

   % : (print_rule list) %

   [
    ((`goal`,(Const_name (`goal`,[(Patt_child (Var_child `topterm`))])),
      (\x y. true)),[],
     (PF
       (H_box [((Nat 0),(PO_context_subcall (`term`,(`topterm`,(I)),[])))])));
    ((`goal`,
      (Const_name
        (`goal`,
         [(Patt_child (Var_child `topterm`));(Var_children `asl`)])),
      (\x y. true)),[],
     (PF (V_box [(((Abs 6),(Nat 0)),
                  (PO_context_subcall (`term`,(`topterm`,(I)),[])));
                 (((Abs 6),(Nat 0)),
                  (PO_format
                    (PF (H_box
                          [((Nat 0),(PO_constant `[`));
                           ((Nat 0),
                            (PO_context_subcall (`dotted`,(`asl`,(I)),[])));
                           ((Nat 0),(PO_constant `]`))]))))])));
    ((`fullgoal`,
      (Const_name
        (`goal`,
         [(Patt_child (Var_child `topterm`));(Var_children `asl`)])),
      (\x y. true)),[],
     (PF (V_box [(((Abs 6),(Nat 0)),
                  (PO_context_subcall (`term`,(`topterm`,(I)),[])));
                 (((Abs 6),(Nat 0)),
                  (PO_expand
                    (H_box [((Nat 0),(PO_constant `[`));
                            ((Nat 0),
                             (PO_context_subcall (`term`,(`asl`,(I)),[])));
                            ((Nat 0),(PO_constant `]`))])))])));
    ((`dotted`,(Const_name (`term`,[(Patt_child (Var_child `term`))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_constant `.`))])))
   ] : print_rule list;;


let printgoal_rules_fun =

   % : (print_rule_function) %

   print_rule_fun printgoal_rules;;


%-----------------------------------------------------------------------------%
