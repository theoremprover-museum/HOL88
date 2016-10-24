% print_the_tree_pp.ml                                                        %
%-----------------------------------------------------------------------------%


let printproof_rules =

   % : (print_rule list) %

   [
    ((`proof`,(Const_name (`unexp`,[(Patt_child (Var_child `flag`));
                                    (Patt_child (Var_child `what`))])),
      (\x y. true)),[],
     (PF (HoV_box [(((Nat 1),(Abs 1),(Nat 0)),
                    (PO_context_subcall (`fullgoal`,(`what`,(I)),[])))])));
    ((`proof`,(Const_name (`unexp`,[(Patt_child (Var_child `what`))])),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_context_subcall (`goal`,(`what`,(I)),[])))])));
    ((`proof`,(Const_name (`exp`,[(Patt_child (Var_child `gl`));
                                  (Patt_child (Var_child `tac`));
                                  (Var_children `kids`)])),(\x y. true)),[],
     (PF (V_box
           [(((Abs 3),(Nat 0)),(PO_context_subcall (`goal`,(`gl`,(I)),[])));
            (((Abs 3),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))));
            (((Abs 3),(Nat 0)),(PO_subcall ((`kids`,(I)),[])))])));
    ((`proof`,(Const_name (`proved`,[(Patt_child (Var_child `thrm`));
                                     (Patt_child (Var_child `tac`))])),
      (\x y. true)),[],
     (PF
       (V_box
         [(((Abs 3),(Nat 0)),
           (PO_format
             (PF (H_box
                   [((Nat 1),
                     (PO_context_subcall (`thm`,(`thrm`,(I)),[])))]))));
          (((Abs 3),(Nat 0)),
           (PO_format
             (PF (H_box [((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))))])));
    ((`proof`,(Const_name (`proved`,[(Patt_child (Var_child `thrm`));
                                     (Patt_child (Var_child `tac`));
                                     (Var_children `kids`)])),(\x y. true)),
     [],
     (PF (V_box
           [(((Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),
                       (PO_context_subcall (`thm`,(`thrm`,(I)),[])))]))));
            (((Abs 3),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))));
            (((Abs 3),(Nat 0)),(PO_subcall ((`kids`,(I)),[])))])));
    ((`finaltac`,(Const_name (`unexp`,[(Patt_child (Var_child `what`))])),
      (\x y. true)),[],
     (PF (H_box
           [((Nat 1),(PO_constant `THEN`));((Nat 1),(PO_constant `----`))])));
    ((`firstfinaltac`,
      (Const_name (`unexp`,[(Patt_child (Var_child `what`))])),(\x y. true)),
     [],(PF (H_box [((Nat 0),(PO_constant `----`))])));
    ((`firstfinaltac`,
      (Const_name (`exp`,[(Patt_child (Var_child `gl`));
                          (Patt_child (Var_child `tac`));
                          (Patt_child (Var_child `kid`))])),(\x y. true)),[],
     (PF
       (V_box
         [(((Abs 1),(Nat 0)),(PO_context_subcall (`ml`,(`tac`,(I)),[])));
          (((Abs 0),(Nat 0)),
           (PO_format
             (PF
               (H_box
                 [((Nat 1),
                   (PO_context_subcall (`finaltac`,(`kid`,(I)),[])))]))))])));
    ((`finaltac`,(Const_name (`exp`,[(Patt_child (Var_child `gl`));
                                     (Patt_child (Var_child `tac`));
                                     (Patt_child (Var_child `kid`))])),
      (\x y. true)),[],
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),(PO_constant `THEN`));
                         ((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall ((`kid`,(I)),[])))])));
    ((`finaltac`,(Const_name (`exp`,[(Patt_child (Var_child `gl`));
                                     (Patt_child (Var_child `tac`));
                                     (Var_children `kids`);
                                     (Patt_child (Var_child `kid`))])),
      (\x y. true)),[],
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),(PO_constant `THEN`));
                         ((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_constant `THENL`));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `[`));
                      ((Nat 1),
                       (PO_format
                         (PF
                           (V_box
                             [(((Abs 0),(Nat 0)),
                               (PO_expand
                                 (H_box
                                   [((Nat 0),
                                     (PO_context_subcall
                                       (`firstfinaltac`,
                                        (`kids`,(I)),[])));
                                    ((Nat 0),
                                     (PO_constant `;`))])));
                              (((Abs 0),(Nat 0)),
                               (PO_context_subcall
                                 (`firstfinaltac`,(`kid`,(I)),[])))]))));
                      ((Nat 1),(PO_constant `]`))]))))])));
    ((`firstfinaltac`,
      (Const_name (`exp`,[(Patt_child (Var_child `gl`));
                          (Patt_child (Var_child `tac`));
                          (Var_children `kids`);
                          (Patt_child (Var_child `kid`))])),(\x y. true)),[],
     (PF (V_box
           [(((Abs 0),(Nat 0)),(PO_context_subcall (`ml`,(`tac`,(I)),[])));
            (((Abs 0),(Nat 0)),(PO_constant `THENL`));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `[`));
                      ((Nat 1),
                       (PO_format
                         (PF
                           (V_box
                             [(((Abs 0),(Nat 0)),
                               (PO_expand
                                 (H_box
                                   [((Nat 0),
                                     (PO_context_subcall
                                       (`firstfinaltac`,
                                        (`kids`,(I)),[])));
                                    ((Nat 0),
                                     (PO_constant `;`))])));
                              (((Abs 0),(Nat 0)),
                               (PO_context_subcall
                                 (`firstfinaltac`,(`kid`,(I)),[])))]))));
                      ((Nat 1),(PO_constant `]`))]))))])));
    ((`finaltac`,
      (Const_name
        (`proved`,
         [(Patt_child (Var_child `gl`));(Patt_child (Var_child `tac`))])),
      (\x y. true)),[],
     (PF (HoV_box [(((Nat 2),(Abs 1),(Nat 0)),(PO_constant `THEN`));
                   (((Nat 2),(Abs 1),(Nat 0)),
                    (PO_context_subcall (`ml`,(`tac`,(I)),[])))])));
    ((`finaltac`,
      (Const_name (`proved`,[(Patt_child (Var_child `gl`));
                             (Patt_child (Var_child `tac`));
                             (Patt_child (Var_child `onechild`))])),
      (\x y. true)),[],
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),(PO_constant `THEN`));
                         ((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall ((`onechild`,(I)),[])))])));
    ((`finaltac`,(Const_name (`proved`,[(Patt_child (Var_child `gl`));
                                        (Patt_child (Var_child `tac`));
                                        (Var_children `kids`);
                                        (Patt_child (Var_child `kid`))])),
      (\x y. true)),[],
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),(PO_constant `THEN`));
                         ((Nat 1),
                          (PO_context_subcall (`ml`,(`tac`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_constant `THENL`));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `[`));
                      ((Nat 1),
                       (PO_format
                         (PF
                           (V_box
                             [(((Abs 0),(Nat 0)),
                               (PO_expand
                                 (H_box
                                   [((Nat 0),
                                     (PO_context_subcall
                                       (`firstfinaltac`,
                                        (`kids`,(I)),[])));
                                    ((Nat 0),
                                     (PO_constant `;`))])));
                              (((Abs 0),(Nat 0)),
                               (PO_context_subcall
                                 (`firstfinaltac`,(`kid`,(I)),[])))]))));
                      ((Nat 1),(PO_constant `]`))]))))])));
    ((`firstfinaltac`,
      (Const_name
        (`proved`,
         [(Patt_child (Var_child `gl`));(Patt_child (Var_child `tac`))])),
      (\x y. true)),[],
     (PF (HoV_box [(((Nat 2),(Abs 1),(Nat 0)),
                    (PO_context_subcall (`ml`,(`tac`,(I)),[])))])));
    ((`firstfinaltac`,
      (Const_name (`proved`,[(Patt_child (Var_child `gl`));
                             (Patt_child (Var_child `tac`));
                             (Patt_child (Var_child `onechild`))])),
      (\x y. true)),[],
     (PF
       (V_box
         [(((Abs 0),(Nat 0)),(PO_context_subcall (`ml`,(`tac`,(I)),[])));
          (((Abs 0),(Nat 0)),
           (PO_format
             (PF
               (H_box [((Nat 1),(PO_context_subcall
                                  (`finaltac`,(`onechild`,(I)),[])))]))))])));
    ((`firstfinaltac`,
      (Const_name (`proved`,[(Patt_child (Var_child `gl`));
                             (Patt_child (Var_child `tac`));
                             (Var_children `kids`);
                             (Patt_child (Var_child `kid`))])),(\x y. true)),
     [],
     (PF (V_box
           [(((Abs 0),(Nat 0)),(PO_context_subcall (`ml`,(`tac`,(I)),[])));
            (((Abs 0),(Nat 0)),(PO_constant `THENL`));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `[`));
                      ((Nat 1),
                       (PO_format
                         (PF
                           (V_box [(((Abs 0),(Nat 0)),
                                    (PO_expand
                                      (H_box
                                        [((Nat 0),
                                          (PO_subcall
                                            ((`kids`,(I)),[])));
                                         ((Nat 0),
                                          (PO_constant `;`))])));
                                   (((Abs 0),(Nat 0)),
                                    (PO_subcall ((`kid`,(I)),[])))]))));
                      ((Nat 1),(PO_constant `]`))]))))])))
   ] : print_rule list;;


let printproof_rules_fun =

   % : (print_rule_function) %

   print_rule_fun printproof_rules;;


%-----------------------------------------------------------------------------%
