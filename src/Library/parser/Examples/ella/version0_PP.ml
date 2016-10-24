
let ella_rules =

   % : (print_rule list) %

   [
    ((`ella`,(Print_metavar
               ((Const_name `name`),
                [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(\s.s))))])));
    ((`ella`,(Print_metavar
               ((Const_name `fnname`),
                [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(\s.s))))])));
    ((`ella`,(Print_metavar
               ((Const_name `type`),
                [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(\s.s))))])));
    ((`ella`,
      (Print_metavar ((Const_name `text`),[(Var_children `decls`)])),
      (\x y. true)),
     (PF (V_box [(((Abs 0),(Nat 1)),
                  (PO_expand (H_box [((Nat 0),(PO_subcall (`decls`,[])));
                                     ((Nat 0),(PO_constant `.`))])))])));
    ((`ella`,(Print_metavar
               ((Const_name `typedec`),[(Var_child `name`);
                                        (Var_child `firstname`);
                                        (Var_children `othernames`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `TYPE`));
          (((Nat 1),(Abs 3),(Nat 0)),
           (PO_format
             (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                           (PO_format
                             (PF (H_box
                                   [((Nat 1),(PO_subcall (`name`,[])));
                                    ((Nat 1),(PO_constant `=`))]))));
                          (((Nat 1),(Abs 3),(Nat 0)),
                           (PO_format
                             (PF (H_box
                                   [((Nat 0),(PO_constant `NEW(`));
                                    ((Nat 0),
                                     (PO_format
                                       (PF (HoV_box
                                             [(((Nat 1),
                                                (Abs (-2)),(Nat 0)),
                                               (PO_subcall
                                                 (`firstname`,[])));
                                              (((Nat 1),(Abs (-2)),
                                                (Nat 0)),
                                               (PO_expand
                                                 (H_box
                                                   [((Nat 1),
                                                     (PO_constant
                                                       `|`));
                                                    ((Nat 1),
                                                     (PO_subcall
                                                       (`othernames`,
                                                        [])))])))]))));
                                    ((Nat 0),(PO_constant `)`))]))))]))))])));
    ((`ella`,
      (Print_metavar ((Const_name `inputitem`),[(Var_child `type`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall (`type`,[])))])));
    ((`ella`,(Print_metavar ((Const_name `inputitem`),
                             [(Var_child `type`);(Var_children `names`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format (PF (H_box [((Nat 0),(PO_subcall (`type`,[])));
                                        ((Nat 0),(PO_constant `:`))]))));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                                           (PO_subcall (`names`,[])))]))))])));
    ((`ella`,(Print_metavar ((Const_name `inputitem_list`),
                             [(Var_children `items`);(Var_child `item`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                                   (PO_expand
                                     (H_box
                                       [((Nat 0),(PO_subcall (`items`,[])));
                                        ((Nat 0),(PO_constant `,`))])));
                                  (((Nat 1),(Abs 0),(Nat 0)),
                                   (PO_subcall (`item`,[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ella`,(Print_metavar ((Const_name `fndec`),[(Var_child `fnname`);
                                                   (Var_child `items`);
                                                   (Var_child `type`);
                                                   (Var_child `fnbody`)])),
      (\x y. true)),
     (PF (V_box [(((Abs 1),(Nat 0)),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Abs 3),(Nat 0)),
                            (PO_format
                              (PF (H_box [((Nat 1),(PO_constant `FN`));
                                          ((Nat 1),
                                           (PO_subcall (`fnname`,[])));
                                          ((Nat 1),(PO_constant `=`))]))));
                           (((Nat 1),(Abs 3),(Nat 0)),
                            (PO_format
                              (PF (H_box
                                    [((Nat 0),
                                      (PO_format
                                        (PF
                                          (HV_box
                                            [(((Nat 1),(Abs 3),
                                               (Nat 0)),
                                              (PO_subcall
                                                (`items`,[])));
                                             (((Nat 1),(Abs 3),
                                               (Nat 0)),
                                              (PO_format
                                                (PF
                                                  (H_box
                                                    [((Nat
                                                        1),
                                                      (PO_constant
                                                        `->`));
                                                     ((Nat 1),
                                                      (PO_subcall
                                                        (`type`,
                                                         [])))]))))]))));
                                     ((Nat 0),(PO_constant `:`))]))))]))));
                 (((Abs 1),(Nat 0)),(PO_subcall (`fnbody`,[])))])));
    ((`ella`,
      (Print_metavar ((Const_name `fnbody`),[(Var_child `fnbody`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall (`fnbody`,[])))])));
    ((`ella`,
      (Print_metavar
        ((Const_name `delay`),[(Var_child `name`);(Var_child `int`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 0),(Abs 3),(Nat 0)),(PO_constant `DELAY`));
            (((Nat 0),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `(`));
                           ((Nat 0),
                            (PO_format
                              (PF (HV_box
                                    [(((Nat 1),(Abs 3),(Nat 0)),
                                      (PO_format
                                        (PF (H_box
                                              [((Nat 0),
                                                (PO_subcall
                                                  (`name`,[])));
                                               ((Nat 0),
                                                (PO_constant `,`))]))));
                                     (((Nat 1),(Abs 3),(Nat 0)),
                                      (PO_subcall (`int`,[])))]))));
                           ((Nat 0),(PO_constant `)`))]))))])));
    ((`ella`,(Print_metavar ((Const_name `unit`),[(Var_child `unit`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall (`unit`,[])))])));
    ((`ella`,(Print_metavar ((Const_name `tuple`),
                             [(Var_children `units`);(Var_child `unit`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                                   (PO_expand
                                     (H_box
                                       [((Nat 0),(PO_subcall (`units`,[])));
                                        ((Nat 0),(PO_constant `,`))])));
                                  (((Nat 1),(Abs 0),(Nat 0)),
                                   (PO_subcall (`unit`,[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ella`,
      (Print_metavar ((Const_name `choosers`),[(Var_child `name`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall (`name`,[])))])));
    ((`ella`,(Print_metavar ((Const_name `choosers`),
                             [(Var_children `names`);(Var_child `name`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                                   (PO_expand
                                     (H_box
                                       [((Nat 0),(PO_subcall (`names`,[])));
                                        ((Nat 0),(PO_constant `,`))])));
                                  (((Nat 1),(Abs 0),(Nat 0)),
                                   (PO_subcall (`name`,[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ella`,(Print_metavar ((Const_name `choices`),
                             [(Var_child `choosers`);(Var_child `unit`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 0),(PO_subcall (`choosers`,[])));
                                 ((Nat 0),(PO_constant `:`))]))));
                  (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall (`unit`,[])))])));
    ((`ella`,
      (Print_metavar ((Const_name `choices_list`),
                      [(Var_children `choices`);(Var_child `choice`)])),
      (\x y. true)),
     (PF
       (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                  (PO_expand (H_box [((Nat 0),(PO_subcall (`choices`,[])));
                                     ((Nat 0),(PO_constant `,`))])));
                 (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall (`choice`,[])))])));
    ((`ella`,(Print_metavar ((Const_name `else_clause`),[])),(\x y. true)),
     PF_empty);
    ((`ella`,
      (Print_metavar ((Const_name `else_clause`),[(Var_child `unit`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `ELSE`));
                  (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall (`unit`,[])))])));
    ((`ella`,(Print_metavar
               ((Const_name `caseclause`),[(Var_child `unit`);
                                           (Var_child `choices_list`);
                                           (Var_child `else_clause`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF (HV_box
                     [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `CASE`));
                      (((Nat 1),(Abs 3),(Nat 0)),
                       (PO_subcall (`unit`,[])))]))));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `OF`));
                           ((Nat 1),(PO_subcall (`choices_list`,[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall (`else_clause`,[])));
            (((Abs 0),(Nat 0)),(PO_constant `ESAC`))])));
    ((`ella`,(Print_metavar
               ((Const_name `series`),
                [(Patt_child
                   (Print_metavar
                     ((Const_name `step_list`),[(Var_children `steps`)])));
                 (Var_child `unit`)])),(\x y. true)),
     (PF (V_box [(((Abs 0),(Nat 0)),(PO_constant `BEGIN`));
                 (((Abs 3),(Nat 0)),
                  (PO_expand (H_box [((Nat 0),(PO_subcall (`steps`,[])));
                                     ((Nat 0),(PO_constant `.`))])));
                 (((Abs 3),(Nat 0)),
                  (PO_format (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                                           (PO_constant `OUTPUT`));
                                          (((Nat 1),(Abs 3),(Nat 0)),
                                           (PO_subcall (`unit`,[])))]))));
                 (((Abs 0),(Nat 0)),(PO_constant `END`))])));
    ((`ella`,
      (Print_metavar
        ((Const_name `makeitem`),
         [(Var_child `fnname`);
          (Patt_child
            (Print_metavar
              ((Const_name `name_list`),[(Var_children `names`)])))])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format (PF (H_box [((Nat 0),(PO_subcall (`fnname`,[])));
                                    ((Nat 0),(PO_constant `:`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                                       (PO_subcall (`names`,[])))]))))])));
    ((`ella`,(Print_metavar
               ((Const_name `make`),
                [(Var_children `makeitems`);(Var_child `makeitem`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `MAKE`));
          (((Nat 1),(Abs 3),(Nat 0)),
           (PO_format
             (PF (V_box
                   [(((Abs 0),(Nat 0)),
                     (PO_expand
                       (H_box
                         [((Nat 0),(PO_subcall (`makeitems`,[])));
                          ((Nat 0),(PO_constant `,`))])));
                    (((Abs 0),(Nat 0)),(PO_subcall (`makeitem`,[])))]))))])));
    ((`ella`,
      (Print_metavar
        ((Const_name `joinitem`),[(Var_child `unit`);(Var_child `name`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall (`unit`,[])));
          (((Nat 1),(Abs 3),(Nat 0)),
           (PO_format (PF (H_box [((Nat 1),(PO_constant `->`));
                                  ((Nat 1),(PO_subcall (`name`,[])))]))))])));
    ((`ella`,(Print_metavar
               ((Const_name `join`),
                [(Var_children `joinitems`);(Var_child `joinitem`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `JOIN`));
          (((Nat 1),(Abs 3),(Nat 0)),
           (PO_format
             (PF (V_box
                   [(((Abs 0),(Nat 0)),
                     (PO_expand
                       (H_box
                         [((Nat 0),(PO_subcall (`joinitems`,[])));
                          ((Nat 0),(PO_constant `,`))])));
                    (((Abs 0),(Nat 0)),(PO_subcall (`joinitem`,[])))]))))])))
   ] : print_rule list;;


let ella_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_rules;;

