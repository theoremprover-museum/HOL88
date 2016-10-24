% ml_subset_pp.ml                                                             %
%-----------------------------------------------------------------------------%


let ml_subset_rules =

   % : (print_rule list) %

   letrec is_curried_infix =
    (\dummy0. ((\meta. apply1 is_ml_curried_infix (bound_name meta)) dummy0))
   and is_paired_infix =
    (\dummy0. ((\meta. apply1 is_ml_paired_infix (bound_name meta)) dummy0))
   in
   [
    ((`ml`,(Const_name (`MK-EMPTY`,[])),(\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `()`))])));
    ((`ml`,
      (Const_name (`MK-BOOLCONST`,[(Patt_child (Var_name (`n`,[])))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_leaf (`n`,(I))))])));
    ((`ml`,(Const_name (`MK-INTCONST`,[(Patt_child (Var_name (`n`,[])))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_leaf (`n`,(I))))])));
    ((`ml`,(Const_name (`MK-TOKCONST`,[(Patt_child (Var_name (`n`,[])))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_constant `\``));
                                   ((Nat 0),(PO_leaf (`n`,(I))));
                                   ((Nat 0),(PO_constant `\``))])));
    ((`ml`,(Const_name (`MK-VAR`,[(Patt_child (Var_name (`n`,[])))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_leaf (`n`,(I))))])));
    ((`ml`,(Const_name (`MK-CON`,[(Patt_child (Var_name (`n`,[])))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_leaf (`n`,(I))))])));
    ((`ml`,(Const_name (`MK-CON0`,[(Patt_child (Var_name (`n`,[])))])),
      (\x y. true)),[],(PF (H_box [((Nat 0),(PO_leaf (`n`,(I))))])));
    ((`ml`,
      (Const_name
        (`MK-UNOP`,
         [(Patt_child (Var_name (`n`,[])));(Patt_child (Var_child `c`))])),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 0),(Abs 0),(Nat 0)),(PO_leaf (`n`,(I))));
                           (((Nat 0),(Abs 0),(Nat 0)),
                            (PO_subcall ((`c`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml`,(Const_name (`MK-BINOP`,[(Patt_child (Var_name (`n`,[])));
                                    (Patt_child (Var_child `c1`));
                                    (Patt_child (Var_child `c2`))])),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Inc 1),(Nat 0)),
                            (PO_subcall ((`c1`,(I)),[])));
                           (((Nat 1),(Inc 1),(Nat 0)),(PO_leaf (`n`,(I))));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_subcall ((`c2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml`,(Print_loop
             ((Const_name
                (`MK-APPN`,
                 [(Patt_child (Print_link
                                ((((Val (Nat 1)),Default),[]),
                                 (Const_name
                                   (`MK-APPN`,
                                    [(Patt_child
                                       (Const_name
                                         (`MK-APPN`,
                                          [(Patt_child Wild_child);
                                           (Patt_child Wild_child)])));
                                     (Patt_child Wild_child)])))));
                  (Patt_child (Var_child `cs`))])),
              (Const_name
                (`MK-APPN`,
                 [(Patt_child
                    (Const_name
                      (`MK-APPN`,
                       [(Patt_child
                          (Const_name
                            (`MK-VAR`,[(Patt_child
                                         (Var_name (`name`,[])))])));
                        (Patt_child (Var_child `arg1`))])));
                  (Patt_child (Var_child `arg2`))])))),
      (is_curried_infix `name`)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Inc 1),(Nat 0)),
                            (PO_format
                              (PF (H_box
                                    [((Nat 0),(PO_constant `(`));
                                     ((Nat 0),
                                      (PO_format
                                        (PF
                                          (HV_box
                                            [(((Nat 1),(Abs 0),
                                               (Nat 0)),
                                              (PO_format
                                                (PF
                                                  (H_box
                                                    [((Nat
                                                        1),
                                                      (PO_context_subcall
                                                        (`ml-infix`,
                                                         (`arg1`,
                                                          (I)),
                                                         [])));
                                                     ((Nat
                                                        1),
                                                      (PO_leaf
                                                        (`name`,
                                                         (I))))]))));
                                             (((Nat 1),(Abs 0),
                                               (Nat 0)),
                                              (PO_subcall
                                                ((`arg2`,(I)),[])))]))));
                                     ((Nat 0),(PO_constant `)`))]))));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_subcall ((`cs`,(rev)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml`,
      (Const_name
        (`MK-APPN`,[(Patt_child
                      (Const_name
                        (`MK-APPN`,
                         [(Patt_child
                            (Const_name
                              (`MK-VAR`,
                               [(Patt_child (Var_name (`name`,[])))])));
                          (Patt_child (Var_child `arg1`))])));
                    (Patt_child (Var_child `arg2`))])),
      (is_curried_infix `name`)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_format
                              (PF (H_box
                                    [((Nat 1),
                                      (PO_context_subcall
                                        (`ml-infix`,(`arg1`,(I)),[])));
                                     ((Nat 1),(PO_leaf (`name`,(I))))]))));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`arg2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml-infix`,
      (Const_name
        (`MK-APPN`,[(Patt_child
                      (Const_name
                        (`MK-APPN`,
                         [(Patt_child
                            (Const_name
                              (`MK-VAR`,
                               [(Patt_child (Var_name (`name`,[])))])));
                          (Patt_child (Var_child `arg1`))])));
                    (Patt_child (Var_child `arg2`))])),
      (is_curried_infix `name`)),[],
     (PF (HV_box [(((Nat 1),(Abs 0),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 1),(PO_subcall ((`arg1`,(I)),[])));
                                 ((Nat 1),(PO_leaf (`name`,(I))))]))));
                  (((Nat 1),(Abs 0),(Nat 0)),
                   (PO_context_subcall (`ml`,(`arg2`,(I)),[])))])));
    ((`ml`,(Print_loop
             ((Const_name
                (`MK-APPN`,
                 [(Patt_child
                    (Print_link
                      ((((Val (Nat 1)),Default),[]),
                       (Const_name
                         (`MK-APPN`,[(Patt_child Wild_child);
                                     (Patt_child Wild_child)])))));
                  (Patt_child (Var_child `cs`))])),
              (Const_name
                (`MK-APPN`,
                 [(Patt_child
                    (Const_name
                      (`MK-VAR`,[(Patt_child (Var_name (`name`,[])))])));
                  (Patt_child
                    (Const_name
                      (`MK-DUPL`,[(Patt_child (Var_child `arg1`));
                                  (Patt_child (Var_child `arg2`))])))])))),
      (is_paired_infix `name`)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Inc 1),(Nat 0)),
                            (PO_format
                              (PF (H_box
                                    [((Nat 0),(PO_constant `(`));
                                     ((Nat 0),
                                      (PO_format
                                        (PF
                                          (HV_box
                                            [(((Nat 1),(Abs 0),
                                               (Nat 0)),
                                              (PO_format
                                                (PF
                                                  (H_box
                                                    [((Nat
                                                        1),
                                                      (PO_context_subcall
                                                        (`ml-infix`,
                                                         (`arg1`,
                                                          (I)),
                                                         [])));
                                                     ((Nat
                                                        1),
                                                      (PO_leaf
                                                        (`name`,
                                                         (I))))]))));
                                             (((Nat 1),(Abs 0),
                                               (Nat 0)),
                                              (PO_subcall
                                                ((`arg2`,(I)),[])))]))));
                                     ((Nat 0),(PO_constant `)`))]))));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_subcall ((`cs`,(rev)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml`,
      (Const_name
        (`MK-APPN`,
         [(Patt_child
            (Const_name
              (`MK-VAR`,[(Patt_child (Var_name (`name`,[])))])));
          (Patt_child
            (Const_name (`MK-DUPL`,[(Patt_child (Var_child `arg1`));
                                    (Patt_child (Var_child `arg2`))])))])),
      (is_paired_infix `name`)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_format
                              (PF (H_box
                                    [((Nat 1),
                                      (PO_context_subcall
                                        (`ml-infix`,(`arg1`,(I)),[])));
                                     ((Nat 1),(PO_leaf (`name`,(I))))]))));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`arg2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml-infix`,
      (Const_name
        (`MK-APPN`,
         [(Patt_child
            (Const_name
              (`MK-VAR`,[(Patt_child (Var_name (`name`,[])))])));
          (Patt_child
            (Const_name (`MK-DUPL`,[(Patt_child (Var_child `arg1`));
                                    (Patt_child (Var_child `arg2`))])))])),
      (is_paired_infix `name`)),[],
     (PF (HV_box [(((Nat 1),(Abs 0),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 1),(PO_subcall ((`arg1`,(I)),[])));
                                 ((Nat 1),(PO_leaf (`name`,(I))))]))));
                  (((Nat 1),(Abs 0),(Nat 0)),
                   (PO_context_subcall (`ml`,(`arg2`,(I)),[])))])));
    ((`ml-infix`,(Var_child `c`),(\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_context_subcall (`ml`,(`c`,(I)),[])))])));
    ((`ml`,(Print_loop
             ((Const_name
                (`MK-APPN`,
                 [(Patt_child (Link_child (((Val (Nat 1)),Default),[])));
                  (Patt_child (Var_child `cs`))])),(Var_child `cs`))),
      (\x y. true)),[],
     (PF (H_box
           [((Nat 0),(PO_constant `(`));
            ((Nat 0),
             (PO_format (PF (HV_box [(((Nat 1),(Inc 1),(Nat 0)),
                                      (PO_subcall ((`cs`,(rev)),[])))]))));
            ((Nat 0),(PO_constant `)`))])));
    ((`ml`,
      (Print_loop
        ((Const_name
           (`MK-ABSTR`,
            [(Patt_child (Var_child `vars`));
             (Patt_child (Link_child (((Val (Nat 1)),Default),[])))])),
         (Var_child `c`))),(\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),(PO_constant `\\`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box [(((Nat 1),(Abs 1),(Nat 0)),
                                  (PO_format
                                    (PF (H_box
                                          [((Nat 1),
                                            (PO_subcall ((`vars`,(I)),[])));
                                           ((Nat 0),(PO_constant `.`))]))));
                                 (((Nat 1),(Abs 1),(Nat 0)),
                                  (PO_subcall ((`c`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml`,
      (Const_name
        (`MK-LIST`,[(Var_children `cl`);(Patt_child (Var_child `c`))])),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `[`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 0),(Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),(PO_subcall ((`cl`,(I)),[])));
                                 ((Nat 0),(PO_constant `;`))])));
                           (((Nat 0),(Abs 0),(Nat 0)),
                            (PO_subcall ((`c`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `]`))])));
    ((`ml`,(Const_name (`MK-LIST`,[])),(\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `[]`))])));
    ((`ml`,
      (Print_loop
        ((Const_name
           (`MK-DUPL`,
            [(Patt_child (Var_child `cl`));
             (Patt_child (Link_child (((Val (Nat 1)),Default),[])))])),
         (Var_child `c`))),(\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF
                      (HV_box [(((Nat 0),(Abs 0),(Nat 0)),
                                (PO_expand
                                  (H_box
                                    [((Nat 0),(PO_subcall ((`cl`,(I)),[])));
                                     ((Nat 0),(PO_constant `,`))])));
                               (((Nat 0),(Abs 0),(Nat 0)),
                                (PO_subcall ((`c`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((`ml`,(Const_name
             (`MK-TEST`,
              [(Patt_child (Const_name (`LIST`,[(Var_children `onces`)])));
               (Patt_child
                 (Const_name (`once`,[(Patt_child (Var_child `c`))])))])),
      (\x y. true)),[],
     (PF (H_box
           [((Nat 0),(PO_constant `(`));
            ((Nat 0),
             (PO_format
               (PF
                 (HoV_box
                   [(((Nat 1),(Abs 0),(Nat 0)),
                     (PO_subcall ((`onces`,(I)),[])));
                    (((Nat 1),(Abs 0),(Nat 0)),
                     (PO_format
                       (PF (HV_box [(((Nat 1),(Abs 1),(Nat 0)),
                                     (PO_constant `else`));
                                    (((Nat 1),(Abs 1),(Nat 0)),
                                     (PO_subcall ((`c`,(I)),[])))]))))]))));
            ((Nat 0),(PO_constant `)`))])));
    ((`ml`,
      (Const_name
        (`MK-TEST`,
         [(Patt_child (Const_name (`LIST`,[(Var_children `onces`)])))])),
      (\x y. true)),[],
     (PF (H_box
           [((Nat 0),(PO_constant `(`));
            ((Nat 0),(PO_format
                       (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                                      (PO_subcall ((`onces`,(I)),[])))]))));
            ((Nat 0),(PO_constant `)`))])));
    ((`ml`,
      (Const_name
        (`once`,
         [(Patt_child (Var_child `c1`));(Patt_child (Var_child `c2`))])),
      (\x y. true)),[],
     (PF
       (HV_box [(((Nat 1),(Abs 0),(Nat 0)),
                 (PO_format
                   (PF (HV_box
                         [(((Nat 1),(Abs 1),(Nat 0)),(PO_constant `if`));
                          (((Nat 1),(Abs 1),(Nat 0)),
                           (PO_subcall ((`c1`,(I)),[])))]))));
                (((Nat 1),(Abs 0),(Nat 0)),
                 (PO_format
                   (PF (HV_box
                         [(((Nat 1),(Abs 1),(Nat 0)),(PO_constant `then`));
                          (((Nat 1),(Abs 1),(Nat 0)),
                           (PO_subcall ((`c2`,(I)),[])))]))))])));
    ((`ml`,(Const_name
             (`MK-LETREC`,
              [(Patt_child
                 (Const_name
                   (`MK-DUPL`,[(Patt_child (Var_child `var1`));
                               (Patt_child
                                 (Print_loop
                                   ((Const_name
                                      (`MK-DUPL`,
                                       [(Patt_child (Var_child `varl`));
                                        (Patt_child
                                          (Link_child
                                            ((Default,Default),[])))])),
                                    (Var_child `varl`))))])));
               (Patt_child
                 (Const_name
                   (`MK-DUPL`,[(Patt_child (Var_child `body1`));
                               (Patt_child
                                 (Print_loop
                                   ((Const_name
                                      (`MK-DUPL`,
                                       [(Patt_child (Var_child `bodyl`));
                                        (Patt_child
                                          (Link_child
                                            ((Default,Default),[])))])),
                                    (Var_child `bodyl`))))])))])),
      (\x y. true)),[],
     (PF
       (V_box [(((Abs 0),(Nat 0)),
                (PO_format
                  (PF (HV_box [(((Nat 1),(Inc 1),(Nat 0)),
                                (PO_constant `letrec`));
                               (((Nat 1),(Inc 1),(Nat 0)),
                                (PO_format
                                  (PF (H_box
                                        [((Nat 1),
                                          (PO_subcall ((`var1`,(I)),[])));
                                         ((Nat 1),(PO_constant `=`))]))));
                               (((Nat 1),(Inc 1),(Nat 0)),
                                (PO_subcall ((`body1`,(I)),[])))]))));
               (((Abs 0),(Nat 0)),
                (PO_expand
                  (HV_box [(((Nat 1),(Inc 1),(Nat 0)),(PO_constant `and`));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 1),(PO_subcall ((`varl`,(I)),[])));
                                 ((Nat 1),(PO_constant `=`))])));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_subcall ((`bodyl`,(I)),[])))])))])));
    ((`ml`,
      (Const_name
        (`MK-LETREC`,
         [(Patt_child (Var_child `c1`));(Patt_child (Var_child `c2`))])),
      (\x y. true)),[],
     (PF (HV_box [(((Nat 1),(Inc 1),(Nat 0)),(PO_constant `letrec`));
                  (((Nat 1),(Inc 1),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 1),(PO_subcall ((`c1`,(I)),[])));
                                 ((Nat 1),(PO_constant `=`))]))));
                  (((Nat 1),(Inc 1),(Nat 0)),(PO_subcall ((`c2`,(I)),[])))])));
    ((`ml`,(Const_name
             (`MK-LET`,
              [(Patt_child
                 (Const_name
                   (`MK-DUPL`,[(Patt_child (Var_child `var1`));
                               (Patt_child
                                 (Print_loop
                                   ((Const_name
                                      (`MK-DUPL`,
                                       [(Patt_child (Var_child `varl`));
                                        (Patt_child
                                          (Link_child
                                            ((Default,Default),[])))])),
                                    (Var_child `varl`))))])));
               (Patt_child
                 (Const_name
                   (`MK-DUPL`,[(Patt_child (Var_child `body1`));
                               (Patt_child
                                 (Print_loop
                                   ((Const_name
                                      (`MK-DUPL`,
                                       [(Patt_child (Var_child `bodyl`));
                                        (Patt_child
                                          (Link_child
                                            ((Default,Default),[])))])),
                                    (Var_child `bodyl`))))])))])),
      (\x y. true)),[],
     (PF
       (V_box [(((Abs 0),(Nat 0)),
                (PO_format
                  (PF (HV_box
                        [(((Nat 1),(Inc 1),(Nat 0)),(PO_constant `let`));
                         (((Nat 1),(Inc 1),(Nat 0)),
                          (PO_format
                            (PF (H_box
                                  [((Nat 1),
                                    (PO_subcall ((`var1`,(I)),[])));
                                   ((Nat 1),(PO_constant `=`))]))));
                         (((Nat 1),(Inc 1),(Nat 0)),
                          (PO_subcall ((`body1`,(I)),[])))]))));
               (((Abs 0),(Nat 0)),
                (PO_expand
                  (HV_box [(((Nat 1),(Inc 1),(Nat 0)),(PO_constant `and`));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 1),(PO_subcall ((`varl`,(I)),[])));
                                 ((Nat 1),(PO_constant `=`))])));
                           (((Nat 1),(Inc 1),(Nat 0)),
                            (PO_subcall ((`bodyl`,(I)),[])))])))])));
    ((`ml`,
      (Const_name
        (`MK-LET`,
         [(Patt_child (Var_child `c1`));(Patt_child (Var_child `c2`))])),
      (\x y. true)),[],
     (PF (HV_box [(((Nat 1),(Inc 1),(Nat 0)),(PO_constant `let`));
                  (((Nat 1),(Inc 1),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 1),(PO_subcall ((`c1`,(I)),[])));
                                 ((Nat 1),(PO_constant `=`))]))));
                  (((Nat 1),(Inc 1),(Nat 0)),(PO_subcall ((`c2`,(I)),[])))])));
    ((`ml`,
      (Const_name
        (`MK-IN`,
         [(Patt_child (Var_child `c1`));(Patt_child (Var_child `c2`))])),
      (\x y. true)),[],
     (PF (H_box
           [((Nat 0),(PO_constant `(`));
            ((Nat 0),
             (PO_format
               (PF
                 (V_box
                   [(((Abs 0),(Nat 0)),(PO_subcall ((`c1`,(I)),[])));
                    (((Abs 0),(Nat 0)),
                     (PO_format
                       (PF
                         (HV_box [(((Nat 1),(Abs 1),(Nat 0)),
                                   (PO_constant `in`));
                                  (((Nat 1),(Abs 1),(Nat 0)),
                                   (PO_subcall ((`c2`,(I)),[])))]))))]))));
            ((Nat 0),(PO_constant `)`))])));
    ((`ml`,(Print_label
             (`term`,(Const_name (`term`,[(Patt_child Wild_child)])))),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_context_subcall (`term`,(`term`,(I)),[])))])));
    ((`ml`,(Print_label
             (`type`,(Const_name (`type`,[(Patt_child Wild_child)])))),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_context_subcall (`type`,(`type`,(I)),[])))])));
    ((`term`,(Const_name (`MK=TYPED`,[(Patt_child (Var_child `term`));
                                      (Patt_child (Var_child `type`))])),
      (\x y. true)),[],
     (PF (HV_box
           [(((Nat 0),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `(`));
                           ((Nat 0),(PO_subcall ((`term`,(I)),[])))]))));
            (((Nat 0),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `:`));
                           ((Nat 0),(PO_subcall ((`type`,(I)),[])))]))));
            (((Nat 0),(Abs 0),(Nat 0)),(PO_constant `)`))])));
    ((`term`,(Const_name (`MK=ANTIQUOT`,[(Patt_child (Var_child `ml`))])),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),(PO_constant `^`));
                 ((Nat 0),(PO_context_subcall (`ml`,(`ml`,(I)),[])));
                 ((Nat 0),(PO_constant `)`))])));
    ((`type`,
      (Const_name (`MK=TYPE=ANTIQUOT`,[(Patt_child (Var_child `ml`))])),
      (\x y. true)),[],
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),(PO_constant `^`));
                 ((Nat 0),(PO_context_subcall (`ml`,(`ml`,(I)),[])));
                 ((Nat 0),(PO_constant `)`))])))
   ] : print_rule list;;


let ml_subset_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ml_subset_rules;;


%-----------------------------------------------------------------------------%
