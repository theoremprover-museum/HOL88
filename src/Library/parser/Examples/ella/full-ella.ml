
let ella_basics_rules =

   % : (print_rule list) %

   letrec quote_quote = (\dummy0. ((\s. letrec dupl s sl =
                                           if (null sl)
                                           then []
                                           else if ((hd sl) = s)
                                                then s.s.(dupl s (tl sl))
                                                else (hd sl).(dupl s (tl sl))
                                        in (implode o (dupl s) o explode)
                                    ) dummy0))
   and is_symbolic_prefix_op =
    (\dummy0. ((\op. apply1 (\s. (s = `+`) or (s = `-`))
                                            (bound_name op)
                ) dummy0))
   in
   [
    ((``,(Print_metavar
           ((Const_name `name`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(I))))])));
    ((``,(Print_metavar ((Const_name `names`),
                         [(Var_child `name1`);(Var_children `name2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`name1`,(I)),[])));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`name2`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `char`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),
     (PF (H_box
           [((Nat 0),(PO_constant `'`));((Nat 0),(PO_leaf (`string`,(I))))])));
    ((``,(Print_metavar ((Const_name `fnname`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `uppercasename`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(I))))])));
    ((``,(Print_metavar
           ((Const_name `symbolicname`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(I))))])));
    ((``,(Print_metavar ((Const_name `macname`),[(Var_child `fnname`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`fnname`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `biopname`),[(Var_child `fnname`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`fnname`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `integervalue`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_leaf (`string`,(I))))])));
    ((``,(Print_metavar
           ((Const_name `string`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `"`));
                 ((Nat 0),(PO_leaf (`string`,(quote_quote `"`))));
                 ((Nat 0),(PO_constant `"`))])));
    ((``,(Print_metavar
           ((Const_name `operator`),
            [(Patt_child (Print_metavar ((Var_name `string`),[])))])),
      (\x y. true)),
     (PF_branch ((is_symbolic_prefix_op `string`),
                 (PF (H_box [((Nat 0),(PO_leaf (`string`,(I))))])),
                 (PF (H_box [((Nat 0),(PO_leaf (`string`,(I))));
                             ((Nat 0),(PO_constant ` `))])))))
   ] : print_rule list;;


let ella_basics_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_basics_rules;;


let ella_text_rules =

   % : (print_rule list) %

   [
    ((``,(Print_metavar
           ((Const_name `text`),
            [(Var_child `declaration1`);(Var_children `declaration2`)])),
      (\x y. true)),
     (PF
       (V_box [(((Abs 0),(Nat 1)),
                (PO_format
                  (PF (H_box
                        [((Nat 0),(PO_subcall ((`declaration1`,(I)),[])));
                         ((Nat 0),(PO_constant `.`))]))));
               (((Abs 0),(Nat 1)),
                (PO_expand
                  (H_box [((Nat 0),(PO_subcall ((`declaration2`,(I)),[])));
                          ((Nat 0),(PO_constant `.`))])))])))
   ] : print_rule list;;


let ella_text_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_text_rules;;


let ella_declarations_rules =

   % : (print_rule list) %

   [
    ((``,
      (Print_metavar ((Const_name `declaration`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `typedecs`),
                      [(Var_children `typedec1`);(Var_child `typedec2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `TYPE`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                              (PO_expand
                                (H_box
                                  [((Nat 0),
                                    (PO_subcall ((`typedec1`,(I)),[])));
                                   ((Nat 0),(PO_constant `,`))])));
                             (((Nat 1),(Abs 0),(Nat 0)),
                              (PO_subcall ((`typedec2`,(I)),[])))]))))])));
    ((``,
      (Print_metavar ((Const_name `intdecs`),
                      [(Var_children `intdec1`);(Var_child `intdec2`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `INT`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (HoV_box
                           [(((Nat 1),(Abs 0),(Nat 0)),
                             (PO_expand
                               (H_box [((Nat 0),
                                        (PO_subcall ((`intdec1`,(I)),[])));
                                       ((Nat 0),(PO_constant `,`))])));
                            (((Nat 1),(Abs 0),(Nat 0)),
                             (PO_subcall ((`intdec2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `constdecs`),
            [(Var_children `constdec1`);(Var_child `constdec2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `CONST`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                              (PO_expand
                                (H_box
                                  [((Nat 0),
                                    (PO_subcall ((`constdec1`,(I)),[])));
                                   ((Nat 0),(PO_constant `,`))])));
                             (((Nat 1),(Abs 0),(Nat 0)),
                              (PO_subcall ((`constdec2`,(I)),[])))]))))])));
    ((``,(Print_metavar ((Const_name `fndecs`),
                         [(Var_children `fndec1`);(Var_child `fndec2`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `FN`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (HoV_box
                           [(((Nat 1),(Abs 0),(Nat 0)),
                             (PO_expand
                               (H_box [((Nat 0),
                                        (PO_subcall ((`fndec1`,(I)),[])));
                                       ((Nat 0),(PO_constant `,`))])));
                            (((Nat 1),(Abs 0),(Nat 0)),
                             (PO_subcall ((`fndec2`,(I)),[])))]))))])));
    ((``,
      (Print_metavar ((Const_name `macdecs`),
                      [(Var_children `macdec1`);(Var_child `macdec2`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `MAC`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (HoV_box
                           [(((Nat 1),(Abs 0),(Nat 0)),
                             (PO_expand
                               (H_box [((Nat 0),
                                        (PO_subcall ((`macdec1`,(I)),[])));
                                       ((Nat 0),(PO_constant `,`))])));
                            (((Nat 1),(Abs 0),(Nat 0)),
                             (PO_subcall ((`macdec2`,(I)),[])))]))))])))
   ] : print_rule list;;


let ella_declarations_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_declarations_rules;;


let ella_types_rules =

   % : (print_rule list) %

   [
    ((``,
      (Print_metavar
        ((Const_name `typedec`),[(Var_child `name`);(Var_child `child`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                           ((Nat 1),(PO_constant `=`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `enum_types`),
            [(Var_children `enum_type1`);(Var_child `enum_type2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `NEW(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 1),(Abs (-2)),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 1),
                                  (PO_subcall ((`enum_type1`,(I)),[])));
                                 ((Nat 1),(PO_constant `|`))])));
                           (((Nat 1),(Abs (-2)),(Nat 0)),
                            (PO_subcall ((`enum_type2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar ((Const_name `enum_type`),[(Var_child `name`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`name`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `enum_type`),
                         [(Var_child `name`);(Var_child `type`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `&`));
                                ((Nat 0),(PO_subcall ((`type`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `enum_int`),
            [(Var_child `name`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `NEW`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `/`));
                                ((Nat 0),(PO_constant `(`));
                                ((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                                ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar
           ((Const_name `enum_chars`),[(Var_child `name`);
                                       (Var_children `enum_char1`);
                                       (Var_child `enum_char2`)])),
      (\x y. true)),
     (PF
       (H_box [((Nat 1),(PO_constant `NEW`));
               ((Nat 1),(PO_subcall ((`name`,(I)),[])));
               ((Nat 1),
                (PO_format
                  (PF (H_box [((Nat 0),(PO_constant `(`));
                              ((Nat 0),
                               (PO_format
                                 (PF (HoV_box
                                       [(((Nat 1),(Abs 0),(Nat 0)),
                                         (PO_expand
                                           (H_box [((Nat 1),
                                                    (PO_subcall
                                                      ((`enum_char1`,
                                                        (I)),[])));
                                                   ((Nat 1),
                                                    (PO_constant `|`))])));
                                        (((Nat 1),(Abs 0),(Nat 0)),
                                         (PO_subcall
                                           ((`enum_char2`,(I)),[])))]))));
                              ((Nat 0),(PO_constant `)`))]))))])));
    ((``,(Print_metavar ((Const_name `enum_char`),[(Var_child `char`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`char`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `enum_char`),
                         [(Var_child `char1`);(Var_child `char2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`char1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`char2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `type`),[(Var_child `type1`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`type1`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `type`),[(Var_child `type11`);(Var_child `type12`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`type11`,(I)),[])));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `->`));
                           ((Nat 1),(PO_subcall ((`type12`,(I)),[])))]))))])));
    ((``,(Print_metavar ((Const_name `type1`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `type_tuple`),
                         [(Var_children `type1`);(Var_child `type2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box [((Nat 0),
                                       (PO_subcall ((`type1`,(I)),[])));
                                      ((Nat 0),(PO_constant `,`))])));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`type2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((``,
      (Print_metavar
        ((Const_name `type_int`),[(Var_child `int`);(Var_child `type`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `]`));
                                ((Nat 0),(PO_subcall ((`type`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `type_STRING`),
                         [(Var_child `int`);(Var_child `name`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `STRING`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `[`));
                           ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                           ((Nat 0),(PO_constant `]`));
                           ((Nat 0),(PO_subcall ((`name`,(I)),[])))]))))])));
    ((``,(Print_metavar ((Const_name `type2`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `type_INT`),[(Var_child `name`);(Var_child `type`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_constant `INT`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `]`));
                                ((Nat 0),(PO_subcall ((`type`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `type_STRING_INT`),
                         [(Var_child `name1`);(Var_child `name2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `STRING`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `[`));
                           ((Nat 0),(PO_constant `INT`));
                           ((Nat 1),(PO_subcall ((`name1`,(I)),[])));
                           ((Nat 0),(PO_constant `]`));
                           ((Nat 0),(PO_subcall ((`name2`,(I)),[])))]))))])));
    ((``,(Print_metavar ((Const_name `type_TYPE`),[(Var_child `name`)])),
      (\x y. true)),(PF (H_box [((Nat 1),(PO_constant `TYPE`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])))])))
   ] : print_rule list;;


let ella_types_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_types_rules;;


let ella_integers_rules =

   % : (print_rule list) %

   letrec prec_val = (\dummy0. ((\symb. case symb
                                        of `+` . 2
                                         | `-` . 2
                                         | `*` . 1
                                         | `%` . 1
                                         | _   . 3
                                 ) dummy0))
   and prec = (\dummy0. ((bound_number `prec`) dummy0))
   and prec_of = (\dummy0. ((\meta. apply1 prec_val (bound_name meta)) dummy0))
   and prec_test =
    (\dummy0. ((\meta. apply2 (curry $<) (prec_of meta) prec) dummy0))
   in
   [
    ((``,(Print_metavar
           ((Const_name `intdec`),[(Var_child `name`);(Var_child `int`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                               ((Nat 1),(PO_constant `=`))]))));
                (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`int`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `int`),[(Var_child `formula`)])),
      (\x y. true)),
     (PF (H_box
           [((Nat 0),(PO_subcall ((`formula`,(I)),[(`prec`,(apply0 4))])))])));
    ((``,(Print_metavar ((Const_name `formula`),[(Var_child `formula1`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`formula1`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `formula`),
            [(Var_child `formula`);
             (Patt_child
               (Print_metavar
                 ((Const_name `operator`),
                  [(Patt_child (Print_metavar ((Var_name `op`),[])))])));
             (Var_child `formula1`)])),(\x y. true)),
     (PF (H_box
           [((Nat 0),
             (PO_format
               (PF_branch ((prec_test `op`),PF_empty,
                           (PF (H_box [((Nat 0),(PO_constant `(`))]))))));
            ((Nat 0),
             (PO_format
               (PF
                 (HV_box
                   [(((Nat 1),(Abs 0),(Nat 0)),
                     (PO_format
                       (PF (H_box
                             [((Nat 1),
                               (PO_subcall
                                 ((`formula`,(I)),
                                  [(`prec`,(prec_of `op`))])));
                              ((Nat 1),(PO_leaf (`op`,(I))))]))));
                    (((Nat 1),(Abs 0),(Nat 0)),
                     (PO_subcall
                       ((`formula1`,(I)),[(`prec`,(prec_of `op`))])))]))));
            ((Nat 0),
             (PO_format
               (PF_branch ((prec_test `op`),PF_empty,
                           (PF (H_box [((Nat 0),(PO_constant `)`))]))))))])));
    ((``,
      (Print_metavar ((Const_name `formula1`),
                      [(Var_child `formula2`);(Var_children `operator`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`operator`,(I)),[])));
                 ((Nat 0),(PO_subcall ((`formula2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `formula2`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `formula2_cond`),
         [(Var_child `boolean`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `IF`));
                           ((Nat 1),(PO_subcall ((`boolean`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `THEN`));
                           ((Nat 1),(PO_subcall ((`int1`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `ELSE`));
                           ((Nat 1),(PO_subcall ((`int2`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_constant `FI`))])));
    ((``,(Print_metavar ((Const_name `formula2_int`),[(Var_child `int`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `(`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar ((Const_name `boolean`),[(Var_child `formula`)])),
      (\x y. true)),
     (PF (H_box
           [((Nat 0),(PO_subcall ((`formula`,(I)),[(`prec`,(apply0 4))])))])))
   ] : print_rule list;;


let ella_integers_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_integers_rules;;


let ella_constants_rules =

   % : (print_rule list) %

   [
    ((``,(Print_metavar ((Const_name `constdec`),
                         [(Var_child `name`);(Var_child `const`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                           ((Nat 1),(PO_constant `=`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`const`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `const`),
                      [(Var_children `const11`);(Var_child `const12`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_expand
               (H_box [((Nat 1),(PO_subcall ((`const11`,(I)),[])));
                       ((Nat 1),(PO_constant `|`))])));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`const12`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `const1`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `const1`),[(Var_child `int`);(Var_child `const1`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `]`));
                                ((Nat 0),(PO_subcall ((`const1`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `const1_STRING`),
                         [(Var_child `int`);(Var_child `const2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `STRING`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `[`));
                           ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                           ((Nat 0),(PO_constant `]`));
                           ((Nat 0),(PO_subcall ((`const2`,(I)),[])))]))))])));
    ((``,(Print_metavar ((Const_name `const2`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `const2_formula2`),
                         [(Var_child `name`);(Var_child `formula2`)])),
      (\x y. true)),
     (PF
       (H_box
         [((Nat 0),(PO_subcall ((`name`,(I)),[])));
          ((Nat 0),(PO_constant `/`));
          ((Nat 0),(PO_subcall ((`formula2`,(I)),[(`prec`,(apply0 4))])))])));
    ((``,(Print_metavar ((Const_name `const2_char`),
                         [(Var_child `name`);(Var_child `char`)])),
      (\x y. true)),(PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 1),(PO_subcall ((`char`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `const2_string`),
                         [(Var_child `name`);(Var_child `string`)])),
      (\x y. true)),(PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 1),(PO_subcall ((`string`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `const2_const2`),
                         [(Var_child `name`);(Var_child `const2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `&`));
                                ((Nat 0),(PO_subcall ((`const2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `const2_tuple`),
                         [(Var_children `const1`);(Var_child `const2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box [((Nat 0),
                                       (PO_subcall ((`const1`,(I)),[])));
                                      ((Nat 0),(PO_constant `,`))])));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`const2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar
           ((Const_name `const2_uninit`),[(Var_child `const2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `?`));
                                ((Nat 0),(PO_subcall ((`const2`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `const2_char_range`),
            [(Var_child `name`);(Var_child `char1`);(Var_child `char2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 1),(PO_constant `(`));
                                ((Nat 0),(PO_subcall ((`char1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`char2`,(I)),[])));
                                ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar
           ((Const_name `const2_int_range`),
            [(Var_child `name`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `/`));
                                ((Nat 0),(PO_constant `(`));
                                ((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                                ((Nat 0),(PO_constant `)`))])))
   ] : print_rule list;;


let ella_constants_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_constants_rules;;


let ella_functions_rules =

   % : (print_rule list) %

   [
    ((``,
      (Print_metavar
        ((Const_name `fndec`),
         [(Var_child `fnname`);(Var_child `fnset`);(Var_child `fnbody`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                           (PO_format
                             (PF (H_box
                                   [((Nat 1),
                                     (PO_subcall ((`fnname`,(I)),[])));
                                    ((Nat 1),(PO_constant `=`))]))));
                          (((Nat 1),(Abs 3),(Nat 0)),
                           (PO_format
                             (PF (H_box
                                   [((Nat 0),
                                     (PO_subcall ((`fnset`,(I)),[])));
                                    ((Nat 0),(PO_constant `:`))]))))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`fnbody`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `fnset`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `fnset`),[(Var_child `int`);(Var_child `fnarrow`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `FNSET`));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 0),(PO_constant `[`));
                               ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                               ((Nat 0),(PO_constant `]`));
                               ((Nat 0),(PO_constant `(`));
                               ((Nat 0),(PO_subcall ((`fnarrow`,(I)),[])));
                               ((Nat 0),(PO_constant `)`))]))))])));
    ((``,
      (Print_metavar
        ((Const_name `fnarrow`),[(Var_child `input`);(Var_child `type`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`input`,(I)),[])));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `->`));
                           ((Nat 1),(PO_subcall ((`type`,(I)),[])))]))))])));
    ((``,
      (Print_metavar ((Const_name `fnarrows`),
                      [(Var_children `fnarrow1`);(Var_child `fnarrow2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `FNSET`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 0),(PO_constant `(`));
                      ((Nat 0),
                       (PO_format
                         (PF
                           (HoV_box
                             [(((Nat 1),(Abs 0),(Nat 0)),
                               (PO_expand
                                 (H_box [((Nat 0),
                                          (PO_subcall
                                            ((`fnarrow1`,(I)),
                                             [])));
                                         ((Nat 0),
                                          (PO_constant `,`))])));
                              (((Nat 1),(Abs 0),(Nat 0)),
                               (PO_subcall ((`fnarrow2`,(I)),[])))]))));
                      ((Nat 0),(PO_constant `)`))]))))])));
    ((``,(Print_metavar
           ((Const_name `input`),
            [(Var_children `inputitem1`);(Var_child `inputitem2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),
                                  (PO_subcall ((`inputitem1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`))])));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`inputitem2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar ((Const_name `inputitem`),[(Var_child `type`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`type`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `inputitem`),
                         [(Var_child `type`);(Var_child `names`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_subcall ((`type`,(I)),[])));
                           ((Nat 0),(PO_constant `:`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`names`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `fnbody`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `fnbody_ARITH`),[(Var_child `int`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `ARITH`));
                (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`int`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `fnbody_BIOP`),[(Var_child `biopname`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `BIOP`));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`biopname`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `fnbody_BIOP`),
                      [(Var_child `biopname`);(Var_child `macparams`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `BIOP`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_subcall ((`biopname`,(I)),[])));
                           ((Nat 0),(PO_constant `{`));
                           ((Nat 0),(PO_subcall ((`macparams`,(I)),[])));
                           ((Nat 0),(PO_constant `}`))]))))])));
    ((``,(Print_metavar ((Const_name `fnbody_REFORM`),[])),(\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `REFORM`))])));
    ((``,(Print_metavar ((Const_name `fnbody_IMPORT`),[])),(\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `IMPORT`))])));
    ((``,(Print_metavar ((Const_name `fnbody_DELAY`),
                         [(Var_child `const1`);(Var_child `int`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `DELAY`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 0),(PO_constant `(`));
                                 ((Nat 0),(PO_subcall ((`const1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`));
                                 ((Nat 1),(PO_subcall ((`int`,(I)),[])));
                                 ((Nat 0),(PO_constant `)`))]))))])));
    ((``,(Print_metavar
           ((Const_name `fnbody_DELAY`),
            [(Var_child `const1`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `DELAY`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 0),(PO_constant `(`));
                                 ((Nat 0),(PO_subcall ((`const1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`));
                                 ((Nat 1),(PO_subcall ((`int1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`));
                                 ((Nat 1),(PO_subcall ((`int2`,(I)),[])));
                                 ((Nat 0),(PO_constant `)`))]))))])));
    ((``,
      (Print_metavar ((Const_name `fnbody_DELAY`),[(Var_child `const11`);
                                                   (Var_child `int1`);
                                                   (Var_child `const12`);
                                                   (Var_child `int2`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `DELAY`));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 0),(PO_constant `(`));
                               ((Nat 0),(PO_subcall ((`const11`,(I)),[])));
                               ((Nat 0),(PO_constant `,`));
                               ((Nat 1),(PO_subcall ((`int1`,(I)),[])));
                               ((Nat 0),(PO_constant `,`));
                               ((Nat 1),(PO_subcall ((`const12`,(I)),[])));
                               ((Nat 0),(PO_constant `,`));
                               ((Nat 1),(PO_subcall ((`int2`,(I)),[])));
                               ((Nat 0),(PO_constant `)`))]))))])));
    ((``,(Print_metavar ((Const_name `fnbody_IDELAY`),
                         [(Var_child `const1`);(Var_child `int`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `IDELAY`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 0),(PO_constant `(`));
                                 ((Nat 0),(PO_subcall ((`const1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`));
                                 ((Nat 1),(PO_subcall ((`int`,(I)),[])));
                                 ((Nat 0),(PO_constant `)`))]))))])));
    ((``,
      (Print_metavar ((Const_name `fnbody_RAM`),[(Var_child `const1`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `RAM`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (H_box [((Nat 0),(PO_constant `(`));
                                 ((Nat 0),(PO_subcall ((`const1`,(I)),[])));
                                 ((Nat 0),(PO_constant `)`))]))))])))
   ] : print_rule list;;


let ella_functions_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_functions_rules;;


let ella_units_rules =

   % : (print_rule list) %

   [
    ((``,(Print_metavar ((Const_name `unit`),[(Var_child `unit1`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `unit`),[(Var_child `unit`);(Var_child `child`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit_fn`),[(Var_child `fnname`);
                                                 (Var_child `unit_names`);
                                                 (Var_child `unit1`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`fnname`,(I)),[])));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_subcall ((`unit_names`,(I)),[])));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit_mac`),[(Var_child `macname`);
                                                  (Var_child `unit_names`);
                                                  (Var_child `unit1`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`macname`,(I)),[])));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_subcall ((`unit_names`,(I)),[])));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit_mac`),[(Var_child `macname`);
                                                  (Var_child `macparams`);
                                                  (Var_child `unit_names`);
                                                  (Var_child `unit1`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 0),(PO_subcall ((`macname`,(I)),[])));
                         ((Nat 0),(PO_constant `{`));
                         ((Nat 0),(PO_subcall ((`macparams`,(I)),[])));
                         ((Nat 0),(PO_constant `}`))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_subcall ((`unit_names`,(I)),[])));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `unit_names`),[(Var_children `name`)])),
      (\x y. true)),
     (PF
       (HoV_box
         [(((Nat 1),(Abs 0),(Nat 0)),
           (PO_expand (H_box [((Nat 0),(PO_constant `@`));
                              ((Nat 0),(PO_subcall ((`name`,(I)),[])))])))])));
    ((``,(Print_metavar
           ((Const_name `macparams`),
            [(Var_children `macparam1`);(Var_child `macparam2`)])),
      (\x y. true)),
     (PF
       (HoV_box
         [(((Nat 1),(Abs 0),(Nat 0)),
           (PO_expand
             (H_box [((Nat 0),(PO_subcall ((`macparam1`,(I)),[])));
                     ((Nat 0),(PO_constant `,`))])));
          (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`macparam2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `macparam`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit1`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit1_1`),
                         [(Var_child `unit2`);(Var_child `unit_names`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit2`,(I)),[])));
          (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit_names`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `unit1_4`),[(Var_child `int`);(Var_child `unit1`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `]`));
                                ((Nat 0),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit1_5`),[(Var_child `name`);
                                                 (Var_child `int1`);
                                                 (Var_child `int2`);
                                                 (Var_child `unit1`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_constant `INT`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 1),(PO_constant `=`));
                                ((Nat 1),(PO_subcall ((`int1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                                ((Nat 0),(PO_constant `]`));
                                ((Nat 0),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `unit1_6`),[(Var_child `name`);(Var_child `unit1`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `&`));
                                ((Nat 0),(PO_subcall ((`unit1`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `unit1_7`),[(Var_child `int`);(Var_child `unit1`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `STRING`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_constant `[`));
                           ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                           ((Nat 0),(PO_constant `]`));
                           ((Nat 0),(PO_subcall ((`unit1`,(I)),[])))]))))])));
    ((``,
      (Print_metavar
        ((Const_name `unit1_8`),[(Var_child `unit2`);(Var_child `name`)])),
      (\x y. true)),(PF (H_box [((Nat 1),(PO_subcall ((`unit2`,(I)),[])));
                                ((Nat 1),(PO_constant `//`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit1_9`),[(Var_child `name`)])),
      (\x y. true)),(PF (H_box [((Nat 1),(PO_constant `IO`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `unit1_9`),[(Var_child `name`);(Var_child `int`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `IO`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `]`))])));
    ((``,(Print_metavar
           ((Const_name `unit1_9`),
            [(Var_child `name`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `IO`));
                                ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                                ((Nat 0),(PO_constant `]`));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                                ((Nat 0),(PO_constant `]`))])));
    ((``,(Print_metavar ((Const_name `unit2`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `unit2_uninit`),[(Var_child `type`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_constant `?`));
                                ((Nat 0),(PO_subcall ((`type`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `unit2_int`),
                         [(Var_child `unit2`);(Var_child `int`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`unit2`,(I)),[])));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `]`))])));
    ((``,(Print_metavar ((Const_name `unit2_unit`),
                         [(Var_child `unit2`);(Var_child `unit`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`unit2`,(I)),[])));
                                ((Nat 0),(PO_constant `[[`));
                                ((Nat 0),(PO_subcall ((`unit`,(I)),[])));
                                ((Nat 0),(PO_constant `]]`))])));
    ((``,(Print_metavar
           ((Const_name `unit2_int_range`),
            [(Var_child `unit2`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`unit2`,(I)),[])));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                                ((Nat 0),(PO_constant `]`))])));
    ((``,
      (Print_metavar
        ((Const_name `unit2_cond`),
         [(Var_child `boolean`);(Var_child `unit1`);(Var_child `unit2`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `IF`));
                           ((Nat 1),(PO_subcall ((`boolean`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `THEN`));
                           ((Nat 1),(PO_subcall ((`unit1`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `ELSE`));
                           ((Nat 1),(PO_subcall ((`unit2`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_constant `FI`))])));
    ((``,(Print_metavar ((Const_name `unit3`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `units`),
                         [(Var_children `unit1`);(Var_child `unit2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box [((Nat 0),
                                       (PO_subcall ((`unit1`,(I)),[])));
                                      ((Nat 0),(PO_constant `,`))])));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`unit2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar
           ((Const_name `caseclause`),[(Var_child `unit`);
                                       (Var_child `choices`);
                                       (Var_child `caseclause_elseof`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `CASE`));
                           ((Nat 1),(PO_subcall ((`unit`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `OF`));
                           ((Nat 1),(PO_subcall ((`choices`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall ((`caseclause_elseof`,(I)),[])));
            (((Abs 0),(Nat 0)),(PO_constant `ESAC`))])));
    ((``,(Print_metavar
           ((Const_name `caseclause`),[(Var_child `unit1`);
                                       (Var_child `choices`);
                                       (Var_child `caseclause_elseof`);
                                       (Var_child `unit2`)])),(\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `CASE`));
                           ((Nat 1),(PO_subcall ((`unit1`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `OF`));
                           ((Nat 1),(PO_subcall ((`choices`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall ((`caseclause_elseof`,(I)),[])));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `ELSE`));
                           ((Nat 1),(PO_subcall ((`unit2`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_constant `ESAC`))])));
    ((``,(Print_metavar
           ((Const_name `caseclause_ELSEOF`),[(Var_children `choices`)])),
      (\x y. true)),
     (PF
       (V_box [(((Abs 0),(Nat 0)),
                (PO_expand
                  (H_box [((Nat 1),(PO_constant `ELSEOF`));
                          ((Nat 1),(PO_subcall ((`choices`,(I)),[])))])))])));
    ((``,
      (Print_metavar ((Const_name `choices`),
                      [(Var_children `choice1`);(Var_child `choice2`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_expand
               (H_box [((Nat 0),(PO_subcall ((`choice1`,(I)),[])));
                       ((Nat 0),(PO_constant `,`))])));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`choice2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `choice`),
                         [(Var_child `choosers`);(Var_child `unit`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_subcall ((`choosers`,(I)),[])));
                           ((Nat 0),(PO_constant `:`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `choosers`),[(Var_child `const`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`const`,(I)),[])))])))
   ] : print_rule list;;


let ella_units_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_units_rules;;


let ella_series_rules =

   % : (print_rule list) %

   [
    ((``,(Print_metavar ((Const_name `series`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `series_BEGINEND`),
                         [(Var_child `unit`);(Var_children `step`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),(PO_constant `BEGIN`));
            (((Abs 3),(Nat 0)),
             (PO_expand (H_box [((Nat 0),(PO_subcall ((`step`,(I)),[])));
                                ((Nat 0),(PO_constant `.`))])));
            (((Abs 3),(Nat 0)),
             (PO_format (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                                      (PO_constant `OUTPUT`));
                                     (((Nat 1),(Abs 3),(Nat 0)),
                                      (PO_subcall ((`unit`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_constant `END`))])));
    ((``,(Print_metavar ((Const_name `series_brackets`),
                         [(Var_child `unit`);(Var_children `step`)])),
      (\x y. true)),
     (PF (H_box
           [((Nat 0),(PO_constant `(`));
            ((Nat 0),
             (PO_format
               (PF (V_box
                     [(((Abs 0),(Nat 0)),
                       (PO_expand
                         (H_box [((Nat 0),
                                  (PO_subcall ((`step`,(I)),[])));
                                 ((Nat 0),(PO_constant `.`))])));
                      (((Abs 0),(Nat 0)),
                       (PO_format
                         (PF (HV_box
                               [(((Nat 1),(Abs 3),(Nat 0)),
                                 (PO_constant `OUTPUT`));
                                (((Nat 1),(Abs 3),(Nat 0)),
                                 (PO_subcall ((`unit`,(I)),[])))]))))]))));
            ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar ((Const_name `step`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `step`),
                      [(Var_child `multiplier`);(Var_child `step_join`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),
           (PO_format
             (PF (H_box
                   [((Nat 1),(PO_constant `FOR`));
                    ((Nat 1),(PO_subcall ((`multiplier`,(I)),[])))]))));
          (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`step_join`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `step_MAKE`),
            [(Var_children `makeitem1`);(Var_child `makeitem2`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `MAKE`));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (V_box [(((Abs 0),(Nat 0)),
                                (PO_expand
                                  (H_box
                                    [((Nat 0),
                                      (PO_subcall ((`makeitem1`,(I)),[])));
                                     ((Nat 0),(PO_constant `,`))])));
                               (((Abs 0),(Nat 0)),
                                (PO_subcall ((`makeitem2`,(I)),[])))]))))])));
    ((``,
      (Print_metavar ((Const_name `step_LET`),
                      [(Var_children `letitem1`);(Var_child `letitem2`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `LET`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (V_box [(((Abs 0),(Nat 0)),
                                  (PO_expand
                                    (H_box
                                      [((Nat 0),
                                        (PO_subcall ((`letitem1`,(I)),[])));
                                       ((Nat 0),(PO_constant `,`))])));
                                 (((Abs 0),(Nat 0)),
                                  (PO_subcall ((`letitem2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `step_JOIN`),
            [(Var_children `joinitem1`);(Var_child `joinitem2`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `JOIN`));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (V_box [(((Abs 0),(Nat 0)),
                                (PO_expand
                                  (H_box
                                    [((Nat 0),
                                      (PO_subcall ((`joinitem1`,(I)),[])));
                                     ((Nat 0),(PO_constant `,`))])));
                               (((Abs 0),(Nat 0)),
                                (PO_subcall ((`joinitem2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `step_PRINT`),
            [(Var_children `printitem1`);(Var_child `printitem2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `PRINT`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (V_box [(((Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),
                                  (PO_subcall ((`printitem1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`))])));
                           (((Abs 0),(Nat 0)),
                            (PO_subcall ((`printitem2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `step_FAULT`),
            [(Var_children `faultitem1`);(Var_child `faultitem2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `FAULT`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (V_box [(((Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),
                                  (PO_subcall ((`faultitem1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`))])));
                           (((Abs 0),(Nat 0)),
                            (PO_subcall ((`faultitem2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `makeitem`),[(Var_child `makeitem_body`);
                                     (Var_child `unit_names`);
                                     (Var_child `names`)])),(\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 0),(PO_subcall ((`makeitem_body`,(I)),[])));
                      ((Nat 1),(PO_subcall ((`unit_names`,(I)),[])));
                      ((Nat 0),(PO_constant `:`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`names`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `makeitem`),[(Var_child `int`);
                                     (Var_child `makeitem_body`);
                                     (Var_child `unit_names`);
                                     (Var_child `names`)])),(\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `[`));
                 ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                 ((Nat 0),(PO_constant `]`));
                 ((Nat 0),
                  (PO_format
                    (PF (HV_box
                          [(((Nat 1),(Abs 3),(Nat 0)),
                            (PO_format
                              (PF (H_box
                                    [((Nat 0),
                                      (PO_subcall
                                        ((`makeitem_body`,(I)),[])));
                                     ((Nat 1),(PO_subcall
                                                ((`unit_names`,(I)),[])));
                                     ((Nat 0),(PO_constant `:`))]))));
                           (((Nat 1),(Abs 3),(Nat 0)),
                            (PO_subcall ((`names`,(I)),[])))]))))])));
    ((``,
      (Print_metavar ((Const_name `makeitem_body`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `makeitem_mac`),[(Var_child `macname`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`macname`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `makeitem_mac`),
                         [(Var_child `macname`);(Var_child `macparams`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`macname`,(I)),[])));
                 ((Nat 0),(PO_constant `{`));
                 ((Nat 0),(PO_subcall ((`macparams`,(I)),[])));
                 ((Nat 0),(PO_constant `}`))])));
    ((``,(Print_metavar
           ((Const_name `makeitem_mac`),[(Var_child `macname`);
                                         (Var_child `macparams1`);
                                         (Var_child `macparams2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`macname`,(I)),[])));
                 ((Nat 0),(PO_constant `{`));
                 ((Nat 0),(PO_subcall ((`macparams1`,(I)),[])));
                 ((Nat 0),(PO_constant `}`));
                 ((Nat 0),(PO_constant `{`));
                 ((Nat 0),(PO_subcall ((`macparams2`,(I)),[])));
                 ((Nat 0),(PO_constant `}`))])));
    ((``,
      (Print_metavar
        ((Const_name `letitem`),[(Var_child `name`);(Var_child `unit`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                               ((Nat 1),(PO_constant `=`))]))));
                (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `joinitem`),[(Var_child `unit`);(Var_child `name`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `->`));
                           ((Nat 1),(PO_subcall ((`name`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `joinitem`),
            [(Var_child `unit`);(Var_child `name`);(Var_child `int`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 0),(PO_constant `->`));
                               ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                               ((Nat 0),(PO_constant `[`));
                               ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                               ((Nat 0),(PO_constant `]`))]))))])));
    ((``,(Print_metavar ((Const_name `joinitem`),[(Var_child `unit`);
                                                  (Var_child `name`);
                                                  (Var_child `int1`);
                                                  (Var_child `int2`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])));
                (((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 0),(PO_constant `->`));
                               ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                               ((Nat 0),(PO_constant `[`));
                               ((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                               ((Nat 0),(PO_constant `]`));
                               ((Nat 0),(PO_constant `[`));
                               ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                               ((Nat 0),(PO_constant `]`))]))))])));
    ((``,(Print_metavar
           ((Const_name `multiplier`),[(Var_child `multiplier_int1`);
                                       (Var_children `multiplier_int2`)])),
      (\x y. true)),
     (PF (HoV_box [(((Nat 1),(Abs 0),(Nat 0)),
                    (PO_subcall ((`multiplier_int1`,(I)),[])));
                   (((Nat 1),(Abs 0),(Nat 0)),
                    (PO_subcall ((`multiplier_int2`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `multiplier_INT`),
            [(Var_child `name`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `INT`));
                           ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                           ((Nat 1),(PO_constant `=`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                           ((Nat 0),(PO_constant `..`));
                           ((Nat 0),(PO_subcall ((`int2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `printitem`),[(Var_child `printables`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`printables`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `printitem`),
                      [(Var_child `boolean`);(Var_child `printables`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `IF`));
                           ((Nat 1),(PO_subcall ((`boolean`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `THEN`));
                      ((Nat 1),(PO_subcall ((`printables`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_constant `FI`))])));
    ((``,(Print_metavar
           ((Const_name `printables`),
            [(Var_child `printable1`);(Var_children `printable2`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Inc 3),(Nat 0)),
           (PO_subcall ((`printable1`,(I)),[])));
          (((Nat 1),(Inc 3),(Nat 0)),(PO_subcall ((`printable2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `printable`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `faultitem`),[(Var_child `printitem`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`printitem`,(I)),[])))])))
   ] : print_rule list;;


let ella_series_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_series_rules;;


let ella_sequences_rules =

   % : (print_rule list) %

   [
    ((``,(Print_metavar ((Const_name `sequence`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `sequence_BEGINEND`),
                      [(Var_child `unit`);(Var_children `sequencestep`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),(PO_constant `BEGIN SEQ`));
            (((Abs 3),(Nat 0)),
             (PO_expand
               (H_box [((Nat 0),(PO_subcall ((`sequencestep`,(I)),[])));
                       ((Nat 0),(PO_constant `;`))])));
            (((Abs 3),(Nat 0)),
             (PO_format (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                                      (PO_constant `OUTPUT`));
                                     (((Nat 1),(Abs 3),(Nat 0)),
                                      (PO_subcall ((`unit`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_constant `END`))])));
    ((``,
      (Print_metavar ((Const_name `sequence_brackets`),
                      [(Var_child `unit`);(Var_children `sequencestep`)])),
      (\x y. true)),
     (PF (H_box
           [((Nat 0),(PO_constant `(`));
            ((Nat 0),(PO_constant `SEQ`));
            ((Nat 1),
             (PO_format
               (PF (V_box
                     [(((Abs 0),(Nat 0)),
                       (PO_expand
                         (H_box
                           [((Nat 0),(PO_subcall
                                       ((`sequencestep`,(I)),[])));
                            ((Nat 0),(PO_constant `;`))])));
                      (((Abs 0),(Nat 0)),
                       (PO_format
                         (PF (HV_box
                               [(((Nat 1),(Abs 3),(Nat 0)),
                                 (PO_constant `OUTPUT`));
                                (((Nat 1),(Abs 3),(Nat 0)),
                                 (PO_subcall ((`unit`,(I)),[])))]))))]))));
            ((Nat 0),(PO_constant `)`))])));
    ((``,
      (Print_metavar ((Const_name `sequencestep`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `sequencestep_VAR`),
                      [(Var_children `varitem1`);(Var_child `varitem2`)])),
      (\x y. true)),
     (PF (HV_box [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `VAR`));
                  (((Nat 1),(Abs 3),(Nat 0)),
                   (PO_format
                     (PF (V_box [(((Abs 0),(Nat 0)),
                                  (PO_expand
                                    (H_box
                                      [((Nat 0),
                                        (PO_subcall ((`varitem1`,(I)),[])));
                                       ((Nat 0),(PO_constant `,`))])));
                                 (((Abs 0),(Nat 0)),
                                  (PO_subcall ((`varitem2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `sequencestep_STATEVAR`),
            [(Var_children `statevaritem1`);(Var_child `statevaritem2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `STATE VAR`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (V_box [(((Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),(PO_subcall
                                            ((`statevaritem1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`))])));
                           (((Abs 0),(Nat 0)),
                            (PO_subcall ((`statevaritem2`,(I)),[])))]))))])));
    ((``,(Print_metavar
           ((Const_name `sequencestep_PVAR`),
            [(Var_child `statevaritem1`);(Var_children `statevaritem2`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),(PO_constant `PVAR`));
            (((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (V_box [(((Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),(PO_subcall
                                            ((`statevaritem1`,(I)),[])));
                                 ((Nat 0),(PO_constant `,`))])));
                           (((Abs 0),(Nat 0)),
                            (PO_subcall ((`statevaritem2`,(I)),[])))]))))])));
    ((``,
      (Print_metavar
        ((Const_name `varitem`),[(Var_child `name`);(Var_child `unit`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                               ((Nat 1),(PO_constant `:=`))]))));
                (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])))])));
    ((``,
      (Print_metavar
        ((Const_name `statevaritem`),[(Var_child `statevaritem_init`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_subcall ((`statevaritem_init`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `statevaritem`),
                         [(Var_child `name`);(Var_child `const1`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                           ((Nat 1),(PO_constant `::=`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`const1`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `statevaritem_INIT`),
                         [(Var_child `name`);(Var_child `const1`)])),
      (\x y. true)),
     (PF (HV_box
           [(((Nat 1),(Abs 3),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_subcall ((`name`,(I)),[])));
                           ((Nat 1),(PO_constant `INIT`))]))));
            (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`const1`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `statement`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `statements`),
            [(Var_children `statement1`);(Var_child `statement2`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `(`));
                 ((Nat 0),
                  (PO_format
                    (PF (HoV_box
                          [(((Nat 1),(Abs 0),(Nat 0)),
                            (PO_expand
                              (H_box
                                [((Nat 0),
                                  (PO_subcall ((`statement1`,(I)),[])));
                                 ((Nat 0),(PO_constant `;`))])));
                           (((Nat 1),(Abs 0),(Nat 0)),
                            (PO_subcall ((`statement2`,(I)),[])))]))));
                 ((Nat 0),(PO_constant `)`))])));
    ((``,(Print_metavar ((Const_name `statement_assign`),
                         [(Var_child `varname`);(Var_child `unit`)])),
      (\x y. true)),
     (PF
       (HV_box [(((Nat 1),(Abs 3),(Nat 0)),
                 (PO_format
                   (PF (H_box [((Nat 1),(PO_subcall ((`varname`,(I)),[])));
                               ((Nat 1),(PO_constant `:=`))]))));
                (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`unit`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `statement_INT`),[(Var_child `name`);
                                          (Var_child `int1`);
                                          (Var_child `int2`);
                                          (Var_child `statement`)])),
      (\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `[`));
                 ((Nat 0),(PO_constant `INT`));
                 ((Nat 1),(PO_subcall ((`name`,(I)),[])));
                 ((Nat 1),(PO_constant `=`));
                 ((Nat 1),(PO_subcall ((`int1`,(I)),[])));
                 ((Nat 0),(PO_constant `..`));
                 ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                 ((Nat 0),(PO_constant `]`));
                 ((Nat 0),(PO_subcall ((`statement`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `statement_cond`),
                         [(Var_child `boolean`);(Var_child `statement`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `IF`));
                           ((Nat 1),(PO_subcall ((`boolean`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),(PO_constant `THEN`));
                         ((Nat 1),(PO_subcall ((`statement`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_constant `FI`))])));
    ((``,(Print_metavar
           ((Const_name `statement_cond`),[(Var_child `boolean`);
                                           (Var_child `statement1`);
                                           (Var_child `statement2`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `IF`));
                           ((Nat 1),(PO_subcall ((`boolean`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `THEN`));
                      ((Nat 1),(PO_subcall ((`statement1`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `ELSE`));
                      ((Nat 1),(PO_subcall ((`statement2`,(I)),[])))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_constant `FI`))])));
    ((``,
      (Print_metavar
        ((Const_name `statement_case`),[(Var_child `unit`);
                                        (Var_child `seqchoices`);
                                        (Var_child `statement_elseof`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `CASE`));
                           ((Nat 1),(PO_subcall ((`unit`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `OF`));
                      ((Nat 1),(PO_subcall ((`seqchoices`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall ((`statement_elseof`,(I)),[])));
            (((Abs 0),(Nat 0)),(PO_constant `ESAC`))])));
    ((``,(Print_metavar
           ((Const_name `statement_case`),[(Var_child `unit`);
                                           (Var_child `seqchoices`);
                                           (Var_child `statement_elseof`);
                                           (Var_child `statement`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box [((Nat 1),(PO_constant `CASE`));
                           ((Nat 1),(PO_subcall ((`unit`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF (H_box
                     [((Nat 1),(PO_constant `OF`));
                      ((Nat 1),(PO_subcall ((`seqchoices`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_subcall ((`statement_elseof`,(I)),[])));
            (((Abs 0),(Nat 0)),
             (PO_format
               (PF
                 (H_box [((Nat 1),(PO_constant `ELSE`));
                         ((Nat 1),(PO_subcall ((`statement`,(I)),[])))]))));
            (((Abs 0),(Nat 0)),(PO_constant `ESAC`))])));
    ((``,
      (Print_metavar
        ((Const_name `statement_ELSEOF`),[(Var_children `seqchoices`)])),
      (\x y. true)),
     (PF (V_box
           [(((Abs 0),(Nat 0)),
             (PO_expand
               (H_box [((Nat 1),(PO_constant `ELSEOF`));
                       ((Nat 1),(PO_subcall ((`seqchoices`,(I)),[])))])))])));
    ((``,(Print_metavar ((Const_name `varname`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `varname_int`),
                         [(Var_child `varname`);(Var_child `int`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`varname`,(I)),[])));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int`,(I)),[])));
                                ((Nat 0),(PO_constant `]`))])));
    ((``,(Print_metavar ((Const_name `varname_unit`),
                         [(Var_child `varname`);(Var_child `unit`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`varname`,(I)),[])));
                                ((Nat 0),(PO_constant `[[`));
                                ((Nat 0),(PO_subcall ((`unit`,(I)),[])));
                                ((Nat 0),(PO_constant `]]`))])));
    ((``,
      (Print_metavar
        ((Const_name `varname_int_range`),
         [(Var_child `varname`);(Var_child `int1`);(Var_child `int2`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`varname`,(I)),[])));
                                ((Nat 0),(PO_constant `[`));
                                ((Nat 0),(PO_subcall ((`int1`,(I)),[])));
                                ((Nat 0),(PO_constant `..`));
                                ((Nat 0),(PO_subcall ((`int2`,(I)),[])));
                                ((Nat 0),(PO_constant `]`))])));
    ((``,(Print_metavar
           ((Const_name `seqchoices`),
            [(Var_children `seqchoice1`);(Var_child `seqchoice2`)])),
      (\x y. true)),
     (PF
       (HoV_box
         [(((Nat 1),(Abs 0),(Nat 0)),
           (PO_expand
             (H_box [((Nat 0),(PO_subcall ((`seqchoice1`,(I)),[])));
                     ((Nat 0),(PO_constant `,`))])));
          (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`seqchoice2`,(I)),[])))])));
    ((``,
      (Print_metavar ((Const_name `seqchoice`),[(Var_child `choosers`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`choosers`,(I)),[])));
                                ((Nat 0),(PO_constant `:`))])));
    ((``,
      (Print_metavar ((Const_name `seqchoice`),
                      [(Var_child `choosers`);(Var_child `statement`)])),
      (\x y. true)),
     (PF
       (HV_box
         [(((Nat 1),(Abs 3),(Nat 0)),
           (PO_format
             (PF (H_box [((Nat 0),(PO_subcall ((`choosers`,(I)),[])));
                         ((Nat 0),(PO_constant `:`))]))));
          (((Nat 1),(Abs 3),(Nat 0)),(PO_subcall ((`statement`,(I)),[])))])))
   ] : print_rule list;;


let ella_sequences_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_sequences_rules;;


let ella_macros_rules =

   % : (print_rule list) %

   [
    ((``,(Print_metavar ((Const_name `macdec`),[(Var_child `macname`);
                                                (Var_child `fnset`);
                                                (Var_child `fnbody`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (HV_box
                     [(((Nat 1),(Abs 3),(Nat 0)),
                       (PO_format
                         (PF (H_box
                               [((Nat 1),
                                 (PO_subcall ((`macname`,(I)),[])));
                                ((Nat 1),(PO_constant `=`))]))));
                      (((Nat 1),(Abs 3),(Nat 0)),
                       (PO_format
                         (PF (H_box
                               [((Nat 0),
                                 (PO_subcall ((`fnset`,(I)),[])));
                                ((Nat 0),(PO_constant `:`))]))))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`fnbody`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `macdec`),[(Var_child `macname`);
                                                (Var_child `macspec`);
                                                (Var_child `fnarrow`);
                                                (Var_child `fnbody`)])),
      (\x y. true)),
     (PF (HoV_box
           [(((Nat 1),(Abs 0),(Nat 0)),
             (PO_format
               (PF (HV_box
                     [(((Nat 1),(Abs 3),(Nat 0)),
                       (PO_format
                         (PF (H_box
                               [((Nat 0),
                                 (PO_subcall ((`macname`,(I)),[])));
                                ((Nat 0),(PO_constant `{`));
                                ((Nat 0),
                                 (PO_subcall ((`macspec`,(I)),[])));
                                ((Nat 0),(PO_constant `}`));
                                ((Nat 1),(PO_constant `=`))]))));
                      (((Nat 1),(Abs 3),(Nat 0)),
                       (PO_format
                         (PF (H_box
                               [((Nat 0),
                                 (PO_subcall ((`fnarrow`,(I)),[])));
                                ((Nat 0),(PO_constant `:`))]))))]))));
            (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`fnbody`,(I)),[])))])));
    ((``,(Print_metavar
           ((Const_name `macspec`),
            [(Var_children `mactypes1`);(Var_child `mactypes2`)])),
      (\x y. true)),
     (PF
       (HoV_box
         [(((Nat 1),(Abs 0),(Nat 0)),
           (PO_expand
             (H_box [((Nat 0),(PO_subcall ((`mactypes1`,(I)),[])));
                     ((Nat 0),(PO_constant `,`))])));
          (((Nat 1),(Abs 0),(Nat 0)),(PO_subcall ((`mactypes2`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `mactypes`),
                         [(Var_child `mactype`);(Var_child `names`)])),
      (\x y. true)),(PF (H_box [((Nat 1),(PO_subcall ((`mactype`,(I)),[])));
                                ((Nat 1),(PO_subcall ((`names`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `mactype`),[(Var_child `child`)])),
      (\x y. true)),(PF (H_box [((Nat 0),(PO_subcall ((`child`,(I)),[])))])));
    ((``,(Print_metavar ((Const_name `mactype_INT`),[])),(\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `INT`))])));
    ((``,(Print_metavar ((Const_name `mactype_TYPE`),[])),(\x y. true)),
     (PF (H_box [((Nat 0),(PO_constant `TYPE`))])))
   ] : print_rule list;;


let ella_macros_rules_fun =

   % : (print_rule_function) %

   print_rule_fun ella_macros_rules;;


let full_ella_rules_fun = ella_basics_rules_fun then_try
                          ella_text_rules_fun then_try
                          ella_declarations_rules_fun then_try
                          ella_types_rules_fun then_try
                          ella_integers_rules_fun then_try
                          ella_constants_rules_fun then_try
                          ella_functions_rules_fun then_try
                          ella_units_rules_fun then_try
                          ella_series_rules_fun then_try
                          ella_sequences_rules_fun then_try
                          ella_macros_rules_fun;;
