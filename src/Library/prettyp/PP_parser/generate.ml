% generate.ml                                                                 %
%-----------------------------------------------------------------------------%

begin_section generate;;

%  Pretty-printing rules for a subset of ML.  %

%  These rules are used to generate ML code from a parse-tree. They appear  %
%  as the ML data structure which represents the rules. No precedence is    %
%  used to reduce the number of parentheses, because the output is only     %
%  intended for code generation.                                            %

let PP_to_ML_rules =

   % : (print_rule list) %

   [

    %  Rule for use with ML code block rule  %

    %  Prints a node name representing some arbitrary string.  %

    (`name`,Var_name (`n`,[]),(\x y. true)),[],
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))]);

    %  Integer constant  %

    (``,Const_name (`INTCONST`,[Patt_child (Var_name (`n`,[]))]),
                                                       (\x y. true)),[],
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))]);

    %  String constant  %

    (``,Const_name (`TOKCONST`,[Patt_child (Var_name (`n`,[]))]),
                                                       (\x y. true)),[],
       (PF_H [Nat 0,PO_constant `\``;
              Nat 0,PO_leaf (`n`,(\s.s));
              Nat 0,PO_constant `\``
             ]);

    %  Variable  %

    (``,Const_name (`VAR`,[Patt_child (Var_name (`n`,[]))]), (\x y. true)),[],
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))]);

    %  Concrete type constructor with argument  %

    (``,Const_name (`CON`,[Patt_child (Var_name (`n`,[]))]), (\x y. true)),[],
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))]);

    %  Concrete type constructor with no argument  %

    (``,Const_name (`CON0`,[Patt_child (Var_name (`n`,[]))]), (\x y. true)),[],
       (PF_H [Nat 0,PO_leaf (`n`,(\s.s))]);

    %  Application of unary operator  %

    (``,Const_name (`UNOP`,[Patt_child (Var_name (`n`,[]));
                            Patt_child (Var_child `c`)
                           ]), (\x y. true)),[],
       (PF_H [Nat 0,PO_constant `(`;
              Nat 0,PO_format (PF_HV [(Nat 0,Abs 0,Nat 0),PO_leaf (`n`,(\s.s));
                                      (Nat 0,Abs 0,Nat 0),PO_subcall
                                                             ((`c`,(\l.l)),[])
                                     ]);
              Nat 0,PO_constant `)`
             ]);

    %  Function application  %

    (``,Const_name (`APPN`,[Patt_child (Var_child `c1`);
                            Patt_child (Var_child `c2`)
                           ]), (\x y. true)),[],
       (PF_H [Nat 0,PO_constant `(`;
              Nat 0,PO_format (PF_HV [(Nat 1,Abs 1,Nat 0),
                                      PO_subcall((`c1`,(\l.l)),[]);
                                      (Nat 1,Abs 1,Nat 0),
                                      PO_subcall((`c2`,(\l.l)),[])
                                     ]);
              Nat 0,PO_constant `)`
             ]);

    %  Abstraction  %

    (``,Const_name (`ABSTR`,[Patt_child (Var_child `c1`);
                             Patt_child (Var_child `c2`)
                            ]), (\x y. true)),[],
       (PF_H [Nat 0,PO_constant `(\\`;
              Nat 0,PO_format
                       (PF_HV [(Nat 1,Abs 1,Nat 0),
                                  PO_format (PF_H [(Nat 0),
                                                      PO_subcall
                                                         ((`c1`,(\l.l)),[]);
                                                   (Nat 0),PO_constant `.`
                                                  ]);
                               (Nat 1,Abs 1,Nat 0),PO_subcall((`c2`,(\l.l)),[])
                              ]);
              Nat 0,PO_constant `)`
             ]);

    %  List of at least one element  %

    (``,Const_name (`LIST`,[Var_children `cl`;Patt_child (Var_child `c`)]),
                                                              (\x y. true)),[],
       (PF_H [Nat 0,PO_constant `[`;
              Nat 0,PO_format
                       (PF_HoV
                          [(Nat 0,Abs 0,Nat 0),
                           PO_expand
                              (H_box [Nat 0,PO_subcall ((`cl`,(\l.l)),[]);
                                      Nat 0,PO_constant `;`
                                     ]);
                           (Nat 0,Abs 0,Nat 0),
                           PO_subcall ((`c`,(\l.l)),[])
                          ]);
              Nat 0,PO_constant `]`
             ]);

    %  Empty list  %

    (``,Const_name (`LIST`,[]),(\x y. true)),[],
       (PF_H [Nat 0,PO_constant `[]`]);

    %  Tuple  %

    (``,Print_loop
          (Const_name
              (`DUPL`,[Patt_child (Var_child `cl`);
                       Patt_child (Link_child (((Val (Nat 1)),Default),[]))
                      ]),
           Var_child `c`
          ),(\x y. true)),[],
       (PF_H [Nat 0,PO_constant `(`;
              Nat 0,PO_format
                       (PF_HV
                          [(Nat 0,Abs 0,Nat 0),
                           PO_expand (H_box [Nat 0,PO_subcall
                                                      ((`cl`,(\l.l)),[]);
                                             Nat 0,PO_constant `,`
                                            ]);
                           (Nat 0,Abs 0,Nat 0),
                           PO_subcall ((`c`,(\l.l)),[])
                          ]);
              Nat 0,PO_constant `)`
             ]);

    %  letrec ... and ...  %

    (``,Const_name
           (`LETREC`,
            [Patt_child
                (Const_name
                    (`DUPL`,
                     [Patt_child (Var_child `var1`);
                      Patt_child
                         (Print_loop
                             (Const_name
                                 (`DUPL`,
                                  [Patt_child (Var_child `varl`);
                                   Patt_child
                                      (Link_child ((Default,Default),[]))
                                  ]),
                              Var_child `varl`
                             ))
                     ]));
             Patt_child
                (Const_name
                    (`DUPL`,
                     [Patt_child (Var_child `body1`);
                      Patt_child
                         (Print_loop
                             (Const_name
                                 (`DUPL`,
                                  [Patt_child (Var_child `bodyl`);
                                   Patt_child
                                      (Link_child ((Default,Default),[]))
                                  ]),
                              Var_child `bodyl`
                             ))
                     ]))
            ]),(\x y. true)),[],
       (PF_V [(Abs 0,Nat 0),
              PO_format
                 (PF_HV [(Nat 1,Inc 1,Nat 0),PO_constant `letrec`;
                         (Nat 1,Inc 1,Nat 0),
                            PO_format
                               (PF_H [Nat 1,PO_subcall ((`var1`,(\l.l)),[]);
                                      Nat 1,PO_constant `=`
                                     ]);
                         (Nat 1,Inc 1,Nat 0),PO_subcall ((`body1`,(\l.l)),[])
                        ]);
              (Abs 0,Nat 0),
              PO_expand
                 (HV_box [(Nat 1,Inc 1,Nat 0),PO_constant `and`;
                          (Nat 1,Inc 1,Nat 0),
                             PO_expand
                                (H_box [Nat 1,PO_subcall ((`varl`,(\l.l)),[]);
                                        Nat 1,PO_constant `=`
                                       ]);
                          (Nat 1,Inc 1,Nat 0),PO_subcall ((`bodyl`,(\l.l)),[])
                         ])
             ]);

    %  letrec ...  %

    (``,Const_name (`LETREC`,[Patt_child (Var_child `c1`);
                              Patt_child (Var_child `c2`)]), (\x y. true)),[],
       (PF_HV [(Nat 1,Inc 1,Nat 0),PO_constant `letrec`;
               (Nat 1,Inc 1,Nat 0),
                  PO_format
                     (PF_H [Nat 1,PO_subcall ((`c1`,(\l.l)),[]);
                            Nat 1,PO_constant `=`
                           ]);
               (Nat 1,Inc 1,Nat 0),PO_subcall ((`c2`,(\l.l)),[])
              ]);

    %  Special block of ML code  %

    (``,Const_name (`ML_FUN`,[Var_children `cl`]), (\x y. true)),[],
       (PF_H [Nat 0,PO_constant `(`;
              Nat 0,
                 PO_format
                    (PF_V [(Abs 0,Nat 0),
                           PO_context_subcall (`name`,(`cl`,(\l.l)),[])
                          ]);
              Nat 0,PO_constant `)`
             ])
   ] : print_rule list;;


%  Print-rule function for above rules.  %

let PP_to_ML_rules_fun =

   % : (print_rule_function) %

   print_rule_fun PP_to_ML_rules;;


%  Write a list of strings to an output port, following all but the last  %
%  with a line-break.                                                     %

let write_strings f port sl =

   % : ((string # string -> void) -> string -> string list -> void) %

   letrec terminate_strings sl' =

      % : (string list -> string list) %

      if (null sl')
      then []
      else if (null (tl sl'))
           then [hd sl']
           else ((hd sl') ^ `\L`).(terminate_strings (tl sl'))

   in do (map (\s. f (port,s)) (terminate_strings sl));;


%  Function to generate a list of strings representing ML code from an ML  %
%  parse-tree for a print-rule. Uses the pretty-printing functions. The    %
%  function assumes an 80-column output. It indents the text by 4 spaces,  %
%  and leaves room for a semi-colon at the end of the text.                %
%  Debugging is active, so that system errors are reported. This is        %
%  controlled by the first argument to `print_box_to_strings'.             %

let generate_rule pt =

   % : (print_tree -> string list) %

   print_box_to_strings true 4
      (print_tree_to_box 78 4 PP_to_ML_rules_fun `` [] pt);;


%  Function to print an ML parse-tree for a print-rule.  %

let write_rule f port pt =

   % : ((string # string -> void) -> string -> print_tree -> void) %

   write_strings f port (generate_rule pt);;


%  Function to print a list of parse-trees derived from print-rules,  %
%  terminating all but the last with a semi-colon and a line-break.   %
%  The last rule is terminated only by a line-break.                  %

letrec write_rules f port ptl =

   % : ((string # string -> void) -> string -> print_tree list -> void) %

   if (null ptl)
   then failwith `write_rules`
   else if (null (tl ptl))
        then do (write_rule f port (hd ptl); f (port,`\L`))
        else do (write_rule f port (hd ptl);
                 f (port,`;`);
                 f (port,`\L`);
                 write_rules f port (tl ptl));;


%  Function to generate a list of strings representing ML code from an ML  %
%  parse-tree for declarations. Uses the pretty-printing functions. The    %
%  function assumes an 80-column output. It indents the text by 3 spaces.  %
%  Debugging is active, so that system errors are reported. This is        %
%  controlled by the first argument to `print_box_to_strings'.             %

let generate_declarations pt =

   % : (print_tree -> string list) %

   print_box_to_strings true 3
      (print_tree_to_box 79 3 PP_to_ML_rules_fun `` [] pt);;


%  Function to print an ML parse-tree for declarations.  %

let write_declarations f port pt =

   % : ((string # string -> void) -> string -> print_tree -> void) %

   do (write_strings f port (generate_declarations pt); f (port,`\L`));;


%  Generate beginning of ML declaration from name of pretty-printer.  %

let generate_head s =

   % : (string -> string list) %

   [``;
    `let `^s^`_rules =`;
    ``;
    `   % : (print_rule list) %`;
    `\L`
   ];;


%  Write beginning of ML declaration.  %

let write_head f port s =

   % : ((string # string -> void) -> string -> string -> void) %

   write_strings f port (generate_head s);;


%  Generate end of ML declaration from name of pretty-printer.  %

let generate_tail s =

   % : (string -> string list) %

   [`   ] : print_rule list;;`;
    ``;
    ``;
    `let `^s^`_rules_fun =`;
    ``;
    `   % : (print_rule_function) %`;
    ``;
    `   print_rule_fun `^s^`_rules;;`;
    `\L`
   ];;


%  Write end of ML declaration.  %

let write_tail f port s =

   % : ((string # string -> void) -> string -> string -> void) %

   write_strings f port (generate_tail s);;


%  Write the whole ML translation of a pretty-printer.  %

%  The parse-tree for the ML translation of the pretty-printer specification  %
%  is split into name of pretty-printer, declarations (if present), and       %
%  a list of rules. Each rule is processed seperately so as to avoid giving   %
%  the pretty-printer too large an amount to process.                         %

let generate_ML (f:(string # string) -> void) port pt =

   % : ((string # string -> void) -> string -> print_tree -> void) %

   case pt
   of (Print_node (`LET`,[Print_node (`VAR`,[Print_node (s,[])]);
                          Print_node (`LIST`,ptl)])) .
         (do (write_head f port s;
              f (port,`   [`); f (port,`\L`);
              write_rules f port ptl;
              write_tail f port s))
    | (Print_node (`LET`,[Print_node (`VAR`,[Print_node (s,[])]);
                          Print_node (`IN`,[pt1; Print_node (`LIST`,ptl)])])) .
         (do (write_head f port s;
              write_declarations f port pt1;
              f (port,`   in`); f (port,`\L`);
              f (port,`   [`); f (port,`\L`);
              write_rules f port ptl;
              write_tail f port s))
    | (_) . failwith `generate_ML`;;

generate_ML;;
end_section generate;;
let generate_ML = it;;

%-----------------------------------------------------------------------------%
