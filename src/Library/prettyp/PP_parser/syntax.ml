% syntax.ml                                                                   %
%-----------------------------------------------------------------------------%

begin_section syntax;;

%  The constant symbols of the pretty-printing language.  %

let PP_quotes = [`'`,`'`; `"`,`"`; `{`,`}`; `#`,`#`; `%`,`%`];;

let PP_keywords = [`prettyprinter`;`rules`;`declarations`;`abbreviations`;
                   `with`;`end`;`where`;`if`;`then`;`else`;
                   `h`;`v`;`hv`;`hov`];;

let PP_specials = [`+`;`-`;`*`;`**`;`***`;`,`;`;`;`:`;`::`;`=`;`:=`;`->`;`..`;
                   `(`;`)`;`**[`;`[`;`]`;`<`;`>`;`<<`;`>>`;`|`];;


%  Error handlers.  %

let syntax_error f port c exp x =

   % : ((string -> string) -> string -> string -> string -> lex_symb -> ?) %

   let got =
      case x
      of (Lex_spec s) . (`the special symbol \``^s^`'`)
       | (Lex_num s)  . (`the number \``^s^`'`)
       | (Lex_id s)   . (`the identifier \``^s^`'`)
       | (Lex_block ((start,end),sl)) . (start^(hd sl ? ``)^`...`^end)
   in  tty_write (`Syntax_error: expected `^exp^`, got `^got^` ...`^`\L`);
       tty_write c;
       copy_chars 200 f port tty_write;
       tty_write `\L`;
       tty_write (`... parse failed.`^`\L`);
       failwith `syntax_error`;;

let general_error f port c exp got =

   % : ((string -> string) -> string -> string -> string -> string -> ?) %

   tty_write (`Syntax error: expected `^exp^`, got `^got^` ...`^`\L`);
   tty_write c;
   copy_chars 200 f port tty_write;
   tty_write `\L`;
   tty_write (`... parse failed.`^`\L`);
   failwith `general_error`;;


%  Symbol reader for pretty-printing language.  %

%  A string enclosed within sharp signs (#) is made into an identifier,  %
%  provided it does not contain line-breaks.                             %

%  A string enclosed within percent signs is treated as a comment,       %
%  i.e. it is discarded.                                                 %

letrec read_PP_symb f port c =

   % : ((string -> string) -> string -> string -> (lex_symb # string)) %

   let (ls',c') = read_symb f port PP_quotes PP_keywords PP_specials c
   in  case ls'
       of (Lex_block ((`#`,`#`),sl)) .
             (if (length sl) = 1
              then (Lex_id (hd sl),c')
              else general_error f port c `\`#'` `a line break`)
        | (Lex_block ((`%`,`%`),_)) . (read_PP_symb f port c')
        | (_) . (ls',c');;


%  The remaining functions in this file all have the same form. They make up  %
%  a recursive descent parser for the pretty-printing language.               %

%  Each function has three arguments. The first two represent the input       %
%  port. When `f' is applied to `port' the next character is obtained.        %
%  The third argument is a pair. The first element of the pair is the next    %
%  symbol to be processed. The second element is the character immediately    %
%  following the symbol in the input.                                         %

%  The result of the function is a triple consisting of the parse-tree        %
%  built by the function, the next symbol to be processed, and the character  %
%  which follows the next symbol.                                             %


let read_PP_number f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_num s) .
         (Print_node (`NUM`,[Print_node (s,[])]), (read_PP_symb f port c))
    | (_) . (syntax_error f port c `a number` ls);;


let read_PP_integer f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `-`) .
         (let (pt,next) = read_PP_number f port (read_PP_symb f port c)
          in  (Print_node (`NEG`,[pt]), next))
    | (_) . (read_PP_number f port (ls,c));;


let read_PP_string f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_block ((`'`,`'`),[s])) .
         (Print_node (`STRING`,[Print_node (s,[])]), (read_PP_symb f port c))
    | (_) . (syntax_error f port c `a string` ls);;


let read_PP_terminal f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_block ((`"`,`"`),[s])) .
         (Print_node (`TERMINAL`,[Print_node (s,[])]), (read_PP_symb f port c))
    | (_) . (syntax_error f port c `a terminal` ls);;


let read_PP_ML_function f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_block ((`{`,`}`),sl)) .
         (Print_node (`ML_FUN`,map (\s. Print_node (s,[])) sl),
                                          (read_PP_symb f port c))
    | (_) . (syntax_error f port c `an ML function` ls);;


letrec read_PP_identifier f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_id s) .
         (Print_node (`ID`,[Print_node (s,[])]), (read_PP_symb f port c))
    | (_) . (syntax_error f port c `an identifier` ls);;


let read_PP_name_metavar f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `***`) .
         (case (read_PP_symb f port c)
          of (Lex_id s,c') .
                (let (pt,next) = read_PP_identifier f port (Lex_id s,c')
                 in (Print_node (`NAME_META`,[pt]), next))
           | (next) . (Print_node (`NAME_META`,[]), next))
    | (_) . (syntax_error f port c `\`***'` ls);;


let read_PP_child_metavar f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `*`) .
         (case (read_PP_symb f port c)
          of (Lex_id s,c') .
                (let (pt,next) = read_PP_identifier f port (Lex_id s,c')
                 in (Print_node (`CHILD_META`,[pt]), next))
           | (next) . (Print_node (`CHILD_META`,[]), next))
    | (_) . (syntax_error f port c `\`*'` ls);;


let read_PP_children_metavar f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `**`) .
         (case (read_PP_symb f port c)
          of (Lex_id s,c') .
                (let (pt,next) = read_PP_identifier f port (Lex_id s,c')
                 in (Print_node (`CHILDREN_META`,[pt]), next))
           | (next) . (Print_node (`CHILDREN_META`,[]), next))
    | (_) . (syntax_error f port c `\`**'` ls);;


letrec read_PP_metavar_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') =
      case ls
      of (Lex_spec `*`) . (read_PP_child_metavar f port (ls,c))
       | (Lex_spec `**`) . (read_PP_children_metavar f port (ls,c))
       | (Lex_spec `***`) . (read_PP_name_metavar f port (ls,c))
       | (_) . (syntax_error f port c `a metavariable` ls)
   in  case ls'
       of (Lex_spec `;`) .
             (let (pt',next) = read_PP_metavar_list f port
                                  (read_PP_symb f port c')
              in  (Print_node (`METAVAR_LIST`,[pt;pt']), next))
        | (_) . (Print_node (`METAVAR_LIST`,[pt]), ls',c');;


let read_PP_min f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) = read_PP_number f port (ls,c)
   in  (Print_node (`MIN`,[pt]), next);;


let read_PP_max f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) = read_PP_number f port (ls,c)
   in  (Print_node (`MAX`,[pt]), next);;


let read_PP_loop_range f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `..`) .
         (let (pt,next) = read_PP_max f port (read_PP_symb f port c)
          in  (Print_node (`LOOP_RANGE`,[pt]), next))
    | (_) .
         (let (pt,ls',c') = read_PP_min f port (ls,c)
          in  case ls'
              of (Lex_spec `..`) .
                    (let (ls'',c'') = read_PP_symb f port c'
                     in  case ls''
                         of (Lex_num _) .
                               (let (pt',next) = read_PP_max f port (ls'',c'')
                                in  (Print_node (`LOOP_RANGE`,[pt;pt']), next))
                          | (_) . (Print_node (`LOOP_RANGE`,[pt]), ls'',c''))
               | (_) . (syntax_error f port c' `\`..'` ls'));;


let read_PP_loop_link f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `<`) .
         (let (ls',c') = read_PP_symb f port c
          in  case ls'
              of (Lex_spec `>`) .
                    (Print_node (`LOOP_LINK`,[]), (read_PP_symb f port c'))
               | (Lex_num _) .
                    (let (pt,ls'',c'') = read_PP_loop_range f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (Print_node (`LOOP_LINK`,[pt]),
                                   (read_PP_symb f port c''))
                          | (Lex_spec `:`) .
                               (let (pt',ls''',c''') =
                                   read_PP_metavar_list f port
                                      (read_PP_symb f port c'')
                                in  case ls'''
                                    of (Lex_spec `>`) .
                                          (Print_node (`LOOP_LINK`,[pt;pt']),
                                              (read_PP_symb f port c'''))
                                     | (_) . (syntax_error f port c'''
                                                            `\`>'` ls'''))
                          | (_) . (syntax_error f port c''
                                         `\`>' or \`:'` ls''))
               | (Lex_spec `..`) .
                    (let (pt,ls'',c'') = read_PP_loop_range f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (Print_node (`LOOP_LINK`,[pt]),
                                   (read_PP_symb f port c''))
                          | (Lex_spec `:`) .
                               (let (pt',ls''',c''') =
                                   read_PP_metavar_list f port
                                      (read_PP_symb f port c'')
                                in  case ls'''
                                    of (Lex_spec `>`) .
                                          (Print_node (`LOOP_LINK`,[pt;pt']),
                                              (read_PP_symb f port c'''))
                                     | (_) . (syntax_error f port c'''
                                                            `\`>'` ls'''))
                          | (_) . (syntax_error f port c''
                                         `\`>' or \`:'` ls''))
               | (_) .
                    (let (pt,ls'',c'') =
                            read_PP_metavar_list f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (Print_node (`LOOP_LINK`,[pt]),
                                   (read_PP_symb f port c''))
                          | (_) . (syntax_error f port c'' `\`>'` ls'')))
    | (_) . (syntax_error f port c `\`<'` ls);;


let read_PP_label f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `|`) .
         (let (pt,ls',c') =
             read_PP_child_metavar f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `|`) .
                    (Print_node (`LABEL`,[pt]), (read_PP_symb f port c'))
               | (_) . (syntax_error f port c' `\`|'` ls'))
    | (_) . (syntax_error f port c `\`|'` ls);;


let read_PP_node_name f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) =
      case ls
      of (Lex_spec `***`) . (read_PP_name_metavar f port (ls,c))
       | (_) . (read_PP_identifier f port (ls,c))
   in  (Print_node (`NODE_NAME`,[pt]), next);;


letrec read_PP_child f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `**`) .
         (let (pt,next) = read_PP_children_metavar f port (ls,c)
          in  (Print_node (`CHILD`,[pt]),next))
    | (_) .
         (let (pt,next) = read_PP_pattern_tree f port (ls,c)
          in  (Print_node (`CHILD`,[pt]),next))

and read_PP_child_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_child f port (ls,c)
   in  case ls'
       of (Lex_spec `,`) .
             (let (pt',next) = read_PP_child_list f port
                                  (read_PP_symb f port c')
              in  (Print_node (`CHILD_LIST`,[pt;pt']), next))
        | (_) . (Print_node (`CHILD_LIST`,[pt]), ls',c')

and read_PP_pattern_tree f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   if ((ls = (Lex_spec `[`)) or (ls = (Lex_spec `<`))) then
         (let (pt,ls',c') =
             case ls
             of (Lex_spec `[`) . (read_PP_loop f port (ls,c))
              | (_) . (read_PP_loop_link f port (ls,c))
          in  case ls'
              of (Lex_spec `]`) .
                    (Print_node (`PATT_TREE`,[pt]), ls',c')
               | (Lex_spec `,`) .
                    (Print_node (`PATT_TREE`,[pt]), ls',c')
               | (Lex_spec `)`) .
                    (Print_node (`PATT_TREE`,[pt]), ls',c')
               | (Lex_spec `->`) .
                    (Print_node (`PATT_TREE`,[pt]), ls',c')
               | (Lex_spec `where`) .
                    (Print_node (`PATT_TREE`,[pt]), ls',c')
               | (_) .
                    (let (pt',next) = read_PP_pattern_tree f port (ls',c')
                     in  (Print_node (`PATT_TREE`,[pt;pt']),next)))
   if (ls = (Lex_spec `|`)) then
         (let (pt,ls',c') = read_PP_label f port (ls,c)
          in  let (pt',next) = read_PP_pattern_tree f port (ls',c')
              in  (Print_node (`PATT_TREE`,[pt;pt']), next))
   if (ls = (Lex_spec `*`)) then
         (let (pt,next) = read_PP_child_metavar f port (ls,c)
          in  (Print_node (`PATT_TREE`,[pt]), next))
   else (let (pt,ls',c') = read_PP_node_name f port (ls,c)
         in  case ls'
             of (Lex_spec `(`) .
                   (let (ls'',c'') = read_PP_symb f port c'
                    in  case ls''
                        of (Lex_spec `)`) .
                              (Print_node (`PATT_TREE`,[pt]),
                                  (read_PP_symb f port c''))
                         | (_) .
                              (let (pt',ls''',c''') =
                                      read_PP_child_list f port (ls'',c'')
                               in  case ls'''
                                   of (Lex_spec `)`) .
                                         (Print_node (`PATT_TREE`,[pt;pt']),
                                             (read_PP_symb f port c'''))
                                    | (_) . (syntax_error f port c'''
                                                           `\`)'` ls''')))
              | (_) . (syntax_error f port c' `\`('` ls'))

and read_PP_loop f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `[`) .
         (let (pt,ls',c') =
                 read_PP_pattern_tree f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `]`) .
                    (Print_node (`LOOP`,[pt]), (read_PP_symb f port c'))
               | (_) . (syntax_error f port c' `\`]'` ls'))
    | (_) . (syntax_error f port c `\`['` ls);;


let read_PP_test f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) =
      case ls
      of (Lex_block ((`{`,`}`),_)) . (read_PP_ML_function f port (ls,c))
       | (_) . (read_PP_identifier f port (ls,c))
   in  (Print_node (`TEST`,[pt]),next);;


let read_PP_pattern f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_string f port (ls,c)
   in  case ls'
       of (Lex_spec `::`) .
             (let (pt',ls'',c'') = read_PP_pattern_tree f port
                                         (read_PP_symb f port c')
              in  case ls''
                  of (Lex_spec `where`) .
                        (let (pt'',next) = read_PP_test f port
                                              (read_PP_symb f port c'')
                         in  (Print_node (`PATTERN`,[pt;pt';pt'']),next))
                   | (_) . (Print_node (`PATTERN`,[pt;pt']), ls'',c''))
        | (_) . (syntax_error f port c' `\`::'` ls');;


let read_PP_transformation f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) =
      case ls
      of (Lex_block ((`{`,`}`),_)) . (read_PP_ML_function f port (ls,c))
       | (_) . (read_PP_identifier f port (ls,c))
   in  (Print_node (`TRANSFORM`,[pt]),next);;


let read_PP_p_special f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') =
      case ls
      of (Lex_spec `*`) . (read_PP_child_metavar f port (ls,c))
       | (Lex_spec `**`) . (read_PP_children_metavar f port (ls,c))
       | (Lex_spec `***`) . (read_PP_name_metavar f port (ls,c))
       | (_) . (syntax_error f port c `a metavariable` ls)
   in  case ls'
       of (Lex_spec `=`) .
             (let (pt',next) = read_PP_transformation f port
                                       (read_PP_symb f port c')
              in  (Print_node (`P_SPECIAL`,[pt;pt']), next))
        | (_) . (syntax_error f port c `\`='` ls');;


letrec read_PP_p_special_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_p_special f port (ls,c)
   in  case ls'
       of (Lex_spec `;`) .
             (let (pt',next) = read_PP_p_special_list f port
                                       (read_PP_symb f port c')
              in  (Print_node (`P_SPECIAL_LIST`,[pt;pt']), next))
        | (_) . (Print_node (`P_SPECIAL_LIST`,[pt]), ls',c');;


let read_PP_int_expression f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) =
      case ls
      of (Lex_block ((`{`,`}`),_)) . (read_PP_ML_function f port (ls,c))
       | (Lex_id _) . (read_PP_identifier f port (ls,c))
       | (_) . (read_PP_integer f port (ls,c))
   in  (Print_node (`INT_EXP`,[pt]),next);;


let read_PP_assignment f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_identifier f port (ls,c)
   in  case ls'
       of (Lex_spec `:=`) .
             (let (pt',next) =
                     read_PP_int_expression f port (read_PP_symb f port c')
              in  (Print_node (`ASSIGN`,[pt;pt']),next))
        | (_) . (syntax_error f port c' `\`:='` ls');;


letrec read_PP_assignments f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_assignment f port (ls,c)
   in  case ls'
       of (Lex_spec `;`) .
             (let (pt',next) = read_PP_assignments f port
                                  (read_PP_symb f port c')
              in  (Print_node (`ASSIGNMENTS`,[pt;pt']), next))
        | (_) . (Print_node (`ASSIGNMENTS`,[pt]), ls',c');;


let read_PP_fun_subcall f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `***`) .
         (let (pt,next) = read_PP_name_metavar f port (ls,c)
          in  (Print_node (`F_SUBCALL`,[pt]),next))
    | (Lex_spec `*`) .
         (let (pt,next) = read_PP_child_metavar f port (ls,c)
          in  (Print_node (`F_SUBCALL`,[pt]),next))
    | (Lex_spec `**`) .
         (let (pt,next) = read_PP_children_metavar f port (ls,c)
          in  (Print_node (`F_SUBCALL`,[pt]),next))
    | (_) .
         (let (pt,ls',c') = read_PP_transformation f port (ls,c)
          in  case ls'
              of (Lex_spec `(`) .
                    (let (ls'',c'') = read_PP_symb f port c'
                     in  case ls''
                         of (Lex_spec `***`) .
                               (let (pt',ls''',c''') =
                                       read_PP_name_metavar f port (ls'',c'')
                                in  case ls'''
                                    of (Lex_spec `)`) .
                                          (Print_node (`F_SUBCALL`,[pt;pt']),
                                              (read_PP_symb f port c'''))
                                     | (_) . (syntax_error f port c'''
                                                            `\`)'` ls'''))
                          | (Lex_spec `*`) .
                               (let (pt',ls''',c''') =
                                       read_PP_child_metavar f port (ls'',c'')
                                in  case ls'''
                                    of (Lex_spec `)`) .
                                          (Print_node (`F_SUBCALL`,[pt;pt']),
                                              (read_PP_symb f port c'''))
                                     | (_) . (syntax_error f port c'''
                                                            `\`)'` ls'''))
                          | (Lex_spec `**`) .
                               (let (pt',ls''',c''') =
                                     read_PP_children_metavar f port (ls'',c'')
                                in  case ls'''
                                    of (Lex_spec `)`) .
                                          (Print_node (`F_SUBCALL`,[pt;pt']),
                                              (read_PP_symb f port c'''))
                                     | (_) . (syntax_error f port c'''
                                                            `\`)'` ls'''))
                          | (_) . (syntax_error f port c''
                                       `a metavariable` ls''))
               | (_) . (syntax_error f port c' `\`('` ls'));;


let read_PP_context_subcall f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_block ((`'`,`'`),_)) .
         (let (pt,ls',c') = read_PP_string f port (ls,c)
          in  case ls'
              of (Lex_spec `::`) .
                    (let (pt',next) = read_PP_fun_subcall f port
                                           (read_PP_symb f port c')
                     in  (Print_node (`C_SUBCALL`,[pt;pt']),next))
               | (_) . (syntax_error f port c' `\`::'` ls'))
    | (_) .
         (let (pt,next) = read_PP_fun_subcall f port (ls,c)
          in  (Print_node (`C_SUBCALL`,[pt]),next));;


let read_PP_leaf_or_subcall f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_context_subcall f port (ls,c)
   in  case ls'
       of (Lex_spec `with`) .
             (let (pt',ls'',c'') = read_PP_assignments f port
                                        (read_PP_symb f port c')
              in  case ls''
                  of (Lex_spec `end`) .
                        (let (ls''',c''') = read_PP_symb f port c''
                         in  case ls'''
                             of (Lex_spec `with`) .
                                   (Print_node (`LEAF_OR_SUBCALL`,[pt;pt']),
                                            (read_PP_symb f port c'''))
                              | (_) . (syntax_error f port c''' `with` ls'''))
                   | (_) . (syntax_error f port c'' `end with` ls''))
        | (_) . (Print_node (`LEAF_OR_SUBCALL`,[pt]), ls',c');;


let read_PP_indent f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `+`) .
         (let (pt,next) = read_PP_integer f port (read_PP_symb f port c)
          in  (Print_node (`INC`,[pt]), next))
    | (_) . (read_PP_integer f port (ls,c));;


let read_PP_h_params f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) = read_PP_number f port (ls,c)
   in  (Print_node (`H_PARAMS`,[pt]),next);;


let read_PP_v_params f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_indent f port (ls,c)
   in  case ls'
       of (Lex_spec `,`) .
             (let (pt',next) = read_PP_number f port (read_PP_symb f port c')
              in  (Print_node (`V_PARAMS`,[pt;pt']),next))
        | (_) . (syntax_error f port c' `\`,'` ls');;


let read_PP_hv_params f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_number f port (ls,c)
   in  case ls'
       of (Lex_spec `,`) .
             (let (pt',ls'',c'') =
                     read_PP_indent f port (read_PP_symb f port c')
              in  case ls''
                  of (Lex_spec `,`) .
                        (let (pt'',next) =
                                read_PP_number f port (read_PP_symb f port c'')
                         in  (Print_node (`HV_PARAMS`,[pt;pt';pt'']),next))
                   | (_) . (syntax_error f port c'' `\`,'` ls''))
        | (_) . (syntax_error f port c' `\`,'` ls');;


let read_PP_hov_params f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_number f port (ls,c)
   in  case ls'
       of (Lex_spec `,`) .
             (let (pt',ls'',c'') =
                     read_PP_indent f port (read_PP_symb f port c')
              in  case ls''
                  of (Lex_spec `,`) .
                        (let (pt'',next) =
                                read_PP_number f port (read_PP_symb f port c'')
                         in  (Print_node (`HOV_PARAMS`,[pt;pt';pt'']),next))
                   | (_) . (syntax_error f port c'' `\`,'` ls''))
        | (_) . (syntax_error f port c' `\`,'` ls');;


let read_PP_h_box f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `h`) .
         (let (pt,next) = read_PP_h_params f port (read_PP_symb f port c)
          in  (Print_node (`H_BOX`,[pt]),next))
    | (_) . (syntax_error f port c `\`h'` ls);;


let read_PP_v_box f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `v`) .
         (let (pt,next) = read_PP_v_params f port (read_PP_symb f port c)
          in  (Print_node (`V_BOX`,[pt]),next))
    | (_) . (syntax_error f port c `\`v'` ls);;


let read_PP_hv_box f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `hv`) .
         (let (pt,next) = read_PP_hv_params f port (read_PP_symb f port c)
          in  (Print_node (`HV_BOX`,[pt]),next))
    | (_) . (syntax_error f port c `\`hv'` ls);;


let read_PP_hov_box f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `hov`) .
         (let (pt,next) = read_PP_hov_params f port (read_PP_symb f port c)
          in  (Print_node (`HOV_BOX`,[pt]),next))
    | (_) . (syntax_error f port c `\`hov'` ls);;


letrec read_PP_object f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,next) =
      case ls
      of (Lex_spec `if`)           . (read_PP_format f port (ls,c))
       | (Lex_spec `[`)            . (read_PP_format f port (ls,c))
       | (Lex_spec `**[`)          . (read_PP_expand f port (ls,c))
       | (Lex_block ((`"`,`"`),_)) . (read_PP_terminal f port (ls,c))
       | (Lex_block ((`'`,`'`),_)) . (read_PP_leaf_or_subcall f port (ls,c))
       | (_)                       . (read_PP_leaf_or_subcall f port (ls,c))
   in  (Print_node (`OBJECT`,[pt]),next)

and read_PP_h_object f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `<`) .
         (let (pt,ls',c') = read_PP_h_params f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `>`) .
                    (let (pt',next) =
                            read_PP_object f port (read_PP_symb f port c')
                     in  (Print_node (`H_OBJECT`,[pt;pt']),next))
               | (_) . (syntax_error f port c' `\`>'` ls'))
    | (_) .
         (let (pt,next) = read_PP_object f port (ls,c)
          in  (Print_node (`H_OBJECT`,[pt]),next))

and read_PP_v_object f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `<`) .
         (let (pt,ls',c') = read_PP_v_params f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `>`) .
                    (let (pt',next) =
                            read_PP_object f port (read_PP_symb f port c')
                     in  (Print_node (`V_OBJECT`,[pt;pt']),next))
               | (_) . (syntax_error f port c' `\`>'` ls'))
    | (_) .
         (let (pt,next) = read_PP_object f port (ls,c)
          in  (Print_node (`V_OBJECT`,[pt]),next))

and read_PP_hv_object f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `<`) .
         (let (pt,ls',c') = read_PP_hv_params f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `>`) .
                    (let (pt',next) =
                            read_PP_object f port (read_PP_symb f port c')
                     in  (Print_node (`HV_OBJECT`,[pt;pt']),next))
               | (_) . (syntax_error f port c' `\`>'` ls'))
    | (_) .
         (let (pt,next) = read_PP_object f port (ls,c)
          in  (Print_node (`HV_OBJECT`,[pt]),next))

and read_PP_hov_object f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `<`) .
         (let (pt,ls',c') = read_PP_hov_params f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `>`) .
                    (let (pt',next) =
                            read_PP_object f port (read_PP_symb f port c')
                     in  (Print_node (`HOV_OBJECT`,[pt;pt']),next))
               | (_) . (syntax_error f port c' `\`>'` ls'))
    | (_) .
         (let (pt,next) = read_PP_object f port (ls,c)
          in  (Print_node (`HOV_OBJECT`,[pt]),next))

and read_PP_h_object_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_h_object f port (ls,c)
   in  case ls'
       of (Lex_spec `]`) .
             (Print_node (`H_OBJECT_LIST`,[pt]), ls',c')
        | (_) .
             (let (pt',ls'',c'') = read_PP_h_object_list f port (ls',c')
              in  (Print_node (`H_OBJECT_LIST`,[pt;pt']), ls'',c''))

and read_PP_v_object_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_v_object f port (ls,c)
   in  case ls'
       of (Lex_spec `]`) .
             (Print_node (`V_OBJECT_LIST`,[pt]), ls',c')
        | (_) .
             (let (pt',ls'',c'') = read_PP_v_object_list f port (ls',c')
              in  (Print_node (`V_OBJECT_LIST`,[pt;pt']), ls'',c''))

and read_PP_hv_object_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_hv_object f port (ls,c)
   in  case ls'
       of (Lex_spec `]`) .
             (Print_node (`HV_OBJECT_LIST`,[pt]), ls',c')
        | (_) .
             (let (pt',ls'',c'') = read_PP_hv_object_list f port (ls',c')
              in  (Print_node (`HV_OBJECT_LIST`,[pt;pt']), ls'',c''))

and read_PP_hov_object_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_hov_object f port (ls,c)
   in  case ls'
       of (Lex_spec `]`) .
             (Print_node (`HOV_OBJECT_LIST`,[pt]), ls',c')
        | (_) .
             (let (pt',ls'',c'') = read_PP_hov_object_list f port (ls',c')
              in  (Print_node (`HOV_OBJECT_LIST`,[pt;pt']), ls'',c''))

and read_PP_box_spec f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `<`) .
         (let (ls',c') = read_PP_symb f port c
          in  case ls'
              of (Lex_spec `h`) .
                    (let (pt,ls'',c'') = read_PP_h_box f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (let (pt',next) = read_PP_h_object_list f port
                                                      (read_PP_symb f port c'')
                                in  (Print_node (`BOX_SPEC`,[pt;pt']),next))
                          | (_) . (syntax_error f port c'' `\`>'` ls''))
               | (Lex_spec `v`) .
                    (let (pt,ls'',c'') = read_PP_v_box f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (let (pt',next) = read_PP_v_object_list f port
                                                      (read_PP_symb f port c'')
                                in  (Print_node (`BOX_SPEC`,[pt;pt']),next))
                          | (_) . (syntax_error f port c'' `\`>'` ls''))
               | (Lex_spec `hv`) .
                    (let (pt,ls'',c'') = read_PP_hv_box f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (let (pt',next) = read_PP_hv_object_list f port
                                                      (read_PP_symb f port c'')
                                in  (Print_node (`BOX_SPEC`,[pt;pt']),next))
                          | (_) . (syntax_error f port c'' `\`>'` ls''))
               | (Lex_spec `hov`) .
                    (let (pt,ls'',c'') = read_PP_hov_box f port (ls',c')
                     in  case ls''
                         of (Lex_spec `>`) .
                               (let (pt',next) = read_PP_hov_object_list f port
                                                      (read_PP_symb f port c'')
                                in  (Print_node (`BOX_SPEC`,[pt;pt']),next))
                          | (_) . (syntax_error f port c'' `\`>'` ls''))
               | (_) . (syntax_error f port c' `a box type` ls'))
    | (_) . (syntax_error f port c `\`<'` ls)

and read_PP_expand f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `**[`) .
         (let (pt,ls',c') = read_PP_box_spec f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `]`) .
                    (Print_node (`EXPAND`,[pt]), (read_PP_symb f port c'))
               | (_) . (syntax_error f port c' `\`]'` ls'))
    | (_) . (syntax_error f port c `\`**['` ls)

and read_PP_format f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `[`) .
         (let (ls',c') = read_PP_symb f port c
          in case ls'
             of (Lex_spec `]`) . (Print_node (`FORMAT`,[]),
                                     (read_PP_symb f port c'))
              | (_) .
                   (let (pt,ls'',c'') = read_PP_box_spec f port (ls',c')
                    in  case ls''
                        of (Lex_spec `]`) .
                              (Print_node (`FORMAT`,[pt]),
                                    (read_PP_symb f port c''))
                         | (_) . (syntax_error f port c'' `\`]'` ls'')))
    | (Lex_spec `if`) .
         (let (pt,ls',c') = read_PP_test f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `then`) .
                    (let (pt',ls'',c'') = read_PP_format f port
                                             (read_PP_symb f port c')
                     in  case ls''
                         of (Lex_spec `else`) .
                               (let (pt'',next) = read_PP_format f port
                                                     (read_PP_symb f port c'')
                                in (Print_node (`FORMAT`,[pt;pt';pt'']),next))
                          | (_) . (syntax_error f port c'' `\`else'` ls''))
               | (_) . (syntax_error f port c' `\`then'` ls'))
    | (_) . (syntax_error f port c `a format` ls);;


let read_PP_rule f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_pattern f port (ls,c)
   in  case ls'
       of (Lex_spec `->`) .
             (let (ls'',c'') = read_PP_symb f port c'
              in  case ls''
                  of (Lex_spec `<<`) .
                        (let (pt',ls''',c''') =
                                read_PP_p_special_list f port
                                       (read_PP_symb f port c'')
                         in  case ls'''
                             of (Lex_spec `>>`) .
                                   (let (pt'',next) =
                                           read_PP_format f port
                                              (read_PP_symb f port c''')
                                    in  (Print_node (`RULE`,[pt;pt';pt'']),
                                                                        next))
                              | (_) . (syntax_error f port c''' `\`>>'` ls'''))
                   | (_) .
                        (let (pt',next) = read_PP_format f port (ls'',c'')
                         in  (Print_node (`RULE`,[pt;pt']),next)))
        | (_) . (syntax_error f port c' `\`->'` ls');;


letrec read_PP_rule_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_rule f port (ls,c)
   in  case ls'
       of (Lex_spec `;`) .
             (let (ls'',c'') = read_PP_symb f port c'
              in  case ls''
                  of (Lex_spec `end`) .
                        (Print_node (`RULE_LIST`,[pt]), ls'',c'')
                   | (_) .
                        (let (pt',ls''',c''') =
                                read_PP_rule_list f port (ls'',c'')
                         in  (Print_node (`RULE_LIST`,[pt;pt']), ls''',c''')))
        | (_) . (syntax_error f port c' `\`;'` ls');;


let read_PP_rules f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `rules`) .
         (let (pt,ls',c') = read_PP_rule_list f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `end`) .
                    (let (ls'',c'') = read_PP_symb f port c'
                     in  case ls''
                         of (Lex_spec `rules`) .
                               (Print_node (`RULES`,[pt]),
                                     read_PP_symb f port c'')
                          | (_) . (syntax_error f port c''
                                      `the keyword \`rules'` ls''))
               | (_) . (syntax_error f port c'
                           `the keywords \`end rules'` ls'))
    | (_) . (syntax_error f port c `the keyword \`rules'` ls);;


let read_PP_binding f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_identifier f port (ls,c)
   in  case ls'
       of (Lex_spec `=`) .
             (let (pt',next) =
                     read_PP_ML_function f port (read_PP_symb f port c')
              in  (Print_node (`BINDING`,[pt;pt']),next))
        | (_) . (syntax_error f port c' `\`='` ls');;


letrec read_PP_binding_list f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   let (pt,ls',c') = read_PP_binding f port (ls,c)
   in  case ls'
       of (Lex_spec `;`) .
             (let (ls'',c'') = read_PP_symb f port c'
              in  case ls''
                  of (Lex_spec `end`) .
                        (Print_node (`BINDING_LIST`,[pt]), ls'',c'')
                   | (_) .
                        (let (pt',next) =
                                read_PP_binding_list f port (ls'',c'')
                         in  (Print_node (`BINDING_LIST`,[pt;pt']),next)))
        | (_) . (syntax_error f port c' `\`;'` ls');;


let read_PP_declarations f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `declarations`) .
         (let (pt,ls',c') = read_PP_binding_list f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `end`) .
                    (let (ls'',c'') = read_PP_symb f port c'
                     in  case ls''
                         of (Lex_spec `declarations`) .
                               (Print_node (`DECLARS`,[pt]),
                                       read_PP_symb f port c'')
                          | (_) . (syntax_error f port c''
                                      `the keyword \`declarations'`
                                                                         ls''))
               | (_) . (syntax_error f port c'
                           `the keywords \`end declarations'` ls'))
    | (_) . (syntax_error f port c `the keyword \`declarations'` ls);;


let read_PP_abbreviations f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `abbreviations`) .
         (let (pt,ls',c') = read_PP_binding_list f port (read_PP_symb f port c)
          in  case ls'
              of (Lex_spec `end`) .
                    (let (ls'',c'') = read_PP_symb f port c'
                     in  case ls''
                         of (Lex_spec `abbreviations`) .
                               (Print_node (`ABBREVS`,[pt]),
                                       read_PP_symb f port c'')
                          | (_) . (syntax_error f port c''
                                      `the keyword \`abbreviations'`
                                                                         ls''))
               | (_) . (syntax_error f port c'
                           `the keywords \`end abbreviations'` ls'))
    | (_) . (syntax_error f port c `the keyword \`abbreviations'` ls);;


let read_PP_body f port (ls,c) =

   % : ((string -> string) -> string -> (lex_symb # string) ->    %
   %                            (print_tree # lex_symb # string)) %

   case ls
   of (Lex_spec `declarations`) .
         (let (pt,ls',c') = read_PP_declarations f port (ls,c)
          in  case ls'
              of (Lex_spec `abbreviations`) .
                    (let (pt',ls'',c'') = read_PP_abbreviations f port (ls',c')
                     in  let (pt'',next) = read_PP_rules f port (ls'',c'')
                         in  (Print_node (`BODY`,[pt;pt';pt'']),next))
               | (_) .
                    (let (pt',next) = read_PP_rules f port (ls',c')
                     in  (Print_node (`BODY`,[pt;pt']),next)))
    | (Lex_spec `abbreviations`) .
         (let (pt,ls',c') = read_PP_abbreviations f port (ls,c)
          in  let (pt',next) = read_PP_rules f port (ls',c')
              in  (Print_node (`BODY`,[pt;pt']),next))
    | (_) .
         (let (pt,next) = read_PP_rules f port (ls,c)
          in  (Print_node (`BODY`,[pt]),next));;


%  `read_PP' differs from the preceding functions. It is the top-level       %
%  parsing function, and so does not require a next symbol and next          %
%  character on input. It also does not need to provide them as part of the  %
%  result. Note that if the terminating keyword `prettyprinter' in the       %
%  source file is not followed by at least one character, the parser will    %
%  think that the input was exhausted before completion, due to it reading   %
%  a character for lookahead.                                                %

let read_PP f (port:string) =

   % : ((string -> string) -> string -> print_tree) %

   let (ls,c) = read_PP_symb f port ` `
   in  case ls
       of (Lex_spec `prettyprinter`) .
             (let (pt,ls',c') = read_PP_identifier f port
                                   (read_PP_symb f port c)
              in  case ls'
                  of (Lex_spec `=`) .
                        (let (pt',ls'',c'') = read_PP_body f port
                                                 (read_PP_symb f port c')
                         in  case ls''
                             of (Lex_spec `end`) .
                                   (let (ls''',c''') = read_PP_symb f port c''
                                    in  case ls'''
                                        of (Lex_spec `prettyprinter`) .
                                              (Print_node (`PP`,[pt;pt']))
                                         | (_) .
                                              (syntax_error f port c'''
                                                 `the keyword \`prettyprinter'`
                                                                        ls'''))
                              | (_) .
                                   (syntax_error f port c''
                                       `the keywords \`end prettyprinter'`
                                                                         ls''))
                   | (_) . (syntax_error f port c' `\`='` ls'))
        | (_) . (syntax_error f port c `the keyword \`prettyprinter'` ls);;

read_PP;;
end_section syntax;;
let read_PP = it;;

%-----------------------------------------------------------------------------%
