% convert.ml                                                                  %
%-----------------------------------------------------------------------------%

begin_section convert;;

%  Error handler.  %

%  This uses the pretty-printer to print the parse-tree on which the  %
%  conversion failed.                                                 %

let construction_error pt s =

   % : (print_tree -> string -> ?) %

   tty_write (`Error: `^s^` ...`^`\L`);
   pretty_print (get_margin ()) 0
      (pp_lang1_rules_fun then_try pp_lang2_rules_fun) `` [] pt;
   tty_write (`... parse failed.`^`\L`);
   failwith `construction_error`;;


%  Function to convert a string into the string which if enclosed within ML   %
%  string quotes and read into ML, would yield the original string as value.  %

%  A backslash is inserted before occurrences of backquote and also before    %
%  occurrences of backslash itself.                                           %

let indirect_string s =

   % : (string -> string) %

   letrec indirect_string' sl =

      % : (string list -> string list) %

      if (null sl)
      then []
      else if ((hd sl) = `\``)
           then `\\`.`\``.(indirect_string' (tl sl))
           else if ((hd sl) = `\\`)
                then `\\`.`\\`.(indirect_string' (tl sl))
                else (hd sl).(indirect_string' (tl sl))

   in (implode o indirect_string' o explode) s;;


%  The following functions are all of the same type. They output a value of   %
%  the same type as their argument. This consists of a pair. The first        %
%  element of the pair is a parse-tree. On input it is a parse-tree for the   %
%  pretty-printing language. On output it is a parse-tree for the             %
%  corresponding ML data structure.                                           %

%  The second element of the pair is an association list of names to          %
%  parse-trees. In most cases the information in the parse-tree for the       %
%  pretty-printing language is precisely the information required for the ML  %
%  parse-tree, no more, no less. However, this is not always the case, and    %
%  the association list allows sub-trees to be moved up or down the tree, so  %
%  that information can be moved around.                                      %

%  The conversion functions which do not make sub-calls return an empty       %
%  association list (unless they generate something themselves). If they      %
%  were to bounce the association list they are given, back up the tree, the  %
%  association list could grow enormously due to repetitions. This is         %
%  because other functions append together the association lists they get     %
%  from their sub-calls, and pass the appended list back up to their caller.  %

let convert_NUM (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`NUM`,ptl)) . (Print_node (`INTCONST`,ptl), [])
    | (_) . failwith `convert_NUM`;;


let convert_NEG (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`NEG`,[pt1])) .
         (let (pt1',sptl1) = convert_NUM (pt1,sptl)
          in  (Print_node (`UNOP`,[Print_node (`-`,[]); pt1']), sptl1))
    | (_) . failwith `convert_NEG`;;


%  `convert_ML_FUN' processes the list of strings representing a block of ML  %
%  code that is to be copied from the source file to the destination file.    %
%  The text is to appear neatly in the generated ML code. When there is only  %
%  one line in the text block, the conversion is easy. Space is trimmed from  %
%  the beginning and the end of the string.                                   %

%  If the block extends over more than one line, the first line must be       %
%  blank, so that the vertical alignment of the text in the source file can   %
%  be deduced. If this condition is satisfied, the first line is discarded,   %
%  and trailing blanks are removed from all of the other lines. Any blank     %
%  lines will now be empty strings. The smallest number of leading blanks in  %
%  those strings which are not empty is computed, and this amount of space    %
%  is removed from the beginning of all the strings which are not blank.      %
%  This process retains the vertical alignment of the text, but removes dead  %
%  space to the left of the block.                                            %

let convert_ML_FUN (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   let destruct ptl =

      % : (print_tree list -> string list) %

      map (\pt. case pt of (Print_node (s,[])) . s
                         | (_) . failwith `convert_ML_FUN`) ptl

   and construct sl =

      % : (string list -> print_tree list) %

      map (\s. Print_node (s,[])) sl

   and convert sl =

      % : (string list -> string list) %

      if ((length sl) = 1)
      then [trim_enclosing_chars [` `] (hd sl)]
      else if ((trim_enclosing_chars [` `] (hd sl)) = ``)
           then let sl' = map (trim_trailing_chars [` `]) (tl sl)
                in  let dead_space = min (map (num_of_leading_chars [` `])
                                              (filter (\s. not (s = ``)) sl'))
                    in  map (\s. if (s = ``)
                                 then s
                                 else substr dead_space
                                         ((strlen s) - dead_space) s) sl'
           else construction_error pt
                   (`the \`{' of a multi-line ML code block must not be ` ^
                    `followed by anything on the same line`)

   in  case pt
       of (Print_node (`ML_FUN`,ptl)) .
             (if (null ptl)
              then failwith `convert_ML_FUN`
              else (Print_node
                      (`ML_FUN`,(construct o convert o destruct) ptl), []))
        | (_) . failwith `convert_ML_FUN`;;


let convert_ID_to_VAR (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`ID`,ptl)) . (Print_node (`VAR`,ptl), [])
    | (_) . failwith `convert_ID_to_VAR`;;


%  The string constant in the next function has to be modified for inclusion  %
%  in ML code. Back-quotes (ML string quotes) have to be preceded by a        %
%  backslash, and any occurrences of backslash itself have to be doubled-up.  %

let convert_ID_to_TOKCONST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`ID`,[Print_node (s,[])])) .
         (Print_node (`TOKCONST`,[Print_node (indirect_string s,[])]), [])
    | (_) . failwith `convert_ID_to_TOKCONST`;;


let convert_METAVAR (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`NAME_META`,[pt1])) . (convert_ID_to_TOKCONST (pt1,sptl))
    | (Print_node (`CHILD_META`,[pt1])) . (convert_ID_to_TOKCONST (pt1,sptl))
    | (Print_node (`CHILDREN_META`,[pt1])) .
         (convert_ID_to_TOKCONST (pt1,sptl))
    | (Print_node (`NAME_META`,[])) . (Print_node (``,[]), [])
    | (Print_node (`CHILD_META`,[])) . (Print_node (``,[]), [])
    | (Print_node (`CHILDREN_META`,[])) . (Print_node (``,[]), [])
    | (_) . failwith `convert_METAVAR`;;


let convert_METAVAR_to_TOKCONST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`NAME_META`,[pt1])) . (convert_ID_to_TOKCONST (pt1,sptl))
    | (Print_node (`CHILD_META`,[pt1])) . (convert_ID_to_TOKCONST (pt1,sptl))
    | (Print_node (`CHILDREN_META`,[pt1])) .
         (convert_ID_to_TOKCONST (pt1,sptl))
    | (Print_node (`NAME_META`,[])) .
         (construction_error pt
             `illegal use of an un-named metavariable`)
    | (Print_node (`CHILD_META`,[])) .
         (construction_error pt
             `illegal use of an un-named metavariable`)
    | (Print_node (`CHILDREN_META`,[])) .
         (construction_error pt
             `illegal use of an un-named metavariable`)
    | (_) . failwith `convert_METAVAR_to_TOKCONST`;;


letrec convert_METAVAR_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`METAVAR_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_METAVAR_to_TOKCONST (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`METAVAR_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_METAVAR_to_TOKCONST (pt1,sptl)
          and (pt2',sptl2) = convert_METAVAR_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_METAVAR_LIST`)
    | (_) . failwith `convert_METAVAR_LIST`;;


let convert_MIN (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`MIN`,[pt1])) .
         (let (pt1',sptl1) = convert_NUM (pt1,sptl)
          in  (Print_node
                  (`APPN`,
                   [Print_node (`CON`,[Print_node (`Val`,[])]);
                    Print_node
                       (`APPN`,
                        [Print_node (`VAR`,[Print_node (`Nat`,[])]); pt1'])
                   ]), sptl1))
    | (_) . failwith `convert_MIN`;;


let convert_MAX (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`MAX`,[pt1])) .
         (let (pt1',sptl1) = convert_NUM (pt1,sptl)
          in  (Print_node
                  (`APPN`,
                   [Print_node (`CON`,[Print_node (`Val`,[])]);
                    Print_node
                       (`APPN`,
                        [Print_node (`VAR`,[Print_node (`Nat`,[])]); pt1'])
                   ]), sptl1))
    | (_) . failwith `convert_MAX`;;


let convert_LOOP_RANGE (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   let default = Print_node (`CON0`,[Print_node (`Default`,[])])
   in  let (pta,ptb,sptl') =
          case pt
          of (Print_node (`LOOP_RANGE`,[pt1])) .
                (case pt1
                 of (Print_node (`MIN`,_)) .
                       (let (pt1',sptl1) = convert_MIN (pt1,sptl)
                        in  (pt1',default,sptl1))
                  | (Print_node (`MAX`,_)) .
                       (let (pt1',sptl1) = convert_MAX (pt1,sptl)
                        in  (default,pt1',sptl1))
                  | (_) . failwith `convert_LOOP_RANGE`)
           | (Print_node (`LOOP_RANGE`,[pt1;pt2])) .
                (let (pt1',sptl1) = convert_MIN (pt1,sptl)
                 and (pt2',sptl2) = convert_MAX (pt2,sptl)
                 in  (pt1',pt2',(sptl1 @ sptl2)))
           | (_) . failwith `convert_LOOP_RANGE`
       in  (Print_node (`DUPL`,[pta;ptb]), sptl');;


let convert_LOOP_LINK (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   let default_list = Print_node (`LIST`,[])
   and default_range =
          Print_node (`DUPL`,[Print_node (`CON0`,[Print_node (`Default`,[])]);
                              Print_node (`CON0`,[Print_node (`Default`,[])])])
   in  let (pta,ptb,sptl') =
          case pt
          of (Print_node (`LOOP_LINK`,[])) . (default_range,default_list,[])
           | (Print_node (`LOOP_LINK`,[pt1])) .
                (case pt1
                 of (Print_node (`LOOP_RANGE`,_)) .
                       (let (pt1',sptl1) = convert_LOOP_RANGE (pt1,sptl)
                        in  (pt1',default_list,sptl1))
                  | (Print_node (`METAVAR_LIST`,_)) .
                       (let (pt1',sptl1) = convert_METAVAR_LIST (pt1,sptl)
                        in  (default_range,pt1',sptl1))
                  | (_) . failwith `convert_LOOP_LINK`)
           | (Print_node (`LOOP_LINK`,[pt1;pt2])) .
                (let (pt1',sptl1) = convert_LOOP_RANGE (pt1,sptl)
                 and (pt2',sptl2) = convert_METAVAR_LIST (pt2,sptl)
                 in  (pt1',pt2',(sptl1 @ sptl2)))
           | (_) . failwith `convert_LOOP_LINK`
       in  (Print_node (`DUPL`,[pta;ptb]), sptl');;


let convert_LABEL (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`LABEL`,[pt1])) . (convert_METAVAR_to_TOKCONST (pt1,sptl))
    | (_) . failwith `convert_LABEL`;;


%  `convert_NODE_NAME' receives the message `CHILD_LIST' from             %
%  `convert_PATT_TREE' and removes it from the list to be passed on. The  %
%  message contains the list of sub-trees of the node being named.        %

let convert_NODE_NAME (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   let child_list = snd (assoc `CHILD_LIST` sptl)
   and sptl' = filter (\x. not ((fst x) = `CHILD_LIST`)) sptl
   in  case pt
       of (Print_node (`NODE_NAME`,[Print_node (`ID`,[pt1])])) .
             (let (pt1',sptl1) = convert_ID_to_TOKCONST
                                    (Print_node (`ID`,[pt1]),sptl')
              in  (Print_node
                      (`APPN`,
                       [Print_node (`CON`,[Print_node (`Const_name`,[])]);
                        Print_node (`DUPL`,[pt1';child_list])
                       ]), sptl1))
        | (Print_node (`NODE_NAME`,[pt1])) .
             (let (pt1',sptl1) = convert_METAVAR (pt1,sptl')
              in  if (pt1' = (Print_node (``,[])))
                  then (Print_node
                           (`APPN`,
                            [Print_node (`CON`,[Print_node (`Wild_name`,[])]);
                             child_list
                            ]), sptl1)
                  else (Print_node
                           (`APPN`,
                            [Print_node (`CON`,[Print_node (`Var_name`,[])]);
                             Print_node (`DUPL`,[pt1';child_list])
                            ]), sptl1))
        | (_) . failwith `convert_NODE_NAME`;;


letrec convert_CHILD (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`CHILD`,[Print_node (`PATT_TREE`,ptl)])) .
         (let (pt1',sptl1) = convert_PATT_TREE
                                (Print_node (`PATT_TREE`,ptl),sptl)
          in  (Print_node
                 (`APPN`,[Print_node (`CON`,[Print_node (`Patt_child`,[])]);
                          pt1'
                         ]), sptl1))
    | (Print_node (`CHILD`,[pt1])) .
         (let (pt1',sptl1) = convert_METAVAR (pt1,sptl)
          in  if (pt1' = (Print_node (``,[])))
              then (Print_node (`CON0`,[Print_node (`Wild_children`,[])]),
                       sptl1)
              else (Print_node
                       (`APPN`,
                        [Print_node (`CON`,[Print_node (`Var_children`,[])]);
                         pt1'
                        ]), sptl1))
    | (_) . failwith `convert_CHILD`

and convert_CHILD_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`CHILD_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_CHILD (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`CHILD_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_CHILD (pt1,sptl)
          and (pt2',sptl2) = convert_CHILD_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_CHILD_LIST`)
    | (_) . failwith `convert_CHILD_LIST`

%  `convert_PATT_TREE' sends a `CHILD_LIST' message to `convert_NODE_NAME'  %
%  containing the sub-trees (children) of the node. It only does this for   %
%  `NODE_NAME' parse-trees.                                                 %

and convert_PATT_TREE (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`PATT_TREE`,[pt1])) .
         (case pt1
          of (Print_node (`NODE_NAME`,_)) .
                (let child_list = (`CHILD_LIST`,Print_node (`LIST`,[]))
                 in  convert_NODE_NAME (pt1,(child_list.sptl)))
           | (Print_node (`CHILD_META`,_)) .
                (let (pt1',sptl1) = convert_METAVAR (pt1,sptl)
                 in  if (pt1' = (Print_node (``,[])))
                     then (Print_node (`CON0`,[Print_node (`Wild_child`,[])]),
                              sptl1)
                     else (Print_node
                              (`APPN`,
                               [Print_node
                                   (`CON`,[Print_node (`Var_child`,[])]);
                                pt1'
                               ]), sptl1))
           | (Print_node (`LOOP_LINK`,_)) .
                (let (pt1',sptl1) = convert_LOOP_LINK (pt1,sptl)
                 in  (Print_node
                         (`APPN`,
                          [Print_node (`CON`,[Print_node (`Link_child`,[])]);
                           pt1'
                          ]), sptl1))
           | (Print_node (`LOOP`,_)) .
                (let (pt1',sptl1) = convert_LOOP (pt1,sptl)
                 and pt2' = Print_node (`CON0`,[Print_node (`Wild_child`,[])])
                 in  (Print_node
                         (`APPN`,
                          [Print_node (`CON`,[Print_node (`Print_loop`,[])]);
                           Print_node (`DUPL`,[pt1';pt2'])
                          ]), sptl1))
           | (_) . failwith `convert_PATT_TREE`)
    | (Print_node (`PATT_TREE`,[pt1;pt2])) .
         (case pt1
          of (Print_node (`NODE_NAME`,_)) .
                (let (pt2',sptl2) = convert_CHILD_LIST (pt2,sptl)
                 in  let (pt1',sptl1) =
                            convert_NODE_NAME (pt1,((`CHILD_LIST`,pt2').sptl))
                     in  (pt1',(sptl1 @ sptl2)))
           | (Print_node (`LABEL`,_)) .
                (let (pt1',sptl1) = convert_LABEL (pt1,sptl)
                 and (pt2',sptl2) = convert_PATT_TREE (pt2,sptl)
                 in  (Print_node
                         (`APPN`,
                          [Print_node (`CON`,[Print_node (`Print_label`,[])]);
                           Print_node (`DUPL`,[pt1';pt2'])
                          ]), sptl1 @ sptl2))
           | (Print_node (`LOOP_LINK`,_)) .
                (let (pt1',sptl1) = convert_LOOP_LINK (pt1,sptl)
                 and (pt2',sptl2) = convert_PATT_TREE (pt2,sptl)
                 in  (Print_node
                         (`APPN`,
                          [Print_node (`CON`,[Print_node (`Print_link`,[])]);
                           Print_node (`DUPL`,[pt1';pt2'])
                          ]), sptl1 @ sptl2))
           | (Print_node (`LOOP`,_)) .
                (let (pt1',sptl1) = convert_LOOP (pt1,sptl)
                 and (pt2',sptl2) = convert_PATT_TREE (pt2,sptl)
                 in  (Print_node
                         (`APPN`,
                          [Print_node (`CON`,[Print_node (`Print_loop`,[])]);
                           Print_node (`DUPL`,[pt1';pt2'])
                          ]), sptl1 @ sptl2))
           | (_) . failwith `convert_PATT_TREE`)
    | (_) . failwith `convert_PATT_TREE`

and convert_LOOP (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`LOOP`,[pt1])) . (convert_PATT_TREE (pt1,sptl))
    | (_) . failwith `convert_LOOP`;;


%  The string constant in the next function has to be modified for inclusion  %
%  in ML code. Back-quotes (ML string quotes) have to be preceded by a        %
%  backslash, and any occurrences of backslash itself have to be doubled-up.  %

let convert_STRING (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`STRING`,[Print_node (s,[])])) .
         (Print_node (`TOKCONST`,[Print_node (indirect_string s,[])]), [])
    | (_) . failwith `convert_STRING`;;


%  `convert_TEST' may require access to an abbreviation. If it does, it  %
%  checks the message list for the appropriate abbreviation.             %

let convert_TEST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`TEST`,[pt1])) .
         (case pt1
          of (Print_node (`ID`,[Print_node (s,[])])) .
                (let pt1' = ( (snd (assoc (`ABBREV_` ^ s) sptl))
                            ? construction_error pt
                                 (`undefined abbreviation \`` ^ s ^ `'`)
                            )
                 in  (pt1',[]))
           | (_) . (convert_ML_FUN (pt1,sptl)))
    | (_) . failwith `convert_TEST`;;


let convert_PATTERN (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`PATTERN`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_STRING (pt1,sptl)
          and (pt2',sptl2) = convert_PATT_TREE (pt2,sptl)
          in  (Print_node
                  (`DUPL`,[pt1';
                           Print_node
                              (`DUPL`,[pt2';
                                       Print_node
                                          (`ML_FUN`,[Print_node
                                                        (`\\x y. true`,[])])
                                      ])
                          ]), sptl1 @ sptl2))
    | (Print_node (`PATTERN`,[pt1;pt2;pt3])) .
         (let (pt1',sptl1) = convert_STRING (pt1,sptl)
          and (pt2',sptl2) = convert_PATT_TREE (pt2,sptl)
          and (pt3',sptl3) = convert_TEST (pt3,sptl)
          in  (Print_node (`DUPL`,[pt1'; Print_node (`DUPL`,[pt2';pt3'])]),
                  sptl1 @ sptl2 @ sptl3))
    | (_) . failwith `convert_PATTERN`;;


%  `convert_TRANSFORM' may require access to an abbreviation. If it does, it  %
%  checks the message list for the appropriate abbreviation.                  %

let convert_TRANSFORM (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`TRANSFORM`,[pt1])) .
         (case pt1
          of (Print_node (`ID`,[Print_node (s,[])])) .
                (let pt1' = ( (snd (assoc (`ABBREV_` ^ s) sptl))
                            ? construction_error pt
                                 (`undefined abbreviation \`` ^ s ^ `'`)
                            )
                 in  (pt1',[]))
           | (_) . (convert_ML_FUN (pt1,sptl)))
    | (_) . failwith `convert_TRANSFORM`;;


let convert_P_SPECIAL (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`P_SPECIAL`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_METAVAR_to_TOKCONST (pt1,sptl)
          and (pt2',sptl2) = convert_TRANSFORM (pt2,sptl)
          in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_P_SPECIAL`;;


letrec convert_P_SPECIAL_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`P_SPECIAL_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_P_SPECIAL (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`P_SPECIAL_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_P_SPECIAL (pt1,sptl)
          and (pt2',sptl2) = convert_P_SPECIAL_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_P_SPECIAL_LIST`)
    | (_) . failwith `convert_P_SPECIAL_LIST`;;


%  `convert_INT_EXP' may require access to an abbreviation. If it does, it  %
%  checks the message list for the appropriate abbreviation.                %

let convert_INT_EXP (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`INT_EXP`,[pt1])) .
         (case pt1
          of (Print_node (`NUM`,_)) .
                (let (pt1',sptl1) = convert_NUM (pt1,sptl)
                 in  (Print_node
                        (`APPN`,[Print_node
                                   (`ML_FUN`,[Print_node(`\\n. \\x y. n`,[])]);
                                 pt1'
                                ]), sptl1))
           | (Print_node (`NEG`,_)) .
                (let (pt1',sptl1) = convert_NEG (pt1,sptl)
                 in  (Print_node
                        (`APPN`,[Print_node
                                   (`ML_FUN`,[Print_node(`\\n. \\x y. n`,[])]);
                                 pt1'
                                ]), sptl1))
           | (Print_node (`ID`,[Print_node (s,[])])) .
                (let pt1' = ( (snd (assoc (`ABBREV_` ^ s) sptl))
                            ? construction_error pt
                                 (`undefined abbreviation \`` ^ s ^ `'`)
                            )
                 in  (pt1',[]))
           | (_) . (convert_ML_FUN (pt1,sptl)))
    | (_) . failwith `convert_INT_EXP`;;


let convert_ASSIGN (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`ASSIGN`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_ID_to_TOKCONST (pt1,sptl)
          and (pt2',sptl2) = convert_INT_EXP (pt2,sptl)
          in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_ASSIGN`;;


letrec convert_ASSIGNMENTS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`ASSIGNMENTS`,[pt1])) .
         (let (pt1',sptl1) = convert_ASSIGN (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`ASSIGNMENTS`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_ASSIGN (pt1,sptl)
          and (pt2',sptl2) = convert_ASSIGNMENTS (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_ASSIGNMENTS`)
    | (_) . failwith `convert_ASSIGNMENTS`;;


%  `convert_F_SUBCALL' sends a `LEAF' message to `convert_C_SUBCALL',      %
%  `convert_LEAF_OR_SUBCALL', and `convert_OBJECT', to tell them that the  %
%  construct they are dealing with is a leaf rather than a subcall. The    %
%  message is just a flag, so it contains a null tree.                     %

let convert_F_SUBCALL (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`F_SUBCALL`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_TRANSFORM (pt1,sptl)
          and (pt2',sptl2) = convert_METAVAR_to_TOKCONST (pt2,sptl)
          and sptl' =
             case pt2
             of (Print_node (`NAME_META`,_)) . [`LEAF`,Print_node (``,[])]
              | (_) . []
          in  (Print_node (`DUPL`,[pt2';pt1']), sptl' @ sptl1 @ sptl2))
    | (Print_node (`F_SUBCALL`,[pt1])) .
         (let (pt1',sptl1) = convert_METAVAR_to_TOKCONST (pt1,sptl)
          and sptl' =
             case pt1
             of (Print_node (`NAME_META`,_)) . [`LEAF`,Print_node (``,[])]
              | (_) . []
          in  (Print_node
                 (`DUPL`,[pt1';
                          Print_node (`ML_FUN`,[Print_node (`I`,[])])
                         ]), sptl' @ sptl1))
    | (_) . failwith `convert_F_SUBCALL`;;


%  If a context is present, `convert_C_SUBCALL' checks for a `LEAF' message.  %
%  If `LEAF' is present, the inclusion of a context is invalid. If not, the   %
%  context is sent as a `CONTEXT' message to `convert_OBJECT'.                %

let convert_C_SUBCALL (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`C_SUBCALL`,[Print_node (`STRING`,[pt']); pt1])) .
         (let (pt1',sptl1) = convert_F_SUBCALL (pt1,sptl)
          and (pt'',sptl'') = convert_STRING (Print_node (`STRING`,[pt']),sptl)
          in  if (can (assoc `LEAF`) sptl1)
              then construction_error pt `invalid use of context change`
              else (pt1',(`CONTEXT`,pt'').(sptl'' @ sptl1)))
    | (Print_node (`C_SUBCALL`,[pt1])) . (convert_F_SUBCALL (pt1,sptl))
    | (_) . failwith `convert_C_SUBCALL`;;


%  If assignments are not present, `convert_LEAF_OR_SUBCALL' uses the        %
%  presence or absence of a `LEAF' message to determine the kind of tree to  %
%  build. If there are assignments, and there is a `LEAF' message, the       %
%  assignments are invalid.                                                  %

let convert_LEAF_OR_SUBCALL (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`LEAF_OR_SUBCALL`,[pt1])) .
         (let (pt1',sptl1) = convert_C_SUBCALL (pt1,sptl)
          in  if (can (assoc `LEAF`) sptl1)
              then (pt1',sptl1)
              else (Print_node (`DUPL`,[pt1'; Print_node (`LIST`,[])]), sptl1))
    | (Print_node (`LEAF_OR_SUBCALL`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_C_SUBCALL (pt1,sptl)
          and (pt2',sptl2) = convert_ASSIGNMENTS (pt2,sptl)
          in  if (can (assoc `LEAF`) sptl1)
              then construction_error pt `invalid use of assignments`
              else (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_LEAF_OR_SUBCALL`;;


%  The string constant in the next function has to be modified for inclusion  %
%  in ML code. Back-quotes (ML string quotes) have to be preceded by a        %
%  backslash, and any occurrences of backslash itself have to be doubled-up.  %

let convert_TERMINAL (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`TERMINAL`,[Print_node (s,[])])) .
         (Print_node (`TOKCONST`,[Print_node (indirect_string s,[])]), [])
    | (_) . failwith `convert_TERMINAL`;;


let convert_INC (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`INC`,[pt1])) .
         (let (pt1',sptl1) =
                 case pt1
                 of (Print_node (`NEG`,_)) . (convert_NEG (pt1,sptl))
                  | (_) . (convert_NUM (pt1,sptl))
          in  (Print_node (`APPN`,[Print_node (`CON`,[Print_node (`Inc`,[])]);
                                   pt1'
                                  ]), sptl1))
    | (_) . failwith `convert_INC`;;


let convert_H_PARAMS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`H_PARAMS`,[pt1])) . 
         (let (pt1',sptl1) = convert_NUM (pt1,sptl)
          in  (Print_node (`APPN`,[Print_node (`CON`,[Print_node (`Nat`,[])]);
                                   pt1'
                                  ]), sptl1))
    | (_) . failwith `convert_H_PARAMS`;;


let convert_V_PARAMS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`V_PARAMS`,[pt1;pt2])) .
         (let (pt1',sptl1) =
                 case pt1
                 of (Print_node (`INC`,_)) . (convert_INC (pt1,sptl))
                  | (_) .
                       (let (pt1'',sptl1') =
                               case pt1
                               of (Print_node (`NEG`,_)) .
                                     (convert_NEG (pt1,sptl))
                                | (_) . (convert_NUM (pt1,sptl))
                        in  (Print_node
                               (`APPN`,[Print_node
                                          (`CON`,[Print_node (`Abs`,[])]);
                                        pt1''
                                       ]), sptl1'))
          and (pt2',sptl2) =
                 convert_H_PARAMS (Print_node (`H_PARAMS`,[pt2]),sptl)
          in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_V_PARAMS`;;


let convert_HV_PARAMS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`HV_PARAMS`,[pt1;pt2;pt3])) .
         (let (pt1',sptl1) =
                 convert_H_PARAMS (Print_node (`H_PARAMS`,[pt1]),sptl)
          and (pt2',sptl2) =
                 convert_V_PARAMS (Print_node (`V_PARAMS`,[pt2;pt3]), sptl)
          in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_HV_PARAMS`;;


let convert_HOV_PARAMS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`HOV_PARAMS`,[pt1;pt2;pt3])) .
         (convert_HV_PARAMS (Print_node (`HV_PARAMS`,[pt1;pt2;pt3]), sptl))
    | (_) . failwith `convert_HOV_PARAMS`;;


let convert_BOX (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`H_BOX`,[pt1])) . (convert_H_PARAMS (pt1,sptl))
    | (Print_node (`V_BOX`,[pt1])) . (convert_V_PARAMS (pt1,sptl))
    | (Print_node (`HV_BOX`,[pt1])) . (convert_HV_PARAMS (pt1,sptl))
    | (Print_node (`HOV_BOX`,[pt1])) . (convert_HOV_PARAMS (pt1,sptl))
    | (_) . failwith `convert_BOX`;;


%  If the object given to `convert_OBJECT' is a leaf or a subcall, the        %
%  function tests for a `LEAF' message. If one is present, it is removed      %
%  before passing the message list on. If there is no `LEAF' message, the     %
%  function builds different trees depending on the presence or absence of a  %
%  `CONTEXT' message. Any `CONTEXT' message is removed before passing the     %
%  message list on. Note that there cannot be both `LEAF' and `CONTEXT'       %
%  messages because context changes are not allowed for leaf objects.         %

letrec convert_OBJECT (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`OBJECT`,[pt1])) .
         (case pt1
          of (Print_node (`TERMINAL`,_)) .
                (let (pt1',sptl1) = convert_TERMINAL (pt1,sptl)
                 in  (Print_node
                        (`APPN`,[Print_node
                                   (`CON`,[Print_node (`PO_constant`,[])]);
                                 pt1'
                                ]), sptl1))
           | (Print_node (`LEAF_OR_SUBCALL`,_)) .
                (let (pt1',sptl1) = convert_LEAF_OR_SUBCALL (pt1,sptl)
                 in  if (can (assoc `LEAF`) sptl1)
                     then let sptl1' = filter (\x. not (fst x = `LEAF`)) sptl1
                          in  (Print_node
                                 (`APPN`,[Print_node
                                            (`CON`,[Print_node
                                                      (`PO_leaf`,[])]);
                                          pt1'
                                         ]), sptl1')
                     else let (context,non_context) =
                                 (`PO_context_subcall`,`PO_subcall`)
                          and sptl1' =
                                 filter (\x. not (fst x = `CONTEXT`)) sptl1
                          in  (Print_node
                                 (`APPN`,
                                  (  [Print_node
                                        (`CON`,[Print_node (context,[])]);
                                      Print_node
                                        (`DUPL`,
                                         [snd (assoc `CONTEXT` sptl1); pt1'])
                                     ]
                                  ?? [`assoc`]
                                     [Print_node
                                        (`CON`,[Print_node (non_context,[])]);
                                      pt1'
                                     ]
                                  )), sptl1'))
           | (Print_node (`FORMAT`,_)) .
                (let (pt1',sptl1) = convert_FORMAT (pt1,sptl)
                 in  (Print_node
                        (`APPN`,[Print_node
                                   (`CON`,[Print_node (`PO_format`,[])]);
                                 pt1'
                                ]), sptl1))
           | (Print_node (`EXPAND`,_)) .
                (let (pt1',sptl1) = convert_EXPAND (pt1,sptl)
                 in  (Print_node
                        (`APPN`,[Print_node
                                   (`CON`,[Print_node (`PO_expand`,[])]);
                                 pt1'
                                ]), sptl1))
           | (_) . failwith `convert_OBJECT`)

%  `convert_H_OBJECT' receives the default box parameters from                %
%  `convert_BOX_SPEC' as a `BOX_PARAMS' message. The message is removed from  %
%  the list before passing it on.                                             %

%  `convert_V_OBJECT', `convert_HV_OBJECT', and `convert_HOV_OBJECT' behave   %
%  similarly.                                                                 %

and convert_H_OBJECT (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`H_OBJECT`,[pt2])) .
         (let pt1' = ( (snd (assoc `BOX_PARAMS` sptl))
                     ? failwith `convert_H_OBJECT`
                     )
          and sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl2))
    | (Print_node (`H_OBJECT`,[pt1;pt2])) .
         (let sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt1',sptl1) = convert_H_PARAMS (pt1,sptl')
              and (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_H_OBJECT`

and convert_V_OBJECT (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`V_OBJECT`,[pt2])) .
         (let pt1' = ( (snd (assoc `BOX_PARAMS` sptl))
                     ? failwith `convert_V_OBJECT`
                     )
          and sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl2))
    | (Print_node (`V_OBJECT`,[pt1;pt2])) .
         (let sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt1',sptl1) = convert_V_PARAMS (pt1,sptl')
              and (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_V_OBJECT`

and convert_HV_OBJECT (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`HV_OBJECT`,[pt2])) .
         (let pt1' = ( (snd (assoc `BOX_PARAMS` sptl))
                     ? failwith `convert_HV_OBJECT`
                     )
          and sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl2))
    | (Print_node (`HV_OBJECT`,[pt1;pt2])) .
         (let sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt1',sptl1) = convert_HV_PARAMS (pt1,sptl')
              and (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_HV_OBJECT`

and convert_HOV_OBJECT (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`HOV_OBJECT`,[pt2])) .
         (let pt1' = ( (snd (assoc `BOX_PARAMS` sptl))
                     ? failwith `convert_HOV_OBJECT`
                     )
          and sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl2))
    | (Print_node (`HOV_OBJECT`,[pt1;pt2])) .
         (let sptl' = filter (\x. not ((fst x) = `BOX_PARAMS`)) sptl
          in  let (pt1',sptl1) = convert_HOV_PARAMS (pt1,sptl')
              and (pt2',sptl2) = convert_OBJECT (pt2,sptl')
              in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_HOV_OBJECT`

and convert_H_OBJECT_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`H_OBJECT_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_H_OBJECT (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`H_OBJECT_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_H_OBJECT (pt1,sptl)
          and (pt2',sptl2) = convert_H_OBJECT_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_H_OBJECT_LIST`)
    | (_) . failwith `convert_H_OBJECT_LIST`

and convert_V_OBJECT_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`V_OBJECT_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_V_OBJECT (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`V_OBJECT_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_V_OBJECT (pt1,sptl)
          and (pt2',sptl2) = convert_V_OBJECT_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_V_OBJECT_LIST`)
    | (_) . failwith `convert_V_OBJECT_LIST`

and convert_HV_OBJECT_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`HV_OBJECT_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_HV_OBJECT (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`HV_OBJECT_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_HV_OBJECT (pt1,sptl)
          and (pt2',sptl2) = convert_HV_OBJECT_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_HV_OBJECT_LIST`)
    | (_) . failwith `convert_HV_OBJECT_LIST`

and convert_HOV_OBJECT_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`HOV_OBJECT_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_HOV_OBJECT (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`HOV_OBJECT_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_HOV_OBJECT (pt1,sptl)
          and (pt2',sptl2) = convert_HOV_OBJECT_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_HOV_OBJECT_LIST`)
    | (_) . failwith `convert_HOV_OBJECT_LIST`

%  `convert_BOX_SPEC' obtains the default box parameters and sends them to  %
%  the objects as a `BOX_PARAMS' message.                                   %

and convert_BOX_SPEC (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`BOX_SPEC`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_BOX (pt1,sptl)
          in  let sptl' = (`BOX_PARAMS`,pt1').sptl
              in  case pt1
                  of (Print_node (`H_BOX`,_)) .
                        (let (pt2',sptl2) = convert_H_OBJECT_LIST (pt2,sptl')
                         in  (Print_node
                                (`APPN`,[Print_node
                                           (`CON`,[Print_node (`H_box`,[])]);
                                         pt2'
                                        ]), sptl1 @ sptl2))
                   | (Print_node (`V_BOX`,_)) .
                        (let (pt2',sptl2) = convert_V_OBJECT_LIST (pt2,sptl')
                         in  (Print_node
                                (`APPN`,[Print_node
                                           (`CON`,[Print_node (`V_box`,[])]);
                                         pt2'
                                        ]), sptl1 @ sptl2))
                   | (Print_node (`HV_BOX`,_)) .
                        (let (pt2',sptl2) = convert_HV_OBJECT_LIST (pt2,sptl')
                         in  (Print_node
                                (`APPN`,[Print_node
                                           (`CON`,[Print_node (`HV_box`,[])]);
                                         pt2'
                                        ]), sptl1 @ sptl2))
                   | (Print_node (`HOV_BOX`,_)) .
                        (let (pt2',sptl2) = convert_HOV_OBJECT_LIST (pt2,sptl')
                         in  (Print_node
                                (`APPN`,[Print_node
                                           (`CON`,[Print_node (`HoV_box`,[])]);
                                         pt2'
                                        ]), sptl1 @ sptl2))
                   | (_) . failwith `convert_BOX_SPEC`)
    | (_) . failwith `convert_BOX_SPEC`

and convert_EXPAND (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`EXPAND`,[pt1])) . (convert_BOX_SPEC (pt1,sptl))
    | (_) . failwith `convert_EXPAND`

and convert_FORMAT (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`FORMAT`,[])) .
         (Print_node (`CON0`,[Print_node (`PF_empty`,[])]), [])
    | (Print_node (`FORMAT`,[pt1])) .
         (let (pt1',sptl1) = convert_BOX_SPEC (pt1,sptl)
          in  (Print_node (`APPN`,[Print_node (`CON`,[Print_node (`PF`,[])]);
                                   pt1'
                                  ]), sptl1))
    | (Print_node (`FORMAT`,[pt1;pt2;pt3])) .
         (let (pt1',sptl1) = convert_TEST (pt1,sptl)
          and (pt2',sptl2) = convert_FORMAT (pt2,sptl)
          and (pt3',sptl3) = convert_FORMAT (pt3,sptl)
          in  (Print_node
                 (`APPN`,[Print_node (`CON`,[Print_node (`PF_branch`,[])]);
                          Print_node (`DUPL`,[pt1';
                                              Print_node (`DUPL`,[pt2';pt3'])
                                             ])
                         ]), sptl1 @ sptl2 @ sptl3))
    | (_) . failwith `convert_FORMAT`;;


let convert_RULE (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`RULE`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_PATTERN (pt1,sptl)
          and (pt2',sptl2) = convert_FORMAT (pt2,sptl)
          in  (Print_node
                 (`DUPL`,
                  [pt1';Print_node (`DUPL`,[Print_node (`LIST`,[]);pt2'])]),
               sptl1 @ sptl2))
    | (Print_node (`RULE`,[pt1;pt2;pt3])) .
         (let (pt1',sptl1) = convert_PATTERN (pt1,sptl)
          and (pt2',sptl2) = convert_P_SPECIAL_LIST (pt2,sptl)
          and (pt3',sptl3) = convert_FORMAT (pt3,sptl)
          in  (Print_node (`DUPL`,[pt1';Print_node (`DUPL`,[pt2';pt3'])]),
               sptl1 @ sptl2 @ sptl3))
    | (_) . failwith `convert_RULE`;;


letrec convert_RULE_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`RULE_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_RULE (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`RULE_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_RULE (pt1,sptl)
          and (pt2',sptl2) = convert_RULE_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_RULE_LIST`)
    | (_) . failwith `convert_RULE_LIST`;;


let convert_RULES (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`RULES`,[pt1])) . (convert_RULE_LIST (pt1,sptl))
    | (_) . failwith `convert_RULES`;;


let convert_BINDING (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`BINDING`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_ID_to_VAR (pt1,sptl)
          and (pt2',sptl2) = convert_ML_FUN (pt2,sptl)
          in  (Print_node (`DUPL`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_BINDING`;;


letrec convert_BINDING_LIST_to_LIST (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`BINDING_LIST`,[pt1])) .
         (let (pt1',sptl1) = convert_BINDING (pt1,sptl)
          in  (Print_node (`LIST`,[pt1']), sptl1))
    | (Print_node (`BINDING_LIST`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_BINDING (pt1,sptl)
          and (pt2',sptl2) = convert_BINDING_LIST_to_LIST (pt2,sptl)
          in  case pt2'
              of (Print_node (`LIST`,ptl)) .
                    (Print_node (`LIST`,(pt1'.ptl)), sptl1 @ sptl2)
               | (_) . failwith `convert_BINDING_LIST_to_LIST`)
    | (_) . failwith `convert_BINDING_LIST_to_LIST`;;


%  The bindings used in declarations are made into an ML `letrec', so that    %
%  they are mutually recursive. The identifiers declared must be function     %
%  valued, but unfortunately ML is too restrictive. It insists that the body  %
%  of the declaration be an abstraction (after having changed arguments on    %
%  the left of the equals sign into bound variables on the right). This       %
%  restriction is overcome by converting the body of the declaration, say     %
%  `body', into (\dummy0. (body dummy0)). This works provided `body' is       %
%  function valued, and `dummy0' does not occur in `body'. To overcome this   %
%  second problem, a function to find an unused identifier is used.           %

letrec convert_BINDING_LIST_to_LETREC (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   let dummy pt =

      % : (print_tree -> print_tree) %

      letrec find_unused_id sl n =

         % : (string list -> int -> string) %

         let s = `dummy` ^ (string_of_int n)
         in  if (strings_contain sl s)
             then find_unused_id sl (n + 1)
             else s

      in let dummy_var =
            find_unused_id
               (case pt
                of (Print_node (`ML_FUN`,ptl)) .
                      (map (\pt'. case pt'
                                  of (Print_node (s,[])) . s
                                   | (_) . failwith
                                              `convert_BINDING_LIST_to_LETREC`
                           ) ptl)
                 | (_) . failwith `convert_BINDING_LIST_to_LETREC`) 0
         in  Print_node
               (`ABSTR`,[Print_node (`VAR`,[Print_node (dummy_var,[])]);
                         Print_node
                           (`APPN`,
                            [pt;
                             Print_node (`VAR`,[Print_node (dummy_var,[])])
                            ])
                        ])

   in case pt
      of (Print_node (`BINDING_LIST`,[pt1])) .
            (let (pt1',sptl1) = convert_BINDING (pt1,sptl)
             in  case pt1'
                 of (Print_node (`DUPL`,[pt1a;pt1b])) .
                       (Print_node (`LETREC`,[pt1a;dummy pt1b]),sptl1)
                  | (_) . failwith `convert_BINDING_LIST_to_LETREC`)
       | (Print_node (`BINDING_LIST`,[pt1;pt2])) .
            (let (pt1',sptl1) = convert_BINDING (pt1,sptl)
             and (pt2',sptl2) = convert_BINDING_LIST_to_LETREC (pt2,sptl)
             in  case (pt1',pt2')
                 of (Print_node (`DUPL`,[pt1a;pt1b]),
                       Print_node (`LETREC`,[pt2a;pt2b])) .
                         (Print_node
                            (`LETREC`,[Print_node (`DUPL`,[pt1a;pt2a]);
                                       Print_node (`DUPL`,[dummy pt1b;pt2b])]),
                          sptl1 @ sptl2)
                  | (_) . failwith `convert_BINDING_LIST_to_LETREC`)
       | (_) . failwith `convert_BINDING_LIST_to_LETREC`;;


let convert_DECLARS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`DECLARS`,[pt1])) .
         (convert_BINDING_LIST_to_LETREC (pt1,sptl))
    | (_) . failwith `convert_DECLARS`;;


%  `convert_ABBREVS' creates a null tree. The bindings of identifiers to  %
%  blocks of ML code which it obtains are sent as `ABBREV_...' messages.  %

let convert_ABBREVS (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   let convert x =
      case x
      of (Print_node (`DUPL`,[Print_node (`VAR`,[Print_node (s,[])]); pt'])) .
            ((`ABBREV_` ^ s),pt')
       | (_) . failwith `convert_ABBREVS`
   in  case pt
       of (Print_node (`ABBREVS`,[pt1])) .
             (let (pt1',sptl1) = convert_BINDING_LIST_to_LIST (pt1,sptl)
              in  case pt1'
                  of (Print_node (`LIST`,ptl)) .
                        (Print_node (``,[]), sptl1 @ (map convert ptl))
                   | (_) . failwith `convert_ABBREVS`)
        | (_) . failwith `convert_ABBREVS`;;


%  The result of the calls to `convert_ABBREVS' in the function below is a    %
%  null tree and a list of messages containing the abbreviation information.  %
%  The messages are passed to `convert_RULES', but are not passed back to     %
%  the function which called `convert_BODY'.                                  %

let convert_BODY (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`BODY`,[pt1])) . (convert_RULES (pt1,sptl))
    | (Print_node (`BODY`,[Print_node (`DECLARS`,ptl); pt2])) .
         (let (pt1',sptl1) = convert_DECLARS (Print_node (`DECLARS`,ptl), sptl)
          and (pt2',sptl2) = convert_RULES (pt2,sptl)
          in  (Print_node (`IN`,[pt1';pt2']), sptl1 @ sptl2))
    | (Print_node (`BODY`,[Print_node (`ABBREVS`,ptl); pt2])) .
         (let (_,sptl1) = convert_ABBREVS (Print_node (`ABBREVS`,ptl), sptl)
          in  convert_RULES (pt2, sptl1 @ sptl))
    | (Print_node (`BODY`,[pt1;pt2;pt3])) .
         (let (_,sptl2) = convert_ABBREVS (pt2,sptl)
          in  let (pt1',sptl1) = convert_DECLARS (pt1,sptl)
              and (pt3',sptl3) = convert_RULES (pt3, sptl2 @ sptl)
              in  (Print_node (`IN`,[pt1';pt3']), sptl1 @ sptl3))
    | (_) . failwith `convert_BODY`;;


let convert_PP (pt,sptl) =

   % : (print_tree # ((string # print_tree) list) ->    %
   %         print_tree # ((string # print_tree) list)) %

   case pt
   of (Print_node (`PP`,[pt1;pt2])) .
         (let (pt1',sptl1) = convert_ID_to_VAR (pt1,sptl)
          and (pt2',sptl2) = convert_BODY (pt2,sptl)
          in  (Print_node (`LET`,[pt1';pt2']), sptl1 @ sptl2))
    | (_) . failwith `convert_PP`;;

convert_PP;;
end_section convert;;
let convert_PP = it;;

%-----------------------------------------------------------------------------%
