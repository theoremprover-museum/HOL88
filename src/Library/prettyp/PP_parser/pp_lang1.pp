% pp_lang1.pp                                                                 %
%-----------------------------------------------------------------------------%


% A pretty-printer for the pretty-printing language (part 1) %

prettyprinter pp_lang1 =

declarations

  % Function to double-up a specified character within a string. %

   quote_quote = {
                  \s. letrec dupl s sl =
                         if (null sl)
                         then []
                         else if ((hd sl) = s)
                              then s.s.(dupl s (tl sl))
                              else (hd sl).(dupl s (tl sl))
                      in (implode o (dupl s) o explode)
                 };

   destruct = {
               \ptaddl.
                  map (\(pt,add).
                          case pt
                          of (Print_node (s,[])) . (s,add)
                           | (_) . failwith `pp_lang_rules_fun`) ptaddl
              };

   construct = {\saddl. map (\(s,add). Print_node (s,[]),add) saddl};

  % `convert' processes the list of strings representing a block of ML code   %
  % in the pretty-printing specification. The text is to appear neatly in the %
  % pretty-printed output. When there is only one line in the text block, the %
  % conversion is easy. Space is trimmed from the beginning and the end of    %
  % the string.                                                               %

  % If the block extends over more than one line, the first line must be      %
  % blank, so that the vertical alignment of the text in the source file can  %
  % be deduced. If this condition is satisfied, the first line is discarded,  %
  % and trailing blanks are removed from all of the other lines. Any blank    %
  % lines will now be empty strings. The smallest number of leading blanks in %
  % those strings which are not empty is computed, and this amount of space   %
  % is removed from the beginning of all the strings which are not blank.     %
  % This process retains the vertical alignment of the text, but removes dead %
  % space to the left of the block.                                           %

   convert = {
              \saddl.
                 if ((length saddl) = 1)
                 then [(trim_enclosing_chars [` `] # I) (hd saddl)]
                 else if ((trim_enclosing_chars [` `] (fst (hd saddl))) = ``)
                      then let saddl' =
                              map (trim_trailing_chars [` `] # I) saddl
                           in  let dead_space =
                                  min (map (num_of_leading_chars [` `])
                                              (filter (\s. not (s = ``))
                                                  (map fst saddl')))
                               in  map (\(s,add).
                                           if (s = ``)
                                           then (s,add)
                                           else (substr dead_space
                                                    ((strlen s) - dead_space)
                                                       s,add)) saddl'
                      else failwith `pp_lang_rules_fun`
             };

  % Functions for determining whether a string is a valid identifier. %

   is_char = {
              \(l,c,u). not (((ascii_code c) < (ascii_code l)) or
                                ((ascii_code c) > (ascii_code u)))
             };

   is_ucase = {\c. is_char (`A`,c,`Z`)};

   is_lcase = {\c. is_char (`a`,c,`z`)};

   is_letter = {\c. (is_ucase c) or (is_lcase c)};

   is_digit = {\c. is_char (`0`,c,`9`)};

   is_underscore = {\c. mem c [`_`]};

   is_id_body = {
                 \sl. if (null sl)
                      then true
                      else if (is_underscore (hd sl))
                           then if (null (tl sl))
                                then false
                                else if (is_letter (hd (tl sl))) or
                                           (is_digit (hd (tl sl)))
                                     then is_id_body (tl (tl sl))
                                     else false
                           else if (is_letter (hd sl)) or (is_digit (hd sl))
                                then is_id_body (tl sl)
                                else false
                };

   not_id = {
             (\sl. if (null sl)
                   then true
                   else if (is_letter (hd sl))
                        then not (is_id_body (tl sl))
                        else true) o explode
            };

  % Function for determining whether a string is a keyword of the %
  % pretty-printing language.                                     %

   is_keyword = {
                 \s. mem s
                      [`prettyprinter`;`rules`;`declarations`;`abbreviations`;
                       `with`;`end`;`where`;`if`;`then`;`else`;
                       `h`;`v`;`hv`;`hov`]
                };

end declarations


abbreviations

  % Abbreviation for a function which produces valid textual output for a    %
  % block of ML code within the pretty-printer specification. An appropriate %
  % formatting is applied, and occurrences of `{' and `}' are doubled-up so  %
  % that they appear as the original input would have done.                  %

   despace = {
              construct o
              (map ((quote_quote `{{` # I) o
                    (quote_quote `}}` # I))) o
              convert o
              destruct
             };

  % Abbreviations for functions which double-up quotes within quoted text. %

   quote_string = {quote_quote `'`};

   quote_terminal = {quote_quote `"`};

  % Abbreviation for a function which surrounds an identifier with sharp      %
  % signs if the string representing the identifier is a keyword or not a     %
  % valid identifier. Any occurrences of `#' within the string are doubled-up %
  % so that they do not appear to be the terminating `#'.                     %

   quote_id = {
               \s. if ((is_keyword s) or (not_id s))
                   then (`#` ^ (quote_quote `#` s) ^ `#`)
                   else s
              };

end abbreviations


% A number of the following rules use a metavariable which matches a list of %
% sub-trees (i.e. zero or more), that is a metavariable beginning with `**', %
% to match a single optional sub-tree (zero or one occurrences).             %

rules
   ''::NUM(***num()) -> [<h 0> ***num];

   ''::NEG(*num) -> [<h 0> "-" *num];

   ''::STRING(***string()) -> [<h 0> "'" quote_string(***string) "'"];

   ''::TERMINAL(***string()) -> [<h 0> """" quote_terminal(***string) """"];

   ''::ML_FUN(**strings) -> [<h 0> "{" [<v 0,0> despace(**strings)] "}" ];

   ''::ID(***id()) -> [<h 0> quote_id(***id)];

   ''::NAME_META(**id) -> [<h 0> "***" **id];

   ''::CHILD_META(**id) -> [<h 0> "*" **id];

   ''::CHILDREN_META(**id) -> [<h 0> "**" **id];

   ''::[METAVAR_LIST(*metavars,<>)]METAVAR_LIST(*metavar) ->
       [<hv 0,3,0> **[<h 0> *metavars ";"] *metavar];

   ''::MIN(*num) -> [<h 0> *num];

   ''::MAX(*num) -> [<h 0> *num];

   ''::LOOP_RANGE(MIN(*num)) -> [<h 0> *num ".."];

   ''::LOOP_RANGE(MAX(*num)) -> [<h 0> ".." *num];

   ''::LOOP_RANGE(*min,*max) -> [<h 0> *min ".." *max];

   ''::LOOP_LINK(*loop_range,*metavar_list) ->
       [<h 0> "<" *loop_range ":" <1> *metavar_list ">"];

   ''::LOOP_LINK(**metavar_list) -> [<h 0> "<" **metavar_list ">"];

   ''::LABEL(*child_meta) -> [<h 0> "|" *child_meta "|"];

   ''::NODE_NAME(*node_name) -> [<h 0> *node_name];

   ''::CHILD(*child) -> [<h 0> *child];

   ''::[CHILD_LIST(*children,<>)]CHILD_LIST(*child) ->
       [<hv 0,3,0> **[<h 0> *children ","] *child];

   ''::PATT_TREE(NODE_NAME(*node_name),*child_list) ->
       [<hv 0,3,0> *node_name [<h 0> "(" *child_list ")"]];

   ''::PATT_TREE(NODE_NAME(*node_name)) -> [<h 0> *node_name "()"];

   ''::PATT_TREE(**x) -> [<hv 0,3,0> **x];

   ''::LOOP(*patt_tree) -> [<h 0> "[" *patt_tree "]"];

   ''::TEST(*test) -> [<h 0> *test];

   ''::PATTERN(*string,*patt_tree,**test) ->
       [<h 0> *string "::" [<hv 1,3,0> *patt_tree
                                       **[<hv 1,3,0> "where" **test]]];

   ''::TRANSFORM(*transform) -> [<h 0> *transform];

   ''::P_SPECIAL(*metavar,*transform) ->
       [<hv 1,3,0> [<h 1> *metavar "="] *transform];

   ''::[P_SPECIAL_LIST(*p_specials,<>)]P_SPECIAL_LIST(*p_special) ->
       [<hov 1,0,0> **[<h 0> *p_specials ";"] *p_special];

end rules


end prettyprinter


%-----------------------------------------------------------------------------%
