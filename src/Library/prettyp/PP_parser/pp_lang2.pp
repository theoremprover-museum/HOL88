% pp_lang2.pp                                                                 %
%-----------------------------------------------------------------------------%


% A pretty-printer for the pretty-printing language (part 2) %

prettyprinter pp_lang2 =

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
   ''::INT_EXP(*int_exp) -> [<h 0> *int_exp];

   ''::ASSIGN(*id,*exp) -> [<hv 1,3,0> [<h 1> *id ":="] *exp];

   ''::[ASSIGNMENTS(*assigns,<>)]ASSIGNMENTS(*assign) ->
       [<hov 1,0,0> **[<h 0> *assigns ";"] *assign];

   ''::F_SUBCALL(*child) -> [<h 0> *child];

   ''::F_SUBCALL(*transform,*metavar) ->
       [<hv 0,3,0> *transform [<h 0> "(" *metavar ")"]];

   ''::C_SUBCALL(*f_subcall) -> [<h 0> *f_subcall];

   ''::C_SUBCALL(*string,*f_subcall) ->
       [<hv 0,3,0> [<h 0> *string "::"] *f_subcall];

   ''::LEAF_OR_SUBCALL(*c_subcall,**assigns) ->
       [<hv 1,3,0> *c_subcall
                   **[<v 0,0> "with"
                              <3,0> **assigns
                              "end with"]];

   ''::INC(*num) -> [<h 0> "+" *num];

   ''::H_PARAMS(*num) -> [<h 0> *num];

   ''::V_PARAMS(*indent,*num) -> [<h 0> *indent "," *num];

   ''::HV_PARAMS(*num1,*indent,*num2) -> [<h 0> *num1 "," *indent "," *num2];

   ''::HOV_PARAMS(*num1,*indent,*num2) -> [<h 0> *num1 "," *indent "," *num2];

   ''::H_BOX(*h_params) -> [<h 1> "h" *h_params];

   ''::V_BOX(*v_params) -> [<h 1> "v" *v_params];

   ''::HV_BOX(*hv_params) -> [<h 1> "hv" *hv_params];

   ''::HOV_BOX(*hov_params) -> [<h 1> "hov" *hov_params];

   ''::OBJECT(*object) -> [<h 0> *object];

   ''::H_OBJECT(**h_params,*object) ->
       [<hv 1,3,0> **[<h 0> "<" **h_params ">"] *object];

   ''::V_OBJECT(**v_params,*object) ->
       [<hv 1,3,0> **[<h 0> "<" **v_params ">"] *object];

   ''::HV_OBJECT(**hv_params,*object) ->
       [<hv 1,3,0> **[<h 0> "<" **hv_params ">"] *object];

   ''::HOV_OBJECT(**hov_params,*object) ->
       [<hv 1,3,0> **[<h 0> "<" **hov_params ">"] *object];

   ''::[H_OBJECT_LIST(*h_objects,<>)]H_OBJECT_LIST(*h_object) ->
       [<hov 1,0,0> *h_objects *h_object];

   ''::[V_OBJECT_LIST(*v_objects,<>)]V_OBJECT_LIST(*v_object) ->
       [<hov 1,0,0> *v_objects *v_object];

   ''::[HV_OBJECT_LIST(*hv_objects,<>)]HV_OBJECT_LIST(*hv_object) ->
       [<hov 1,0,0> *hv_objects *hv_object];

   ''::[HOV_OBJECT_LIST(*hov_objects,<>)]HOV_OBJECT_LIST(*hov_object) ->
       [<hov 1,0,0> *hov_objects *hov_object];

   ''::BOX_SPEC(*box,*object_list) ->
       [<h 0> "<" *box ">" <1> *object_list];

   ''::EXPAND(*box_spec) -> [<h 0> "**[" *box_spec "]"];

   ''::FORMAT() -> [<h 0> "[]"];

   ''::FORMAT(*box_spec) -> [<h 0> "[" *box_spec "]"];

   ''::FORMAT(*test,*format1,*format2) ->
       [<hov 1,0,0> [<h 1> "if" *test]
                    [<h 1> "then" *format1]
                    [<h 1> "else" *format2]];

   ''::RULE(PATTERN(*string,*patt_tree,**test),**p_specials,*format) ->
       [<h 0> *string
              "::"
              [<hov 1,0,0> [<h 1> [<hv 1,3,0> *patt_tree
                                              **[<hv 1,3,0> "where" **test]]
                                  "->"]
                           **[<h 1> "<<" **p_specials ">>"]
                           *format]];

  % `rules' is a keyword, so it must be quoted. %

   ''::[RULE_LIST(*#rules#,<>)]RULE_LIST(*rule) ->
       [<v 0,1> **[<h 0> *#rules# ";"] [<h 0> *rule ";"]];

   ''::RULES(*rule_list) ->
       [<v 3,0> "rules" *rule_list <0,1> "end rules"];

   ''::BINDING(*id,*ml_fun) ->
       [<hv 1,3,0> [<h 1> *id "="] *ml_fun];

   ''::[BINDING_LIST(*bindings,<>)]BINDING_LIST(*binding) ->
       [<v 0,1> **[<h 0> *bindings ";"] [<h 0> *binding ";"]];

   ''::DECLARS(*binding_list) ->
       [<v 3,0> "declarations" *binding_list <0,1> "end declarations"];

   ''::ABBREVS(*binding_list) ->
       [<v 3,0> "abbreviations" *binding_list <0,1> "end abbreviations"];

   ''::BODY(**x) -> [<v 0,2> **x];

   ''::PP(*id,*body) ->
       [<v 0,1> [<h 1> "prettyprinter" *id "="]
                *body
                <0,2> "end prettyprinter"];

end rules


end prettyprinter


%-----------------------------------------------------------------------------%
