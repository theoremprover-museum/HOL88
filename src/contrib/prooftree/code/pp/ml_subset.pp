
% Pretty-printing rules for a subset of ML %

% These rules are used to generate ML code from a parse-tree.   %
% Precedence could be used to reduce the number of parentheses. %


prettyprinter ml_subset =

declarations

  % Functions for detecting infix operators %

   is_curried_infix = {\meta. apply1 is_ml_curried_infix (bound_name meta)};

   is_paired_infix = {\meta. apply1 is_ml_paired_infix (bound_name meta)};

end declarations


rules
  % Void %

   'ml'::#MK-EMPTY#() -> [<h 0> "()"];

  % Boolean constant %

   'ml'::#MK-BOOLCONST#(***n()) -> [<h 0> ***n];

  % Integer constant %

   'ml'::#MK-INTCONST#(***n()) -> [<h 0> ***n];

  % String constant %

   'ml'::#MK-TOKCONST#(***n()) -> [<h 0> "`" ***n "`"];

  % Variable %

   'ml'::#MK-VAR#(***n()) -> [<h 0> ***n];

  % Concrete type constructor with argument %

   'ml'::#MK-CON#(***n()) -> [<h 0> ***n];

  % Concrete type constructor with no argument %

   'ml'::#MK-CON0#(***n()) -> [<h 0> ***n];

  % Application of unary operator %

   'ml'::#MK-UNOP#(***n(),*c) -> [<h 0> "(" [<hv 0,0,0> ***n *c] ")"];

  % Application of binary operator %

   'ml'::#MK-BINOP#(***n(),*c1,*c2) ->
         [<h 0> "(" [<hv 1,+1,0> *c1 ***n *c2] ")"];

  % Infixes %

   'ml'::[#MK-APPN#(<1..>#MK-APPN#(#MK-APPN#(*,*),*),*cs)]
         #MK-APPN#(#MK-APPN#(#MK-VAR#(***name()),*arg1),*arg2)
            where {is_curried_infix `name`} ->
         [<h 0> "("
          [<hv 1,+1,0>
           [<h 0> "(" [<hv 1,0,0> [<h 1> 'ml-infix'::*arg1 ***name] *arg2] ")"]
           {rev}(*cs)] ")"];

   'ml'::#MK-APPN#(#MK-APPN#(#MK-VAR#(***name()),*arg1),*arg2)
            where {is_curried_infix `name`} ->
         [<h 0> "(" [<hv 1,0,0> [<h 1> 'ml-infix'::*arg1 ***name] *arg2] ")"];

   'ml-infix'::#MK-APPN#(#MK-APPN#(#MK-VAR#(***name()),*arg1),*arg2)
                  where {is_curried_infix `name`} ->
               [<hv 1,0,0> [<h 1> *arg1 ***name] 'ml'::*arg2];

   'ml'::[#MK-APPN#(<1..>#MK-APPN#(*,*),*cs)]
         #MK-APPN#(#MK-VAR#(***name()),#MK-DUPL#(*arg1,*arg2))
            where {is_paired_infix `name`} ->
         [<h 0> "("
          [<hv 1,+1,0>
           [<h 0> "(" [<hv 1,0,0> [<h 1> 'ml-infix'::*arg1 ***name] *arg2] ")"]
           {rev}(*cs)] ")"];

   'ml'::#MK-APPN#(#MK-VAR#(***name()),#MK-DUPL#(*arg1,*arg2))
            where {is_paired_infix `name`} ->
         [<h 0> "(" [<hv 1,0,0> [<h 1> 'ml-infix'::*arg1 ***name] *arg2] ")"];


   'ml-infix'::#MK-APPN#(#MK-VAR#(***name()),#MK-DUPL#(*arg1,*arg2))
                  where {is_paired_infix `name`} ->
               [<hv 1,0,0> [<h 1> *arg1 ***name] 'ml'::*arg2];

   'ml-infix'::*c -> [<h 0> 'ml'::*c];

  % Function application %

   'ml'::[#MK-APPN#(<1..>,*cs)]*cs -> [<h 0> "(" [<hv 1,+1,0> {rev}(*cs)] ")"];

  % Abstraction %

   'ml'::[#MK-ABSTR#(*vars,<1..>)]*c ->
         [<h 0> "(" "\" [<hv 1,1,0> [<h 1> *vars <0> "."] *c] ")"];

  % List of at least one element %

   'ml'::#MK-LIST#(**cl,*c) ->
         [<h 0> "[" [<hov 0,0,0> **[<h 0> **cl ";"] *c] "]"];

  % Empty list %

   'ml'::#MK-LIST#() -> [<h 0> "[]"];

  % Tuple %

   'ml'::[#MK-DUPL#(*cl,<1..>)]*c ->
         [<h 0> "(" [<hv 0,0,0> **[<h 0> *cl ","] *c] ")"];

  % if ... then ... then ... else ... %

   'ml'::#MK-TEST#(LIST(**onces),once(*c)) ->
         [<h 0> "(" [<hov 1,0,0> **onces [<hv 1,1,0> "else" *c]] ")"];

  % if ... then ... then ... %

   'ml'::#MK-TEST#(LIST(**onces)) -> [<h 0> "(" [<hov 1,0,0> **onces] ")"];

  % if ... then ... %

   'ml'::once(*c1,*c2) ->
         [<hv 1,0,0> [<hv 1,1,0> "if" *c1] [<hv 1,1,0> "then" *c2]];

  % letrec ... and ... %

   'ml'::#MK-LETREC#(#MK-DUPL#(*var1,[#MK-DUPL#(*varl,<>)]*varl),
                     #MK-DUPL#(*body1,[#MK-DUPL#(*bodyl,<>)]*bodyl)) ->
         [<v 0,0> [<hv 1,+1,0> "letrec" [<h 1> *var1 "="] *body1]
                  **[<hv 1,+1,0> "and" **[<h 1> *varl "="] *bodyl]];

  % letrec ... %

   'ml'::#MK-LETREC#(*c1,*c2) -> [<hv 1,+1,0> "letrec" [<h 1> *c1 "="] *c2];

  % let ... and ... %

   'ml'::#MK-LET#(#MK-DUPL#(*var1,[#MK-DUPL#(*varl,<>)]*varl),
                  #MK-DUPL#(*body1,[#MK-DUPL#(*bodyl,<>)]*bodyl)) ->
         [<v 0,0> [<hv 1,+1,0> "let" [<h 1> *var1 "="] *body1]
                  **[<hv 1,+1,0> "and" **[<h 1> *varl "="] *bodyl]];

  % let ... %

   'ml'::#MK-LET#(*c1,*c2) -> [<hv 1,+1,0> "let" [<h 1> *c1 "="] *c2];

  % in ... %

   'ml'::#MK-IN#(*c1,*c2) ->
         [<h 0> "(" [<v 0,0> *c1 [<hv 1,1,0> "in" *c2]] ")"];

  % Terms %

   'ml'::|*term|term(*) -> [<h 0> 'term'::*term];

  % Types %

   'ml'::|*type|type(*) -> [<h 0> 'type'::*type];

  % Typed terms %

   'term'::#MK=TYPED#(*term,*type) ->
           [<hv 0,0,0> [<h 0> "(" *term ] [<h 0> ":" *type] ")"];

  % Antiquotations in terms %

   'term'::#MK=ANTIQUOT#(*ml) -> [<h 0> "(" "^" 'ml'::*ml ")"];

  % Antiquotations in types %

   'type'::#MK=TYPE=ANTIQUOT#(*ml) -> [<h 0> "(" "^" 'ml'::*ml ")"];

end rules


end prettyprinter
