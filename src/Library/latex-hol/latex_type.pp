% latex_type.pp by Wai Wong 15 may 1991 based on hol_type.pp                  %
%-----------------------------------------------------------------------------%

% A pretty-printer for HOL types %

prettyprinter latex_type =

declarations

  % Function for detecting infix type constructors %

   is_type_infix = {\meta. meta is_a_member_of [`fun`;`prod`;`sum`]};

  % Mapping infix constructors to their symbols %

   symb_of = {
              \symb. case symb
                     of `fun`  . `->`
                      | `prod` . `\\#`
                      | `sum`  . `+`
                      | _      . symb
             };

  % Functions for handling the precedence of type constructors %
  % Uses the function `type_prec' defined in `precedence.ml'   %

   prec = {bound_number `prec`};

   prec_of = {\meta. apply1 type_prec (bound_name meta)};

   prec_test = {\meta. apply2 (curry $<) (prec_of meta) prec};

end declarations


abbreviations
   symb = {symb_of};

  % `max_type_prec' is defined in the file `precedence.ml' %

   max_prec = {apply0 max_type_prec};

end abbreviations


rules

  % Variable types and the names of type constructors %

   'type'::VAR(***op()) -> [<h 0> symb(***op)];

   'type'::OP(***op())  -> [<h 0> symb(***op)];

  % Compound type with an infix constructor %

  % Type is enclosed in parentheses if constructor has a lower or the same %
  % precedence as the parent constructor. The precedence of the parent     %
  % constructor is held in the parameter `prec' and is updated prior to    %
  % recursive calls of the printer.                                        %

   'type'::OP(***op(),*type1,*type2) where {is_type_infix `op`} ->
           [<h 0> if {prec_test `op`} then [] else [<h 0> "("]
                  [<hv 1,3,0> [<h 1> *type1 with
                                               prec := {prec_of `op`}
                                            end with
                                     symb(***op)]
                              *type2 with
                                        prec := {prec_of `op`}
                                     end with]
                  if {prec_test `op`} then [] else [<h 0> ")"]];

  % All other compound types %

  % The recursive calls to print the sub-types are made with the precedence %
  % set to its highest numerical value (lowest precedence) so that the      %
  % sub-types do not appear enclosed within parentheses.                    %

   'type'::OP(***op(),**types,*type) ->
           [<hv 0,3,0> [<h 0> "("
                              [<hv 0,+3,0> **[<h 0> **types with
                                                               prec := max_prec
                                                            end with
                                                    ","]
                                           *type with
                                                    prec := max_prec
                                                 end with]
                              ")"]
                       symb(***op)];

  % Wrap quotes and a colon around type when a type labelling node is     %
  % encountered. Also, initialise precedence of parent constructor to be  %
  % lowest precedence (highest numerical value) so that the type within   %
  % the quotes is not enclosed within parentheses. This initialisation is %
  % also required to prevent an error occurring.                          %

   'type'::type(*type) -> [<h 0> """:"
                                 *type with
                                          prec := max_prec
                                       end with
                                 """"];

  % If type to be printed is part of a term, switch context and initialise %
  % precedence parameter. Call printer on whole tree. If the type passed   %
  % on from the term printer still contains its labelling node, the        %
  % previous rule will display an unwanted set of quotes in the middle of  %
  % the term.                                                              %

   'term'::*type -> [<h 0> 'type'::*type with
                                            prec := max_prec
                                         end with];

end rules


end prettyprinter


%-----------------------------------------------------------------------------%
