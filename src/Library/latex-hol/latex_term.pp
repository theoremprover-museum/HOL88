% latex_term.pp by Wai Wong 15 May 1991 based on hol_term.pp                  %
%-----------------------------------------------------------------------------%

% A pretty-printer for HOL terms %
				   
% Should be used along with a printer for HOL types %

prettyprinter latex_term =

declarations

  % Function for detecting associative operators %

   is_right_assoc = {
                     \meta. meta is_a_member_of
                               [`/\\`;`\\/`;`<=>`;`o`;`+`;`*`;`EXP`]
                    };

  % Function for detecting infix operators %

   is_an_infix = {\meta. apply1 is_infix (bound_name meta)};

  % Function for detecting binders %

   is_a_res_quan = {\meta. apply1 is_res_quan (bound_name meta)};

  % Function for detecting binders %

   is_a_binder = {\meta. apply1 is_binder (bound_name meta)};

   nullvarl = {\meta. apply1 null (bound_children meta)};

  % Functions for handling the precedence of terms           %
  % Uses the function `term_prec' defined in `precedence.ml' %

   prec = {bound_number `prec`};

   prec_of = {\meta. apply1 term_prec (bound_name meta)};

   prec_of_const = {\symb. apply0 (term_prec symb)};

   prec_test_metab = {\meta. apply2 (curry $>) (prec_of meta) prec};

   prec_test_meta = {\meta. apply2 (curry $<) (prec_of meta) prec};

   prec_test_const = {\symb. apply2 (curry $<) (prec_of_const symb) prec};


  % Function to prefix an operator with a `$' if it is an infix, a binder %
  % or ~.                                                                 %
    prefix_sym = {
             \symb. let prf = if ((is_infix symb) or (is_binder symb))
			 then (`\\$`) else (``) in
                    (if (exists (\s. symb = s)
			[`/\\`; `\\/`; `==>`; `<=>`; `*`; `~`; `!`; `?`] )
			then (prf ^ symb_of(symb))
                    else (prf ^ `\\CONST{{` ^ symb_of(symb) ^ `}}`))
            };  

end declarations


abbreviations

  symb = { symb_of };
  prefix = { prefix_sym };
  mkvar = { dovar };
  mkinfix =  { doinfix };

  % Function to reverse a list of sub-trees bound to a metavariable %

   rev = {rev};

  % `min_term_prec' and `max_term_prec' are defined in the file %
  % `precedence.ml'.                                            %

   min_prec = {apply0 min_term_prec};

   max_prec = {apply0 max_term_prec};

end abbreviations


rules

  % The constant `NIL' is printed as `[]' %

   'term'::CONST(NIL(),**) -> [<h 0> "\NIL "];

  % Variables with no type information %

   'term'::VAR(***var()) -> [<h 0> mkvar(***var)];

  % Variables with type information %

  % The node `type', used to label the sub-tree for the type, is stripped %
  % off before printing it. This assumes that rules exist for handling    %
  % types in the context `term'. The `:' used to separate the variable    %
  % name from its type is taken to have a precedence. This is used to     %
  % determine whether or not to put parentheses around the variable/type  %
  % unit.                                                                 %

   'term'::VAR(***var(),type(*type)) ->
           [<h 0> if {prec_test_const `:`} then [] else [<h 0> "("]
                  [<hv 0,0,0> mkvar(***var) [<h 0> ":" *type]]
                  if {prec_test_const `:`} then [] else [<h 0> ")"]];

  % Constants are prefixed with `$' if infixes, binders or ~. Note that this %
  % pretty-printer contains many rules which have special actions for        %
  % particular constants. These rules are set up to work whether or not type %
  % information is present. This is done by using ** to match the sub-tree   %
  % containing the type information. ** can also match nothing, so it also   %
  % works if the type information is not present.                            %

  % Constants with no type information %

   'term'::CONST(***const()) -> [<h 0> prefix(***const)];

  % Constants with type information %

   'term'::CONST(***const(),type(*type)) ->
           [<h 0> if {prec_test_const `:`} then [] else [<h 0> "("]
                  [<hv 0,0,0> prefix(***const) [<h 0> ":" *type]]
                  if {prec_test_const `:`} then [] else [<h 0> ")"]];

  % Pairs. %

  % These are treated separately from other infixes because no space is to %
  % appear between the comma and the components of the pair.               %

  % The rule actually deals with tuples represented by nested pairs. This  %
  % prevents unnecessary bracketing.                                       %

   'term'::[COMB(COMB(CONST(***op(),**),*comps),<1..:***op>)]*comp
              where {`op` is_a_member_of [`,`]} ->
           [<h 0> if {prec_test_meta `op`} then [] else [<h 0> "("]
                  [<hv 0,0,0> **[<h 0> *comps with
                                                 prec := {prec_of `op`}
                                              end with
                                       ***op]
                              *comp with
                                       prec := {prec_of `op`}
                                    end with]
                  if {prec_test_meta `op`} then [] else [<h 0> ")"]];

  % Associative operators (assumed to be right associative) %

% special rule for EXP %
   'term'::[COMB(COMB(CONST(***op(),**),*args),<1..:***op>)]*arg
              where { `op` is_a_member_of [`EXP`] } ->
           [<h 0> if {prec_test_meta `op`} then [] else [<h 0> "("]
                  [<hov 1,0,0> "(" **[<hv 1,0,0> *args with
                                                      prec := {prec_of `op`}
                                                   end with
                                  ")\:\CONST{EXP}\:(" ]
                               *arg with
                                       prec := {prec_of `op`}
                                    end with ")" ]
                  if {prec_test_meta `op`} then [] else [<h 0> ")"]];

  % These are dealt with separately from other infixes so that unnecessary %
  % levels of parentheses can be omitted. To avoid ambiguities, the normal %
  % rule for infixes inserts parentheses when two operators of the same    %
  % precedence occur together. If the two operators are the same, and the  %
  % operator is associative, the ambiguity can only be in the structure,   %
  % not in the meaning.                                                    %

  % The rule deals with not just two operators, but a whole chain of them. %
  % If the sub-expressions do not fit on one line, they appear vertically, %
  % each but the last being followed by the operator.                      %

   'term'::[COMB(COMB(CONST(***op(),**),*args),<1..:***op>)]*arg
              where {is_right_assoc `op`} ->
           [<h 0> if {prec_test_meta `op`} then [] else [<h 0> "("]
                  [<hov 1,0,0> **[<hv 1,0,0> *args with
                                                      prec := {prec_of `op`}
                                                   end with
                                             symb(***op)]
                               *arg with
                                       prec := {prec_of `op`}
                                    end with]
                  if {prec_test_meta `op`} then [] else [<h 0> ")"]];

  % Infixes. %

  % Note that rules which deal with more specialised infixes appear before %
  % this rule so as to have priority over it.                              %

   'term'::COMB(COMB(CONST(***op(),**),*arg1),*arg2)
              where {is_an_infix `op`} ->
           [<h 0> if {prec_test_meta `op`} then [] else [<h 0> "("]
                  [<hv 1,3,0> [<h 1> *arg1 with
                                              prec := {prec_of `op`}
                                           end with
                                     mkinfix(***op)]
                              *arg2 with
                                       prec := {prec_of `op`}
                                    end with]
                  if {prec_test_meta `op`} then [] else [<h 0> ")"]];

  % Rule for `~'. %

  % This is dealt with separately from other prefixes because no space is %
  % to appear between the `~' and its argument.                           %

   'term'::COMB(CONST(***op(),**),*arg)
              where {`op` is_a_member_of [`~`]} ->
           [<h 0> if {prec_test_meta `op`} then [] else [<h 0> "("]
                  symb(***op)
                  *arg with
                          prec := {prec_of `op`}
                       end with
                  if {prec_test_meta `op`} then [] else [<h 0> ")"]];

  % Restricted quatifiers. %

   'term'::[COMB(COMB(CONST(***op(),**),*pred),ABS(*bvs,<1..:***op;*pred>))]*body
              where {is_a_res_quan `op`} ->

		<< *bv = {new_children (\x. [hd x]) `bvs`};
		   *bvs = {new_children tl `bvs`} >>

           [<h 0> if {prec_test_metab `op`} then [<h 0> "("] else []
                  [<hv 1,3,0>
    	    	     [<h 0> symb(***op)
                    	 [<h 1> *bv
				if {nullvarl `bvs`}
				then []
				else [<h 1> **[<h 0> "\," *bvs with
                                                    prec := min_prec
                                                 end with ]]] 
			 "\RESDOT "
			 [<h 1> *pred with 
				  prec := {prec_of `op`}
					end with ]
                                     "\DOT"]
                              *body with
                                       prec := {prec_of `op`}
                                    end with]
                  if {prec_test_metab `op`} then [<h 0> ")"] else [] ];

  % Binders. %

  % When a binder is applied to an abstraction, the name of the binder   %
  % replaces the lambda. This rule deals with nested bindings, pulling   %
  % the bound variables into a list. The name of the binder is displayed %
  % only once, followed by the bound variables separated by spaces,      %
  % followed by a dot and the body of the binding.                       %

  % The rule assumes that terms containing bound variables as tuples     %
  % have been converted from the form using `UNCURRY' to a form in which %
  % a tuple takes the place of a single bound variable. As a term, the   %
  % latter form is not valid, but as a parse-tree it is fine. The rule   %
  % implicitly handles tuples in place of variables, because it makes a  %
  % recursive call to print the bound variables. Actually this is not    %
  % quite true. To ensure that a tuple of variables is enclosed within   %
  % parentheses, the recursive call has to be made with the precedence   %
  % set to its lowest value (highest precedence). Single variables will  %
  % not appear in parentheses because the rule for variables ignores the %
  % value of the precedence parameter.                                   %

   'term'::[COMB(CONST(***op(),**),ABS(*bvs,<1..:***op>))]*body
              where {is_a_binder `op`} ->

		<< *bv = {new_children (\x. [hd x]) `bvs`};
		   *bvs = {new_children tl `bvs`} >>

           [<h 0> if {prec_test_metab `op`} then [<h 0> "("] else []
                  [<hv 1,3,0>
    	    	     [<h 0> symb(***op)
                    	 [<h 1> *bv
				if {nullvarl `bvs`}
				then []
				else [<h 1> **[<h 0> "\," *bvs with
                                                    prec := min_prec
                                                 end with ]]] 
                                     "\DOT"]
                              *body with
                                       prec := {prec_of `op`}
                                    end with]
                  if {prec_test_metab `op`} then [<h 0> ")"] else []];

  % Abstractions. %

  % The lambda of abstractions is allocated a precedence. The rule is %
  % analogous to the one for binders. See the comments for that rule. %

   'term'::[ABS(*bvs,<>ABS(**))]ABS(*bv, *body)
		->
           [<h 0> if {prec_test_const `\\`} then [] else [<h 0> "("]
                  [<hv 1,3,0> [<h 1> "\LAMBDA"
                                     [<h 1>  **[<h 1> *bvs  with
                                                    prec := min_prec
                                                 end with "\,"]]
                                *bv     "\DOT"]
                              *body with
                                       prec := {prec_of_const `\\`}
                                    end with]
                  if {prec_test_const `\\`} then [] else [<h 0> ")"]];

  % Conditionals. %

  % All three sub-expressions are printed subject to the precedence of %
  % the `COND' constant.                                               %

   'term'::COMB(COMB(COMB(CONST(COND(),**),*cond),*x),*y) ->
           [<h 0> "("
                  [<hov 1,0,0> [<hv 1,0,0> *cond with
                                                    prec :=
                                                       {prec_of_const `COND`}
                                                 end with
                                           "\Rightarrow "]
                               [<hv 1,0,0> *x with
                                                 prec := {prec_of_const `COND`}
                                              end with
                                           "\mid "]
                               *y with
                                     prec := {prec_of_const `COND`}
                                  end with]
                   ")"];

  % Let statements %

  % The second rule is the main rule for `LET'. The pattern loops down a  %
  % chain of LETs, stopping before the last one so that it can bind the   %
  % sub-expressions for the last LET separately. It does this because the %
  % last LET is in fact the first one to appear in the textual            %
  % representation (i.e. the LET chain is in reverse order) and the first %
  % textual LET is printed differently to the others (it begins with      %
  % `let' whereas the others begin with `and').                           %

  % At the end of the chain of LETs there is a chain of abstractions, the %
  % bound variables of which are the variables being declared. These are  %
  % in the textual order. After the chain of abstractions, comes the `in' %
  % body (which is bound to the metavariable `*body').                    %

  % For each LET in the chain there is a chain of abstractions. The bound %
  % variables are the arguments of the identifier being declared, and the %
  % body is the body of the declaration. The pattern binds the bodies to  %
  % the metavariables `*letbodyl' and `*letbody'. Each of the abstraction %
  % chains is also bound (to either `*argsl' or `*args'). The individual  %
  % arguments cannot be bound because lists of lists are flattened by the %
  % pretty-printer. An attempt to bind the individual arguments would     %
  % result in one list of all the arguments to all of the LETs, with no   %
  % indication of which arguments belong to which LET. The first of the   %
  % two rules for pretty-printing let statements is used to print the     %
  % chain of arguments for each LET. It throws away the body. It only     %
  % matches in the context of having been called from the second `let'    %
  % rule. It makes recursive calls to the printer to print the variables  %
  % in the normal context for terms.                                      %

  % If the number of argument sets is not the same as the number of       %
  % variables seemingly being declared, the rule fails to match (this is  %
  % done by the `where' clause). The LETs will then be printed as raw     %
  % terms. The difference in numbers occurs if the `in' body is itself a  %
  % lambda abstraction, and although this structure can be printed as a   %
  % proper `let' statement, the standard HOL pretty-printer does not do   %
  % it.                                                                   %

  % As indicated previously, some of the bound lists are in reverse       %
  % order. This is rectified before using the format to display the text. %

  % The identifiers declared in the let statement, and the names of their %
  % arguments are printed subject to the highest precedence (lowest       %
  % numerical value). This ensures that they are enclosed within          %
  % parentheses if they are in fact tuples rather than single variables.  %
  % This assumes that instances of UNCURRY have been converted (see the   %
  % comments for the rule for binders).                                   %

   'term_let'::[ABS(*args,<>)] -> [<h 1> 'term'::*args];

   'term'::[COMB(COMB(CONST(LET(),**),<>COMB(COMB(CONST(LET(),**),*),*)),
                 |*argsl|[ABS(*,<>)]*letbodyl)]
           COMB(COMB(CONST(LET(),**),ABS(*bv,[ABS(*bvl,<>)]*body)),
                |*args|[ABS(*,<>)]*letbody)

              where {
                     apply2 (\x y. length x = length y)
                               (bound_children `bvl`)
                                  (bound_children `argsl`)
                    } ->

           << **argsl = {new_children rev `argsl`};
              **letbodyl = {new_children rev `letbodyl`} >>

           [<h 0> if {prec_test_const `LET`} then [] else [<h 0> "("]
                  [<hov 1,0,0> [<hv 1,1,0> [<h 1> "\KEYWD{let}\;"
                                                  *bv with
                                                         prec := min_prec
                                                      end with
                                                  'term_let'::*args
                                                     with
                                                        prec := min_prec
                                                     end with
                                                  "="]
                                           *letbody with
                                                       prec :=
                                                          {prec_of_const `LET`}
                                                    end with]
                               **[<hv 1,1,0> **[<hv 1,0,0> "\;\KEYWD{and}"
                                                      *bvl with
                                                              prec := min_prec
                                                           end with
                                                      'term_let'::**argsl
                                                         with
                                                            prec := min_prec
                                                         end with
                                                      "="]
                                             **letbodyl
                                                with
                                                   prec :=
                                                      {prec_of_const `LET`}
                                                end with]
                               [<v 0,0> "\;\KEYWD{in}"
                                [<hv 1,0,0> *body with
                                               prec := {prec_of_const `LET`}
                                            end with]]]
                  if {prec_test_const `LET`} then [] else [<h 0> ")"]];

  % Lists (see also the rule for the constant `NIL') %

  % The elements of the list are obtained from a chain of applications of %
  % the constant `CONS'. The looping pattern used stops before the last   %
  % CONS so that the last element can be bound separately. The last       %
  % element has to be treated differently (it is not followed by a        %
  % semi-colon). The rule works for lists of one or more elements.        %

  % Lists are not explicitly assigned a precedence. They never need to be %
  % enclosed within parentheses because they are already enclosed within  %
  % brackets. `;' is given the lowest possible precedence (highest        %
  % numerical value), so the elements of a list never appear enclosed     %
  % within parentheses.                                                   %

   'term'::[COMB(COMB(CONST(CONS(),**),*elems),<>COMB(**))]
           COMB(COMB(CONST(CONS(),**),*elem),CONST(NIL(),**)) ->
           [<h 0> "["
                  [<hov 0,0,0> **[<h 0> *elems with
                                                  prec := max_prec
                                               end with
                                        ";"]
                               *elem with
                                        prec := max_prec
                                     end with]
                  "]"];

  % Function applications. %

  % Every application not covered by a preceding rule is dealt with by  %
  % this one. The precedence used is that of the null string. The       %
  % precedence table assigns the highest precedence to anything it does %
  % not recognise. Thus user defined functions have the highest         %
  % precedence. So, the arguments to the function appear in parentheses %
  % unless they are just identifiers. This rule deals with functions    %
  % applied to one or more arguments. Note that the pattern binds the   %
  % arguments in the reverse of the textual order, so the list has to   %
  % be reversed before printing.                                        %

   'term'::[COMB(<1..>,*rands)]*rator ->
		<< *rands = {new_children rev `rands`} >>
           [<h 0> if {prec_test_const ``} then [] else [<h 0> "("]
                  [<hv 1,3,0> *rator with
                                        prec := {prec_of_const ``}
                                     end with
                              **[<h 0> "\," *rands with
                                             prec := {prec_of_const ``}
                                          end with]]
                  if {prec_test_const ``} then [] else [<h 0> ")"]];

  % Wrap quotes around term when a term labelling node is encountered.     %
  % Also, initialise precedence of parent constructor to be lowest         %
  % precedence (highest numerical value) so that the term within the       %
  % quotes is not enclosed within parentheses. This initialisation is also %
  % required to prevent an error occurring.                                %

   'term'::term(*term) -> [<h 0> """"
                                 *term with
                                          prec := max_prec
                                       end with
                                 """"];

  % If term to be printed is part of a thm, switch context and initialise  %
  % precedence parameter. Call printer on whole tree. If the term passed   %
  % on from the thm printer still contains its labelling node, the         %
  % previous rule will display an unwanted set of quotes in the middle of  %
  % the thm.                                                               %

   'thm'::*term -> [<h 0> 'term'::*term with
                                           prec := max_prec
                                        end with];

end rules


end prettyprinter


%-----------------------------------------------------------------------------%
