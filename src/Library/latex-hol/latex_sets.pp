% latex_sets.pp by Wai Wong 15 may 1991 				%
%-----------------------------------------------------------------------%

% A pretty-printer for HOL sets library %

% Should be used along with a printer for HOL terms %

prettyprinter latex_sets =

abbreviations
   max_prec = {apply0 max_term_prec};

end abbreviations


rules
% rule for empty set %
   'term'::CONST(EMPTY(),**) -> [<h 0> "\EMPTYSET "];

% rule for GSPEC %
	'term'::COMB(CONST(GSPEC(),**),
		     ABS(*var,COMB(COMB(CONST(*),*elem),*spec))) ->
		[<h 0> "\BEGINSET " [<hv 1,1,0> *elem with
					prec := max_prec
					end with
			"\SUCHTHAT " *spec with
				prec := max_prec
				end with]
		 "\ENDSET "];

% rule for enumerated sets %
   'term'::[COMB(COMB(CONST(INSERT(),**),*elems),<>COMB(**))]
           COMB(COMB(CONST(INSERT(),**),*elem),CONST(EMPTY(),**)) ->
           [<h 0> "\BEGINSET " [<hv 0,0,0> **[<h 0> *elems with
                                                     prec := max_prec
                                                  end with
                                           ","]
                                  *elem with
                                           prec := max_prec
                                        end with] "\ENDSET "];

end rules

end prettyprinter
