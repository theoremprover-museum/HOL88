% latex_thm.pp by Wai Wong 15 may 1991 based on hol_thm.pp                    %
%-----------------------------------------------------------------------------%

% A pretty-printer for HOL theorems %

% Should be used along with printers for HOL terms and types %

prettyprinter latex_thm =

rules

  % Hypothesis to be printed only as an abbreviation %

   'thm'::dot() -> [<h 0> "."];

  % Strip node labelling a term before printing it. This assumes that rules %
  % exist for handling terms in the context `thm'.                          %

   'thm'::term(*term) -> [<h 0> *term];

  % Theorem with abbreviated hypotheses %

   'thm'::thm(*concl,dots(**dots)) ->
          [<h 1> [<h 0> **dots] "\THM" *concl];

  % Theorem with hypotheses in full (at least one hypothesis) %

   'thm'::thm(*concl,hyp(**hyps,*hyp)) ->
          [<hov 1,0,0> **[<h 0> **hyps ","]
                       *hyp
                       [<h 1> "\THM" *concl]];

  % Theorem with hypotheses in full (but no hypotheses present) %

   'thm'::thm(*concl,hyp()) -> [<h 1> "\THM" *concl];

end rules


end prettyprinter


%-----------------------------------------------------------------------------%
