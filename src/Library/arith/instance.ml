%****************************************************************************%
% FILE          : instance.ml                                                %
% DESCRIPTION   : Conversional for increasing the power of a conversion by   %
%                 allowing it to work on a substitution instance of a term   %
%                 that is acceptable to it.                                  %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 30th January 1992                                          %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 29th July 1992                                             %
%****************************************************************************%

%----------------------------------------------------------------------------%
% INSTANCE_T_CONV : (term -> term list) -> conv -> conv                      %
%                                                                            %
% Generalizes a conversion that is used to prove formulae true by replacing  %
% any syntactically unacceptable subterms with variables, attempting to      %
% prove this generalised formula, and if successful re-instantiating.        %
% The first argument is a function for obtaining a list of syntactically     %
% unacceptable subterms of a term. This function should include in its       %
% result list any variables in the term that do not appear in other subterms %
% returned. The second argument is the conversion to be generalised.         %
%----------------------------------------------------------------------------%

let INSTANCE_T_CONV detector conv tm =
 let (univs,tm') = strip_forall tm
 in  let insts = setify (detector tm')
 in  let vars = map (genvar o type_of) insts
 in  let tm'' = list_mk_forall (vars,subst (combine (vars,insts)) tm')
 in  EQT_INTRO (GENL univs (SPECL insts (EQT_ELIM (conv tm''))));;
