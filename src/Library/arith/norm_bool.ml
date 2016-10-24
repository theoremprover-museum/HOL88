%****************************************************************************%
% FILE          : norm_bool.ml                                               %
% DESCRIPTION   : Functions for normalizing Boolean terms.                   %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 4th March 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 23rd July 1992                                             %
%****************************************************************************%

%============================================================================%
% Conversions for normalizing Boolean terms                                  %
%============================================================================%

%----------------------------------------------------------------------------%
% EQ_IMP_ELIM_QCONV : (term -> bool) -> conv                                 %
%                                                                            %
% Eliminates Boolean equalities and implications from terms consisting of    %
% =,==>,/\,\/,~ and atoms. The atoms are specified by the predicate that the %
% conversion takes as its first argument.                                    %
%----------------------------------------------------------------------------%

letrec EQ_IMP_ELIM_QCONV is_atom tm =
 (if (is_atom tm) then ALL_QCONV tm
  if (is_neg tm) then (RAND_QCONV (EQ_IMP_ELIM_QCONV is_atom)) tm
  if (is_eq tm) then
     ((ARGS_QCONV (EQ_IMP_ELIM_QCONV is_atom)) THENQC EQ_EXPAND_CONV) tm
  if (is_imp tm) then
     ((ARGS_QCONV (EQ_IMP_ELIM_QCONV is_atom)) THENQC IMP_EXPAND_CONV) tm
  else ARGS_QCONV (EQ_IMP_ELIM_QCONV is_atom) tm
 ) ?\s qfailwith s `EQ_IMP_ELIM_QCONV`;;

%----------------------------------------------------------------------------%
% MOVE_NOT_DOWN_QCONV : (term -> bool) -> conv -> conv                       %
%                                                                            %
% Moves negations down through a term consisting of /\,\/,~ and atoms. The   %
% atoms are specified by a predicate (first argument). When a negation has   %
% reached an atom, the conversion `qconv' (second argument) is applied to    %
% the negation of the atom. `qconv' is also applied to any non-negated atoms %
% encountered.                                                               %
%----------------------------------------------------------------------------%

letrec MOVE_NOT_DOWN_QCONV is_atom qconv tm =
 (if (is_atom tm) then (qconv tm)
  if (is_neg tm)
  then (let tm' = rand tm
        in  if (is_atom tm') then (qconv tm)
            if (is_neg tm') then (NOT_NOT_NORM_CONV THENQC
                                  (MOVE_NOT_DOWN_QCONV is_atom qconv)) tm
            if (is_conj tm') then
               (NOT_CONJ_NORM_CONV THENQC
                (ARGS_QCONV (MOVE_NOT_DOWN_QCONV is_atom qconv))) tm
            if (is_disj tm') then
               (NOT_DISJ_NORM_CONV THENQC
                (ARGS_QCONV (MOVE_NOT_DOWN_QCONV is_atom qconv))) tm
            else fail)
  if ((is_conj tm) or (is_disj tm)) then
     (ARGS_QCONV (MOVE_NOT_DOWN_QCONV is_atom qconv) tm)
  else fail
 ) ?\s qfailwith s `MOVE_NOT_DOWN_QCONV`;;

%----------------------------------------------------------------------------%
% DISJ_LINEAR_QCONV : conv                                                   %
%                                                                            %
% Linearizes disjuncts using the following conversion applied recursively:   %
%                                                                            %
%    "(x \/ y) \/ z"                                                         %
%    ================================                                        %
%    |- (x \/ y) \/ z = x \/ (y \/ z)                                        %
%----------------------------------------------------------------------------%

letrec DISJ_LINEAR_QCONV tm =
 (if ((is_disj tm) & (is_disj (arg1 tm)))
  then (DISJ_ASSOC_NORM_CONV THENQC
        (RAND_QCONV (TRY_QCONV DISJ_LINEAR_QCONV)) THENQC
        (TRY_QCONV DISJ_LINEAR_QCONV)) tm
  else fail
 ) ?\s qfailwith s `DISJ_LINEAR_QCONV`;;

%----------------------------------------------------------------------------%
% DISJ_NORM_FORM_QCONV : conv                                                %
%                                                                            %
% Puts a term involving /\ and \/ into disjunctive normal form. Anything     %
% other than /\ and \/ is taken to be an atom and is not processed.          %
%                                                                            %
% The disjunction returned is linear, i.e. the disjunctions are associated   %
% to the right. Each disjunct is a linear conjunction.                       %
%----------------------------------------------------------------------------%

letrec DISJ_NORM_FORM_QCONV tm =
 (if (is_conj tm) then
     (if (is_disj (arg1 tm)) then
         ((RATOR_QCONV (RAND_QCONV (ARGS_QCONV DISJ_NORM_FORM_QCONV))) THENQC
          (RAND_QCONV DISJ_NORM_FORM_QCONV) THENQC
          RIGHT_DIST_NORM_CONV THENQC
          (ARGS_QCONV DISJ_NORM_FORM_QCONV) THENQC
          (TRY_QCONV DISJ_LINEAR_QCONV)) tm
      if (is_disj (arg2 tm)) then
         ((RATOR_QCONV (RAND_QCONV DISJ_NORM_FORM_QCONV)) THENQC
          (RAND_QCONV (ARGS_QCONV DISJ_NORM_FORM_QCONV)) THENQC
          LEFT_DIST_NORM_CONV THENQC
          (ARGS_QCONV DISJ_NORM_FORM_QCONV) THENQC
          (TRY_QCONV DISJ_LINEAR_QCONV)) tm
      if (is_conj (arg1 tm)) then
         (CONJ_ASSOC_NORM_CONV THENQC DISJ_NORM_FORM_QCONV) tm
      else ((RAND_QCONV DISJ_NORM_FORM_QCONV) THENQC
            (\tm'. if (is_disj (arg2 tm'))
                   then DISJ_NORM_FORM_QCONV tm'
                   else ALL_QCONV tm')) tm)
  if (is_disj tm) then
     ((ARGS_QCONV DISJ_NORM_FORM_QCONV) THENQC
      (TRY_QCONV DISJ_LINEAR_QCONV)) tm
  else ALL_QCONV tm
 ) ?\s qfailwith s `DISJ_NORM_FORM_QCONV`;;
