%****************************************************************************%
% FILE          : generalize.ml                                              %
% DESCRIPTION   : Generalization.                                            %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 21st June 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 12th October 1992                                          %
%****************************************************************************%

%----------------------------------------------------------------------------%
% is_generalizable : string list -> term -> bool                             %
%                                                                            %
% Function to determine whether or not a term has the correct properties to  %
% be generalizable. It takes a list of accessor function names as its first  %
% argument. This is for efficiency. It could compute them itself, but if an  %
% external function is going to call is_generalizable many times it is       %
% better for the external function to compute the list of accessors.         %
%----------------------------------------------------------------------------%

let is_generalizable accessors tm =
   not ((is_var tm) or
        (is_explicit_value_template tm) or
        (is_eq tm) or
        (mem ((fst o dest_const o fst o strip_comb) tm) accessors ? false));;

%----------------------------------------------------------------------------%
% generalizable_subterms : string list -> term -> term list                  %
%                                                                            %
% Computes the generalizable subterms of a literal, given a list of accessor %
% function names.                                                            %
%----------------------------------------------------------------------------%

let generalizable_subterms accessors tm =
 (setify (find_bm_terms (is_generalizable accessors) tm)
 ) ? failwith `generalizable_subterms`;;

%----------------------------------------------------------------------------%
% minimal_common_subterms : term list -> term list                           %
%                                                                            %
% Given a list of terms, this function removes from the list any term that   %
% has one of the other terms as a proper subterm. It also eliminates any     %
% duplicates.                                                                %
%----------------------------------------------------------------------------%

let minimal_common_subterms tml =
   let tml' = setify tml
   in  filter
        (\tm. not (exists (\tm'. (is_subterm tm' tm) & (not (tm' = tm))) tml'))
         tml';;

%----------------------------------------------------------------------------%
% to_be_generalized : term -> term list -> term -> bool                      %
%                                                                            %
% This function decides whether a subterm of a literal should be generalized.%
% It takes a literal, a list of other literals, and a subterm of the literal %
% as arguments. The subterm should be generalized if it occurs in one of the %
% other literals, or if the literal is an equality and it occurs on both     %
% sides, or if the literal is the negation of an equality and the subterm    %
% occurs on both sides.                                                      %
%----------------------------------------------------------------------------%

let to_be_generalized tm tml gen =
 (let (l,r) = dest_eq (dest_neg tm)
  in  if ((is_subterm gen l) & (is_subterm gen r))
      then true
      else fail) ?
 (let (l,r) = dest_eq tm
  in  if ((is_subterm gen l) & (is_subterm gen r))
      then true
      else fail) ?
 (exists (is_subterm gen) tml);;

%----------------------------------------------------------------------------%
% terms_to_be_generalized : term -> term list                                %
%                                                                            %
% Given a clause, this function determines the subterms of the clause that   %
% are to be generalized. For each literal, the function computes the         %
% generalizable subterms. It then filters out those subterms that are not to %
% be generalized. It only looks at the remaining literals when doing this,   %
% not at those already processed. This is legitimate because if the subterm  %
% occurs in a previous literal, it would have already been added to the main %
% list of subterms that should be generalized. Before returning this main    %
% list, the function removes any non-minimal common subterms. This operation %
% also removes any duplicates.                                               %
%----------------------------------------------------------------------------%

let terms_to_be_generalized tm =
   let accessors = all_accessors ()
   in  letrec terms_to_be_generalized' tml =
          if (null tml)
          then []
          else let h.t = tml
               in  let gens = generalizable_subterms accessors h
               in  let gens' = filter (to_be_generalized h t) gens
               in  gens' @ (terms_to_be_generalized' t)
   in  minimal_common_subterms (terms_to_be_generalized' (disj_list tm));;

%----------------------------------------------------------------------------%
% distinct_var : term list -> type -> term                                   %
%                                                                            %
% Function to generate a sensibly-named variable of a specified type.        %
% Variables that the new variable must be distinct from can be specified in  %
% the first argument. The new variable will be named according to the first  %
% letter of the top-level constructor in the specified type, or if the type  %
% is a simple polymorphic type, the name `x' is used. The actual name will   %
% be this name followed by zero or more apostrophes.                         %
%----------------------------------------------------------------------------%

let distinct_var vars ty =
   let letter = ((hd o explode o fst o dest_type) ty) ? `x`
   in  variant vars (mk_var (letter,ty));;

%----------------------------------------------------------------------------%
% distinct_vars : term list -> type list -> term list                        %
%                                                                            %
% Generates new variables using `distinct_var' for each of the types in the  %
% given list. The function ensures that each of the new variables are        %
% distinct from each other, as well as from the argument list of variables.  %
%----------------------------------------------------------------------------%

letrec distinct_vars vars tyl =
   if (null tyl)
   then []
   else let var = distinct_var vars (hd tyl)
        in  var.(distinct_vars (var.vars) (tl tyl));;

%----------------------------------------------------------------------------%
% apply_gen_lemma : term -> thm -> thm                                       %
%                                                                            %
% Given a term to be generalized and a generalization lemma, this function   %
% tries to apply the lemma to the term. The result, if successful, is a      %
% specialization of the lemma.                                               %
%                                                                            %
% The function checks that the lemma has no hypotheses, and then extracts a  %
% list of subterms of the conclusion that match the given term and contain   %
% all the free variables of the conclusion. The second condition prevents    %
% new variables being introduced into the goal clause. The ordering of the   %
% subterms in the list is dependent on the implementation of `find_terms',   %
% but probably doesn't matter anyway, because the function tries each of     %
% them until it finds one that is acceptable.                                %
%                                                                            %
% Each subterm is tried as follows. A matching between the subterm and the   %
% term to be generalized is obtained. This is used to instantiate the lemma. %
% The function then checks that when the conclusion of this new theorem is   %
% generalized (by replacing the term to be generalized with a variable), the %
% function symbol of the term to be generalized no longer appears in it.     %
%----------------------------------------------------------------------------%

let apply_gen_lemma tm th =
 (let apply_gen_lemma' subtm =
     let (tm_bind,ty_bind) = match subtm tm
     in  let (insts,vars) = split tm_bind
     in  let th' = ((SPECL insts) o (GENL vars) o (INST_TYPE ty_bind)) th
     in  let gen_conc = subst [(genvar (type_of tm),tm)] (concl th')
         and f = fst (strip_comb tm)
         in  if (is_subterm f gen_conc)
             then fail
             else th'
  in  let ([],conc) = dest_thm th
  in  let conc_vars = frees conc
  in  let good_subterm subtm =
         (can (match subtm) tm) & (null (subtract conc_vars (frees subtm)))
  in  let subtms = rev (find_terms good_subterm conc)
  in  tryfind apply_gen_lemma' subtms
 ) ? failwith `apply_gen_lemma`;;

%----------------------------------------------------------------------------%
% applicable_gen_lemmas : term list -> thm list                              %
%                                                                            %
% Computes instantiations of generalization lemmas applicable to a list of   %
% terms, the terms to be generalized.                                        %
%----------------------------------------------------------------------------%

let applicable_gen_lemmas tml =
   flat (map (\tm. mapfilter (apply_gen_lemma tm) (gen_lemmas ())) tml);;

%----------------------------------------------------------------------------%
% generalize_heuristic : (term # bool) -> ((term # bool) list # proof)       %
%                                                                            %
% Generalization heuristic.                                                  %
%                                                                            %
% This function first computes the terms to be generalized in a clause. It   %
% fails if there are none. It then obtains a list of instantiated            %
% generalization lemmas for these terms. Each of these lemmas is transformed %
% to a theorem of the form |- x = F. If the original lemma was a negation,   %
% x is the argument of the negation. Otherwise x is the negation of the      %
% original lemma.                                                            %
%                                                                            %
% The negated lemmas are added to the clause, and the result is generalized  %
% by replacing each of the terms to be generalized by new distinct           %
% variables. This generalized clause is returned together with a proof of    %
% the original clause from it.                                               %
%                                                                            %
% The proof begins by specializing the variables that were used to replace   %
% the generalized terms. The theorem is then of the form:                    %
%                                                                            %
%    |- lemma1 \/ lemma2 \/ ... \/ lemman \/ original_clause            (1)  %
%                                                                            %
% We have a theorem |- lemmai = F for each i between 1 and n. Consider the   %
% first of these. From it, the following theorem can be obtained:            %
%                                                                            %
%    |- lemma1 \/ lemma2 \/ ... \/ lemman \/ original_clause =               %
%          F   \/ lemma2 \/ ... \/ lemman \/ original_clause                 %
%                                                                            %
% Simplifying using |- F \/ x = x, this gives:                               %
%                                                                            %
%    |- lemma1 \/ lemma2 \/ ... \/ lemman \/ original_clause =               %
%                 lemma2 \/ ... \/ lemman \/ original_clause                 %
%                                                                            %
% From this theorem and (1), we obtain:                                      %
%                                                                            %
%    |- lemma2 \/ ... \/ lemman \/ original_clause                           %
%                                                                            %
% Having repeated this process for each of the lemmas, the proof eventually  %
% returns a theorem for the original clause, i.e. |- original_clause.        %
%----------------------------------------------------------------------------%

let generalize_heuristic (tm,(ind:bool)) =
 (let NEGATE th =
     let ([],tm) = dest_thm th
     in  if (is_neg tm)
         then EQF_INTRO th
         else EQF_INTRO
                 (CONV_RULE
                     (REWR_CONV
                         (SYM (SPEC_ALL (hd (CONJUNCTS NOT_CLAUSES))))) th)
  and ELIM_LEMMA lemma th =
     let rest = snd (dest_disj (concl th))
     in  EQ_MP (CONV_RULE (RAND_CONV (REWR_CONV F_OR))
                          (AP_THM (AP_TERM "$\/" lemma) rest)) th
  in  let gen_terms = assert (\l. not (null l)) (terms_to_be_generalized tm)
  in  let lemmas = map NEGATE (applicable_gen_lemmas gen_terms)
  in  let tm' = itlist (curry mk_disj) (map (lhs o concl) lemmas) tm
  in  let new_vars = distinct_vars (frees tm') (map type_of gen_terms)
  in  let tm'' = subst (combine (new_vars,gen_terms)) tm'
  in  let proof th'' =
         let th' = SPECL gen_terms (GENL new_vars th'')
         in  rev_itlist ELIM_LEMMA lemmas th'
  in  ([(tm'',ind)],apply_proof (proof o hd) [tm''])
 ) ? failwith `generalize_heuristic`;;
