%****************************************************************************%
% FILE          : terms_and_clauses.ml                                       %
% DESCRIPTION   : Rewriting terms and simplifying clauses.                   %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 7th June 1991                                              %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 16th October 1992                                          %
%****************************************************************************%

%----------------------------------------------------------------------------%
% rewrite_with_lemmas : (term list -> term list -> conv) ->                  %
%                        term list -> term list -> conv                      %
%                                                                            %
% Function to rewrite with known lemmas (rewrite rules) in the reverse order %
% in which they were introduced. Applies the first applicable lemma, or if   %
% none are applicable it leaves the term unchanged.                          %
%                                                                            %
% A rule is applicable if its LHS matches the term, and it does not violate  %
% the `alphabetical' ordering rule if it is a permutative rule. To be        %
% applicable, the hypotheses of the rules must be satisfied. The function    %
% takes a general rewrite rule, a chain of hypotheses and a list of          %
% assumptions as arguments. It uses these to try to satisfy the hypotheses.  %
% If a hypotheses is in the assumption list, it is assumed. Otherwise a      %
% check is made that the hypothesis is not already a goal of the proof       %
% procedure. This is to prevent looping. If it's not already a goal, the     %
% function attempts to rewrite the hypotheses, with it added to the chain of %
% hypotheses.                                                                %
%                                                                            %
% Before trying to establish the hypotheses of a rewrite rule, it is         %
% necessary to instantiate any free variables in the hypotheses. This is     %
% done by trying to find an instantiation that makes one of the hypotheses   %
% equal to a term in the assumption list.                                    %
%----------------------------------------------------------------------------%

let rewrite_with_lemmas rewrite hyp_chain assumps tm =
   let rewrite_hyp h =
      (EQT_INTRO (ASSUME (find (\tm. tm = h) assumps))) ?
      (if (mem h hyp_chain)
       then ALL_CONV h
       else rewrite (h.hyp_chain) assumps h)
   in
   letrec try_rewrites assumps ths =
      if (null ths)
      then failwith `try_rewrites`
      else ( (let th = inst_frees_in_hyps assumps (hd ths)
              in  let hyp_ths = map (EQT_ELIM o rewrite_hyp) (hyp th)
              in  itlist PROVE_HYP hyp_ths th)
           ? (try_rewrites assumps (tl ths))
           )
   in try_rewrites assumps (applicable_rewrites tm) ? ALL_CONV tm;;

%----------------------------------------------------------------------------%
% rewrite_explicit_value : conv                                              %
%                                                                            %
% Explicit values are normally unchanged by rewriting, but in the case of a  %
% numeric constant, it is expanded out into SUC form.                        %
%----------------------------------------------------------------------------%

letrec rewrite_explicit_value tm =
   letrec conv tm = (num_CONV THENC TRY_CONV (RAND_CONV conv)) tm
   in ((TRY_CONV conv) THENC
       (TRY_CONV (ARGS_CONV rewrite_explicit_value))) tm;;

%----------------------------------------------------------------------------%
% COND_T = |- (T => t1 | t2) = t1                                            %
% COND_F = |- (F => t1 | t2) = t2                                            %
%----------------------------------------------------------------------------%

let [COND_T;COND_F] = CONJUNCTS (SPEC_ALL COND_CLAUSES);;

%----------------------------------------------------------------------------%
% COND_LEFT =                                                                %
% |- !b x x' y. (b ==> (x = x')) ==> ((b => x | y) = (b => x' | y))          %
%----------------------------------------------------------------------------%

let COND_LEFT =
 prove
  ("!b x x' (y:*). (b ==> (x = x')) ==> ((b => x | y) = (b => x' | y))",
   REPEAT GEN_TAC THEN
   BOOL_CASES_TAC "b:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% COND_RIGHT =                                                               %
% |- !b y y' x. (~b ==> (y = y')) ==> ((b => x | y) = (b => x | y'))         %
%----------------------------------------------------------------------------%

let COND_RIGHT =
 prove
  ("!b y y' (x:*). (~b ==> (y = y')) ==> ((b => x | y) = (b => x | y'))",
   REPEAT GEN_TAC THEN
   BOOL_CASES_TAC "b:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% COND_ID = |- !b t. (b => t | t) = t                                        %
%----------------------------------------------------------------------------%

% Already defined in HOL %

%----------------------------------------------------------------------------%
% COND_RIGHT_F = |- (b => b | F) = b                                         %
%----------------------------------------------------------------------------%

let COND_RIGHT_F =
 prove
  ("(b => b | F) = b",
   BOOL_CASES_TAC "b:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% COND_T_F = |- (b => T | F) = b                                             %
%----------------------------------------------------------------------------%

let COND_T_F =
 prove
  ("(b => T | F) = b",
   BOOL_CASES_TAC "b:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% rewrite_conditional : (term list -> conv) -> term list -> conv             %
%                                                                            %
% Rewriting conditionals. Takes a general rewrite function and a list of     %
% assumptions as arguments.                                                  %
%                                                                            %
% The function assumes that the term it is given is of the form "b => x | y" %
% First it recursively rewrites b to b'. If b' is T or F, the conditional is %
% reduced to x or y, respectively. The result is then rewritten recursively. %
% If b' is not T or F, both x and y are rewritten, under suitable additional %
% assumptions about b'. An attempt is then made to rewrite the new           %
% conditional with one of the following:                                     %
%                                                                            %
%    (b => x | x) ---> x                                                     %
%    (b => b | F) ---> b                                                     %
%    (b => T | F) ---> b                                                     %
%                                                                            %
% The three rules are tried in the order shown above.                        %
%----------------------------------------------------------------------------%

let rewrite_conditional rewrite assumps tm =
 (let th1 = RATOR_CONV (RATOR_CONV (RAND_CONV (rewrite assumps))) tm
  in  let tm1 = rhs (concl th1)
  in  let (b',x,y) = dest_cond tm1
  in  if (is_T b') then
         (th1 TRANS (((REWR_CONV COND_T) THENC (rewrite assumps)) tm1))
      if (is_F b') then
         (th1 TRANS (((REWR_CONV COND_F) THENC (rewrite assumps)) tm1))
      else let th2 = DISCH b' (rewrite (b'.assumps) x)
        in let x' = rand (rand (concl th2))
        in let th3 = MP (ISPECL [b';x;x';y] COND_LEFT) th2
        in let tm3 = rhs (concl th3)
        in let notb' = mk_neg b'
        in let th4 = DISCH notb' (rewrite (notb'.assumps) y)
        in let y' = rand (rand (concl th4))
        in let th5 = MP (ISPECL [b';y;y';x'] COND_RIGHT) th4
        in let th6 = ((REWR_CONV COND_ID) ORELSEC
                      (REWR_CONV COND_RIGHT_F) ORELSEC
                      (TRY_CONV (REWR_CONV COND_T_F))) (rhs (concl th5))
        in th1 TRANS th3 TRANS th5 TRANS th6
 ) ? failwith `rewrite_conditional`;;

%----------------------------------------------------------------------------%
% EQ_T = |- (x = T) = x                                                      %
%----------------------------------------------------------------------------%

let EQ_T =
 prove
  ("(x = T) = x",
   BOOL_CASES_TAC "x:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% EQ_EQ = |- (x = (y = z)) = ((y = z) => (x = T) | (x = F))                  %
%----------------------------------------------------------------------------%

let EQ_EQ =
 prove
  ("(x = ((y:*) = z)) = ((y = z) => (x = T) | (x = F))",
   BOOL_CASES_TAC "x:bool" THEN
   BOOL_CASES_TAC "(y:*) = z" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% EQ_F = |- (x = F) = (x => F | T)                                           %
%----------------------------------------------------------------------------%

let EQ_F =
 prove
  ("(x = F) = (x => F | T)",
   BOOL_CASES_TAC "x:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% prove_terms_not_eq : term -> term -> thm                                   %
%                                                                            %
% Function to prove that the left-hand and right-hand sides of an equation   %
% are not equal. Works with Boolean constants, explicit values, and terms    %
% involving constructors and variables.                                      %
%----------------------------------------------------------------------------%

let prove_terms_not_eq l r =
   letrec STRUCT_CONV tm =
      (bool_EQ_CONV ORELSEC
       num_EQ_CONV ORELSEC
       (\tm. let (l,r) = dest_eq tm
             in  let ty_name = (fst o dest_type) (type_of l)
             in  let ty_conv = shell_struct_conv (sys_shell_info ty_name)
             in  ty_conv STRUCT_CONV tm) ORELSEC
       % REFL_CONV ORELSEC   Omitted because it cannot generate false %
       ALL_CONV) tm
   in (let th = STRUCT_CONV (mk_eq (l,r))
       in  if (is_F (rhs (concl th))) then th else fail
      ) ? failwith `prove_terms_not_eq`;;

%----------------------------------------------------------------------------%
% rewrite_equality : (term list -> term list -> conv) ->                     %
%                     term list -> term list -> conv                         %
%                                                                            %
% Function for rewriting equalities. Takes a general rewrite function, a     %
% chain of hypotheses and a list of assumptions as arguments.                %
%                                                                            %
% The left-hand and right-hand sides of the equality are rewritten           %
% recursively. If the two sides are then identical, the term is rewritten to %
% T. If it can be shown that the two sides are not equal, the term is        %
% rewritten to F. Otherwise, the function rewrites with the first of the     %
% following rules that is applicable (or it leaves the term unchanged if     %
% none are applicable):                                                      %
%                                                                            %
%    (x = T)       ---> x                                                    %
%    (x = (y = z)) ---> ((y = z) => (x = T) | (x = F))                       %
%    (x = F)       ---> (x => F | T)                                         %
%                                                                            %
% The result is then rewritten using the known lemmas (rewrite rules).       %
%----------------------------------------------------------------------------%

let rewrite_equality rewrite hyp_chain assumps tm =
 (let th1 = ((RATOR_CONV (RAND_CONV (rewrite hyp_chain assumps))) THENC
             (RAND_CONV (rewrite hyp_chain assumps))) tm
  in  let tm1 = rhs (concl th1)
  in  let (l,r) = dest_eq tm1
  in  if (l = r)
      then th1 TRANS (EQT_INTRO (ISPEC l EQ_REFL))
      else (th1 TRANS (prove_terms_not_eq l r))
         ? (let th2 = ((REWR_CONV EQ_T) ORELSEC
                       (REWR_CONV EQ_EQ) ORELSEC
                       (TRY_CONV (REWR_CONV EQ_F))) tm1
            in  let th3 = rewrite_with_lemmas
                             rewrite hyp_chain assumps (rhs (concl th2))
            in  th1 TRANS th2 TRANS th3)
 ) ? failwith `rewrite_equality`;;

%----------------------------------------------------------------------------%
% rewrite_application :                                                      %
%    (term -> string list -> term list -> term list -> conv) ->              %
%     term -> string list -> term list -> term list -> conv                  %
%                                                                            %
% Function for rewriting applications. It takes a general rewriting function,%
% a literal (the literal containing the function call), a list of names of   %
% functions that are tentatively being opened up, a chain of hypotheses, and %
% a list of assumptions as arguments.                                        %
%                                                                            %
% The function begins by rewriting the arguments. It then determines the     %
% name of the function being applied. If this is a constructor, no further   %
% rewriting is done. Otherwise, from the function name, the number of the    %
% argument used for recursion (or zero if the definition is not recursive)   %
% and expansion theorems for each possible constructor are obtained. If the  %
% function is not recursive the call is opened up and the body is rewritten. %
% If the function has no definition, the application is rewritten using the  %
% known lemmas.                                                              %
%                                                                            %
% If the definition is recursive, but this function has already been         %
% tentatively opened up, the version of the application with the arguments   %
% rewritten is returned.                                                     %
%                                                                            %
% Otherwise, the application is rewritten with the known lemmas. If any of   %
% the lemmas are applicable the result of the rewrite is returned. Otherwise %
% the function determines the name of the constructor appearing in the       %
% recursive argument, and looks up its details. If this process fails due to %
% either the recursive argument not being an application of a constructor,   %
% or because the constructor is not known, the function call cannot be       %
% expanded, so the original call (with arguments rewritten) is returned.     %
%                                                                            %
% Provided a valid constructor is present in the recursive argument position %
% the call is tentatively opened up. The body is rewritten with the name of  %
% the function added to the `tentative openings' list. (Actually, the name   %
% is not added to the list if the recursive argument of the call was an      %
% explicit value). The result is compared with the unopened call to see if   %
% it has good properties. If it does, the simplified body is returned.       %
% Otherwise the unopened call is returned.                                   %
%----------------------------------------------------------------------------%

let rewrite_application rewrite lit funcs hyp_chain assumps tm =
 (let th1 = ARGS_CONV (rewrite lit funcs hyp_chain assumps) tm
  in  let tm1 = rhs (concl th1)
  in  let (f,args) = strip_comb tm1
  in  let name = fst (dest_const f)
  in
  if (mem name (all_constructors ()))
  then th1
  else
  (let (i,constructors) = snd (get_def name)
   in  if (i = 0) then
          (let th2 = REWR_CONV (snd (hd constructors)) tm1
           in  let th3 = rewrite lit funcs hyp_chain assumps (rhs (concl th2))
           in  th1 TRANS th2 TRANS th3)
       if (mem name funcs) then th1
       else let th2 =
               rewrite_with_lemmas (rewrite lit funcs) hyp_chain assumps tm1
            in  let tm2 = rhs (concl th2)
            in  if (tm2 = tm1)
                then let argi = el i args
                     in  let constructor =
                            (fst (dest_const (fst (strip_comb argi))) ? ``)
                     in  ( (let th = snd (assoc constructor constructors)
                            in  let th3 = REWR_CONV th tm1
                            in  let tm3 = rhs (concl th3)
                            in  let funcs' =
                                   if (is_explicit_value argi)
                                   then funcs
                                   else name.funcs
                            in  let th4 =
                                   rewrite lit funcs' hyp_chain assumps tm3
                            in  let tm4 = rhs (concl th4)
                            in  if (good_properties assumps tm1 tm4 lit)
                                then th1 TRANS th3 TRANS th4
                                else th1)
                         ? th1
                         )
                else th1 TRANS th2)
  ??[`get_def`]
    (th1 TRANS (rewrite_with_lemmas (rewrite lit funcs) hyp_chain assumps tm1))
 ) ? failwith `rewrite_application`;;

%----------------------------------------------------------------------------%
% rewrite_term : term -> string list -> term list -> term list -> conv       %
%                                                                            %
% Function for rewriting a term. Arguments are as follows:                   %
%                                                                            %
%    lit       : the literal containing the term to be rewritten.            %
%    funcs     : names of functions that have been tentatively opened up.    %
%    hyp_chain : hypotheses that we are trying to satisfy by parent calls.   %
%    assumps   : a list of assumptions.                                      %
%    tm        : the term to be rewritten.                                   %
%----------------------------------------------------------------------------%

letrec rewrite_term lit funcs hyp_chain assumps tm =
 (EQT_INTRO (ASSUME (find (\t. t = tm) assumps))) ?
 (EQF_INTRO (ASSUME (find (\t. t = mk_neg tm) assumps))) ? 
 (let rewrite = rewrite_term lit funcs
  in  if (is_var tm) then ALL_CONV tm
      if (is_explicit_value tm) then rewrite_explicit_value tm
      if (is_cond tm) then rewrite_conditional (rewrite hyp_chain) assumps tm
      if (is_eq tm) then rewrite_equality rewrite hyp_chain assumps tm
      else rewrite_application rewrite_term lit funcs hyp_chain assumps tm
 ) ? failwith `rewrite_term`;;

%----------------------------------------------------------------------------%
% COND_RAND = |- !f b x y. f (b => x | y) = (b => f x | f y)                 %
%----------------------------------------------------------------------------%

% Already defined in HOL %

%----------------------------------------------------------------------------%
% COND_RATOR = |- !b f g x. (b => f | g) x = (b => f x | g x)                %
%----------------------------------------------------------------------------%

% Already defined in HOL %

%----------------------------------------------------------------------------%
% MOVE_COND_UP_CONV : conv                                                   %
%                                                                            %
% Moves all conditionals in a term up to the top-level. Checks to see if the %
% term contains any conditionals before it starts to do inference. This      %
% improves the performance significantly. Alternatively, failure could be    %
% used to avoid rebuilding unchanged sub-terms. This would be even more      %
% efficient.                                                                 %
%----------------------------------------------------------------------------%

letrec MOVE_COND_UP_CONV tm =
 (if (not (can (find_term is_cond) tm)) then ALL_CONV tm
  if (is_cond tm) then
     ((RATOR_CONV (RATOR_CONV (RAND_CONV MOVE_COND_UP_CONV))) THENC
      (RATOR_CONV (RAND_CONV MOVE_COND_UP_CONV)) THENC
      (RAND_CONV MOVE_COND_UP_CONV)) tm
  if (is_comb tm) then
     (let (op,arg) = dest_comb tm
      in  if (is_cond op) then
             ((REWR_CONV COND_RATOR) THENC MOVE_COND_UP_CONV) tm
          if (is_cond arg) then
             ((REWR_CONV COND_RAND) THENC MOVE_COND_UP_CONV) tm
          else (let th = ((RATOR_CONV MOVE_COND_UP_CONV) THENC
                          (RAND_CONV MOVE_COND_UP_CONV)) tm
                in  let tm' = rhs (concl th)
                in  if (tm' = tm)
                    then th
                    else th TRANS (MOVE_COND_UP_CONV tm')))
  else ALL_CONV tm
 ) ? failwith `MOVE_COND_UP_CONV`;;

%----------------------------------------------------------------------------%
% COND_OR = |- (b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)           %
%----------------------------------------------------------------------------%

let COND_OR =
 prove
  ("(b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)",
   BOOL_CASES_TAC "b:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% COND_EXPAND = |- (x => y | z) = ((~x \/ y) /\ (x \/ z))                    %
%----------------------------------------------------------------------------%

% Already proved %

%----------------------------------------------------------------------------%
% NOT_NOT_NORM = |- ~~x = x                                                  %
%----------------------------------------------------------------------------%

% Already proved %

%----------------------------------------------------------------------------%
% LEFT_OR_OVER_AND = |- !t1 t2 t3. t1 \/ t2 /\ t3 = (t1 \/ t2) /\ (t1 \/ t3) %
%----------------------------------------------------------------------------%

% Already available in HOL %

%----------------------------------------------------------------------------%
% MOVE_NOT_THRU_CONDS_CONV : conv                                            %
%                                                                            %
% Function to push a negation down through (possibly) nested conditionals.   %
% Eliminates any double-negations that may be introduced.                    %
%----------------------------------------------------------------------------%

letrec MOVE_NOT_THRU_CONDS_CONV tm =
 (if (is_neg tm)
  then if (is_cond (rand tm))
       then ((REWR_CONV COND_RAND) THENC
             (RATOR_CONV (RAND_CONV MOVE_NOT_THRU_CONDS_CONV)) THENC
             (RAND_CONV MOVE_NOT_THRU_CONDS_CONV)) tm
       else TRY_CONV (REWR_CONV NOT_NOT_NORM) tm
  else ALL_CONV tm
 ) ? failwith `MOVE_NOT_THRU_CONDS_CONV`;;

%----------------------------------------------------------------------------%
% EXPAND_ONE_COND_CONV : conv                                                %
%                                                                            %
% The function takes a term which it assumes to be either a conditional or   %
% the disjunction of a conditional and some other term, and applies one of   %
% the following rewrites as appropriate:                                     %
%                                                                            %
%    |- (b => x | y) = (~b \/ x) /\ (b \/ y)                                 %
%                                                                            %
%    |- (b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)                  %
%                                                                            %
% If b happens to be a conditional, the negation of ~b is moved down through %
% the conditional (and any nested conditionals).                             %
%----------------------------------------------------------------------------%

let EXPAND_ONE_COND_CONV tm =
 (((REWR_CONV COND_OR) ORELSEC (REWR_CONV COND_EXPAND)) THENC
  (RATOR_CONV (RAND_CONV (RATOR_CONV (RAND_CONV MOVE_NOT_THRU_CONDS_CONV)))))
 tm ? failwith `EXPAND_ONE_COND_CONV`;;

%----------------------------------------------------------------------------%
% OR_OVER_ANDS_CONV : conv -> conv                                           %
%                                                                            %
% Distributes an OR over an arbitrary tree of conjunctions and applies a     %
% conversion to each of the disjunctions that make up the new conjunction.   %
%----------------------------------------------------------------------------%

letrec OR_OVER_ANDS_CONV conv tm =
   if (is_disj tm)
   then if (is_conj (rand tm))
        then ((REWR_CONV LEFT_OR_OVER_AND) THENC
              (RATOR_CONV (RAND_CONV (OR_OVER_ANDS_CONV conv))) THENC
              (RAND_CONV (OR_OVER_ANDS_CONV conv))) tm
        else conv tm
   else ALL_CONV tm;;

%----------------------------------------------------------------------------%
% EXPAND_COND_CONV : conv                                                    %
%                                                                            %
% The function takes a term which it assumes to be either a conditional or   %
% the disjunction of a conditional and some other term, and expands the      %
% conditional into a disjunction using one of:                               %
%                                                                            %
%    |- (b => x | y) = (~b \/ x) /\ (b \/ y)                                 %
%                                                                            %
%    |- (b => x | y) \/ z = (~b \/ x \/ z) /\ (b \/ y \/ z)                  %
%                                                                            %
% The b, x and y may themselves be conditionals. If so, the function expands %
% these as well, and so on, until there are no more conditionals. At each    %
% stage disjunctions are distributed over conjunctions so that the final     %
% result is a conjunction `tree' where each of the conjuncts is a            %
% disjunction. The depth of a disjunction in the conjunction tree indicates  %
% the number of literals that have been added to the disjunction compared to %
% the original term.                                                         %
%----------------------------------------------------------------------------%

letrec EXPAND_COND_CONV tm =
 (EXPAND_ONE_COND_CONV THENC
  (RATOR_CONV (RAND_CONV ((RAND_CONV EXPAND_COND_CONV) THENC
                          (OR_OVER_ANDS_CONV EXPAND_COND_CONV)))) THENC
  (RAND_CONV ((RAND_CONV EXPAND_COND_CONV) THENC
              (OR_OVER_ANDS_CONV EXPAND_COND_CONV)))) tm
 ? ALL_CONV tm;;

%----------------------------------------------------------------------------%
% SPLIT_CLAUSE_ON_COND_CONV : int -> conv                                    %
%                                                                            %
% The function takes a number n and a term which it assumes to be a          %
% disjunction of literals in which the (n-1)th argument has had all          %
% conditionals moved to the top level.                                       %
%                                                                            %
% The function dives down to the (n-1)th literal (disjunct) and expands the  %
% conditionals into disjunctions, resulting in a conjunction `tree' in which %
% each conjunct is a disjunction.                                            %
%                                                                            %
% As the function `backs out' from the (n-1)th literal it distributes the    %
% ORs over the conjunction tree.                                             %
%----------------------------------------------------------------------------%

let SPLIT_CLAUSE_ON_COND_CONV n tm =
 (funpow n (\conv. (RAND_CONV conv) THENC (OR_OVER_ANDS_CONV ALL_CONV))
     EXPAND_COND_CONV tm
 ) ? failwith `SPLIT_CLAUSE_ON_COND_CONV`;;

%----------------------------------------------------------------------------%
% simplify_one_literal : int -> term -> (thm # int)                          %
%                                                                            %
% Attempts to simplify one literal of a clause assuming the negations of the %
% other literals. The number n specifies which literal to rewrite. If n = 0, %
% the first literal is rewritten. The function fails if n is out of range.   %
%                                                                            %
% If the literal to be simplified is negative, the function simplifies the   %
% corresponding atom, and negates the result. If this new result is T or F,  %
% the clause is rebuilt by discharging the assumptions. This process may     %
% reduce the number of literals in the clause, so the theorem returned is    %
% paired with -1 (except when processing the last literal of a clause in     %
% which case returning 0 will, like -1, cause a failure when an attempt is   %
% made to simplify the next literal, but is safer because it can't cause     %
% looping if the literal has not been removed. This is the case when the     %
% last literal has been rewritten to F. In this situation, the discharging   %
% function does not eliminate the literal).                                  %
%                                                                            %
% If the simplified literal contains conditionals, these are brought up to   %
% the top-level. The clause is then rebuilt by discharging. If no            %
% conditionals were present the theorem is returned with 0, indicating that  %
% the number of literals has not changed. Otherwise the clause is split into %
% a conjunction of clauses, so that the conditionals are eliminated, and the %
% result is returned with the number 1 to indicate that the number of        %
% literals has increased.                                                    %
%----------------------------------------------------------------------------%

let simplify_one_literal n tm =
 (let negate tm = if (is_neg tm) then (rand tm) else (mk_neg tm)
  and NEGATE th =
         let tm = rhs (concl th)
         and th' = AP_TERM "$~" th
         in  if (is_T tm) then th' TRANS (el 2 (CONJUNCTS NOT_CLAUSES))
             if (is_F tm) then th' TRANS (el 3 (CONJUNCTS NOT_CLAUSES))
             else th'
  in  let (overs,y.unders) = chop_list n (disj_list tm)
  in  let overs' = map negate overs
      and unders' = map negate unders
  in  let th1 =
         if (is_neg y)
         then NEGATE (rewrite_term y [] [] (overs' @ unders') (rand y))
         else rewrite_term y [] [] (overs' @ unders') y
  in  let tm1 = rhs (concl th1)
  in  if ((is_T tm1) or (is_F tm1))
      then (MULTI_DISJ_DISCH (overs',unders') th1,
            if (null unders) then 0 else (-1))
      else let th2 = th1 TRANS (MOVE_COND_UP_CONV tm1)
           in  let tm2 = rhs (concl th2)
           in  let th3 = MULTI_DISJ_DISCH (overs',unders') th2
           in  if (is_cond tm2)
               then (CONV_RULE (RAND_CONV (SPLIT_CLAUSE_ON_COND_CONV n)) th3,1)
               else (th3,0)
 ) ? failwith `simplify_one_literal`;;

%----------------------------------------------------------------------------%
% simplify_clause : int -> term -> (term list # proof)                       %
% simplify_clauses : int -> term -> (term list # proof)                      %
%                                                                            %
% Functions for simplifying a clause by rewriting each literal in turn       %
% assuming the negations of the others.                                      %
%                                                                            %
% The integer argument to simplify_clause should be zero initially. It will  %
% then attempt to simplify the first literal. If the result is true, no new  %
% clauses are produced. Otherwise, the function proceeds to simplify the     %
% next literal. This has to be done differently according to the changes     %
% that took place when simplifying the first literal.                        %
%                                                                            %
% If there was a reduction in the number of literals, this must have been    %
% due to the literal being shown to be false, because the true case has      %
% already been eliminated. So, there must be one less literal, and so n is   %
% unchanged on the recursive call. If there was no change in the number of   %
% literals, n is incremented by 1. Otherwise, not only have new literals     %
% been introduced, but also the clause has been split into a conjunction of  %
% clauses. simplify_clauses is called to handle this case.                   %
%                                                                            %
% When all the literals have been processed, n will become out of range and  %
% cause a failure. This is trapped, and the simplified clause is returned.   %
%                                                                            %
% When the clause has been split into a conjunction of clauses, the depth of %
% a clause in the tree of conjunctions indicates how many literals have been %
% added to that clause. simplify_clauses recursively splits conjunctions,    %
% incrementing n as it proceeds, until it reaches a clause. It then calls    %
% simplify_clause to deal with the clause.                                   %
%----------------------------------------------------------------------------%

letrec simplify_clause n tm =
 (let (th,change_flag) = simplify_one_literal n tm
  in  let tm' = rhs (concl th)
  in  if (is_T tm')
      then ([],apply_proof (\ths. EQT_ELIM th) [])
      else let (tms,proof) =
              if (change_flag < 0) then simplify_clause n tm'
              if (change_flag = 0) then simplify_clause (n + 1) tm'
              else simplify_clauses (n + 1) tm'
           in  (tms,(\ths. EQ_MP (SYM th) (proof ths))))
 ? ([tm],apply_proof hd [tm])

and simplify_clauses n tm =
 (let (tm1,tm2) = dest_conj tm
  in  let (tms1,proof1) = simplify_clauses (n + 1) tm1
      and (tms2,proof2) = simplify_clauses (n + 1) tm2
  in  (tms1 @ tms2,
       \ths. let (ths1,ths2) = chop_list (length tms1) ths
             in  CONJ (proof1 ths1) (proof2 ths2)))
 ? (simplify_clause n tm);;

%----------------------------------------------------------------------------%
% simplify_heuristic : (term # bool) -> ((term # bool) list # proof)         %
%                                                                            %
% Wrapper for simplify_clause. This function has the correct type and        %
% properties to be used as a `heuristic'. In particular, if the result of    %
% simplify_clause is a single clause identical to the input clause,          %
% a failure is generated.                                                    %
%----------------------------------------------------------------------------%

let simplify_heuristic (tm,(ind:bool)) =
 (let (tms,proof) = simplify_clause 0 tm
  in  if (tms = [tm])
      then fail
      else (map (\tm. (tm,ind)) tms,proof)
 ) ? failwith `simplify_heuristic`;;

%----------------------------------------------------------------------------%
% NOT_EQ_F = |- !x. ~(x = x) = F                                             %
%----------------------------------------------------------------------------%

let NOT_EQ_F =
 GEN_ALL
  ((AP_TERM "$~" (SPEC_ALL REFL_CLAUSE)) TRANS
   (el 2 (CONJUNCTS NOT_CLAUSES)));;

%----------------------------------------------------------------------------%
% subst_heuristic : (term # bool) -> ((term # bool) list # proof)            %
%                                                                            %
% `Heuristic' for eliminating from a clause, a negated equality between a    %
% variable and another term not containing the variable. For example, given  %
% the clause:                                                                %
%                                                                            %
%    x1 \/ ~(x = t) \/ x3 \/ f x \/ x5                                       %
%                                                                            %
% the function returns the clause:                                           %
%                                                                            %
%    x1 \/ F \/ x3 \/ f t \/ x5                                              %
%                                                                            %
% So, all occurrences of x are replaced by t, and the equality x = t is      %
% `thrown away'. The F could be eliminated, but the simplification heuristic %
% will deal with it, so there is no point in duplicating the code.           %
%                                                                            %
% The function fails if there are no equalities that can be eliminated.      %
%                                                                            %
% The function proves the following three theorems:                          %
%                                                                            %
%    ~(x = t) |- x1 \/ ~(x = t) \/ x3 \/ f x \/ x5                           %
%                                                                            %
%       x = t |- x1 \/ ~(x = t) \/ x3 \/ f x \/ x5 =                         %
%                x1 \/     F    \/ x3 \/ f t \/ x5                           %
%                                                                            %
%             |- (x = t) \/ ~(x = t)                                         %
%                                                                            %
% and returns the term "x1 \/ F \/ x3 \/ f t \/ x5" to be proved. When given %
% this term as a theorem, it is possible to prove from the second theorem:   %
%                                                                            %
%       x = t |- x1 \/ ~(x = t) \/ x3 \/ f x \/ x5                           %
%                                                                            %
% which together with the first and third theorems yields a theorem for the  %
% original clause.                                                           %
%----------------------------------------------------------------------------%

let subst_heuristic (tm,(ind:bool)) =
 (let check (v,t) = (is_var v) & (not (mem v (frees t)))
  in  letrec split_disjuncts tml =
         if (can (assert check o dest_eq o dest_neg) (hd tml))
         then ([],tml)
         else (\(l1,l2). ((hd tml).l1,l2)) (split_disjuncts (tl tml))
  in  let (overs,neq.unders) = split_disjuncts (disj_list tm)
  in  let eq = dest_neg neq
  in  let (v,t) = dest_eq eq
  in  let ass = ASSUME neq
  in  let th1 = itlist DISJ2 overs (DISJ1 ass (list_mk_disj unders) ? ass)
      and th2 = SUBS [ISPEC t NOT_EQ_F] (SUBST_CONV [(ASSUME eq,v)] tm tm)
      and th3 = SPEC eq EXCLUDED_MIDDLE
  in  let tm' = rhs (concl th2)
  in  let proof th = DISJ_CASES th3 (EQ_MP (SYM th2) th) th1
  in  ([(tm',ind)],apply_proof (proof o hd) [tm'])
 ) ? failwith `subst_heuristic`;;
