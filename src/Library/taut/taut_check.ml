%****************************************************************************%
% FILE          : taut_check.ml                                              %
% DESCRIPTION   : Tautology checking by Boolean case analysis.               %
%                                                                            %
%                 Method suggested by Tom Melham.                            %
%                                                                            %
%                 Simplification done after each variable instantiation.     %
%                                                                            %
%                 Optimised for terms with more than two variables by        %
%                 eliminating some duplicated sub-calls.                     %
%                                                                            %
%                 Optimised for cases when the body simplifies to true or    %
%                 false before all the variables have been analysed.         %
%                                                                            %
%                 Simplification optimised to avoid rebuilding subterms that %
%                 are not changed.                                           %
%                                                                            %
%                 Experiments have been performed with special code for      %
%                 cases when the first argument of AND, OR, IMP and COND     %
%                 simplifies to a value that makes simplification of certain %
%                 other arguments unnecessary. The results suggested that in %
%                 general slightly fewer intermediate theorems are           %
%                 generated, but that due to the overhead of testing, the    %
%                 execution times are slightly longer.                       %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 9th July 1991                                              %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 24th September 1991                                        %
%****************************************************************************%

begin_section taut_check;;

%============================================================================%
% Discriminator functions for T (true) and F (false)                         %
%============================================================================%

let is_T = let T = "T" in \tm. tm = T
and is_F = let F = "F" in \tm. tm = F;;

%============================================================================%
% Theorems used for Boolean case analysis                                    %
%============================================================================%

%----------------------------------------------------------------------------%
% BOOL_CASES_T_F = |- !f. (f T = F) ==> ((!x. f x) = F)                      %
%----------------------------------------------------------------------------%

let BOOL_CASES_T_F =
 prove
  ("!f. (f T = F) ==> ((!x. f x) = F)",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC "T" THEN
   ASM_REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% BOOL_CASES_F_F = |- !f. (f F = F) ==> ((!x. f x) = F)                      %
%----------------------------------------------------------------------------%

let BOOL_CASES_F_F =
 prove
  ("!f. (f F = F) ==> ((!x. f x) = F)",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC "F" THEN
   ASM_REWRITE_TAC []);;

%============================================================================%
% Conversions for doing Boolean case analysis                                %
%============================================================================%

%----------------------------------------------------------------------------%
% BOOL_CASES_BOTH_T_RULE : (thm # thm) -> conv                               %
%                                                                            %
% BOOL_CASES_BOTH_T_RULE (|- f[T] = T, |- f[F] = T) "!x. f[x]" returns the   %
% theorem |- (!x. f[x]) = T.                                                 %
%----------------------------------------------------------------------------%

let BOOL_CASES_BOTH_T_RULE (thT,thF) tm =
 (let (x,body) = dest_forall tm
  in  let cases_thm = SPEC x BOOL_CASES_AX
  in  let thT' = TRANS (SUBST_CONV [ASSUME (mk_eq(x,"T")),x] body body) thT
      and thF' = TRANS (SUBST_CONV [ASSUME (mk_eq(x,"F")),x] body body) thF
  in  let th = DISJ_CASES cases_thm thT' thF'
  in  (EQT_INTRO o (GEN x) o EQT_ELIM) th
 ) ? failwith `BOOL_CASES_BOTH_T_RULE`;;

%----------------------------------------------------------------------------%
% BOOL_CASES_T_F_RULE : thm -> conv                                          %
%                                                                            %
% BOOL_CASES_T_F_RULE (|- f[T] = F) "!x. f[x]" returns the theorem           %
% |- (!x. f[x]) = F.                                                         %
%----------------------------------------------------------------------------%

let BOOL_CASES_T_F_RULE thT tm =
 (let (x,body) = dest_forall tm
  in  let f = mk_abs (x,body)
  in  let thT' = TRANS (BETA_CONV (mk_comb(f,"T"))) thT
      and th = AP_TERM "$!:(bool -> bool) -> bool"
                  (ABS x (BETA_CONV (mk_comb(f,x))))
  in  let th1 = SPEC f BOOL_CASES_T_F
  in  let th2 = MP th1 thT'
  in  (SYM th) TRANS th2
 ) ? failwith `BOOL_CASES_T_F_RULE`;;

%----------------------------------------------------------------------------%
% BOOL_CASES_F_F_RULE : thm -> conv                                          %
%                                                                            %
% BOOL_CASES_F_F_RULE (|- f[F] = F) "!x. f[x]" returns the theorem           %
% |- (!x. f[x]) = F.                                                         %
%----------------------------------------------------------------------------%

let BOOL_CASES_F_F_RULE thF tm =
 (let (x,body) = dest_forall tm
  in  let f = mk_abs (x,body)
  in  let thF' = TRANS (BETA_CONV (mk_comb(f,"F"))) thF
      and th = AP_TERM "$!:(bool -> bool) -> bool"
                  (ABS x (BETA_CONV (mk_comb(f,x))))
  in  let th1 = SPEC f BOOL_CASES_F_F
  in  let th2 = MP th1 thF'
  in  (SYM th) TRANS th2
 ) ? failwith `BOOL_CASES_F_F_RULE`;;

%============================================================================%
% Conversions that use failure to indicate that they have not changed their  %
% input term, and hence save the term from being rebuilt unnecessarily.      %
%============================================================================%

%----------------------------------------------------------------------------%
% Failure string indicating that a term has not been changed by the          %
% conversion applied to it.                                                  %
%----------------------------------------------------------------------------%

let qconv = `QCONV`;;

%----------------------------------------------------------------------------%
% QCONV : conv -> conv                                                       %
%                                                                            %
% Takes a conversion that uses failure to indicate that it has not changed   %
% its argument term, and produces an ordinary conversion.                    %
%----------------------------------------------------------------------------%

let QCONV conv tm = (conv tm) ??[qconv](REFL tm);;

%----------------------------------------------------------------------------%
% ALL_QCONV : conv                                                           %
%                                                                            %
% Identity conversion for conversions using failure.                         %
%----------------------------------------------------------------------------%

let ALL_QCONV:conv = \tm. failwith qconv;;

%----------------------------------------------------------------------------%
% THENQC : conv -> conv -> conv                                              %
%                                                                            %
% Takes two conversions that use failure and produces a conversion that      %
% applies them in succession. The new conversion also uses failure. It fails %
% if neither of the two argument conversions cause a change.                 %
%----------------------------------------------------------------------------%

let THENQC conv1 conv2 tm =
 (let th1 = conv1 tm
  in  ((th1 TRANS (conv2 (rhs (concl th1)))) ??[qconv] th1))
 ??[qconv] (conv2 tm);;

%----------------------------------------------------------------------------%
% ORELSEQC : conv -> conv -> conv                                            %
%                                                                            %
% Takes two conversions that use failure and produces a conversion that      %
% tries the first one, and if this fails for a reason other than that the    %
% term is unchanged, it tries the second one.                                %
%----------------------------------------------------------------------------%

let ORELSEQC (conv1:conv) conv2 tm =
 (conv1 tm) ?\s if (s = qconv) then (failwith qconv) else (conv2 tm);;

%----------------------------------------------------------------------------%
% TRY_QCONV : conv -> conv                                                   %
%                                                                            %
% Applies a conversion, and if it fails, raises a `qconv' failure indicating %
% that the term is unchanged.                                                %
%----------------------------------------------------------------------------%

let TRY_QCONV conv =
 ORELSEQC conv ALL_QCONV;;

%----------------------------------------------------------------------------%
% RAND_QCONV : conv -> conv                                                  %
%                                                                            %
% Applies a conversion to the rand of a term, propagating any failure that   %
% indicates that the subterm is unchanged.                                   %
%----------------------------------------------------------------------------%

let RAND_QCONV conv tm =
 let (rator,rand) = dest_comb tm ? failwith `RAND_QCONV`
 in  AP_TERM rator (conv rand);;

%----------------------------------------------------------------------------%
% RATOR_QCONV : conv -> conv                                                 %
%                                                                            %
% Applies a conversion to the rator of a term, propagating any failure that  %
% indicates that the subterm is unchanged.                                   %
%----------------------------------------------------------------------------%

let RATOR_QCONV conv tm =
 let (rator,rand) = dest_comb tm ? failwith `RATOR_QCONV`
 in  AP_THM (conv rator) rand;;

%----------------------------------------------------------------------------%
% ABS_QCONV : conv -> conv                                                   %
%                                                                            %
% Applies a conversion to the body of an abstraction, propagating any        %
% failure that indicates that the subterm is unchanged.                      %
%----------------------------------------------------------------------------%

let ABS_QCONV conv tm =
 let (bv,body) = dest_abs tm ? failwith `ABS_QCONV`
 in  let bodyth = conv body
 in  ABS bv bodyth ? failwith `ABS_QCONV`;;

%============================================================================%
% Theorems used for simplifying Boolean terms                                %
%============================================================================%

%----------------------------------------------------------------------------%
% T_REFL = |- T = T                                                          %
% F_REFL = |- F = F                                                          %
%----------------------------------------------------------------------------%

let T_REFL = REFL "T"
and F_REFL = REFL "F";;

%============================================================================%
% Conversions used for simplifying Boolean terms                             %
%============================================================================%

%----------------------------------------------------------------------------%
% NOT_CONV : conv                                                            %
%                                                                            %
%    |- !t. ~~t = t                                                          %
%    |- ~T = F                                                               %
%    |- ~F = T                                                               %
%----------------------------------------------------------------------------%

let NOT_CONV =
 let [th1;th2;th3] = CONJUNCTS NOT_CLAUSES
 in \tm.
 (let arg = dest_neg tm
  in  if (is_T arg) then th2
      if (is_F arg) then th3
      else SPEC (dest_neg arg) th1
 ) ? failwith `NOT_CONV`;;

%----------------------------------------------------------------------------%
% EQ_CONV : conv                                                             %
%                                                                            %
%    |- (t = t) = T                                                          %
%    |- (T = t) = t                                                          %
%    |- (t = T) = t                                                          %
%    |- (F = t) = ~t                                                         %
%    |- (t = F) = ~t                                                         %
%----------------------------------------------------------------------------%

let EQ_CONV =
 let th1 = INST_TYPE [":bool",":*"] REFL_CLAUSE
 and [th2;th3;th4;th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
 in \tm.
 (let (arg1,arg2) = dest_eq tm
  in  if (is_T arg1) then SPEC arg2 th2
      if (is_T arg2) then SPEC arg1 th3
      if (is_F arg1) then SPEC arg2 th4
      if (is_F arg2) then SPEC arg1 th5
      if (arg1 = arg2) then SPEC arg1 th1
      else fail
 ) ? failwith `EQ_CONV`;;

%----------------------------------------------------------------------------%
% EQ_THEN_NOT_CONV : conv                                                    %
%                                                                            %
% Behaves as for EQ_CONV, then if EQ_CONV generated a top level negation, it %
% tries to apply NOT_CONV.                                                   %
%----------------------------------------------------------------------------%

let EQ_THEN_NOT_CONV tm =
 if ((is_F (rand (rator tm))) or (is_F (rand tm)))
 then (EQ_CONV THENC (TRY_CONV NOT_CONV)) tm
 else EQ_CONV tm;;

%----------------------------------------------------------------------------%
% AND_CONV : conv                                                            %
%                                                                            %
%    |- T /\ t = t                                                           %
%    |- t /\ T = t                                                           %
%    |- F /\ t = F                                                           %
%    |- t /\ F = F                                                           %
%    |- t /\ t = t                                                           %
%----------------------------------------------------------------------------%

let AND_CONV =
 let [th1;th2;th3;th4;th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
 in \tm.
 (let (arg1,arg2) = dest_conj tm
  in  if (is_T arg1) then SPEC arg2 th1
      if (is_T arg2) then SPEC arg1 th2
      if (is_F arg1) then SPEC arg2 th3
      if (is_F arg2) then SPEC arg1 th4
      if (arg1 = arg2) then SPEC arg1 th5
      else fail
 ) ? failwith `AND_CONV`;;

%----------------------------------------------------------------------------%
% OR_CONV : conv                                                             %
%                                                                            %
%    |- T \/ t = T                                                           %
%    |- t \/ T = T                                                           %
%    |- F \/ t = t                                                           %
%    |- t \/ F = t                                                           %
%    |- t \/ t = t                                                           %
%----------------------------------------------------------------------------%

let OR_CONV =
 let [th1;th2;th3;th4;th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
 in \tm.
 (let (arg1,arg2) = dest_disj tm
  in  if (is_T arg1) then SPEC arg2 th1
      if (is_T arg2) then SPEC arg1 th2
      if (is_F arg1) then SPEC arg2 th3
      if (is_F arg2) then SPEC arg1 th4
      if (arg1 = arg2) then SPEC arg1 th5
      else fail
 ) ? failwith `OR_CONV`;;

%----------------------------------------------------------------------------%
% IMP_CONV : conv                                                            %
%                                                                            %
%    |- T ==> t = t                                                          %
%    |- t ==> T = T                                                          %
%    |- F ==> t = T                                                          %
%    |- t ==> t = T                                                          %
%    |- t ==> F = ~t                                                         %
%----------------------------------------------------------------------------%

let IMP_CONV =
 let [th1;th2;th3;th4;th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
 in \tm.
 (let (arg1,arg2) = dest_imp tm
  in  if (is_neg tm) then fail
      if (is_T arg1) then SPEC arg2 th1
      if (is_T arg2) then SPEC arg1 th2
      if (is_F arg1) then SPEC arg2 th3
      if (is_F arg2) then SPEC arg1 th5
      if (arg1 = arg2) then SPEC arg1 th4
      else fail
 ) ? failwith `IMP_CONV`;;

%----------------------------------------------------------------------------%
% IMP_THEN_NOT_CONV : conv                                                   %
%                                                                            %
% Behaves as for IMP_CONV, then if IMP_CONV generated a top level negation,  %
% it tries to apply NOT_CONV.                                                %
%----------------------------------------------------------------------------%

let IMP_THEN_NOT_CONV tm =
 if (is_F (rand tm))
 then (IMP_CONV THENC (TRY_CONV NOT_CONV)) tm
 else IMP_CONV tm;;

%----------------------------------------------------------------------------%
% IF_CONV : conv                                                             %
%                                                                            %
%    |- (T => t1 | t2) = t1                                                  %
%    |- (F => t1 | t2) = t2                                                  %
%----------------------------------------------------------------------------%

let IF_CONV =
 let [th1;th2] =
    map GEN_ALL
       (CONJUNCTS (SPEC_ALL (INST_TYPE [(":bool",":*")] COND_CLAUSES)))
 in \tm.
 (let (arg1,arg2,arg3) = dest_cond tm
  in  if (is_T arg1) then SPECL [arg2;arg3] th1
      if (is_F arg1) then SPECL [arg2;arg3] th2
      else fail
 ) ? failwith `IF_CONV`;;

%----------------------------------------------------------------------------%
% SIMP_PROP_QCONV : conv                                                     %
%                                                                            %
% Conversion for simplifying propositional terms containing constants,       %
% variables, equality, implication, AND, OR, NOT and conditionals.           %
% Uses failure to avoid rebuilding unchanged subterms.                       %
%----------------------------------------------------------------------------%

letrec SIMP_PROP_QCONV tm =
 let ARGS_QCONV tm =
    let (op,[arg1;arg2]) = strip_comb tm
    in  (let th1 = SIMP_PROP_QCONV arg1
         in  let th = AP_TERM op th1
         in  (MK_COMB (th,SIMP_PROP_QCONV arg2)) ??[qconv](AP_THM th arg2))
        ??[qconv](let th2 = SIMP_PROP_QCONV arg2 in AP_TERM (rator tm) th2)
 in
 (if ((is_const tm) or (is_var tm)) then ALL_QCONV tm
  if (is_neg tm) then
     (THENQC (RAND_QCONV SIMP_PROP_QCONV) (TRY_QCONV NOT_CONV)) tm
  if (is_eq tm) then (THENQC ARGS_QCONV (TRY_QCONV EQ_THEN_NOT_CONV)) tm
  if (is_conj tm) then (THENQC ARGS_QCONV (TRY_QCONV AND_CONV)) tm
  if (is_disj tm) then (THENQC ARGS_QCONV (TRY_QCONV OR_CONV)) tm
  if (is_imp tm) then (THENQC ARGS_QCONV (TRY_QCONV IMP_THEN_NOT_CONV)) tm
  if (is_cond tm) then
     (THENQC (THENQC (RATOR_QCONV (THENQC (RATOR_QCONV
                                              (RAND_QCONV SIMP_PROP_QCONV))
                                          (RAND_QCONV SIMP_PROP_QCONV)))
                     (RAND_QCONV SIMP_PROP_QCONV))
             (TRY_QCONV IF_CONV)) tm
  else failwith `SIMP_PROP_QCONV`
 );;

%============================================================================%
% Tautology checking                                                         %
%============================================================================%

%----------------------------------------------------------------------------%
% DEPTH_FORALL_QCONV : conv -> conv                                          %
%                                                                            %
% Auxiliary function for applying a conversion inside universal              %
% quantifications.                                                           %
% Uses failure to avoid rebuilding unchanged subterms.                       %
%----------------------------------------------------------------------------%

letrec DEPTH_FORALL_QCONV conv tm =
 if (is_forall tm)
 then RAND_QCONV (ABS_QCONV (DEPTH_FORALL_QCONV conv)) tm
 else conv tm;;

%----------------------------------------------------------------------------%
% FORALL_T : term list -> thm                                                %
%                                                                            %
% Given a list of variables ["x1";...;"xn"] (allowed to be empty), this      %
% function returns the theorem |- (!x1 ... xn. T) = T.                       %
%----------------------------------------------------------------------------%

let FORALL_T vars =
 (if (null vars)
  then T_REFL
  else EQT_INTRO (GENL vars TRUTH)
 ) ? failwith `FORALL_T`;;

%----------------------------------------------------------------------------%
% FORALL_F : term list -> thm                                                %
%                                                                            %
% Given a list of variables ["x1";...;"xn"] (allowed to be empty), this      %
% function returns the theorem |- (!x1 ... xn. F) = F.                       %
%----------------------------------------------------------------------------%

let FORALL_F =
 let forall_simp = SPEC "F" (INST_TYPE [":bool",":*"] FORALL_SIMP)
 in
 letrec FORALL_F' vars =
 (if (null vars)
  then F_REFL
  else (FORALL_EQ (hd vars) (FORALL_F' (tl vars))) TRANS forall_simp
 ) ? failwith `FORALL_F`
 in FORALL_F';;

%----------------------------------------------------------------------------%
% TAUT_CHECK_CONV : conv                                                     %
%                                                                            %
% Given a propositional term with all variables universally quantified,      %
% e.g. "!x1 ... xn. f[x1,...,xn]", this conversion proves the term to be     %
% either true or false, i.e. it returns one of:                              %
%                                                                            %
%    |- (!x1 ... xn. f[x1,...,xn]) = T                                       %
%    |- (!x1 ... xn. f[x1,...,xn]) = F                                       %
%----------------------------------------------------------------------------%

letrec TAUT_CHECK_CONV tm =
 (let (vars,tm') = strip_forall tm
  in
  if (is_T tm') then FORALL_T vars
  if (is_F tm') then FORALL_F vars
  else let (var,body) = dest_forall tm
       in  let tmT = subst ["T",var] body
       in  let thT1 = QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) tmT
       in  let tmT' = rhs (concl thT1)
       in  let thT2 = TAUT_CHECK_CONV tmT'
       in  let thT3 = thT1 TRANS thT2
       in  if (is_F (rhs (concl thT3)))
           then BOOL_CASES_T_F_RULE thT3 tm
           else let tmF = subst ["F",var] body
                in  let thF1 = QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) tmF
                in  let tmF' = rhs (concl thF1)
                in  let thF2 = if (tmF' = tmT')
                               then thT2
                               else TAUT_CHECK_CONV tmF'
                in  let thF3 = thF1 TRANS thF2
                in  if (is_F (rhs (concl thF3)))
                    then BOOL_CASES_F_F_RULE thF3 tm
                    else BOOL_CASES_BOTH_T_RULE (thT3,thF3) tm
 ) ? failwith `TAUT_CHECK_CONV`;;

%----------------------------------------------------------------------------%
% PTAUT_CONV :conv                                                           %
%                                                                            %
% Given a propositional term with all variables universally quantified,      %
% e.g. "!x1 ... xn. f[x1,...,xn]", this conversion proves the term to be     %
% either true or false, i.e. it returns one of:                              %
%                                                                            %
%    |- (!x1 ... xn. f[x1,...,xn]) = T                                       %
%    |- (!x1 ... xn. f[x1,...,xn]) = F                                       %
%                                                                            %
% This conversion tries to simplify before calling TAUT_CHECK_CONV. It also  %
% accepts propositional terms that are not fully universally quantified.     %
% However, for such a term, the conversion will fail if it is not true.      %
% Consider the term "!x2 ... xn. f[x1,...,xn]". TAUT_CHECK_CONV proves       %
% one of:                                                                    %
%                                                                            %
%    |- (!x1 ... xn. f[x1,...,xn]) = T                                       %
%    |- (!x1 ... xn. f[x1,...,xn]) = F                                       %
%                                                                            %
% The former can be manipulated as follows:                                  %
%                                                                            %
%    |- (!x1 ... xn. f[x1,...,xn]) = T                                       %
%    |- !x1 ... xn. f[x1,...,xn]                                             %
%    |- !x2 ... xn. f[x1,...,xn]                                             %
%    |- (!x2 ... xn. f[x1,...,xn]) = T                                       %
%                                                                            %
% However when the fully quantified term is false, we have:                  %
%                                                                            %
%    |- (!x1 ... xn. f[x1,...,xn]) = F                                       %
%    |- ~(!x1 ... xn. f[x1,...,xn])                                          %
%    |- ?x1. ~(!x2 ... xn. f[x1,...,xn])                                     %
%    |- ?x1. ((!x2 ... xn. f[x1,...,xn]) = F)                                %
%                                                                            %
% whereas we want:                                                           %
%                                                                            %
%    |- !x1. ((!x2 ... xn. f[x1,...,xn]) = F)                                %
%                                                                            %
% i.e.                                                                       %
%                                                                            %
%    |- (!x2 ... xn. f[x1,...,xn]) = F                                       %
%                                                                            %
% The conversions given here are not capable of proving the latter theorem   %
% since it is not purely propositional.                                      %
%----------------------------------------------------------------------------%

let PTAUT_CONV tm =
 (let vars = frees tm
  in  let tm' = list_mk_forall (vars,tm)
  in  let th = ((QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV)) THENC
                TAUT_CHECK_CONV) tm'
  in  if (null vars)
      then th
      else if (is_F (rhs (concl th)))
           then failwith `PTAUT_CONV -- false for at least one interpretation`
           else (EQT_INTRO o (SPECL vars) o EQT_ELIM) th
 )
 ?\s if (s = `PTAUT_CONV -- false for at least one interpretation`)
     then failwith s
     else failwith `PTAUT_CONV`;;

%----------------------------------------------------------------------------%
% PTAUT_TAC : tactic                                                         %
%                                                                            %
% Tactic for solving propositional terms.                                    %
%----------------------------------------------------------------------------%

let PTAUT_TAC = CONV_TAC PTAUT_CONV;;

%----------------------------------------------------------------------------%
% PTAUT_PROVE : conv                                                         %
%                                                                            %
% Given a propositional term "t", this conversion returns the theorem |- t   %
% if "t" is a tautology. Otherwise it fails.                                 %
%----------------------------------------------------------------------------%

let PTAUT_PROVE tm = (EQT_ELIM (PTAUT_CONV tm)) ? failwith `PTAUT_PROVE`;;

%============================================================================%
% Tautology checking including instances of propositional tautologies        %
%============================================================================%

%----------------------------------------------------------------------------%
% non_prop_terms : term -> term list                                         %
%                                                                            %
% Computes a list of subterms of a term that are either variables or Boolean %
% valued non-propositional terms. The result list may contain duplicates.    %
%----------------------------------------------------------------------------%

letrec non_prop_terms tm =
   let non_prop_args tm =
      let (op,args) = ((fst o dest_const) # I) (strip_comb tm)
      in  if (mem op [`T`;`F`;`~`;`=`;`/\\`;`\\/`;`==>`;`COND`])
          then flat (map non_prop_terms args)
          else fail
   in  non_prop_args tm
    ?  if (dest_type (type_of tm) = (`bool`,[])) then [tm]
       else failwith `non_prop_terms`;;

%----------------------------------------------------------------------------%
% TAUT_CONV : conv                                                           %
%                                                                            %
% Given a term, "t", that is a valid propositional formula or valid instance %
% of a propositional formula, this conversion returns the theorem |- t = T.  %
% The variables in "t" do not have to be universally quantified.             %
%                                                                            %
% Example:                                                                   %
%                                                                            %
%    TAUT_CONV "!x n y z. x \/ ~(n < 0) \/ y \/ z \/ (n < 0)"  --->          %
%    |- (!x n y z. x \/ ~n < 0 \/ y \/ z \/ n < 0) = T                       %
%----------------------------------------------------------------------------%

let TAUT_CONV tm =
 (let (univs,tm') = strip_forall tm
  in  let insts = setify (non_prop_terms tm')
  in  let vars = map (genvar o type_of) insts
  in  let tm'' = list_mk_forall (vars,subst (combine (vars,insts)) tm')
  in  EQT_INTRO (GENL univs (SPECL insts (PTAUT_PROVE tm'')))
 ) ? failwith `TAUT_CONV`;;

%----------------------------------------------------------------------------%
% TAUT_TAC : tactic                                                          %
%                                                                            %
% Tactic for solving propositional formulae and instances of propositional   %
% formulae.                                                                  %
%----------------------------------------------------------------------------%

let TAUT_TAC = CONV_TAC TAUT_CONV;;

%----------------------------------------------------------------------------%
% TAUT_PROVE : conv                                                          %
%                                                                            %
% Given a valid propositional formula, or a valid instance of a              %
% propositional formula, "t", this conversion returns the theorem |- t.      %
%----------------------------------------------------------------------------%

let TAUT_PROVE tm = (EQT_ELIM (TAUT_CONV tm)) ? failwith `TAUT_PROVE`;;

%============================================================================%
% Export top-level functions from section                                    %
%============================================================================%

(PTAUT_CONV,PTAUT_TAC,PTAUT_PROVE,TAUT_CONV,TAUT_TAC,TAUT_PROVE);;
end_section taut_check;;
let (PTAUT_CONV,PTAUT_TAC,PTAUT_PROVE,TAUT_CONV,TAUT_TAC,TAUT_PROVE) = it;;
