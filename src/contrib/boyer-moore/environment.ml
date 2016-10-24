%****************************************************************************%
% FILE          : environment.ml                                             %
% DESCRIPTION   : Environment of definitions and pre-proved theorems for use %
%                 in automation.                                             %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 8th May 1991                                               %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 12th October 1992                                          %
%****************************************************************************%

%----------------------------------------------------------------------------%
% Reference variable to hold the defining theorems for operators currently   %
% defined within the system. Each definition is stored as a triple. The      %
% first component is the name of the operator. The second is the number of   %
% the recursive argument. If the operator is not defined recursively, this   %
% number is zero. The third component is a list of pairs of type constructor %
% names and the theorems that define the behaviour of the operator for each  %
% constructor. If the operator is not recursive, the constructor names are   %
% empty (null) strings.                                                      %
%----------------------------------------------------------------------------%

letref system_defs = []:(string # int # (string # thm) list) list;;

%----------------------------------------------------------------------------%
% new_def : thm -> void                                                      %
%                                                                            %
% Make a new definition available. Checks that theorem has no hypotheses,    %
% then splits it into conjuncts. The variables for each conjunct are         %
% specialised and then the conjuncts are made into equations.                %
%                                                                            %
% For each equation, a triple is obtained, consisting of the name of the     %
% function on the LHS, the number of the recursive argument, and the name of %
% the constructor used in that argument. This process fails if the LHS is    %
% not an application of a constant (possibly to zero arguments), or if more  %
% than one of the arguments is anything other than a variable. The argument  %
% that is not a variable must be an application of a constructor. If the     %
% function is not recursive, the argument number returned is zero.           %
%                                                                            %
% Having obtained a triple for each equation, a check is made that the first %
% two components are the same for each equation. Then, the equations are     %
% saved together with constructor names for each, and the name of the        %
% operator being defined, and the number of the recursive argument.          %
%----------------------------------------------------------------------------%

let new_def th =
 (let make_into_eqn th =
     let tm = concl th
     in  if (is_eq tm) then th
         if (is_neg tm) then EQF_INTRO th
         else EQT_INTRO th
  and get_constructor th =
     let tm = lhs (concl th)
     in  let (f,args) = strip_comb tm
     in  let name = fst (dest_const f)
     in  let bools = number_list (map is_var args)
     in  let i = itlist (\(b,i) n. if ((not b) & (n = 0)) then i
                                   if b then n else fail) bools 0
     in  if (i = 0)
         then ((name,i),``)
         else ((name,i),fst (dest_const (fst (strip_comb (el i args)))))
  in  let ([],tm) = dest_thm th
  in  let ths = CONJ_LIST (length (conj_list tm)) th
  in  let ths' = map SPEC_ALL ths
  in  let eqs = map make_into_eqn ths'
  in  let constructs = map get_constructor eqs
  in  let (xl,yl) = (setify # I) (split constructs)
  in  let (name,i) = if (length xl = 1) then (hd xl) else fail
  in  do (system_defs := (name,i,combine (yl,eqs)).system_defs)
 ) ? failwith `new_def`;;

%----------------------------------------------------------------------------%
% defs : void -> thm list list                                               %
%                                                                            %
% Returns a list of lists of theorems currently being used as definitions.   %
% Each list in the list is for one operator.                                 %
%----------------------------------------------------------------------------%

let defs (():void) = map ((map snd) o snd o snd) system_defs;;

%----------------------------------------------------------------------------%
% get_def : string -> (string # int # (string # thm) list)                   %
%                                                                            %
% Function to obtain the definition information of a named operator.         %
%----------------------------------------------------------------------------%

let get_def name = assoc name system_defs ? failwith `get_def`;;

%----------------------------------------------------------------------------%
% Reference variable for a list of theorems currently proved in the system.  %
% These theorems are available to the automatic proof procedures for use as  %
% rewrite rules. The elements of the list are actually pairs of theorems.    %
% The first theorem is that specified by the user. The second is an          %
% equivalent theorem in a standard form.                                     %
%----------------------------------------------------------------------------%

letref system_rewrites = []:(thm # thm) list;;

%----------------------------------------------------------------------------%
% CONJ_IMP_IMP_IMP = |- x /\ y ==> z = x ==> y ==> z                         %
%----------------------------------------------------------------------------%

let CONJ_IMP_IMP_IMP =
 prove
  ("((x /\ y) ==> z) = (x ==> (y ==> z))",
   BOOL_CASES_TAC "x:bool" THEN
   BOOL_CASES_TAC "y:bool" THEN
   BOOL_CASES_TAC "z:bool" THEN
   REWRITE_TAC []);;

%----------------------------------------------------------------------------%
% CONJ_UNDISCH : thm -> thm                                                  %
%                                                                            %
% Undischarges the conjuncts of the antecedant of an implication.            %
% e.g. |- x /\ (y /\ z) /\ w ==> x  --->  x, y /\ z, w |- x                  %
%                                                                            %
% Has to check for negations, because UNDISCH processes them when we don't   %
% want it to.                                                                %
%----------------------------------------------------------------------------%

letrec CONJ_UNDISCH th =
 (let th' = CONV_RULE (REWR_CONV CONJ_IMP_IMP_IMP) th
  in  let th'' = UNDISCH th'
  in  CONJ_UNDISCH th'')
 ? (if not (is_neg (concl th)) then UNDISCH th else fail)
 ? failwith `CONJ_UNDISCH`;;

%----------------------------------------------------------------------------%
% new_rewrite_rule : thm -> void                                             %
%                                                                            %
% Make a new rewrite rule available. Checks that theorem has no hypotheses.  %
% The theorem is saved together with an equivalent theorem in a standard     %
% form. Theorems are fully generalized, then specialized with unique         %
% variable names (genvars), and then standardized as follows:                %
%                                                                            %
%    |- (h1 /\ ... /\ hn) ==> (l = r)  --->  h1, ..., hn |- l = r            %
%    |- (h1 /\ ... /\ hn) ==> ~b       --->  h1, ..., hn |- b = F            %
%    |- (h1 /\ ... /\ hn) ==> b        --->  h1, ..., hn |- b = T            %
%    |- l = r                          --->  |- l = r                        %
%    |- ~b                             --->  |- b = F                        %
%    |- b                              --->  |- b = T                        %
%                                                                            %
% A conjunction of rules may be given. The function will treat each conjunct %
% in the theorem as a separate rule.                                         %
%----------------------------------------------------------------------------%

letrec new_rewrite_rule th =
 (if (is_conj (concl th))
  then do (map new_rewrite_rule (CONJUNCTS th))
  else
  let ([],tm) = dest_thm th
  in  let th' = GSPEC (GEN_ALL th)
  in  let th'' = CONJ_UNDISCH th' ? th'
  in  let tm'' = concl th''
  in  let th''' =
         if (is_eq tm'') then th''
         if (is_neg tm'') then EQF_INTRO th''
         else EQT_INTRO th''
  in  do (system_rewrites := (th,th''').system_rewrites)
 ) ? failwith `new_rewrite_rule`;;

%----------------------------------------------------------------------------%
% rewrite_rules : void -> thm list                                           %
%                                                                            %
% Returns the list of theorems currently being used as rewrites, in the form %
% they were originally given by the user.                                    %
%----------------------------------------------------------------------------%

let rewrite_rules (():void) = map fst system_rewrites;;

%----------------------------------------------------------------------------%
% Reference variable to hold the generalisation lemmas currently known to    %
% the system.                                                                %
%----------------------------------------------------------------------------%

letref system_gen_lemmas = []:thm list;;

%----------------------------------------------------------------------------%
% new_gen_lemma : thm -> void                                                %
%                                                                            %
% Make a new generalisation lemma available.                                 %
% Checks that the theorem has no hypotheses.                                 %
%----------------------------------------------------------------------------%

let new_gen_lemma th =
   if (null (hyp th))
   then do (system_gen_lemmas := th.system_gen_lemmas)
   else failwith `new_gen_lemma`;;

%----------------------------------------------------------------------------%
% gen_lemmas : void -> thm list                                              %
%                                                                            %
% Returns the list of theorems currently being used as                       %
% generalisation lemmas.                                                     %
%----------------------------------------------------------------------------%

let gen_lemmas (():void) = system_gen_lemmas;;
