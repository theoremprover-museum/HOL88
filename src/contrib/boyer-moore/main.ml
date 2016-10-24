%****************************************************************************%
% FILE          : main.ml                                                    %
% DESCRIPTION   : The main functions for the Boyer-Moore-style prover.       %
%                                                                            %
% READS FILES   : <none>                                                     %
% WRITES FILES  : <none>                                                     %
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 27th June 1991                                             %
%                                                                            %
% LAST MODIFIED : R.J.Boulton                                                %
% DATE          : 13th October 1992                                          %
%****************************************************************************%

%----------------------------------------------------------------------------%
% BOYER_MOORE : conv                                                         %
%                                                                            %
% Boyer-Moore-style automatic theorem prover.                                %
% Given a term "tm", attempts to prove |- tm.                                %
%----------------------------------------------------------------------------%

let BOYER_MOORE tm =
 proof_print_depth := 0;
 (proof_print_newline
     (WATERFALL
         [clausal_form_heuristic;
          subst_heuristic;
          simplify_heuristic;
          use_equality_heuristic;
          generalize_heuristic;
          irrelevance_heuristic]
         induction_heuristic
         (tm,false))
 ) ? failwith `BOYER_MOORE`;;

%----------------------------------------------------------------------------%
% BOYER_MOORE_CONV : conv                                                    %
%                                                                            %
% Boyer-Moore-style automatic theorem prover.                                %
% Given a term "tm", attempts to prove |- tm = T.                            %
%----------------------------------------------------------------------------%

let BOYER_MOORE_CONV tm =
 (EQT_INTRO (BOYER_MOORE tm)) ? failwith `BOYER_MOORE_CONV`;;

%----------------------------------------------------------------------------%
% HEURISTIC_TAC :                                                            %
%    ((term # bool) -> ((term # bool) list # proof)) list -> tactic          %
%                                                                            %
% Tactic to do automatic proof using a list of heuristics. The tactic will   %
% fail if it thinks the goal is not a theorem. Otherwise it will either      %
% prove the goal, or return as subgoals the conjectures it couldn't handle.  %
%                                                                            %
% If the `proof_printing' flag is set to true, the tactic displays each new  %
% conjecture it generates, prints blank lines between subconjectures which   %
% resulted from a split, and prints a final blank line when it can do no     %
% more.                                                                      %
%                                                                            %
% Given a goal, the tactic constructs an implication from it, so that the    %
% hypotheses are made available. It then tries to prove this implication.    %
% When it can do no more, the function splits the clauses that it couldn't   %
% prove into disjuncts. The last disjunct is assumed to be a conclusion, and %
% the rest are taken to be hypotheses. These new goals are returned together %
% with a proof of the original goal.                                         %
%                                                                            %
% The proof takes a list of theorems for the subgoals and discharges the     %
% hypotheses so that the theorems are in clausal form. These clauses are     %
% then used to prove the implication that was constructed from the original  %
% goal. Finally the antecedants of this implication are undischarged to give %
% a theorem for the original goal.                                           %
%----------------------------------------------------------------------------%

let HEURISTIC_TAC heuristics (asl,w) =
 proof_print_depth := 0;
 (let negate tm = if (is_neg tm) then (rand tm) else (mk_neg tm)
  and NEG_DISJ_DISCH tm th =
     if (is_neg tm)
     then DISJ_DISCH (rand tm) th
     else CONV_RULE (REWR_CONV IMP_DISJ_THM) (DISCH tm th)
  in  let tm = list_mk_imp (asl,w)
  in  let tree = proof_print_newline
                    (waterfall (clausal_form_heuristic.heuristics) (tm,false))
  in  let tml = map fst (fringe_of_clause_tree tree)
  in  let disjsl = map disj_list tml
  in  let goals = map (\disjs. (map negate (butlast disjs),last disjs)) disjsl
  in  let proof thl =
         let thl' = map (\(th,goal). itlist NEG_DISJ_DISCH (fst goal) th)
                           (combine (thl,goals))
         in  funpow (length asl) UNDISCH (prove_clause_tree tree thl')
  in  (goals,proof)
 ) ? failwith `HEURISTIC_TAC`;;

%----------------------------------------------------------------------------%
% BOYER_MOORE_TAC : tactic                                                   %
%                                                                            %
% Tactic to do automatic proof using Boyer & Moore's heuristics. The tactic  %
% will fail if it thinks the goal is not a theorem. Otherwise it will either %
% prove the goal, or return as subgoals the conjectures it couldn't handle.  %
%----------------------------------------------------------------------------%

let BOYER_MOORE_TAC aslw =
 (HEURISTIC_TAC
     [subst_heuristic;
      simplify_heuristic;
      use_equality_heuristic;
      generalize_heuristic;
      irrelevance_heuristic;
      induction_heuristic]
     aslw
 ) ? failwith `BOYER_MOORE_TAC`;;

%----------------------------------------------------------------------------%
% BM_SIMPLIFY_TAC : tactic                                                   %
%                                                                            %
% Tactic to do automatic simplification using Boyer & Moore's heuristics.    %
% The tactic will fail if it thinks the goal is not a theorem. Otherwise, it %
% will either prove the goal or return the simplified conjectures as         %
% subgoals.                                                                  %
%----------------------------------------------------------------------------%

let BM_SIMPLIFY_TAC aslw =
 (HEURISTIC_TAC [subst_heuristic;simplify_heuristic] aslw
 ) ? failwith `BM_SIMPLIFY_TAC`;;

%----------------------------------------------------------------------------%
% BM_INDUCT_TAC : tactic                                                     %
%                                                                            %
% Tactic which attempts to do a SINGLE induction using Boyer & Moore's       %
% heuristics. The cases of the induction are returned as subgoals.           %
%----------------------------------------------------------------------------%

let BM_INDUCT_TAC aslw =
 (letref induct = true
  in  let once_induction_heuristic x =
         if induct then (induct := false; induction_heuristic x) else fail
  in  HEURISTIC_TAC [once_induction_heuristic] aslw
 ) ? failwith `BM_INDUCT_TAC`;;
