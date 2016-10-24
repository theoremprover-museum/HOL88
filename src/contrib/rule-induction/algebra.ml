% ===================================================================== %
% File		: algebra.ml						%
% DESCRIPTION   : Maximal trace semantics and transition semantics of a	%
%		  small process algebra.              			%
%									%
% AUTHORS	: Juanito Camilleri and Tom Melham		       	%
% DATE		: 91.05.13						%
% ===================================================================== %


% --------------------------------------------------------------------- %
% Open a new theory and load the inductive definitions library.		%
% --------------------------------------------------------------------- %

new_theory `algebra`;;

load_library `ind_defs`;;

% --------------------------------------------------------------------- %
% Load the string library.               				%
% --------------------------------------------------------------------- %

load_library `string`;;

% ===================================================================== %
% Syntax of a small process algebra		        		%
% ===================================================================== %

% --------------------------------------------------------------------- %
% We use the recursive types package to define the syntax of a small	%
% process algebra, with processes					%
%									%
%    agent  ::=   Nil                    [does nothing]			%
%               | Pre  label agent       [prefix agent with label]	%
%               | Sum  agent agent       [nondeterministic choice]	%
%	        | Prod agent agent       [composition]			%
%									%
% The different syntactic classes of processes are thus represented by 	%
% the constructors (constant functions):				%
%									%
%  Nil:agent, Pre:label->agent->agent, Sum and Prod:agent->agent->agent	%
%									%
% for the concrete data type :agent.  The type :label here is just an	%
% abbreviation for :string.						%
% --------------------------------------------------------------------- %

new_type_abbrev (`label`, ":string");;

let agent = 
    define_type `agent`
      `agent =  Nil 
              |  Pre   label  agent
              |  Sum   agent  agent
              |  Prod  agent  agent`;;

% ===================================================================== %
% Standard syntactic theory, derived by the recursive types package.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% prove structural induction theorem for agent.                         %
% --------------------------------------------------------------------- %
let induct = save_thm (`induct`,prove_induction_thm agent);;

% --------------------------------------------------------------------- %
% prove cases theorem for agent.                                        %
% --------------------------------------------------------------------- %
let cases = save_thm (`cases`, prove_cases_thm induct);;

% --------------------------------------------------------------------- %
% Prove that the constructors of the type :agent yield syntactically 	%
% distinct values. One typically needs all symmetric forms of the	%
% inequalities, so we package them all together here.			%
% --------------------------------------------------------------------- %
let distinct =
    let ths = CONJUNCTS (prove_constructors_distinct agent) in
    let rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths in
        save_thm(`distinct`, LIST_CONJ (ths @ rths));;

% --------------------------------------------------------------------- %
% Prove that the constructors Pre, Sum and Prod are one-to-one.         %
% --------------------------------------------------------------------- %
let agent11 =
    let [Pre11;Sum11;Prod11] =
        (CONJUNCTS (prove_constructors_one_one agent)) in
        map save_thm
        [(`Pre11`,Pre11);
         (`Sum11`,Sum11);
         (`Prod11`,Prod11)];;

% ===================================================================== %
% Definition of a maximal trace semantics for the process algebra.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Type abbreviation for traces.   These are just finite sequences of 	%
% labels, represented here by lists.					%
% --------------------------------------------------------------------- %
new_type_abbrev (`trace`, ":(label)list");;

% --------------------------------------------------------------------- %
% Inductive definition of a trace relation MTRACE.  This is defined so	%
% that MTRACE P A means A is the maximal trace of the process P. The 	%
% definition is done inductively by the rules given below.	     	%
% --------------------------------------------------------------------- %

let (trules,tind) =
    let MTRACE = "MTRACE:agent->trace->bool" in
    new_inductive_definition false `MTRACE_DEF` 

    ("^MTRACE P A", [])

    [ [                                             
      %-------------------------------------------- % ],
                     "^MTRACE Nil []"               ;   


      [               "^MTRACE P A"                 
      %-------------------------------------------- % ],
              "^MTRACE (Pre a P) (CONS a A)"        ;


      [                 "^MTRACE P A"                
      %-------------------------------------------- % ],
                    "^MTRACE (Sum P Q) A"           ;


      [                 "^MTRACE Q A"                
      %-------------------------------------------- % ],
                    "^MTRACE (Sum P Q) A"           ;


      [    "^MTRACE P A";          "^MTRACE Q A"    
      %-------------------------------------------- % ],
                  "^MTRACE (Prod P Q) A"            ];;


% --------------------------------------------------------------------- %
% Definition of a terminal process: one with [] as a maximal trace.	%
% --------------------------------------------------------------------- %

let TERMINAL_DEF =
    new_definition (`TERMINAL_DEF`, "TERMINAL P = MTRACE P []");;


% --------------------------------------------------------------------- %
% Stronger form of rule induction.					%
% --------------------------------------------------------------------- %

let tsind = derive_strong_induction (trules,tind);;

% --------------------------------------------------------------------- %
% Standard rule induction tactic for MTRACE. This uses the weaker form  %
% of the rule induction theorem, and both premisses and side conditions %
% are just assumed (in stripped form).  				%
% --------------------------------------------------------------------- %

let MTRACE_INDUCT_TAC =
    RULE_INDUCT_THEN tind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Prove the case analysis theorem for the rules defining MTRACE.	%
% --------------------------------------------------------------------- %

let tcases = derive_cases_thm (trules,tind);;

% --------------------------------------------------------------------- %
% Tactics for each of the rules defining MTRACE.			%
% --------------------------------------------------------------------- %
let [Nil_TAC;Pre_TAC;SumL_TAC;SumR_TAC;Prod_TAC] = map RULE_TAC trules;;

% --------------------------------------------------------------------- %
% Given the tactics defined above for each rule, we now define a tactic %
% that searches for a proof that a process has some particular maximal  %
% trace, given some assumptions about maximal traces.  Note that there	%
% are two Sum rules, so our tactic may have to do some backtracking in  %
% the proof.  In addition to seaching using the MTRACE rules, the 	%
% looks for solutions among the assumptions as well as back-chaining 	%
% with any implications among the assumptions. The tactics fails unless %
% it completely solves the goal.					%
% --------------------------------------------------------------------- %

letrec MTRACE_TAC g =
   (REPEAT STRIP_TAC THEN
    FIRST [Nil_TAC;
           FIRST_ASSUM MATCH_ACCEPT_TAC;
           Pre_TAC THEN MTRACE_TAC;
           SumL_TAC THEN MTRACE_TAC;
           SumR_TAC THEN MTRACE_TAC;
           Prod_TAC  THEN MTRACE_TAC;
   	   FIRST_ASSUM MATCH_MP_TAC THEN MTRACE_TAC]) g ? 
   failwith `MTRACE_TAC`;;

% --------------------------------------------------------------------- %
% The following is a little rule for getting simplified instances of	%
% the tcases theorem.  All it does is to specialize tcases to the 	%
% supplied process, rewrite using the distinctness and injectivity of	%
% constrctors, and eliminate redundant equations using REDUCE. Examples %
% of using MTCASE are:							%
%									%
%   #MTCASE "Prod P Q";;						%
%   |- !P Q A. MTRACE(Prod P Q)A = MTRACE P A /\ MTRACE Q A		%
%									%
%   #MTCASE "Sum P Q";;							%
%   |- !P Q A. MTRACE(Sum P Q)A = MTRACE P A \/ MTRACE Q A		%
%									%
% --------------------------------------------------------------------- %

let MTCASE =
    let SIMPLIFY = REWRITE_RULE (distinct . agent11) in
    \tm. let th1 = SIMPLIFY (SPEC tm tcases) in
         GEN_ALL (CONV_RULE (ONCE_DEPTH_CONV REDUCE) th1);;

% ===================================================================== %
% Inductive definition of a labelled transition system.                	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% We now define a labelled transition relation TRANS P l Q to mean	%
% there that process P can participate in action l and thereby evolve	%
% into process Q.  The definition is done inductively, as usual.        %
% --------------------------------------------------------------------- %

let (lrules,lind) =
    let TRANS = "TRANS: agent->label->agent->bool" in
    new_inductive_definition false `TRANS_DEF` 

    ("^TRANS G b E",[])

    [ [			                      
      % ------------------------------------- % ],
               "^TRANS (Pre a Q) a Q"         ;

 
      [	           "^TRANS P a P'"             
      % ------------------------------------- % ],
               "^TRANS (Sum P Q) a P'"        ;


      [	           "^TRANS Q a Q'"            
      % ------------------------------------- % ],
               "^TRANS (Sum P Q) a Q'"        ;


      [ "^TRANS P a P'";      "^TRANS Q a Q'"; 
      %-------------------------------------- % ],
          "^TRANS (Prod P Q) a (Prod P' Q')"  ];;

% --------------------------------------------------------------------- %
% Strong form of rule induction for TRANS.	      			%
% --------------------------------------------------------------------- %

let lsind = derive_strong_induction (lrules,lind);;

% --------------------------------------------------------------------- %
% Standard rule induction tactic for TRANS. This again just uses the	%
% weaker form of rule induction theorem.  Both premisses and side 	%
% conditions are assumed (in stripped form).  				%
% --------------------------------------------------------------------- %

let TRANS_INDUCT_TAC =
    RULE_INDUCT_THEN lind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Cases theorem for TRANS. 						%
% --------------------------------------------------------------------- %

let lcases =  derive_cases_thm (lrules,lind);;

% --------------------------------------------------------------------- %
% Tactics for the TRANS rules.						%
% --------------------------------------------------------------------- %
let [TPre_TAC;TSumL_TAC;TSumR_TAC;TProd_TAC] = map RULE_TAC lrules;;

% --------------------------------------------------------------------- %
% Given the tactics defined above for each rule, we construct a tactic  %
% that searches for a proof of TRANS P a Q, with becktracking in the 	%
% Sum case.  The tactic also looks for the solution on the assumption	%
% list of the goal, with backchaining through implications. 		%
% --------------------------------------------------------------------- %
letrec TRANS_TAC g =
   (REPEAT STRIP_TAC THEN
    FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
           TPre_TAC;
           TSumL_TAC THEN TRANS_TAC;
           TSumR_TAC THEN TRANS_TAC;
           TProd_TAC  THEN TRANS_TAC;
   	   FIRST_ASSUM MATCH_MP_TAC THEN TRANS_TAC]) g ? 
   failwith `TRANS_TAC`;;

% ===================================================================== %
% Inductive definition of a trace transition system                	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% We now define a transition system that accumulates the trace of a	%
% process.  This is essentially the reflexive-transitive closure of	%
% TRANS, but with the label being a list of the labels from TRANS.	%
% --------------------------------------------------------------------- %

let (Lrules,Lind) =
    let TRANSIT = "TRANSIT: agent->(label)list->agent->bool" in
    new_inductive_definition false `TRANSIT_DEF`

    ("^TRANSIT X L Y",[])

    [ [                                       
         				        ],
      % --------------------------------------- %
              "^TRANSIT P [] P"             ;


      [  "TRANS (P:agent) (a:label) (Q:agent)";

                  "^TRANSIT Q B P'"             ],
      % --------------------------------------- %
               "^TRANSIT P (CONS a B) P'"       ];;


% --------------------------------------------------------------------- %
% Strong form of rule induction for labelled (trace) transitions.      	%
% --------------------------------------------------------------------- %

let Lsind = derive_strong_induction (Lrules,Lind);;

% --------------------------------------------------------------------- %
% Rule induction tactic for TRANSIT.					%
% --------------------------------------------------------------------- %

let TRANSIT_INDUCT_TAC = RULE_INDUCT_THEN Lind ASSUME_TAC ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Cases theorem for the trace transition system.		      	%
% --------------------------------------------------------------------- %

let Lcases = derive_cases_thm (Lrules,Lind);;

% --------------------------------------------------------------------- %
% A tactic for each TRANSIT rule. If matching conclusions to goals,     %
% the two rules are mutually exclusive---so only the following single	%
% tactic is needed.							%
% --------------------------------------------------------------------- %

let TRANSIT_TAC = MAP_FIRST RULE_TAC Lrules;;

% ===================================================================== %
% Theorem 1: Maximal trace semantics `agrees' with transition semantics	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Lemma 1 is to prove the following theorem:				%
%									%
%    |- !P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (CONS a A)  %
%									%
% The proof is a straightforward rule induction on TRANS, followed by	%
% a case analysis on MTRACE Q A when Q is a product (Prod), and then	%
% completed by a simple search for the proof of the conclusion using 	%
% the tactic MTRACE_TAC.						%
% --------------------------------------------------------------------- %

let Lemma1 =
    PROVE
    ("!P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (CONS a A)",  
     TRANS_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     let PCASES = PURE_ONCE_REWRITE_RULE [MTCASE "Prod P Q"] in
     DISCH_THEN (STRIP_ASSUME_TAC o PCASES) THEN MTRACE_TAC);;

% --------------------------------------------------------------------- %
% Theorem 1:  |- !P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A    %
%									%
% This theorem shows that the trace semantics agrees with the 		%
% trace-transition semantics, in the sense that if we follow the	%
% transitions of a process P until we reach a terminal process Q, that	%
% is a process with an empty maximal trace, then we will have gone	%
% through a maximal trace of P.						%
% --------------------------------------------------------------------- %

let Theorem1 =
    prove_thm
    (`Theorem1`,
     "!P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A",
     PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] THEN 
     TRANSIT_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
     RES_TAC THEN IMP_RES_TAC Lemma1);;

% --------------------------------------------------------------------- %
% Corollary 1: !P A Q. TRANSIT P A Nil ==> MTRACE P A                   %
%									%
% Note that the converse does not hold.					%
% --------------------------------------------------------------------- %

let Corollary1 = 
    prove_thm
    (`Corollary1`,
     "!P A. TRANSIT P A Nil ==> MTRACE P A",
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN MATCH_MP_TAC Theorem1 THEN
     PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] THEN
     MTRACE_TAC);;

% ===================================================================== %
% Theorem 2: Transition semantics `agrees' with maximal trace semantics %
% ===================================================================== %

% --------------------------------------------------------------------- %
% The following tactic is for solving existentially-quantified goals,	%
% the bodies of which are conjunctions of assertions of membership in	%
% one or more of the inductively-defined relations we're working with.  %
% All it does is to reduce the goal with the supplied witness, and then %
% apply the tactic for the relevant relation.				%
% --------------------------------------------------------------------- %

let EXISTS_SEARCH_TAC tm =
     EXISTS_TAC tm THEN REPEAT STRIP_TAC THEN
       TRY(FIRST [TRANS_TAC; MTRACE_TAC; TRANSIT_TAC]);;

% --------------------------------------------------------------------- %
% A little tactic for case analysis on the trace-transition system. 	%
% When supplied with a term "TRANSIT P A Q", which should be one of the %
% assumptions of the current goal, the tactic gets the corresponding	%
% instance of the TRANSIT case analysis theorem, simplifies out any	%
% false case, and enriches the goal with the remaining facts, either by	%
% assuming them or, in the case of equations, by substitution.		%
% --------------------------------------------------------------------- %

let TRANSIT_CASES_TAC = 
    let SUBST_ASSUME th g = SUBST_ALL_TAC th g ? STRIP_ASSUME_TAC th g in
    let TTAC = (REPEAT_TCL STRIP_THM_THEN SUBST_ASSUME) in
    \tm. let th1 = UNDISCH(fst(EQ_IMP_RULE(REWR_CONV Lcases tm))) in
         let th2 = REWRITE_RULE [NOT_CONS_NIL;NOT_NIL_CONS;CONS_11] th1 in
             REPEAT_TCL STRIP_THM_THEN SUBST_ASSUME th2;;

% --------------------------------------------------------------------- %
% Lemma 2 shows that the trace of a product is just the trace of its	%
% two components in the relation TRANSIT. The proof is a sraightfoward	%
% structural induction on the list A, with simplification using the     %
% case analysis theorem for TRANSIT.					%
% --------------------------------------------------------------------- %

let Lemma2 =
    PROVE
    ("!A P Q P' Q'.
       TRANSIT P A Q /\ TRANSIT P' A Q' ==> TRANSIT (Prod P P') A (Prod Q Q')",
     INDUCT_THEN list_INDUCT ASSUME_TAC THEN
     PURE_ONCE_REWRITE_TAC [Lcases] THEN
     REWRITE_TAC ([NOT_NIL_CONS;NOT_CONS_NIL;CONS_11] @ agent11) THEN
     CONV_TAC (ONCE_DEPTH_CONV REDUCE) THEN
     REPEAT STRIP_TAC THEN EXISTS_SEARCH_TAC "Prod Q'' Q'''");;

% --------------------------------------------------------------------- %
% Theorem 2:  |- !P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q	%
%									%
% This theorem shows that the transition semantics `agrees' with the	%
% trace semantics, in the sense that every maximal trace A leads in the %
% transition semantics to a terminal process.  The proof proceeds by	%
% rule induction on MTRACE P A, followed by semi-automatic search for 	%
% proofs of TRANSIT P A Q and TERMINAL Q.  The user supplies a witness 	%
% for any existential goals that arise.  There is also a case analysis  %
% on the TRANSIT assumption in the Sum cases, there being different 	%
% witnesses required for the two TRANSIT rules.				%
% --------------------------------------------------------------------- %

let Theorem2 =
    prove_thm
    (`Theorem2`,
     "!P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q",
     PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] THEN
     MTRACE_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [EXISTS_SEARCH_TAC "Nil";
      MAP_EVERY EXISTS_SEARCH_TAC ["Q:agent";"P:agent"];
      TRANSIT_CASES_TAC "TRANSIT P A Q" THENL
      [EXISTS_SEARCH_TAC "Sum P Q'";
       MAP_EVERY EXISTS_SEARCH_TAC ["Q:agent"; "Q'':agent"]];
      TRANSIT_CASES_TAC "TRANSIT Q A Q'" THENL
      [EXISTS_SEARCH_TAC "Sum P Q";
       MAP_EVERY EXISTS_SEARCH_TAC ["Q':agent"; "Q'':agent"]]; 
      IMP_RES_TAC Lemma2 THEN EXISTS_SEARCH_TAC "Prod Q' Q''"]);;

% ===================================================================== %
% Theorem3: The transition and maximal trace semantics `agree'.		%
% ===================================================================== %

let Theorem3 =
    prove_thm
    (`Theorem3`,
     "!P A. MTRACE P A = (?Q. TRANSIT P A Q /\ TERMINAL Q)",
     REPEAT (EQ_TAC ORELSE STRIP_TAC) THENL
     [MATCH_MP_TAC Theorem2 THEN FIRST_ASSUM ACCEPT_TAC;
      IMP_RES_TAC Theorem1]);;


% ===================================================================== %
% Definitions of notions of equivalence                                 %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Maximal trace equivalence. Two processes are maximal trace equivalent %
% if they have the same maximal traces.					%
% --------------------------------------------------------------------- %

let MEQUIV_DEF =
    new_infix_definition 
    (`MEQUIV_DEF`,    
     "MEQUIV P Q = (!A. MTRACE P A = MTRACE Q A)");;

% --------------------------------------------------------------------- %
% Bisimulation equivalence.  A binary relation s:agent->agent->bool is  %
% a simulation if s P Q implies that any transitions that P can do can  %
% also be done by Q such that the corresponding successive pairs of	%
% agents remain in the relation s.  Equivalence is then defined to be 	%
% the bisimulation (simulation whose inverse is also a simulation).	%
% --------------------------------------------------------------------- %

let SIM_DEF =
    new_definition 
    (`SIM_DEF`,
     "SIM s = 
      !P Q. s P Q ==>
            !a P'. TRANS P a P' ==> ?Q'. TRANS Q a Q' /\ s P' Q'");;

let BEQUIV_DEF =
    new_infix_definition 
    (`BEQUIV_DEF`,
     "BEQUIV P Q = ?s. SIM s /\ s P Q /\ SIM(\x y. s y x)");;


% --------------------------------------------------------------------- %
% End of example.							%
% --------------------------------------------------------------------- %

close_theory();;
quit();;

