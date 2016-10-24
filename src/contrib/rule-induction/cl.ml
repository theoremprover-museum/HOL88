% ===================================================================== %
% FILE		: cl.ml							%
% DESCRIPTION   : Creates the syntactic theory of combinatory logic and %
%		  defines reduction of terms in the logic. Proves the	%
%		  Church-Rosser theorem for this reduction relation.	%
%									%
% AUTHORS	: Tom Melham and Juanito Camilleri			%
% DATE		: 91.10.09						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Open a new theory and load the inductive definitions library.		%
% --------------------------------------------------------------------- %

new_theory `cl`;;

load_library `ind_defs`;;


% ===================================================================== %
% Syntax of the combinatory logic.					%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The recursive types package is used to define the syntax of terms in 	%
% combnatory logic. The syntax is:					%
%									%
%    U ::=   s  |  k  |  U1 ' U2					%
%                                                                       %
% where U, U1, and U2 range over terms. In higher order logic, terms of	%
% combinatory logic are represented by the following constructors of a	%
% recursive type cl:							%
%						                        %
%    s:cl,  k:cl, and ap:cl -> cl -> cl					%
%									%
% We are unfortunately prevented from the using upper-case letter S, as %
% this is already a constant in the built-in HOL theory heirarchy. For  %
% notational clarity, we later introduce an infix constant ' for the	%
% application constructor shown above as `ap'.				%
% --------------------------------------------------------------------- %

let cl = define_type `cl` `cl = s | k | ap cl cl`;;


% --------------------------------------------------------------------- %
% Define an infix constructor for application.				%
% --------------------------------------------------------------------- %

new_letter `'`;;
let ap_def = new_infix_definition(`ap_def`, "' = ap");;


% --------------------------------------------------------------------- %
% Replace `ap' by the infix.						%
% --------------------------------------------------------------------- %

let cl = save_thm(`cl_thm`, SUBS [SYM ap_def] cl);;


% ===================================================================== %
% Standard syntactic theory, derived by the recursive types package.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Structural induction theorem for terms of combinatory logic .		%
% --------------------------------------------------------------------- %

let induct = save_thm (`induct`,prove_induction_thm cl);;

% --------------------------------------------------------------------- %
% Exhaustive case analysis theorem for terms of combinatory logic.	%
% --------------------------------------------------------------------- %

let cases = save_thm (`cases`, prove_cases_thm induct);;

% --------------------------------------------------------------------- %
% Prove that the application constructor is one-to-one.			%
% --------------------------------------------------------------------- %

let ap11 = save_thm(`ap11`, prove_constructors_one_one cl);;

% --------------------------------------------------------------------- %
% Prove that the constructors yield syntactically distinct values. One	%
% typically needs all symmetric forms of the inequalities.		%
% --------------------------------------------------------------------- %

let distinct =
    let ths = CONJUNCTS (prove_constructors_distinct cl) in
    let rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths in
        save_thm(`distinct`, LIST_CONJ (ths @ rths));;


% ===================================================================== %
% Inductive definition of reduction of CL terms.			%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Definition of weak contraction.					%
%                                                                       %
% The one-step contraction relation -> is inductively defined by the 	%
% rules shown below.  This is the `weak contraction' relation of 	%
% Hindley and Seldin.  A weak redex is a term of the form Kxy or Sxyz.  %
% A term U weakly contracts to V (i.e. U -1-> V) if V can be obtained   %
% by replacing one occurrence of a redex in U, where a redex Kxy is	%
% replaced by x and a redex Sxyz is replaced by (xz)yz.  The first two  %
% rules in the inductive definition given below define the contraction  % 
% of redexes; the second two rules define the contraction of subterms.	%
% --------------------------------------------------------------------- %

new_special_symbol `-1->`;;

let (Crules,Cind) =
    let CTR = "-1->:cl->cl->bool" in
    new_inductive_definition true `contract` 

    ("^CTR U V", [])

    [ [                                                               
      % ------------------------------------------------------ % ],
                       "^CTR ((k ' x) ' y) x"                  ;

      [                                                              
      %------------------------------------------------------- % ],
           "^CTR (((s ' x) ' y) ' z)  ((x ' z) ' (y ' z))"     ;


      [                     "^CTR x y"                               
      %------------------------------------------------------- % ],
                      "^CTR (x ' z) (y ' z)"                   ;


      [                     "^CTR x y"                              
      %------------------------------------------------------- % ],
                      "^CTR (z ' x) (z ' y)"                     ];;



% --------------------------------------------------------------------- %
% Stronger form of rule induction.					%
% --------------------------------------------------------------------- %

let Csind = derive_strong_induction (Crules,Cind);;

% --------------------------------------------------------------------- %
% Standard rule induction tactic for -1->.  This uses the weaker form   %
% of the rule induction theorem; and both premisses and side conditions %
% are just assumed (in stripped form).  				%
% --------------------------------------------------------------------- %

let C_INDUCT_TAC =
    RULE_INDUCT_THEN Cind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Prove the case analysis theorem for the contraction rules.		%
% --------------------------------------------------------------------- %

let Ccases = derive_cases_thm (Crules,Cind);;

% --------------------------------------------------------------------- %
% Tactics for each of the contraction rules.				%
% --------------------------------------------------------------------- %
let [Ck_TAC;Cs_TAC;LCap_TAC;RCap_TAC] = map RULE_TAC Crules;;


% --------------------------------------------------------------------- %
% The weak reduction relation on terms in combinatory logic is just the %
% reflexive-transitive closure of -1->.  We define reflexive-transitive %
% closure inductively as follows, and then define the weak reduction 	%
% relation ---> to be RTC -1->.						%
% --------------------------------------------------------------------- %

let (RTCrules,RTCind) =
    let RTC = "RTC:(*->*->bool)->*->*->bool" in
    new_inductive_definition false `RTC` 

    ("^RTC R x y", ["R:*->*->bool"])

    [ [				       
      % ------------------------------ % "R (x:*) (y:*):bool"],
                "^RTC R x y"	       ;

      [				       
      % ------------------------------ % ],
                "^RTC R x x"	       ;


      [  "^RTC R x z"; "^RTC R z y"    
      %------------------------------- % ],
                "^RTC R x y"	       ];;



% --------------------------------------------------------------------- %
% Standard rule induction tactic for RTC.				%
% --------------------------------------------------------------------- %

let RTC_INDUCT_TAC =
    RULE_INDUCT_THEN RTCind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Tactics for the RTC rules.						%
% --------------------------------------------------------------------- %

let [RTC_IN_TAC;RTC_REFL_TAC;RTC_TRANS_TAC] = map RULE_TAC RTCrules;;


% --------------------------------------------------------------------- %
% Case analysis theorem for RTC.					%
% --------------------------------------------------------------------- %

let RTCcases = derive_cases_thm (RTCrules,RTCind);;


% --------------------------------------------------------------------- %
% Definition of weak reduction.						%
% --------------------------------------------------------------------- %

new_special_symbol `--->`;;
let reduce = new_infix_definition(`reduce`, "(--->) = RTC (-1->)");;


% ===================================================================== %
% Theorem : -1-> does not have the Church-Rosser property. 		%
%									%
% We wish to prove that weak reduction is Church-Rosser.  If we could 	%
% prove that the one-step contraction -1-> has this property, then we	%
% could also show that reduction does, since taking the reflexive-	%
% transitive closure of a relation preserves the Church-Rosser theorem. %
% Unfortunately, however, -1-> is not Church- Rosser, as the following	%
% counterexample shows.	  						%
%									%
% The counter example is ki(ii) where i = skk. We have that:		%
%									%
%             ki(ii)							%
%              /  \							%
%             /    \							%
%            /      \							%
%           i    ki(ki)(ki)						%
%                   /							%
%                  /							%
%                 /							%
%                i							%
%									%
% But i doesn't contract to i (or indeed to any other term).		%
% ===================================================================== %

% --------------------------------------------------------------------- %
% We first define i to be skk.						%
% --------------------------------------------------------------------- %

let iDEF = new_definition (`iDEF`, "i = (s ' k) ' k");;

% --------------------------------------------------------------------- %
% Given the tactics defined above for each rule, it is straightforward 	%
% to construct a tactic for automatically checking an assertion that	%
% one term contracts to another.  The tactic just does a search for a   %
% proof using the rules for -1->.					%
% --------------------------------------------------------------------- %

letrec CONT_TAC g =
   FIRST [Cs_TAC;
          Ck_TAC;
          LCap_TAC THEN CONT_TAC;
          RCap_TAC THEN CONT_TAC] g ? 
   failwith `CONT_TAC`;;


% --------------------------------------------------------------------- %
% We can now use this tactic to show the following lemmas:		%
%									%
%    1) ki(ii) -1-> i 							%
%    2) ki(ii) -1-> ki((ki)(ki))					%
%    3) ki((ki)(ki)) -1-> i						%
% --------------------------------------------------------------------- %

let lemma1 =
    PROVE
    ("((k ' i) ' (i ' i)) -1-> i",
     CONT_TAC);;

let lemma2 =
    PROVE
    ("((k ' i) ' (i ' i)) -1-> (k ' i) ' ((k ' i) ' (k ' i))",
     SUBST1_TAC iDEF THEN CONT_TAC);;

let lemma3 =
    PROVE
    ("((k ' i) ' ((k ' i) ' (k ' i))) -1-> i",
     SUBST1_TAC iDEF THEN CONT_TAC);;

% --------------------------------------------------------------------- %
% For the proof that ~?U. i -1-> U, we construct some infrastructure 	%
% for a general way of dealing with contractability assertions.  The    %
% core of this consists of a tactic that rewrites assertions of the     %
% form "U -1-> V" with the cases theorem for -1-> :			%
% 									%
%   |- !U V.								%
%       U -1-> V =							%
%       (?y. U = (k ' V) ' y) \/					%
%       (?x y z. (U = ((s ' x) ' y) ' z) /\ (V = (x ' z) ' (y ' z))) \/ %
%       (?x y z. (U = x ' z) /\ (V = y ' z) /\ x -1-> y) \/		%
%       (?x y z. (U = z ' x) /\ (V = z ' y) /\ x -1-> y)		%
%									%
% The full method is as follows:					%
%									%
%   1) rewrite just once using the cases theorem			%
%									%
%        PURE_ONCE_REWRITE_TAC [Ccases]					%
%									%
%   2) simplify any equations between cl-terms that arise from step	%
%      1 by using distinctness and injectivity of application.  Also 	%
%      normalize conjunctions and disjunctions.				%
%									%
%        REWRITE_TAC [distinct;ap11;GSYM CONJ_ASSOC; LEFT_AND_OVER_OR]  %
%									%
%   3) move any buried existential quantifiers outwards through 	%
%      conjunctions and inwards through disjunctions.			%
%									%
%        let outc = LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV  %
%        CONV_TAC (REDEPTH_CONV outc) THEN				%
%        CONV_TAC (REDEPTH_CONV EXISTS_OR_CONV) 			%
%									%
%   4) eliminate redundant equations using REDUCE from ind_defs		%
%									%
%        CONV_TAC (ONCE_DEPTH_CONV REDUCE)				%
%									%
% The overall effect is one step of expansion with the cases theorem,	%
% followed by a renormalization step.  Repeat as often as needed, but   %
% note that REPEAT may loop.  Could guard step 1 with a stopping	%
% condition if necessary.  Note that the normal form is a disjunction   %
% of existentially-quantified conjunctions.				%
% --------------------------------------------------------------------- %

let EXPAND_CASES_TAC =
    let outc = LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV in
    PURE_ONCE_REWRITE_TAC [Ccases] THEN
    REWRITE_TAC [distinct;ap11;GSYM CONJ_ASSOC; LEFT_AND_OVER_OR] THEN
    CONV_TAC (REDEPTH_CONV outc) THEN
    CONV_TAC (REDEPTH_CONV EXISTS_OR_CONV) THEN
    CONV_TAC (ONCE_DEPTH_CONV REDUCE);;

% --------------------------------------------------------------------- %
% We can now use this tactic to prove that i doesn't contract to any 	%
% term of combinatory logic.  Note that since the transition in fact	%
% does NOT hold, step 2 of EXPAND_CASES_TAC eventually solves the goal. %
% Hence we may use REPEAT here.						%
% --------------------------------------------------------------------- %

let lemma4 =
    PROVE
    ("~?U. i -1-> U",
     SUBST_TAC [iDEF] THEN REPEAT EXPAND_CASES_TAC);;


% --------------------------------------------------------------------- %
% We now have our counterexample to show that -1-> does not have the	%
% Church-Rosser property.  We first define an abbreviation for the 	%
% assertion that a relation R has this property.			%
% --------------------------------------------------------------------- %

let CR =
    new_definition
    (`CR`,
      "CR (R: * -> * -> bool) =
       !a b. R a b ==> !c. R a c ==> ?d. R b d /\ R c d");;

% --------------------------------------------------------------------- %
% Use the counterexample to show that -1-> is not Church-Rosser.	%
% The conversion NOT_CONV moves negations inwards through quantifiers,	%
% applies Demorgan's laws where ever possible, and simplifies ~~P to P.	%
% --------------------------------------------------------------------- %

let NOT_CONV =
    let ths = CONJUNCTS(SPEC_ALL DE_MORGAN_THM) in
    let rcnv = map REWR_CONV (CONJUNCT1 NOT_CLAUSES . ths) in
        REDEPTH_CONV (FIRST_CONV ([NOT_FORALL_CONV; NOT_EXISTS_CONV] @ rcnv));;

let NOT_C_CR =
    prove_thm
    (`NOT_C_CR`,
     "~CR($-1->)",
     PURE_REWRITE_TAC [CR;IMP_DISJ_THM] THEN
     CONV_TAC NOT_CONV THEN
     EXISTS_TAC "(k ' i) ' (i ' i)" THEN
     EXISTS_TAC "(k ' i) ' ((k ' i) ' (k ' i))" THEN
     REWRITE_TAC [lemma2] THEN
     EXISTS_TAC "i" THEN
     REWRITE_TAC [lemma1;CONV_RULE NOT_EXISTS_CONV lemma4]);;

% ===================================================================== %
% Inductive definition of parallel reduction of CL terms		%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Definition of one-step parallel contraction.				%
% 									%
% This one-step contraction relation has the Church-Rosser property,    %
% and its transitive closure (parallel reduction) therefore also does.  %
% Moreover, parallel reduction and ---> are the same relation, so we can%
% prove the Church-Rosser theorem for ---> by proving it for parallel	%
% reduction.  The inductive definition of one-step parallel contraction %
% is given below.  The allow any number of redexes among the subterms   %
% of a term to be contracted in a single step.				%
% --------------------------------------------------------------------- %

new_special_symbol `=1=>`;;

let (PCrules,PCind) =
    let PCTR = "=1=>:cl->cl->bool" in
    new_inductive_definition true `pcontract` 

    ("^PCTR U V", [])

    [ [
      % ------------------------------------------------------ % ],
                             "^PCTR x x"                       ;

      [                                                               
      % ------------------------------------------------------ % ],
                       "^PCTR ((k ' x) ' y) x"                 ;

      [                                                               
      %------------------------------------------------------- % ],
           "^PCTR (((s ' x) ' y) ' z)  ((x ' z) ' (y ' z))"    ;


      [              "^PCTR w x";     "^PCTR y z"                       
      %------------------------------------------------------- % ],
                       "^PCTR (w ' y) (x ' z)"                   ];;



% --------------------------------------------------------------------- %
% Stronger form of rule induction.					%
% --------------------------------------------------------------------- %

let PCsind = derive_strong_induction (PCrules,PCind);;


% --------------------------------------------------------------------- %
% Standard rule induction tactic for =1=>.				%
% --------------------------------------------------------------------- %

let PC_INDUCT_TAC =
    RULE_INDUCT_THEN PCind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Case analysis theorem for =1=>.					%
% --------------------------------------------------------------------- %

let PCcases = derive_cases_thm (PCrules,PCind);;


% --------------------------------------------------------------------- %
% Tactics for each of the parallel contraction rules.			%
% --------------------------------------------------------------------- %
let [PC_REFL_TAC;PCk_TAC;PCs_TAC;PCap_TAC] = map RULE_TAC PCrules;;

% --------------------------------------------------------------------- %
% Given the tactics defined above for each rule, it is straightforward 	%
% to construct a tactic for automatically checking an assertion that	%
% one term contracts to another.  The tactic just does a search for a   %
% proof using the rules for =1=>.					%
% --------------------------------------------------------------------- %

letrec PC_TAC g =
   FIRST [PC_REFL_TAC;
          PCk_TAC;
          PCs_TAC;
          PCap_TAC THEN PC_TAC] g ? ALL_TAC g;;


% --------------------------------------------------------------------- %
% The weak reduction relation on terms in combinatory logic is just the %
% transitive closure of =1=>.  Transitive is defined inductively as	%
% follows.  Note that the transitivity rule formulated as:		%
%									%
%            TC R x z 							%
%   R1:   -------------- R z y						%
%            TC R x y							%
%									%
% and not as								%
%									%
%          TC R x z   TC R z y						%
%   R2:  ------------------------					%
%              TC R x z							%
%									%
% This is because rule R1 gives a linear structure to rule inductions   %
% for transitive closure, which make the details of these proofs easier %
% to handle than the tree-shaped structure induced by rule R2.		%
%									%
% Once transitive closure has been defined, the parallel reduction 	%
% relation ===> can just be defined to be TC =1=>.			%
% --------------------------------------------------------------------- %

let (TCrules,TCind) =
    let TC = "TC:(*->*->bool)->*->*->bool" in
    new_inductive_definition false `TC` 

    ("^TC R x y", ["R:*->*->bool"])

    [ [				       
      % ------------------------------ %  "R (x:*) (y:*):bool"],
                "^TC R x y"	       ;

      [         "^TC R x z"	       
      %------------------------------- % ;  "R (z:*) (y:*):bool"],
                "^TC R x y"	       ];;


% --------------------------------------------------------------------- %
% Standard rule induction tactic for TC.				%
% --------------------------------------------------------------------- %

let TC_INDUCT_TAC =
    RULE_INDUCT_THEN TCind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;;


% --------------------------------------------------------------------- %
% Tactics for the TC rules.						%
% --------------------------------------------------------------------- %

let [TC_IN_TAC;TC_TRANS_TAC] = map RULE_TAC TCrules;;


% --------------------------------------------------------------------- %
% Strong form of rule induction for TC.					%
% --------------------------------------------------------------------- %

let TCsind = derive_strong_induction (TCrules,TCind);;


% --------------------------------------------------------------------- %
% Now, define parallel reduction for terms of CL.			%
% --------------------------------------------------------------------- %

new_special_symbol `===>`;;
let preduce = new_infix_definition(`preduce`, "(===>) = TC (=1=>)");;

% ===================================================================== %
% Theorem: ===> and ---> are the same relation.				%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The following sequence of lemmas show that the rules for the single	%
% step contraction -1-> also hold its reflexive-transitive closure, 	%
% namely the relation --->.  The proofs are trivial for the k and s	%
% axioms. For the two application rules, we need a simple induction	%
% on the rules defining RTC.  						%
% --------------------------------------------------------------------- %

let Rk_THM =
    PROVE
    ("!a b. ((k ' a) ' b) ---> a",
     SUBST1_TAC reduce THEN
     RTC_IN_TAC THEN Ck_TAC);;

let Rs_THM =
    PROVE
    ("!a b c. (((s ' a) ' b) ' c) ---> ((a ' c) ' (b ' c))",
     SUBST1_TAC reduce THEN
     RTC_IN_TAC THEN Cs_TAC);;

let LRap_THM =
    PROVE
    ("!a b. a ---> b ==> !c. (a ' c) ---> (b ' c)",
     SUBST1_TAC reduce THEN
     RTC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [RTC_IN_TAC THEN LCap_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      RTC_REFL_TAC;
      RTC_TRANS_TAC THEN EXISTS_TAC "z ' c" THEN ASM_REWRITE_TAC[]]);;

let RRap_THM =
    PROVE
    ("!a b. a ---> b ==> !c. (c ' a) ---> (c ' b)",
     SUBST1_TAC reduce THEN
     RTC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [RTC_IN_TAC THEN RCap_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      RTC_REFL_TAC;
      RTC_TRANS_TAC THEN EXISTS_TAC "c ' z" THEN ASM_REWRITE_TAC[]]);;

% --------------------------------------------------------------------- %
% To avoid having to expand ---> into RTC -1->, we also prove that the  %
% rules for reflexive-transitive closure hold of --->.  The proofs are  %
% completely trivial.							%
% --------------------------------------------------------------------- %

let CONT_IN_RED =
    PROVE
    ("!U V. U -1-> V ==> U ---> V",
     REWRITE_TAC (reduce . RTCrules));;


let RED_REFL =
    PROVE
    ("!U. U ---> U",
     REWRITE_TAC (reduce . RTCrules));;


let RED_TRANS =
    PROVE
    ("!U V. (?W. U ---> W /\ W ---> V) ==> (U ---> V)",
     REWRITE_TAC (reduce . RTCrules));;


% --------------------------------------------------------------------- %
% We can now use these lemmas to prove that the relation ===> is a 	%
% subset of --->. The proof has two parts. The first is to show that if %
% there is a one-step parallel reduction U =1=> V, then U ---> V. Given %
% the lemmas proved above, it is easy to show that ---> is closed under %
% the rules that define =1=>, and hence by rule induction that =1=> is	%
% a subset of --->.							%
% --------------------------------------------------------------------- %


let PCONT_SUB_RED =
    PROVE
    ("!U V. U =1=> V ==> U ---> V",
     PC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_ACCEPT_TAC RED_REFL;
      MATCH_ACCEPT_TAC Rk_THM;
      MATCH_ACCEPT_TAC Rs_THM;
      MATCH_MP_TAC RED_TRANS THEN
      EXISTS_TAC "(x ' y)" THEN CONJ_TAC THENL
      [IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) LRap_THM;
       IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) RRap_THM]]);;

% --------------------------------------------------------------------- %
% Given this result, one can then prove that ===> is a subset of ---> 	%
% by rule induction.  The previous lemma just states that the relation  %
% ---> is closed under the inclusion rule for TC =1=>. And one can also %
% prove that ---> is closed under the transitivity rule, since we have	%
% already above proved that ---> is transitive.  Hence, by rule 	%
% induction of transitive closure, TC =1=> is a subset of --->.		%
% --------------------------------------------------------------------- %

let PRED_SUB_RED =
    PROVE
    ("!U V. (U ===> V) ==> U ---> V",
     SUBST1_TAC preduce THEN
     TC_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     IMP_RES_TAC PCONT_SUB_RED THEN
     IMP_RES_TAC RED_TRANS);;


% --------------------------------------------------------------------- %
% The proof of the converse inclusion, that ---> is a subset of ===>,	%
% is similar.  Again, we begin with a series of lemmas which establish	%
% that the rules defining =1=> hold for its transitive closure ===>.	%
% --------------------------------------------------------------------- %

let PRk_THM =
    PROVE
    ("!a b. ((k ' a) ' b) ===> a",
     SUBST1_TAC preduce THEN
     TC_IN_TAC THEN PC_TAC);;

let PRs_THM =
    PROVE
    ("!a b c. (((s ' a) ' b) ' c) ===> ((a ' c) ' (b ' c))",
     SUBST1_TAC preduce THEN
     TC_IN_TAC THEN PC_TAC);;

% --------------------------------------------------------------------- %
% The application case is slightly trickier than the two analogous 	%
% application theorems in the previous series of lemmas. Because of the %
% way the transitivity rule is formulated, a double rule induction is   %
% needed.								%
% --------------------------------------------------------------------- %

let PRap_THM =
    PROVE
    ("!a b. (a ===> b) ==> !c d. (c ===> d) ==> ((a ' c) ===> (b ' d))",
     SUBST1_TAC preduce THEN
     REPEAT TC_INDUCT_TAC THENL
     [TC_IN_TAC;
      TC_TRANS_TAC THEN EXISTS_TAC "y ' z" THEN CONJ_TAC;
      TC_TRANS_TAC THEN EXISTS_TAC "z ' x'" THEN CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN TC_IN_TAC;ALL_TAC];
      TC_TRANS_TAC THEN EXISTS_TAC "y ' z'" THEN CONJ_TAC] THEN
     PC_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

% --------------------------------------------------------------------- %
% We also need to show that ===> is reflexive and transitive. Note that	%
% in the transitivity case we need a careful formulation of the 	%
% induction hypothesis, because of the way the transitivity rule for TC %
% is stated.  In particular, we induct on b ===> c, rather than on	%
% a ===> b.								%
% --------------------------------------------------------------------- %

let PR_REFL =
    PROVE
    ("!U. U ===> U",
     SUBST1_TAC preduce THEN
     TC_IN_TAC THEN PC_TAC);;

let PR_TRANS = 
    PROVE
    ("!b c. (b ===> c) ==> !a. (a ===> b) ==> (a ===> c)",
     SUBST1_TAC preduce THEN
     TC_INDUCT_TAC THEN REPEAT STRIP_TAC THENL
     [TC_TRANS_TAC THEN EXISTS_TAC "x:cl";
      TC_TRANS_TAC THEN EXISTS_TAC "z:cl" THEN RES_TAC] THEN
     ASM_REWRITE_TAC[]);;


% --------------------------------------------------------------------- %
% We now show by rule induction that -1-> is a subset of ===>. We have	%
% already proved that the s and k rules for -1-> also hold for ===>.    %
% Futhermore, the two application rules for -1-> follow easily for the 	%
% relation ===>, since the more general application rule holds for this %
% relation and since it is reflexive.					%
% --------------------------------------------------------------------- %

let CONT_SUB_PRED =
    PROVE
    ("!U V. U -1-> V ==> U ===> V",
     C_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_ACCEPT_TAC PRk_THM;
      MATCH_ACCEPT_TAC PRs_THM;
      ASSUME_TAC (SPEC "z:cl" PR_REFL) THEN IMP_RES_TAC PRap_THM;
      ASSUME_TAC (SPEC "z:cl" PR_REFL) THEN IMP_RES_TAC PRap_THM]);;

% --------------------------------------------------------------------- %
% That ---> is a subset of ===> now follows by rule induction.  We have %
% shown that ===> contains -1-> and that it is reflexive and transitive.%
% So ===> is closed under the rules for RTC -1->, and hence ---> is a   %
% subset of ===>.							%
% --------------------------------------------------------------------- %

let RED_SUB_PRED =
    PROVE
    ("!U V. U ---> V ==> U ===> V",
     SUBST1_TAC reduce THEN
     RTC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [IMP_RES_TAC CONT_SUB_PRED;
      MATCH_ACCEPT_TAC PR_REFL;
      IMP_RES_TAC PR_TRANS]);;

% --------------------------------------------------------------------- %
% The equality of ---> and ===> follows immediately.			%
% --------------------------------------------------------------------- %

let RED_EQ_PRED =
    prove_thm
    (`RED_EQ_PRED`,
     "!U V. U ---> V = U ===> V",
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [IMP_RES_TAC RED_SUB_PRED; IMP_RES_TAC PRED_SUB_RED]);;

% ===================================================================== %
% Theorem: taking the transitive closure preserves Church-Rosser.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% Lemma: we can fill in any `strip' one transition wide.  That is, if	%
% R has the Church-Rosser rpoperty, then we have that 			%
%									%
%             a                                        a		%
%            / \				      / \		%
%  if       b   \       then there exists d st:      b   \		%
%                \                                    \   \		%
%                 c                                    \   c		%
%							\ /		%
%							 d	        %
%									%
% The choice of formulation for the transitivity rule makes the proof a %
% straightforward rule indction down the a-to-c leg of the rectangle.   %
% --------------------------------------------------------------------- %

let CR_LEMMA =
    prove_thm
    (`CR_LEMMA`,
     "!R:*->*->bool.
       CR R ==> !a c. TC R a c ==> !b. R a b ==> ?d. TC R b d /\ R c d",
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC [CR] THEN STRIP_TAC THEN
     TC_INDUCT_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THENL
     [EXISTS_TAC "d':*" THEN CONJ_TAC THENL
      [TC_IN_TAC THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
      EXISTS_TAC "d'':*" THEN CONJ_TAC THENL
      [TC_TRANS_TAC THEN EXISTS_TAC "d:*" THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM ACCEPT_TAC]]);;


% --------------------------------------------------------------------- %
% With a second rule induction, down the other `leg' of the diamond, we %
% can now prove that taking the transitive closure preserves the Church %
% Rosser property. The theorem is that if R is Church-Rosser, then:	%
%									%
%             a                                        a		%
%            / \				      / \		%
%  if       /   \       then there exists d st:      /   \		%
%          /     \                                  /     \		%
%         b       c                                b       c		%
%						    \     /		%
%						     \   /		%
%						      \ /		%
%						       d		%
%									%
% The proof is by rule induction on TC R a b.				%
% --------------------------------------------------------------------- %

let TC_PRESERVES_CR_THM = 
    PROVE
    ("!R:*->*->bool.
        CR R ==> 
           !a c. TC R a c ==> !b. TC R a b ==> ?d. TC R b d /\ TC R c d",
     GEN_TAC THEN STRIP_TAC THEN TC_INDUCT_TAC THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC CR_LEMMA THEN
      IMP_RES_TAC (el 1 TCrules) THEN
      EXISTS_TAC "d:*" THEN 
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      RES_THEN (\th. STRIP_ASSUME_TAC th THEN ASSUME_TAC th) THEN
      IMP_RES_TAC CR_LEMMA THEN
      EXISTS_TAC "d':*" THEN CONJ_TAC THENL
      [TC_TRANS_TAC THEN EXISTS_TAC "d:*" THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       FIRST_ASSUM ACCEPT_TAC]]);;

let TC_PRESERVES_CR =
    prove_thm
    (`TC_PRESERVES_CR`,
     "!R:*->*->bool. CR R ==> CR (TC R)",
     REPEAT STRIP_TAC THEN
     PURE_ONCE_REWRITE_TAC [CR] THEN
     PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN
     MATCH_MP_TAC TC_PRESERVES_CR_THM THEN
     FIRST_ASSUM ACCEPT_TAC);;

% ===================================================================== %
% Theorem: the parallel contraction relation =1=> is Church-Rosser.	%
% ===================================================================== %

% --------------------------------------------------------------------- %
% We define a conversion EXPAND_PC_CASES_CONV for expanding with the 	%
% cases theorem for =1=>.  This is analogous to EXPAND_CASES_TAC above, %
% except that it's a conversion, and it is designed to fail for terms   %
% that do not contain at least one subterm "U =1=> V" where U and V are %
% not both variables.  This condition means you can repeat (REPEATC) 	%
% this conversion, and the resulting conversion will always halt.	%
% --------------------------------------------------------------------- %

let EXPAND_PC_CASES_CONV =
    let guard tm = 
        let _,[x;y] = strip_comb tm in
        if (is_var x & is_var y) then fail else REWR_CONV PCcases tm in
    let outc = LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV in
    CHANGED_CONV (ONCE_DEPTH_CONV guard) THENC
    REWRITE_CONV [distinct;ap11;GSYM CONJ_ASSOC; 
                  LEFT_AND_OVER_OR;RIGHT_AND_OVER_OR] THENC
    REDEPTH_CONV outc THENC
    REDEPTH_CONV EXISTS_OR_CONV THENC
    ONCE_DEPTH_CONV REDUCE;;

% --------------------------------------------------------------------- %
% Now for the main theorem. The proof proceeds by strong rule induction %
% on the relation =1=>.  The four cases in the induction are:		%
%									%
%  1) "(w ' y) =1=> c ==> (?d. (x ' z) =1=> d /\ c =1=> d)"		%
%     [ "w =1=> x" ]							%
%     [ "!c. w =1=> c ==> (?d. x =1=> d /\ c =1=> d)" ]			%
%     [ "y =1=> z" ]							%
%     [ "!c. y =1=> c ==> (?d. z =1=> d /\ c =1=> d)" ]			%
%									%
%  2) "(((s ' x) ' y) ' z) =1=> c ==>					%
%      (?d. ((x ' z) ' (y ' z)) =1=> d /\ c =1=> d)"			%
%									%
%  3) "((k ' x) ' y) =1=> c ==> (?d. x =1=> d /\ c =1=> d)"		%
%									%
%  4) "x =1=> c ==> (?d. x =1=> d /\ c =1=> d)"				%
%                                                                       %
% Cases 2,3 and 4 are solved by case analysis (using PCcases) on the 	%
% antecedent, followed by straightforward search for the proof of the	%
% consequent using the tactics for =1=>.  Case 1 is solved also by	%
% first analysing the antecedent by PCcases followed by search for the  %
% proof.  In two sub-cases, however, one needs to do a case analysis	%
% on the strong induction assumption.  See the proof below for details.	%
% --------------------------------------------------------------------- %

let CR_THEOREM =
    TAC_PROOF(([], "CR $=1=>"),
    let ecnv = REPEATC EXPAND_PC_CASES_CONV in
    let ttac th g = SUBST_ALL_TAC th g ? ASSUME_TAC th g in
    let mkcases = REPEAT_TCL STRIP_THM_THEN ttac in
    let STRIP_PC_TAC =
        REPEAT STRIP_TAC THEN PC_TAC THEN
        TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) in
    PURE_ONCE_REWRITE_TAC [CR] THEN
    RULE_INDUCT_THEN PCsind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
    REPEAT GEN_TAC THENL
    [DISCH_TAC THEN EXISTS_TAC "c:cl" THEN STRIP_PC_TAC;

     DISCH_THEN (mkcases o CONV_RULE ecnv) THENL
     map EXISTS_TAC ["x:cl";"c:cl";"x:cl";"z':cl"] THEN STRIP_PC_TAC;

     DISCH_THEN (mkcases o CONV_RULE ecnv) THENL     
     map EXISTS_TAC ["((x ' z) ' (y ' z))";
		     "((x ' z) ' (y ' z))";
		     "((x ' z') ' (y ' z'))";
		     "((x ' z') ' (z'' ' z'))";
		     "((z''' ' z') ' (z'' ' z'))"] THEN STRIP_PC_TAC;

     DISCH_THEN (mkcases o CONV_RULE ecnv) THENL
     [EXISTS_TAC "x ' z" THEN STRIP_PC_TAC;
      let cth = UNDISCH (fst(EQ_IMP_RULE (ecnv "(k ' c) =1=> x"))) in
      DISJ_CASES_THEN (REPEAT_TCL STRIP_THM_THEN ttac) cth THENL
      map EXISTS_TAC ["c:cl";"z':cl"] THEN STRIP_PC_TAC;
      let cth = UNDISCH (fst(EQ_IMP_RULE (ecnv "((s ' x') ' y') =1=> x"))) in
      DISJ_CASES_THEN (REPEAT_TCL STRIP_THM_THEN ttac) cth THENL
      map EXISTS_TAC ["((x' ' z) ' (y' ' z))";
                      "((x' ' z) ' (z' ' z))";
                      "((z'' ' z) ' (z' ' z))"] THEN STRIP_PC_TAC;
      RES_TAC THEN EXISTS_TAC "d'' ' d" THEN STRIP_PC_TAC]]);;

% --------------------------------------------------------------------- %
% We now do the following trivial proof.				%
% --------------------------------------------------------------------- %

let preduce_HAS_CR =
    prove_thm
    (`preduce_HAS_CR`,
     "CR(===>)",
     REWRITE_TAC [preduce] THEN
     MATCH_MP_TAC TC_PRESERVES_CR THEN
     ACCEPT_TAC CR_THEOREM);;

% --------------------------------------------------------------------- %
% Q.E.D. 								%
% --------------------------------------------------------------------- %

let CHURCH_ROSSER = 
    prove_thm
    (`CHURCH_ROSSER`,
     "CR $--->",
     let th = EXT (GEN "U:cl" (EXT (SPEC "U:cl" RED_EQ_PRED))) in
     REWRITE_TAC [th;preduce_HAS_CR]);;


% --------------------------------------------------------------------- %
% End of example.							%
% --------------------------------------------------------------------- %

close_theory();;
quit();;
