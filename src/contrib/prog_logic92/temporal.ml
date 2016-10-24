%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        | 
|                                                              |
| temporal.ml                                                  |
|                                                              |
| DESCRIPTION:	                                               |
|                                                              |
| Temporal-style specifications                                |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

new_theory `temporal`;;

load_library `taut`;;

loadf `mytactics`;;

loadf `l_arith_hack`;;
loadf `l_lnum`;;
loadf `l_exseq`;;
loadf `l_sem`;;
loadf `l_hoare`;;

%
| The assertion language 
%

let wff = define_type `wff`
	`wff =	  START
		| TFINAL
		| AFINAL
		| ASSERT (state->bool)
		| CONJ wff wff
		| DISJ wff wff
		| EQ wff wff
		| NEG wff
		| IMP wff wff
		| NEXT wff
		| ALL wff
		| SOME wff`;;


%
| Make certain constructors infixes as well
%

let imp = new_infix_definition
(	`imp`,
	"!fmla1 fmla2. imp fmla1 fmla2 = IMP fmla1 fmla2"
);;

let conj = new_infix_definition
(	`conj`,
	"!fmla1 fmla2. conj fmla1 fmla2 = CONJ fmla1 fmla2"
);;

let disj = new_infix_definition
(	`disj`,
	"!fmla1 fmla2. disj fmla1 fmla2 = DISJ fmla1 fmla2"
);;

let eq = new_infix_definition
(	`eq`,
	"!fmla1 fmla2. eq fmla1 fmla2 = EQ fmla1 fmla2"
);;

set_interface_map 
	[`DISJ`,`disj`;`disj`,`DISJ`;
	 `CONJ`,`conj`;`conj`,`CONJ`;
	 `EQ`,`eq`;`eq`,`EQ`;
	 `IMP`,`imp`;`imp`,`IMP`];;

%
| Satisfaction of an assertion by an exseq at some point
%

% Defined in parts to get around mut. recursive types problem %

let holds = new_recursive_definition false wff `holds`
	"(holds e i START = (i = 0)) /\
	 (holds e i TFINAL = TERM e /\ (WHOLE i = PR(length e))) /\
	 (holds e i AFINAL = ABORT e /\ (WHOLE i = PR(length e))) /\
	 (holds e i (ASSERT P) = 
		((WHOLE i) <+ length e 
			=> P(elt(WHOLE i) e) 
			|  P(last e))) /\
	 (holds e i (NEG fmla) = 
		~holds e i fmla) /\
	 (holds e i (fmla1 imp fmla2) = 
		holds e i fmla1 ==> 
		holds e i fmla2) /\
	 (holds e i (fmla1 conj fmla2) = 
		holds e i fmla1 /\ 
		holds e i fmla2) /\
	 (holds e i (fmla1 disj fmla2) = 
		holds e i fmla1 \/ 
		holds e i fmla2) /\
 	 (holds e i (fmla1 eq fmla2) = 
		(holds e i fmla1 = 
		 holds e i fmla2)) /\
	 (holds e i(NEXT fmla) = holds e(SUC i)fmla)  /\
	 (holds e i (ALL fmla) = 
		!j. (i <= j) ==> holds e j fmla) /\
	 (holds e i (SOME fmla) = 
		?j.  (i <= j) /\ holds e j fmla)";;

%-
| Satisfaction 
-%
 
new_special_symbol `|=`;;

let sat = new_definition
(	`sat`,
	"!fmla:wff. |= fmla = !e i. holds e i fmla"
);;

%-
 Rule for lifting boolean tautologies. 
 Only works on theorems about booleans and polymorphics

eg.

CONJ_ASSOC;;
|- !t1 t2 t3. t1 /\ t2 /\ t3 = (t1 /\ t2) /\ t3

LIFT CONJ_ASSOC;;
|- !t1 t2 t3.
    |= ((t1 conj (t2 conj t3)) eq ((t1 conj t2) conj t3))

-%

let LIFT th =
	let varlist,tm = strip_forall(concl th) in
	let fn = \var.
		let varname,vartype = dest_var var in
			mk_comb("holds e i",mk_var(varname,":wff"))
			   in
	let th' = GENL["e:exseq";"i:num"]
		  (REWRITE_RULE[SYM_th holds]
			(ISPECL (map fn varlist) th)) in
	GEN_ALL(REWRITE_RULE[SYM_th sat]th');;

%-
| Derivation of axioms 
-%

let ALL_ALL = prove_thm
(	`ALL_ALL`,
	"!fmla. |= ((ALL(ALL fmla)) eq (ALL fmla))",
	REWRITE_TAC[sat;holds]
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[RES_TAC
		 THEN HALF_ASM_REWRITE_TAC
			[lnum_less_eq_reduce
			;LESS_EQ_REFL
			]
		;IMP_RES_TAC LESS_EQ_TRANS
		 THEN RES_TAC
		]
);;

let SOME_SOME = prove_thm
(	`SOME_SOME`,
	"!fmla. |= ((SOME(SOME fmla)) eq (SOME fmla))",
	REWRITE_TAC[sat;holds]
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[EXISTS_TAC "j':num"
		 THEN IMP_RES_TAC LESS_EQ_TRANS
		 THEN ASM_REWRITE_TAC[]
		;EXISTS_TAC "j:num"
		 THEN ASM_REWRITE_TAC[]
		 THEN EXISTS_TAC "j:num"
		 THEN ASM_REWRITE_TAC[LESS_EQ_REFL]
		]
);;

let ALL_once = prove_thm
(	`ALL_once`,
	"!fmla. |= ((ALL fmla) imp fmla)",
	REWRITE_TAC[sat;holds]
	THEN REPEAT STRIP_TAC
	THEN HALF_ASM_REWRITE_TAC[LESS_EQ_REFL]
);;

let NEXT_NEG = prove_thm
(	`NEXT_NEG`,
	"!fmla. |= ((NEXT(NEG fmla)) eq (NEG(NEXT fmla)))",
	REWRITE_TAC[sat;holds]
	THEN TAUT_TAC
);;

let ALL_over_imp = prove_thm
(	`ALL_over_imp`,
	"!fmla1 fmla2. 
	  |= ((ALL(fmla1 imp fmla2) imp 
		((ALL fmla1) imp (ALL fmla2))))",
	REWRITE_TAC[sat;holds]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
);;

let NEXT_over_imp = prove_thm
(	`NEXT_over_imp`,
	"!fmla1 fmla2. 
	  |= ((NEXT(fmla1 imp fmla2) imp 
		((NEXT fmla1) imp (NEXT fmla2))))",
	REWRITE_TAC[sat;holds]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[]
);;

let ALL_NEXT = prove_thm
(	`ALL_NEXT`,
	"!fmla. |= ((ALL fmla) imp (NEXT fmla))",
	REWRITE_TAC[sat;holds]
	THEN REPEAT STRIP_TAC
	THEN HALF_ASM_REWRITE_TAC[LESS_EQ_SUC_REFL]
);;

let lemma = ONCE_REWRITE_RULE[holds](REWRITE_RULE[sat]ALL_ALL);;

let ALL_NEXT_ALL = prove_thm
(	`ALL_NEXT_ALL`,
	"!fmla. 
	  |= ((ALL fmla) imp (NEXT(ALL fmla)))",
	ONCE_REWRITE_TAC[sat]
	THEN ONCE_REWRITE_TAC[holds]
	THEN ONCE_REWRITE_TAC
		[SYM_th lemma]
	THEN ONCE_REWRITE_TAC[SYM_th holds]
	THEN REPEAT STRIP_TAC
	THEN HALF_ASM_REWRITE_TAC[REWRITE_RULE[sat]ALL_NEXT]
);;

let ALL_imp_NEXT_ALL = prove_thm
(	`ALL_imp_NEXT_ALL`,
	"!fmla. |= ((ALL(fmla imp (NEXT fmla))) imp (fmla imp (ALL fmla)))",
	REWRITE_TAC[sat;holds]
	THEN REPEAT GEN_TAC 
	THEN REPEAT DISCH_TAC
	THEN INDUCT_TAC
	THENL	[REWRITE_TAC[LESS_EQ_0]
		 THEN DISCH_THEN (SUBST1_TAC o SYM)
		 THEN ASM_REWRITE_TAC[]
		;DISCH_TAC
		 THEN FIRST_ASSUM(DISJ_CASES_TAC o (REWRITE_RULE[LESS_OR_EQ]))
		 THENL	[IMP_RES_TAC(SYM_th LESS_EQ_LESS_SUC)
			 THEN RULE_ASSUM_TAC de_imp
		 	 THEN HALF_ASM_REWRITE_TAC[]
			;ASM_RULE_REWRITE_TAC SYM_th []
			]
		]
);; 

let lemma = TAUT_PROVE "~(p==>q)=(p /\ ~q)";;

let SOME_as_ALL = prove_thm
(	`SOME_as_ALL`,
	"!fmla. |= ((SOME fmla) eq (NEG(ALL(NEG fmla))))",
	REWRITE_TAC[sat;holds]
	THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	THEN REWRITE_TAC[lemma]
);;

%-
| Derive standard propositional axioms
-%

let prop_ax1 = LIFT(TAUT_PROVE "!p q. p==>(q==>p)");;

let prop_ax2 = LIFT(TAUT_PROVE "!p q r. (p==>(q==>r))==>((p==>q)==>(p==>r))");;

let prop_ax3 = LIFT(TAUT_PROVE "!p q. (~q==>~p)==>((~q==>p)==>q)");;

%-
| Rules follow
-%

%-
| Modus Ponens
-%

let modus_ponens = prove_thm
(	`modus_ponens`,
	"!f1 f2. |= f1 /\ |=(f1 imp f2) ==> |= f2",
	REWRITE_TAC[sat;holds]
	THEN REPEAT STRIP_TAC
	THEN HALF_ASM_REWRITE_TAC[]
);;

%-
| Generalization
-%

let generalize = prove_thm
(	`generalize`,
	"!f. |= f ==> |= (ALL f)",
	REWRITE_TAC[sat;holds]
	THEN REPEAT STRIP_TAC
	THEN HALF_ASM_REWRITE_TAC[]
);;

%-
| Satisfaction of an assertion by a command
-%

new_special_symbol `|==`;;

let csat = new_infix_definition
(	`csat`,
	"!c f. $|== c f = !e i. c e ==> holds e i f"
);;

let sat_csat = prove_thm
(	`sat_csat`,
	"!f. |= f ==> !c. c |== f",
	REWRITE_TAC[sat;csat]
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
);;

%-
| Derive Hoare specs as special cases
-%

let spec_as_temp = prove_thm
(	`spec_as_temp`,
	"!c P Q. 
	  spec P c Q = 
	  c |== ((ASSERT P) conj START) imp (ALL(TFINAL imp (ASSERT Q)))",
	REWRITE_TAC[spec;csat;holds]
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC	
	THENL	[ASM_REWRITE_TAC[SYM_th last]
		 THEN COND_CASES_TAC
		 THEN RULE_ASSUM_TAC de_imp
		 THEN HALF_ASM_REWRITE_TAC[]
		 THEN REWRITE_ASM[zero_less_length]
		 THEN ASM_REWRITE_TAC[first]
		;REPLACE_FIRST_ASSUM
			(ASSUME_TAC o (SPECL["e:exseq";"0:num"]))
		 THEN REWRITE_ASM[zero_less_length;first]
		 THEN REWRITE_ASM[TERM]
		 THEN IMP_RES_TAC is_WHOLE_choose
		 THEN ASSUME_TAC(SPEC "e:exseq" zero_less_length)
		 THEN REWRITE_ASM[last;PR]
		 THEN REPLACE_FIRST_ASSUM
			(ASSUME_TAC o (SPEC "n-1"))
		 THEN REWRITE_ASM[lnum_less_reduce]
		 THEN IMP_RES_TAC LESS_LESS_EQ_SUB1
		 THEN IMP_RES_TAC (REWRITE_RULE[PRE_SUB1]PRE_K_K)
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[last;PR]
		]
);;

let total_spec_as_temp = prove_thm
(	`total_spec_as_temp`,
	"!c P Q. 
	  total_spec P c Q = 
	  c |== ((ASSERT P) conj START) imp (SOME(TFINAL conj (ASSERT Q)))",
	REWRITE_TAC[total_spec_alt;csat;holds]
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT (GEN_TAC ORELSE (DISCH_THEN STRIP_ASSUME_TAC))	
	THENL	[REWRITE_ASM[zero_less_length]
		 THEN RES_TAC
		 THEN REWRITE_ASM[first;TERM]
		 THEN ASM_REWRITE_TAC[TERM]
		 THEN IMP_RES_TAC is_WHOLE_choose
		 THEN EXISTS_TAC "n-1"
		 THEN REWRITE_ASM[last;PR]
		 THEN ASM_REWRITE_TAC[PR]
		 THEN ASSUME_TAC(SPEC "e:exseq" zero_less_length)
		 THEN REWRITE_ASM[lnum_less_reduce]
 		 THEN IMP_RES_TAC LESS_LESS_EQ_SUB1
		 THEN COND_CASES_TAC
		 THEN ASM_REWRITE_TAC[]
		;REPLACE_FIRST_ASSUM
			(ASSUME_TAC o (SPECL["e:exseq";"0:num"]))
		 THEN REWRITE_ASM[zero_less_length;first]
		 THEN RES_TAC
		 THEN IMP_RES_TAC length_PR_less
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[last]
		]
);;

close_theory();;
