
%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        | 
|                                                              |
| sem.ml                                                       |
|                                                              |
| DESCRIPTION:	                                               |
|                                                              |
| Defines the semantics of programming constructs              |
| using execution sequences.  				       |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

new_theory `sem`;;
loadf `mytactics`;;

loadf `l_arith_hack`;;
loadf `l_cpo`;;
loadf `l_lnum`;;
loadf `l_exseq`;;
loadf `l_pred`;;

%
| Commands are sets of exseqs, 
| represented by their membership predicate 
| Note that partial commands are allowed
%

new_type_abbrev(`command`, ":exseq -> bool");; 

%
| Define a function that returns the domain (guard) of a commmand
%

let grd = new_definition (
	`grd`,
	"!c:command.!s:state. grd c s = 
		?e. c e /\ (first e = s)"
);; 

let total = new_definition (
	`total`,
	"!c:command. total c = (grd c = true)"
);;
 
%
|  A deterministic command contains only one program sequence
|  starting at a given state. 
%

let det = new_definition (
	`det`,
	"!c:command. 
	 det c = 
		!p1 p2. 
		(c p1) ==> (c p2) ==> 
		(first p2 = first p1) ==> (p1 = p2)"
);;

%
| Atomic commands
%

let skip = new_definition (
	`skip`,
	"skip p = ?s s. p= pair(s, s)"
);; 

let skip_grd = prove_thm 
(	`skip_grd`,
	"grd skip = true",
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC[skip;grd;ALL]
	THEN GEN_TAC
	THEN EXISTS_TAC "pair(f,f)"
	THEN REWRITE_TAC[pair_first]
	THEN EXISTS_TAC "f:state"
	THEN REFL_TAC
);;

let empty = new_definition (
	`empty`,
	"!e:exseq. empty e = F"
);; 

let empty_grd = prove_thm (
	`empty_grd`,
	"grd empty = false",
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC [grd;NONE;empty]
);;

let abort = new_definition (
	`abort`,
	"!e:exseq. abort e = ?s:state. e = abort_pair(s, s)"
);; 

let abort_grd = prove_thm
(	`abort_grd`,
	"grd abort = true",
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC [grd;ALL;abort]
	THEN GEN_TAC
	THEN EXISTS_TAC "abort_pair(f,f)"
	THEN REWRITE_TAC[abort_pair_first]
	THEN EXISTS_TAC "f:state"
	THEN REFL_TAC
);;

let havoc =	
	new_definition
	 (`havoc`,
	  "havoc = \e.TERM e");;

let havoc_grd = prove_thm
(	`havoc_grd`,
	"grd havoc = true",
	CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC [grd;ALL;havoc]
	THEN BETA_TAC
	THEN GEN_TAC
	THEN EXISTS_TAC "pair(f,f)"
	THEN REWRITE_TAC[pair_first;pair_TERM]
);;                      
 
new_special_symbol `:=`;;

let assign = new_infix_definition 
(	`assign`,
	"!x. !exp:state->num.
	 := x exp = \p.?s s'.(p = pair(s, s')) /\ (s' = bnd (exp s) x s)"
);;

let assign_alt = prove_thm
(	`assign_alt`,
	"!exp x e. (x:=exp) e = ?s.e = pair(s, bnd(exp s) x s)",
	REPEAT GEN_TAC
	THEN REWRITE_TAC[assign]
	THEN BETA_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[EXISTS_TAC "s:state"
		 THEN ASM_REWRITE_TAC[]
		;MAP_EVERY EXISTS_TAC["s:state";"bnd(exp s)x s"]
		 THEN ASM_REWRITE_TAC[]
		]
);;

let assign_grd = prove_thm
(	`assign_grd`,
	"!exp x. grd (x:=exp) = true",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [grd;ALL;assign]
	THEN BETA_TAC
	THEN REPEAT GEN_TAC
	THEN EXISTS_TAC "pair(f,bnd(exp f)x f)"
	THEN REWRITE_TAC[pair_first]
	THEN EXISTS_TAC "f:state"
	THEN EXISTS_TAC "bnd(exp f)x f"
	THEN REWRITE_TAC[]
);;

%
| Define random assignment
%

let update = new_definition
(	`update`,	
	"!x:tok.!s:state. update x e = 
		?s val. e = pair(s, bnd val x s)" 
);;

let update_grd = prove_thm
(	`update_grd`,
	"!x. grd (update x) = true",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [grd;ALL;update]
	THEN REPEAT GEN_TAC
	THEN EXISTS_TAC "pair(f,bnd val x f)"
	THEN REWRITE_TAC[pair_first]
	THEN EXISTS_TAC "f:state"
	THEN EXISTS_TAC "val:num"
	THEN REFL_TAC
);;

%
| Define non-deterministic choice between commands
%

new_special_symbol `||`;;

let choose = new_infix_definition (
	`choose`,
	"!c1 c2:command. 
	 || c1 c2 = \p. (c1 p) \/ (c2 p)"
);;               
    
let choose_grd = prove_thm (
	`choose_grd`,
	"!c1 c2. grd (c1 || c2) = (grd c1) OR (grd c2)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [grd;choose;OR]
        THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REWRITE_TAC [RIGHT_AND_OVER_OR]
	THEN CONV_TAC (DEPTH_CONV EXISTS_OR_CONV)
	THEN REWRITE_TAC[]
);;

%
| Define sequential choice between commands, orelse
%

new_special_symbol `|X|`;;

let orelse = new_infix_definition (
	`orelse`,
	"!c1 c2:command. 
	 |X| c1 c2 e = (c1 e) \/ ~(grd c1 (first e)) /\ (c2 e)"
);;	


let orelse_id = prove_thm
(	`orelse_id`,
	"!c. (empty |X| c = c) /\ (c |X| empty = c)",
	GEN_TAC
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [orelse]
	THEN REWRITE_TAC[empty;empty_grd;NONE]
);;

let orelse_grd = prove_thm
(	`orelse_grd`,
	"!c1 c1. grd (c1 |X| c2) = (NOT(grd c1)) IMPLIES (grd c2)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[grd;orelse;IMPLIES;NOT]
	THEN BETA_TAC
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THENL	[EXISTS_TAC "e:exseq"
		 THEN ASM_REWRITE_TAC[]
		;RULE_ASSUM_TAC(CONV_RULE LEFT_IMP_FORALL_CONV)
		 THEN RULE_ASSUM_TAC
			(CONV_RULE(DEPTH_CONV RIGHT_IMP_EXISTS_CONV))
		 THEN REPLACE_FIRST_ASSUM STRIP_ASSUME_TAC
		 THEN ASM_CASES_TAC "!e'.~(c1 e' /\ (first e' = f))"
		 THENL	[EXISTS_TAC "e':exseq"
			 THEN FIRST_ASSUM(ASSUME_TAC o (SPEC "e:exseq"))
			 THEN RES_TAC
			 THEN ASM_REWRITE_TAC[]
			;FIRST_ASSUM 
				(CHOOSE_TAC o 
				 (CONV_RULE NOT_FORALL_CONV))
			 THEN EXISTS_TAC "e'':exseq"
			 THEN RULE_ASSUM_TAC (REWRITE_RULE[])
			 THEN ASM_REWRITE_TAC[]
			]
		]
);;

%        
| Define
|
| "c1;;
|  c2   " ie. program sequencing 
|
%

new_special_symbol `;;`;;

let seq = new_infix_definition (
	`seq`,
	"!c1 c2.!e:exseq.
	 ;; c1 c2 e = 
		(c1 e /\ ~TERM e) \/ 
		(?e1 e2. c1 e1
			 /\ TERM e1 
			 /\ c2 e2 
			 /\ (first e2 = last e1) 
			 /\ (e = e1 <*> e2)
		)"
);;

let seq_grd_total = prove_thm
(	`seq_grd_total`,
	"!c1 c2. total c2 ==> (grd c1 = grd (c1 ;; c2))",
	REWRITE_TAC[total]
	THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [grd;seq;ALL]
	THEN REPEAT STRIP_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[ASM_CASES_TAC "TERM e"
		 THENL	[FIRST_ASSUM
				(STRIP_ASSUME_TAC o (SPEC "last e"))
			 THEN EXISTS_TAC "e <*> e'"
			 THEN IMP_RES_TAC join_first
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ2_TAC
			 THEN MAP_EVERY EXISTS_TAC["e:exseq";"e':exseq"]
			 THEN ASM_REWRITE_TAC[]
			;EXISTS_TAC "e:exseq"
			 THEN ASM_REWRITE_TAC[]
			]
		;EXISTS_TAC "e:exseq"
		 THEN ASM_REWRITE_TAC[]
		;EXISTS_TAC "e1:exseq"
		 THEN IMP_RES_TAC join_first
		 THEN REWRITE_ASM[]
		 THEN ASM_REWRITE_TAC[]
		]
);;


let seq_left_fixed = prove_thm
(	`seq_left_fixed`,
	"!c. empty ;; c = empty",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [seq; empty]
);;

% In the following proof, REPEAT STRIP_TAC fails,
  yet it should never fail. The part that fails is
  CHOOSE
  Later: this is a bug in hol2.0 fixed in hol2.1
%

let seq_assoc = prove_thm
(	`seq_assoc`,
	"!c1 c2 c3. (c1 ;; c2) ;; c3 = c1 ;; (c2 ;; c3)",
	CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [seq]
	THEN BETA_TAC
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THENL	[DISCH_THEN DISJ_CASES_TAC	 
		 THENL	[FIRST_ASSUM STRIP_ASSUME_TAC
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ2_TAC
			 THEN MAP_EVERY EXISTS_TAC ["e1:exseq";"e2:exseq"]
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ1_TAC
			 THEN IMP_RES_TAC join_TERM
			 THEN ASM_REWRITE_TAC[]
			 THEN ASSUM_LIST 
				((REWRITE_TERML "e1<*>e2") o SYML_th)
			 THEN ASM_REWRITE_TAC[]
			;FIRST_ASSUM (CHOOSE_THEN CHOOSE_TAC)
			 THEN FIRST_ASSUM STRIP_ASSUME_TAC
			 THEN DISJ2_TAC
			 THEN RES_TAC
			 THEN MAP_EVERY EXISTS_TAC 
				["e1':exseq";"e2'<*>e2:exseq"]
			 THEN ASM_REWRITE_TAC[]
			 THEN CONJ_TAC
			 THENL	[DISJ2_TAC
				 THEN MAP_EVERY EXISTS_TAC
					["e2':exseq";"e2:exseq"]
				 THEN REWRITE_TAC[]
				 THEN UNDISCH_TAC "TERM e1"	
				 THEN ASSUM_LIST (REWRITE_TERML "e1:exseq")
				 THEN DISCH_TAC
				 THEN IMP_RES_TAC join_TERM
				 THEN ASM_REWRITE_TAC[]
				 THEN IMP_RES_TAC join_last
				;UNDISCH_TAC "TERM e1"	
				 THEN ASSUM_LIST (REWRITE_TERML "e1:exseq")
				 THEN DISCH_TAC
				 THEN IMP_RES_TAC join_TERM
				 THEN IMP_RES_TAC join_last
				 THEN ASSUM_LIST
					((REWRITE_TERML "last e1'")
					o SYML_th)
				 THEN UNDISCH_TAC "first e2 = last e1"
				 THEN ASSUM_LIST(REWRITE_TERML "e1:exseq")
				 THEN ASSUM_LIST
					(REWRITE_TERML "last(e1'<*>e2')")
				 THEN DISCH_TAC
			 	 THEN IMP_RES_TAC join_first
				 THEN ASSUM_REDUCE_TAC
				 THEN IMP_RES_TAC join_assoc
				 THEN ASM_REWRITE_TAC[]	
				]
			]
		;REPEAT STRIP_TAC
		 THEN ASM_REWRITE_TAC[]
		 THENL	[IMP_RES_TAC join_TERM
			 THEN UNDISCH_TAC "~TERM e2"
			 THEN ASSUM_LIST(REWRITE_TERML "TERM e2")
			 THEN DISCH_TAC
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ1_TAC
			 THEN DISJ2_TAC
			 THEN MAP_EVERY EXISTS_TAC["e1:exseq";"e2:exseq"]
			 THEN ASM_REWRITE_TAC[]
			;IMP_RES_TAC join_TERM
			 THEN ASM_REWRITE_TAC[]
			 THEN DISJ2_TAC
			 THEN MAP_EVERY EXISTS_TAC
				["e1 <*> e1'"
				;"e2':exseq"
				]
			 THEN ASM_REWRITE_TAC[]
			 THEN IMP_RES_TAC join_first
			 THEN UNDISCH_TAC "first e2 = last e1"
			 THEN ASM_REWRITE_TAC[]
			 THEN DISCH_TAC
			 THEN IMP_RES_TAC join_last
			 THEN IMP_RES_TAC join_TERM
			 THEN DETOUR
				(IMP_RES_TAC join_assoc
				 THEN ASM_REWRITE_TAC[])
			 THEN MAP_EVERY EXISTS_TAC["e1:exseq";"e1':exseq"]
			 THEN ASM_REWRITE_TAC[]
			]
		]
);;

%
| Define a guarded command, which restricts the domain
| of the command. This will convert any total command to a partial command
| May be read as "If P then c" but this is NOT If_fI (P --> c)
%

new_special_symbol `-->`;;

let gcom = new_infix_definition (
	`gcom`,
	"!P.!c:command. 
	 --> P c = \e:exseq. P (first e) /\ c e" 
);; 


let gcom_grd = prove_thm (
	`gcom_grd`,
	"!P c. grd (P-->c) = P AND (grd c)",
        CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [grd;gcom;AND]
	THEN CONV_TAC (DEPTH_CONV BETA_CONV) 
	THEN REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN TRY (UNDISCH_TAC "(P(first e)):bool")
	THEN ASM_REWRITE_TAC[]
	THEN TRY DISCH_TAC
	THEN EXISTS_TAC "e:exseq" 
	THEN ASSUM_REDUCE_TAC 
	THEN ASM_REWRITE_TAC[]
);; 

%
| Define the conditional If .. fI
| This is now a unary operator on commands
| which aborts outside the domain of the command
% 

let If_fI = new_definition (
	`If_fI`,
	"!c:command.
	 If_fI c = c |X| abort "
);; 

let If_fI_grd = prove_thm
(	`If_fI_grd`,
	"!c. grd(If_fI c) = true",
	REWRITE_TAC[If_fI;orelse_grd;abort_grd;IMPLIES;ALL]
);;

%
| Define the sequence of finite products of a chain
| of execution sequences.
%

let TTseq = new_prim_rec_definition
(	`TTseq`,
	"(TTseq (Seq:num->exseq) 0 = (Seq 0)) /\
	 (TTseq Seq (SUC n) = (TTseq Seq n) <*> (Seq(n+1)))"
);; 

let TTseq_chain = prove_thm 
(	`TTseq_chain`,
	"!Seq.
	 (!n.TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 chain $<=| (TTseq Seq)",
	REWRITE_TAC [chain;SYM_th ADD1;TTseq]
	THEN REPEAT STRIP_TAC
	THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (SPEC "i:num"))
	THEN SUPPOSE_TAC 
		"!n.(last(Seq n) =
			 last(TTseq Seq n)) /\ TERM(TTseq Seq n)"
	THENL	[MAPFILTER_ASSUM (STRIP_ASSUME_TAC o (SPEC "i:num"))
		 THEN IMP_RES_TAC join_inc
		 THEN FIRST_ASSUM SUBST_ALL_TAC 
		 THEN RES_TAC
		 THEN IMP_RES_TAC exseq_strict_imp_subseq
		;INDUCT_TAC
		 THEN ASM_REWRITE_TAC [TTseq;SYM_th ADD1]
		 THEN MAPFILTER_ASSUM (STRIP_ASSUME_TAC o (SPEC "n:num"))
		 THEN IMP_RES_TAC join_last
		 THEN FIRST_ASSUM 
			(FORK (SUBST_ALL_TAC o CONJUNCT1) 
			      (ASSUME_TAC o CONJUNCT2))
		 THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (SPEC "SUC n"))
		 THEN IMP_RES_TAC join_last
		 THEN ASM_REWRITE_TAC[]
		 THEN IMP_RES_TAC join_TERM
		]
);;

%
| Define 'iteration' of commands
%

new_special_symbol `^^`;;

let iter = new_recursive_definition true num_Axiom `iter`
 	"(^^ (c:command) 0 = c) /\
  	 (^^ c (SUC n) = c ;; (^^ c n))";;

let iter_swop = prove_thm
(	`iter_swop`,
	"!n c. (c ^^ n) ;; c = c ;; (c ^^ n)",
	INDUCT_TAC
	THEN REWRITE_TAC[iter]
	THEN ASM_REWRITE_TAC[seq_assoc]
);;

%
| General recursion by Kleene closure under <*>
%


let next = new_definition
(	`next`,
	"!c:command.!e e':exseq. 
	 next c e e' = TERM e /\ c e' /\ (first e' = last e)"
);;

let rec = new_definition
(	`rec`,
	"!c:command.!e:exseq. 
	 rec c e =
		?Seq. c(Seq 0) /\
			((?m.(!n. (n<m ==> next c (Seq n) (Seq(SUC n)))) /\
			    (!e'. ~ next c (Seq m) e') /\
			    (e = TTseq Seq m)
			) \/
			((!n. next c (Seq n) (Seq(SUC n))) /\
			 (e = lub $<=| (TTseq Seq))
			))"
);;

let lemma7 = PROVE
(	"!Seq c m.
	 (!n. n < m ==> next c(Seq n)(Seq(SUC n))) ==>  
	 (!n. n < m ==> TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n)))", 
	REWRITE_TAC[next]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[SYM_th ADD1]
);;

let lemma8 = PROVE
(	"!Seq c.
	 (!n. next c(Seq n)(Seq(SUC n))) ==>  
	 (!n. TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n)))", 
	REWRITE_TAC[next]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN ASM_REWRITE_TAC[SYM_th ADD1]
);;

% Attempt to construct a sequence from c starting at e %

let select_seq = new_prim_rec_definition
(	`select_seq`,
	"(select_seq c (e:exseq) 0 = e) /\
	 (select_seq c e (SUC n) = 
		@e'. next c (select_seq c e n) e')"
);;

let lemma9 = PROVE
(	"!e c n. 
	  ~next c(select_seq c e n)(select_seq c e(SUC n)) =
	  !e'. ~ next c (select_seq c e n) e'",
	REWRITE_TAC [select_seq]
	THEN CONV_TAC (DEPTH_CONV SELECT_CONV)
	THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN REWRITE_TAC[]
);;

let TTseq_first_last_finite = prove_thm
(	`TTseq_first_last_finite`,
	"!Seq m.
	 (!n. n<m ==> TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 (first(TTseq Seq m) = first(Seq 0)) 
		/\ (TERM(Seq m) = TERM(TTseq Seq m))
		/\ (TERM(Seq m) ==> (last(TTseq Seq m) = last(Seq m)))",
	GEN_TAC
	THEN INDUCT_TAC
	THEN REWRITE_TAC[TTseq]
	THEN DISCH_TAC
	THEN RULE_ASSUM_TAC (REWRITE_RULE[SYM_th LESS_EQ_LESS_SUC])
	THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (SPEC "m:num"))
	THEN RULE_ASSUM_TAC (REWRITE_RULE [LESS_EQ_REFL])
	THEN MAPFILTER_ASSUM STRIP_ASSUME_TAC
	THEN SUPPOSE_TAC 
		"(!n. n < m ==> TERM(Seq n) /\ 
			(first(Seq(n + 1)) = last(Seq n)))"
	THENL	[RES_TAC
		 THEN UNDISCH_TAC "first(Seq(m + 1)) = last(Seq m)" 
		 THEN ASSUM_LIST (REWRITE_TAC o SYML_th)
		 THEN DISCH_TAC
		 THEN REWRITE_TAC[ADD1]
		 THEN MAP_EVERY IMP_RES_TAC [join_TERM;join_last;join_first]
		 THEN ASM_REWRITE_TAC[]
		;GEN_TAC
		 THEN DISCH_TAC
		 THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
		 THEN RES_TAC
		 THEN ASM_REWRITE_TAC[]
		]
);;

let TTseq_first_last = prove_thm
(	`TTseq_first_last`,
	"!Seq.
	 (!n.TERM(Seq n) /\ (first(Seq(n+1)) = last(Seq n))) ==>
	 !n.(TERM(TTseq Seq n)) /\
	    (first(TTseq Seq n) = first(Seq 0)) /\
	    (last(TTseq Seq n) = last(Seq n))",
	GEN_TAC
	THEN DISCH_TAC
	THEN INDUCT_TAC
	THEN ASM_REWRITE_TAC[TTseq]
	THEN ASSUM_LIST ((REWRITE_TERML "first(Seq 0)") o SYML_th)
	THEN FIRST_ASSUM (MP_TAC o (SPEC "n:num"))
	THEN ASSUM_LIST ((REWRITE_TERML "last(Seq (n:num))") o SYML_th)
	THEN DISCH_TAC
	THEN EVERY_ASSUM STRIP_ASSUME_TAC
	THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (SPEC "n+1"))
	THEN MAP_EVERY IMP_RES_TAC [join_TERM;join_last;join_first]
	THEN REWRITE_TAC[ADD1]
	THEN ASSUM_REDUCE_TAC
);;

let rec_grd = prove_thm
(	`rec_grd`,
	"!c. grd c = grd(rec c)",
	GEN_TAC
	THEN CONV_TAC FUN_EQ_CONV
	THEN REWRITE_TAC [grd;rec]
	THEN GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THENL	[ASM_CASES_TAC 
			"!n. next c(select_seq c e n)(select_seq c e(SUC n))"
		 THENL	[EXISTS_TAC "lub $<=| (TTseq (select_seq c e))"
			 THEN ONE_IMP_RES_TAC lemma8 
			 THEN MAP_EVERY IMP_RES_TAC
				[TTseq_chain 
				;lub_first
				]
			 THEN ASM_REWRITE_TAC[TTseq;select_seq]
			 THEN EXISTS_TAC "select_seq c e"
			 THEN ASM_REWRITE_TAC [select_seq]
			;FIRST_ASSUM(ASSUME_TAC o (CONV_RULE NOT_FORALL_CONV))
			 THEN FIRST_ASSUM CHOOSE_TAC
			 THEN ASSUME_TAC 
					(BETA_RULE (SPEC 
					 "\n.~next c(select_seq c e n)
					 (select_seq c e(SUC n))" well_order
					))
			 THEN FIRST_ASSUM ONE_IMP_RES_TAC
			 THEN MAPFILTER_ASSUM CHOOSE_TAC
			 THEN IMP_RES_TAC well_order_less
			 THEN RULE_ASSUM_TAC BETA_RULE
			 THEN RULE_ASSUM_TAC (REWRITE_RULE[])
			 THEN EXISTS_TAC "TTseq (select_seq c e)m"
			 THEN ONE_IMP_RES_TAC lemma7
			 THEN IMP_RES_TAC TTseq_first_last_finite
			 THEN ASM_REWRITE_TAC [select_seq]
			 THEN EXISTS_TAC "select_seq c e"
			 THEN ASM_REWRITE_TAC [select_seq]
			 THEN EXISTS_TAC "m:num"		
			 THEN ASM_REWRITE_TAC[]
			 THEN RULE_ASSUM_TAC(REWRITE_RULE[least])
			 THEN RULE_ASSUM_TAC BETA_RULE
			 THEN EVERY_ASSUM STRIP_ASSUME_TAC
			 THEN IMP_RES_TAC lemma9	
			]
		;EXISTS_TAC "Seq 0:exseq"
		 THEN ONE_IMP_RES_TAC lemma7
		 THEN IMP_RES_TAC TTseq_first_last_finite
		 THEN UNDISCH_TAC  "first e = f"
		 THEN ASM_REWRITE_TAC[]
		;ONE_IMP_RES_TAC lemma8
		 THEN IMP_RES_TAC TTseq_first_last
		 THEN UNDISCH_TAC "first e = f"
		 THEN IMP_RES_TAC TTseq_chain
		 THEN IMP_RES_TAC lub_first
		 THEN ASM_REWRITE_TAC[]
		 THEN DISCH_TAC
		 THEN EXISTS_TAC "Seq 0:exseq"
		 THEN ASM_REWRITE_TAC[]
		]
);;


let do_od = new_definition
(	`do_od`,
	"!c. do_od c = (rec c) |X| skip" 
);;

let do_od_grd = prove_thm
(	`do_od_grd`,
	"!c. grd(do_od c) = true",
	REWRITE_TAC[do_od;orelse_grd;skip_grd]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC [ALL;IMPLIES]
);;

let do_od_total = prove_thm
(	`do_od_total`,
	"!c. total(do_od c)",
	REWRITE_TAC[total;do_od_grd]
);;

%
| Define some languages in denotational style by structural 
| induction
%

let lang = define_type `lang`
	`lang =   SKIP
		| EMPTY
		| FAIL
		| HAVOC
		| ASSIGN tok (state->num)
		| UPDATE tok
		| SEQ lang lang
		| CHOOSE lang lang
		| ORELSE lang lang
		| GCOM (state->bool) lang
		| IF_FI lang
		| DO_OD lang`;;

let M = new_recursive_definition false lang `M`
	"(M SKIP = skip) /\
	 (M EMPTY = empty) /\
	 (M FAIL = abort) /\
	 (M HAVOC = havoc) /\
	 (M (ASSIGN x exp) = (x:=exp)) /\
	 (M (UPDATE x) = (update x)) /\
	 (M (SEQ f1 f2) = (M f1) ;; (M f2)) /\
	 (M (CHOOSE f1 f2) = (M f1) || (M f2)) /\
	 (M (ORELSE c1 c2) = (M c1) || (M c2)) /\
	 (M (GCOM P c) = (P --> (M c))) /\
	 (M (IF_FI c) = If_fI(M c)) /\
	 (M (DO_OD c) = do_od(M c))";; 

close_theory();;
