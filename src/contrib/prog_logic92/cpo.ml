%---------------------------------------------------------------------------- 
| FILE: cpo.ml
|
| A little theory of partial orders, mainly just defns
| and well-founded sets 
| 
| AUTHOR: Gavan Tredoux 
-----------------------------------------------------------------------------%

new_theory `cpo`;;

loadf `mytactics`;;

%
load_library `more_arithmetic`;;
%

loadf `l_arith_hack`;;

let refl = new_definition (
	`refl`,
   	"!r:*->*->bool. refl r = (!d:*. r d d)"
);;
   
let antisym = new_definition (
	`antisym`,
	"!r:*->*->bool. 
	 antisym r = (!d1 d2. r d1 d2 /\ r d2 d1 ==> (d1 = d2))"
);; 

let trans = new_definition (
	`trans`,
	"!r:*->*->bool. 
	 trans r = (!d1 d2 d3. r d1 d2 /\ r d2 d3 ==> r d1 d3)"
);;

let partial_order = new_definition (
	`partial_order`,
	"!r:*->*->bool.
	 partial_order r = refl r /\ antisym r /\ trans r"
);; 

let chain = new_definition (
	`chain`,
   	"!Ch:num->*. !r:*->*->bool. 
	 chain r Ch = !i. r (Ch i) (Ch (i+1))"
);;
 
let chain_comp = prove_thm (
	`chain_comp`,
	"!Ch.!r:*->*->bool. 
	 partial_order r ==> ( chain r Ch = !n.!m. r (Ch n) (Ch(n+m)) )", 
	REWRITE_TAC[chain;partial_order;refl;antisym;trans]
	THEN REPEAT STRIP_TAC
	THEN EQ_TAC
	THEN DISCH_TAC
	THEN GEN_TAC
	THENL	[INDUCT_TAC
		 THENL	[ASM_REWRITE_TAC[ADD_0] 
			;REWRITE_TAC[ADD1;ADD_ASSOC]
			 THEN FIRST_ASSUM (ASSUME_TAC o (SPEC "n+m"))
                  	 THEN RES_TAC
			]
		;ASM_REWRITE_TAC[]
		]
);;

let chain_less_eq = prove_thm ( 
	`chain_less_eq`,
	"!C.!r:*->*->bool.
	partial_order r ==> (chain r C = !n m. n <= m ==> r (C n) (C m))",
	REPEAT GEN_TAC
	THEN DISCH_THEN (FORK MP_TAC ASSUME_TAC)   
	THEN IMP_RES_TAC chain_comp
	THEN REWRITE_TAC [partial_order;refl;trans;antisym]
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN EQ_TAC
	THEN DISCH_TAC
	THENL	[REWRITE_TAC [LESS_OR_EQ]
		 THEN REPEAT STRIP_TAC
		 THENL	[IMP_RES_TAC LESS_ADD
			 THEN ASSUM_LIST (ONCE_REWRITE_TAC o SYML_th)
			 THEN ONCE_REWRITE_TAC [ADD_SYM]
			 THEN ONCE_ASM_REWRITE_TAC[]
			;ASM_REWRITE_TAC[]
			]
		;REPEAT STRIP_TAC
		 THEN ASSUME_TAC (SPECL ["n:num";"m:num"] LESS_EQ_ADD)
		 THEN RES_TAC
		]
);;

let chain_total = prove_thm (
	`chain_total`,
	"!C.!r:*->*->bool. partial_order r ==> chain r C ==> !m n. r (C m) (C n) \/ r (C n) (C m)",
        REPEAT GEN_TAC 
	THEN DISCH_TAC
	THEN IMP_RES_TAC chain_less_eq 
	THEN ASM_REWRITE_TAC[]
	THEN DISCH_TAC
	THEN REPEAT GEN_TAC
	THEN DISJ_CASES_SPLIT "n <= m" 
	THENL	[RES_THEN \th.REWRITE_TAC[th] 
		;IMP_RES_TAC LESS_EQ_SYM
                 THEN RES_THEN \th.REWRITE_TAC[th] 
		] 
);;

%
| Upper bounds
%

let is_ub = new_definition (
	`is_ub`,
	"!d:*. !C:num->*. !r.
	 is_ub r d C = !n. r (C n) d"
);;

%
| Least upper bounds. Non-constructive.
%

let is_lub = new_definition (
	`is_lub`,
	"!d:*.!C:num->*.!r. 
	 is_lub r d C = is_ub r d C /\ (!k. is_ub r k C ==> r d k)"
);; 

let lub = new_definition (
	`lub`,   
        "!C.!r:*->*->bool. lub r C = @d. is_lub r d C"
);;

%
: Prove that lubs are unique in a partial order
%

let lub_unique = prove_thm
(	`lub_unique`,
	"!C r.!a b:*. 
	 partial_order r ==>
	 is_lub r a C ==>
	 is_lub r b C ==> (a = b)",
	REWRITE_TAC [partial_order;antisym;is_lub;is_ub]
	THEN REPEAT STRIP_TAC
	THEN RES_TAC
	THEN RES_TAC
);; 

let lub_eq = prove_thm
(	`lub_eq`,
	"!C r.!a:*.
	 partial_order r ==>
	 is_lub r a C ==> (a = lub r C)",
	REPEAT STRIP_TAC
	THEN REWRITE_TAC [lub]
	THEN SUPPOSE_TAC "?a:*.is_lub r a C"
	THENL	[FIRST_ASSUM (ASSUME_TAC o SELECT_RULE)
		 THEN IMP_RES_TAC lub_unique
		;EXISTS_TAC "a:*"
		 THEN ASM_REWRITE_TAC[]
		]
);;

% 
: Prove that lubs aren't affected by adding a smaller element
%

let lub_add_one = prove_thm
(	`lub_add_one`,	
	"!C r.!a:*.
	 partial_order r ==>
	 r a (C 0) ==>
	 is_lub r (lub r C) C ==>
	 (lub r C = lub r (\i. (i=0) => a | C(i-1)))",
	REPEAT STRIP_TAC
	THEN SUPPOSE_TAC "is_lub r (lub r C) (\i. (i=0) => (a:*) | C(i-1))"
	THENL	[IMP_RES_TAC lub_eq
		;REWRITE_TAC[is_lub;is_ub]
		 THEN REWRITE_ASM[is_lub;is_ub]
		 THEN BETA_TAC
		 THEN REPEAT STRIP_TAC
		 THENL	[COND_CASES_TAC
			 THENL	[FIRST_ASSUM
					(STRIP_ASSUME_TAC 
					o (SPEC "0")
					o CONJUNCT1)
				 THEN UNDISCH_TAC "partial_order (r:*->*->bool)"
				 THEN REWRITE_TAC [partial_order;trans]
				 THEN DISCH_THEN IMP_RES_TAC
				;ASM_REWRITE_TAC[]
				]
			;SUPPOSE_TAC "!n:num.(r:*->*->bool)(C n)k"
			 THENL	[RES_TAC
				;GEN_TAC
				 THEN FIRST_ASSUM (MP_TAC o (SPEC "n+1"))
				 THEN REWRITE_TERML "n+1=0"
					[SYM_th ADD1;SUC_NOT_0]
			 	THEN ASM_REWRITE_TAC[ADD_SUB]
				]
			] 				
		] 
);;

let is_max = new_definition (
	`is_max`,
	"!d C.!r:*->*->bool.
	 is_max r d C = (?n. d = C n) /\ is_ub r d C"
);;                          

let max = new_definition (      
	`max`,
        "!C.!r:*->*->bool. max r C = @d. is_max r d C" 
);;

let max_is_lub = prove_thm (       
	`max_is_lub`,
	"!d C.!r:*->*->bool.
	 is_max r d C ==> is_lub r d C",
	REWRITE_TAC [is_max;is_lub] 
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN REPLACE_ASSUM "is_ub (r:*->*->bool) (k:*) (C:num->*)"
		(\th.REWRITE_RULE[is_ub] th) 
	THEN ASM_REWRITE_TAC[]
);;       
    
let stunt_chain = new_definition (
	`stunt_chain`,
	"!C.!r:*->*->bool.
	 stunt_chain r C = chain r C /\ ?n. is_ub r (C n) C"
);;

let stunt_chain_lub = prove_thm (
	`stunt_chain_lub`,
        "!C.!r:*->*->bool.
	 stunt_chain r C ==> ?n. is_lub r (C n) C", 
	REWRITE_TAC [stunt_chain;chain;is_lub]
	THEN REPEAT STRIP_TAC 
	THEN EXISTS_TAC "n:num"
	THEN ASM_REWRITE_TAC[] 
	THEN GEN_TAC 
	THEN REWRITE_TAC [is_ub]
	THEN DISCH_THEN (\th.REWRITE_TAC[th])
);; 

let not_stunt_chain = prove_thm (
	`not_stunt_chain`,
   	"!C.!r:*->*->bool.
	 partial_order r ==> 
	 chain r C ==> 
	 ~stunt_chain r C ==> 
	 !n.?m. r (C n) (C m) /\ ~(C n = C m)",
	REWRITE_TAC [stunt_chain]
	THEN REPEAT GEN_TAC
	THEN DISCH_TAC
	THEN DISCH_TAC
	THEN ASM_REWRITE_TAC[is_ub]
	THEN CONV_TAC ((DEPTH_CONV NOT_EXISTS_CONV) THENC (DEPTH_CONV NOT_FORALL_CONV)) 
	THEN REPEAT STRIP_TAC
	THEN FIRST_ASSUM (CHOOSE_TAC o (SPEC "n:num"))
	THEN IMP_RES_TAC chain_total
        THEN FIRST_ASSUM (DISJ_CASES_TAC o (SPECL ["n:num";"n':num"])) 
        THENL	[EXISTS_TAC "n':num"
		 THEN ASM_REWRITE_TAC[]
		 THEN STRIP_TAC
		 THEN FIRST_ASSUM SUBST_ALL_TAC
		 THEN REPLACE_ASSUM "partial_order (r:*->*->bool)"
			(REWRITE_RULE [partial_order;refl]) 
		 THEN RES_TAC
		; RES_TAC 
		]
);;

let cpo = new_definition (
	`cpo`,
   	"!r:*->*->bool. 
	 cpo r = partial_order r /\ !C.chain r C ==> is_lub r (lub r C) C" 
);;

%
| Well-founded predicates (sets) with respect to a relation
%

let dec_chain = new_definition
(	`dec_chain`,
	"!C:num->*.!W:*->bool.!R:*->*->bool. 
	 dec_chain C W R = (!n. W(C n)) /\ (!n.R (C(SUC n)) (C n))" 
);;

let wfp = new_definition
(	`wfp`,
	"!W:*->bool.!R:*->*->bool.wfp W R = ~?C. dec_chain C W R"
);;

close_theory();;
