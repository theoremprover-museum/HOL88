% Extends The Basic Theory For TRACES In CSP                    	 %
% 									 %
% FILE		: order.ml     					         %
% DESCRIPTION	: Defines the <= operator for finite traces and infinite %
%                 alphabets. Also defines the operator "in" and		 %
%		  monotonic functions.                                   %
% 									 %
% READS FILES	: restrict.th                                   	 %
% WRITES FILES  : order.th						 %
%									 %
% AUTHOR	: Albert John Camilleri					 %
% AFFILIATION   : Hewlett-Packard Laboratories, Bristol		 	 %
% DATE		: 89.02.07						 %
% REVISED	: 91.10.01						 %


new_theory `order`;;

new_parent `restrict`;;

map (load_theorem `list_lib1`) [`APPEND_EQ_NIL`; `APPEND_NIL`; `APPEND_ID`];;

let PREFIX =
    new_infix_definition
       (`PREFIX`, "!s t:(*)list. ($LEQ s t) = ?u:(*) list. (APPEND s u) = t");;

let LEAST =
    prove_thm
       (`LEAST`,
	"! s:* list. [] LEQ s",
	REWRITE_TAC [PREFIX; APPEND] THEN
	GEN_TAC THEN
	EXISTS_TAC "s:* list" THEN
	REWRITE_TAC []);;

let REFLEXIVE =
    prove_thm
       (`REFLEXIVE`,
	"! s:* list. s LEQ s",
	REWRITE_TAC [PREFIX] THEN
	GEN_TAC THEN
	EXISTS_TAC "[]:* list" THEN
	REWRITE_TAC [APPEND_NIL]);;

let ANTI_SYMM =
    prove_thm
       (`ANTI_SYM`,
	"! s t:(*) list. (s LEQ t /\ t LEQ s) ==> (s = t)",
	REWRITE_TAC [PREFIX] THEN
	REPEAT STRIP_TAC THEN
	POP_ASSUM (ASSUME_TAC o SYM) THEN
	UNDISCH_TAC "APPEND (s:* list) u = (t:* list)" THEN
	ASM_REWRITE_TAC [SYM (SPEC_ALL APPEND_ASSOC)] THEN
	ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
	REWRITE_TAC [APPEND_ID; APPEND_EQ_NIL] THEN
	STRIP_TAC);;

let TRANS_PREFIX =
    prove_thm
       (`TRANS_PREFIX`,
	"! s t v:(*) list. (s LEQ t /\ t LEQ v) ==> (s LEQ v)",
	REWRITE_TAC [PREFIX] THEN
	ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
	REPEAT STRIP_TAC THEN
	EXISTS_TAC "(APPEND (u:* list) u')" THEN
	ASM_REWRITE_TAC [APPEND_ASSOC]);;

let RIGHT_AND_EXISTS_TAC = CONV_TAC (DEPTH_CONV RIGHT_AND_EXISTS_CONV);;

let ST_IND_PREFIX =
    prove_thm
       (`ST_IND_PREFIX`,
	"! (s t:* list) (x:*).
           ((APPEND [x] s) LEQ t) =
           ((~(t = [])) /\ (x = HD t) /\ (s LEQ (TL t)))",
	GEN_TAC THEN
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [PREFIX; APPEND_EQ_NIL; NOT_CONS_NIL;
	             HD; TL; APPEND; CONS_11] THEN
	RIGHT_AND_EXISTS_TAC THEN
	REWRITE_TAC[]);;

let ST_IND_PREFIX' =
    save_thm (`ST_IND_PREFIX'`, REWRITE_RULE [APPEND] ST_IND_PREFIX);;

let TOT_ORDER_PREFIX =
    prove_thm
       (`TOT_ORDER_PREFIX`,
	"! s t v:(*)list.
           ((s LEQ v) /\ (t LEQ v)) ==> ((s LEQ t) \/ (t LEQ s))",
	REPEAT (LIST_INDUCT_TAC THEN
	        REWRITE_TAC [LEAST] THEN
	        GEN_TAC) THEN
	REWRITE_TAC [ST_IND_PREFIX'; HD; TL; NOT_CONS_NIL] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC THEN
	ASM_REWRITE_TAC []);;

let IN_TRACE =
    new_infix_definition
       (`IN_TRACE`,
	"! s t:(*)list. $in s t = (? u v. t = (APPEND u (APPEND s v)))");;

let MONOTONIC =
    new_definition
       (`MONOTONIC`,
	"MONOTONIC (f:(*)list->(*)list) =
         ! s t:(*)list. s LEQ t ==> (f s) LEQ (f t)");;

close_theory();;
