% Extends The Basic Theory For TRACES In CSP                    	 %
% 									 %
% FILE		: restrict.ml     					 %
% DESCRIPTION	: Defines the restriction operator and proves some of    %
%                 its properties. Restriction is defined over finite     %
%                 traces and infinite alphabets.                         %
% 									 %
% LOADS LIBRARY : sets							 %
% READS FILES	: traces.th, boolarith2.th                          	 %
% WRITES FILES  : restrict.th						 %
%									 %
% AUTHOR	: Albert J Camilleri					 %
% AFFILIATION	: Hewlett-Packard Laboratories, Bristol			 %
% DATE		: 89.02.06						 %
% REVISED	: 91.10.01						 %


new_theory `restrict`;;

load_library `sets`;;

map new_parent [`traces`; `boolarith2`];;

map (load_theorem `boolarith2`) [`INV_SUC_LEQ`; `LESS_EQ_0_N`];;
load_theorem `boolarith1` `NOT_EQ_LEQ`;;
load_theorem `list_lib1` `NOT_LENGTH_EQ`;;

let RESTRICT =
    new_list_rec_definition
       (`RESTRICT`,
        "(RESTRICT [] (A:(*)set) = []) /\
         (RESTRICT (CONS (x:*) t) (A:(*)set) =
            (x IN A) => (CONS x (RESTRICT t A)) | (RESTRICT t A))");;

let STRICT_REST =
    prove_thm
       (`STRICT_REST`,
	"! A:(*)set. RESTRICT [] A = []",
	REWRITE_TAC [CONJUNCT1 RESTRICT]);;

let DISTRIB_REST =
    prove_thm
       (`DISTRIB_REST`,
	"! s t (A:(*)set).
           RESTRICT (APPEND s t) A = (APPEND (RESTRICT s A) (RESTRICT t A))",
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [APPEND; RESTRICT] THEN
	REPEAT STRIP_TAC THEN
	DISJ_CASES_TAC (SPEC "(h:*) IN (A:(*)set)" EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC[APPEND]);;

let RESTR_EMPTY =
    prove_thm
       (`RESTR_EMPTY`,
	"! s:* list. RESTRICT s {} = []",
	LIST_INDUCT_TAC THEN
	ASM_REWRITE_TAC [RESTRICT; NOT_IN_EMPTY]);;

let REP_RESTR =
    prove_thm
       (`REP_RESTR`,
	"! s (A B:(*)set).
	   (RESTRICT (RESTRICT s A) B) = (RESTRICT s (A INTER B))",
	LIST_INDUCT_TAC THEN
	REWRITE_TAC [RESTRICT] THEN
	REPEAT GEN_TAC THEN
	DISJ_CASES_TAC (SPEC "(h:*) IN (A:(*)set)" EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC [RESTRICT] THEN
	DISJ_CASES_TAC (SPEC "(h:*) IN (B:(*)set)" EXCLUDED_MIDDLE) THEN
	ASM_REWRITE_TAC[IN_INTER]);;

let LEQ_ID =
    GEN_ALL
     (REWRITE_RULE [SYM (SPEC_ALL ADD1)] (SPECL ["m:num";"1"] LESS_EQ_ADD));;

let MAX_LEN_REST =
    prove_thm
       (`MAX_LEN_REST`,
	"! (A:(*)set) s. LENGTH (RESTRICT s A) <= LENGTH s",
	GEN_TAC THEN
	LIST_INDUCT_TAC THENL
	[REWRITE_TAC [RESTRICT;LENGTH;LESS_EQ_0_N];
	 GEN_TAC THEN
	 DISJ_CASES_TAC (SPEC "(h:*) IN (A:(*)set)" EXCLUDED_MIDDLE) THEN
	 ASM_REWRITE_TAC[RESTRICT;LENGTH;INV_SUC_LEQ] THEN
	 ASSUME_TAC (SPEC "LENGTH (s:* list)" LEQ_ID) THEN
	 IMP_RES_TAC LESS_EQ_TRANS THEN
	 ASM_REWRITE_TAC []]);;

let REST_LEMMA =
    prove_thm
       (`REST_LEMMA`,
	"!(A:(*)set) (s:(*)list) a.
           ~((LENGTH (RESTRICT s A)) = (LENGTH (CONS a s)))",
	REWRITE_TAC
	  [NOT_EQ_LEQ;
	   LENGTH;
	   REWRITE_RULE
	     [GEN_ALL (SYM (SPEC_ALL (LESS_OR_EQ)))]
	     (ONCE_REWRITE_RULE [DISJ_SYM] LESS_THM);
	   MAX_LEN_REST]);;

let REST_CONS_THM =
    save_thm
       (`REST_CONS_THM`,
	GEN_ALL
	 (MP (SPECL ["CONS a (s:* list)"; "RESTRICT s (A:(*)set)"]
		    NOT_LENGTH_EQ)
	     (SPEC_ALL REST_LEMMA)));;

close_theory();;
