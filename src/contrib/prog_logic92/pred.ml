%--------------------------------------------------------------+
|                                                              |
| FILE:                                                        | 
|                                                              |
| pred.ml                                                      |
|                                                              |
| DESCRIPTION:	                                               |
|                                                              |
| A little theory of predicates   			       |
|                                                              |
| AUTHOR:                                                      |
|                                                              |
| G. Tredoux                                                   |
|                                                              |
+--------------------------------------------------------------%

%
| Define a little theory of predicates
| where a predicate is a mapping * -> bool
%

new_theory `pred`;;

loadf `mytactics`;;
loadf `l_exseq`;;

let NONE = 
	new_definition
	 (`NONE`,
	  "false = \(s:*).F");;

let ALL=
	new_definition
	 (`ALL`,
 	 "true = \(s:*).T");; 

let NOT =
	new_definition
	 (`NOT`,
	  "NOT (b:*->bool) = \s. ~(b s)");;

let OR =
	new_infix_definition
	 (`OR`,
	  "!b b':* -> bool. OR b b' = \s. b s \/ b' s");; 

let AND =
	new_infix_definition
	 (`AND`,
	  "!b b':*->bool. AND b b' = \s. b s /\ b' s");; 

let IMPLIES =
	new_infix_definition
	 (`IMPLIES`,
	  "!b b':*->bool. IMPLIES b b' = \s. (b s) ==> (b' s)");; 

let  EWR = new_definition (
	`EWR`,
	"!p:*->bool. EWR p = !t.p t"
);;  
 
let  SW = new_definition (
	`SW`,
	"!p:*->bool. SW p = ?t.p t"
);;

let PRED_AND_OVER_FORALL = prove_thm
(	`PRED_AND_OVER_FORALL`,
	"!P Q:*->bool. (!s.P s /\ Q s) = (!s.P s) /\ (!s.Q s)",
	REPEAT GEN_TAC
	THEN EQ_TAC
	THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
);;

%
| Predicates on program states, quantifying over program
| variables
%

let bnd = new_definition 
(	`bnd`,
	"!x:tok.!s:state.!value:num.
	 bnd value x s = \z.(z=x) => value | s z"
);;


let forevery = new_definition
(	`forevery`,
	"!P. forevery x P = \s.!val. P(bnd val x s)"
);;

let forsome = new_definition
(	`forsome`,
	"!P. forsome x P = \s.?val. P(bnd val x s)"
);;

%
| Substitution of an expression for a variable in a predicate
%

let subs = new_definition
(	`subs`,
	"!exp x.!P:state->bool. subs exp x P = \s:state.P(bnd (exp s) x s)"
);;

close_theory ();;
