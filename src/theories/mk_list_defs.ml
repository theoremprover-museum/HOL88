%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_list_defs.ml                                       %
%                                                                             %
%     DESCRIPTION:      Extends the theory list.th with some definitions of   %
%                       funstions on lists.                                   %
%                       Some of the definitions was in the file               %
%                       mk_list_thms.ml which contains only theorems now.     %
%                                                                             %
%     AUTHORS:          T. F. Melham (86.11.24 for the original definitions)  %
%                       W. Wong (2 Jan 94 for new definitons)                 %
%                                                                             %
%     WRITES FILES:     list.th                                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1987                                     %
%                       W. Wong 1994                                          %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% --------------------------------------------------------------------- %
% Reopen the theory							%
% --------------------------------------------------------------------- %
extend_theory `list`;;
new_parent `combin`;;

% --------------------------------------------------------------------- %
% fetch the axiom for lists.						%
% --------------------------------------------------------------------- %
let list_Axiom = theorem `list` `list_Axiom`;;

let num_Axiom = theorem `prim_rec` `num_Axiom`;;
let PRE = theorem `prim_rec` `PRE`;;

let UNCURRY_DEF = definition `bool` `UNCURRY_DEF`;;
let o_DEF = definition `combin` `o_DEF`;;

%<
% --------------------------------------------------------------------- %
% Fetch a few theorems from num.th					%
% --------------------------------------------------------------------- %
let NOT_SUC = theorem `num` `NOT_SUC`;;
let INV_SUC = theorem `num` `INV_SUC`;;

% --------------------------------------------------------------------- %
% Fetch a few theorems from prim_rec.th					%
% --------------------------------------------------------------------- %
let num_Axiom = theorem `prim_rec` `num_Axiom`;;
let NOT_LESS_0 = theorem `prim_rec` `NOT_LESS_0`;;
let LESS_0 = theorem `prim_rec` `LESS_0`;;
let LESS_MONO = theorem `prim_rec` `LESS_MONO`;;
let INV_SUC_EQ = theorem `prim_rec` `INV_SUC_EQ`;;

% --------------------------------------------------------------------- %
% Fetch a few things from arithmetic.th					%
% --------------------------------------------------------------------- %
let ADD_CLAUSES = theorem `arithmetic` `ADD_CLAUSES`;;
let LESS_MONO_EQ = theorem `arithmetic` `LESS_MONO_EQ`;;
let ADD_EQ_0 = theorem `arithmetic` `ADD_EQ_0`;;
let SUC_NOT = theorem `arithmetic` `SUC_NOT`;; % WW %
>%
% --------------------------------------------------------------------- %
% We need to load in the induction tactic.  It's in ml/ind.ml, but it	%
% is part of hol rather than basic hol. So it's loaded in uncompiled 	%
% (because it may not have been recompiled since basic-hol was last	%
% rebuilt. 						 [TFM 88.04.02] %
% --------------------------------------------------------------------- %

loadt (concat ml_dir_pathname `ind.ml`);;

% --------------------------------------------------------------------- %
% Create an induction tactic for :num					%
% --------------------------------------------------------------------- %
let INDUCT_TAC = INDUCT_THEN (theorem `num` `INDUCTION`) ASSUME_TAC;;

% --------------------------------------------------------------------- %
% Load the code for primitive recursive definitions on arbitrary types.	%
% 									%
% Note that prim_rec_ml.o must be recompiled if basic-hol has been	%
% rebuilt. The uncompiled version is therefore loaded here.        	%
%									%
% TFM 88.04.02								%
% --------------------------------------------------------------------- %
loadt (concat ml_dir_pathname `prim_rec.ml`);;

% --------------------------------------------------------------------- %
% Load the auxiliary code for recursive types.				%
% NOTE: uses things defined in prim_rec.ml (load uncompiled)		%
% --------------------------------------------------------------------- %
loadt (concat ml_dir_pathname `tyfns.ml`);;

let LIST_INDUCT_TAC  = 
    let list_INDUCT = prove_induction_thm list_Axiom in
        INDUCT_THEN list_INDUCT ASSUME_TAC;;

loadt (concat ml_dir_pathname `numconv.ml`);;

% ---------------------------------------------------------------------	%
% Definitions of NULL, HD and TL.					%
% --------------------------------------------------------------------- %

let NULL_DEF = 
    new_recursive_definition false list_Axiom `NULL_DEF`
      "(NULL NIL = T) /\ (NULL (CONS (h:*) t) = F)";;

let HD = 
    new_recursive_definition false list_Axiom `HD`
      "(HD (CONS (h:*) t) = h)";;

let TL = 
    new_recursive_definition false list_Axiom `TL`
      "(TL (CONS (h:*) t) = t)";;

let new_list_rec_definition = 
        \(name,tm). new_recursive_definition false list_Axiom name tm;;

%----------------------------------------------------------------%
%- Alternative list constructor---adding element to the tail end-%
%----------------------------------------------------------------%

let SNOC = new_list_rec_definition (`SNOC`,
 "(SNOC (x:*) ([]:(*)list) = [x]) /\
  (SNOC x (CONS x' l) = CONS x' (SNOC x l))");;

%----------------------------------------------------------------%
%- Reductions	    	    	    				-%
%- Spec:    	    	    	    				-%
%-	FOLDR f [x0;x1;...;xn-1] e = f(x0,f(x1,...f(xn-1,e)...))-%
%-	FOLDL f e [x0;x1;...;xn-1] = f(...f(f(e,x0),x1),...xn-1)-%
%----------------------------------------------------------------%
let FOLDR = new_list_rec_definition(`FOLDR`,
    "(FOLDR (f:*->**->**) e [] = e) /\
     (FOLDR f e (CONS x l) = f x (FOLDR f e l))");;

let FOLDL = new_list_rec_definition(`FOLDL`,
    "(FOLDL (f:**->*->**) e [] = e) /\
     (FOLDL f e (CONS x l) = FOLDL f (f e x) l)");;

%----------------------------------------------------------------%
%- Fitler   	    	    	    				-%
%- Spec:    	    	    	    				-%
%- 	FILTER P [x0; ...; xn-1] = [...;xi;...]			-%
%- 	  where P xi holds for all xi in the resulting list	-%
%----------------------------------------------------------------%
let FILTER = new_list_rec_definition(`FILTER`,
    "(!P. FILTER P [] = []) /\
     (!(P:*->bool) x l. FILTER P (CONS x l) =
	(P x => CONS x (FILTER P l) | FILTER P l))");;

%----------------------------------------------------------------%
%- Cumulation 	    	    	    				-%
%- Spec:    	    	    	    				-%
%- 	SCANL * e [x0;x1;...xn] =   				-%
%- 	 [e; e * x0; (e * x0) * x1; ...; (e * x0)* ... * xn]    -%
%- 	SCANR * e [x0;x1;...xn] =   				-%
%- 	 [x0 * ... * (xn * e); ...; xn-1 * (xn * e); xn * e; e] -%
%----------------------------------------------------------------%
let SCANL = new_list_rec_definition(`SCANL`,
    "(SCANL (f:**->*->**) e [] = [e]) /\
     (SCANL f e (CONS x l) = CONS e (SCANL f (f e x) l))");;

let SCANR = new_list_rec_definition(`SCANR`,
    "(SCANR (f:*->**->**) e [] = [e]) /\
     (SCANR (f:*->**->**) e (CONS x l) =
      CONS (f x (HD (SCANR f e l))) (SCANR f e l))");;


%================================================================%
%- Derived Functions	    	    				-%
%================================================================%

%----------------------------------------------------------------%
%- Reverse  	    	    	    				-%
%----------------------------------------------------------------%
let REVERSE = new_list_rec_definition (`REVERSE`,
 "(REVERSE [] = []) /\
  (REVERSE (CONS (x:*) l) = SNOC x (REVERSE l))");;

%----------------------------------------------------------------%
%- Concatenation of two lists 	    				-%
%- Spec:    	    	    	    				-%
%-   APPEND [x0;...;xn-1] [x'0;...;x'm-1] =			-%
%-  	 [x0;...;xn-1;x'0;...;x'm-1] 				-%
%----------------------------------------------------------------%
let APPEND = 
    new_recursive_definition false list_Axiom `APPEND`
      "(!l. APPEND NIL l = (l:(*)list)) /\
       (!l1 l2 h. APPEND (CONS h l1) l2 = CONS h (APPEND l1 l2))";;

%----------------------------------------------------------------%
%- Concatenation of a list of lists   				-%
%- Spec:    	    	    	    				-%
%-	FLAT [[x00;...;x0n-1];...;[xp-10;...;xp-1n-1]] =	-%
%-		[x00;...;x0n-1;...;xp-10;...;xp-1n-1]		-%
%----------------------------------------------------------------%
let FLAT = 
    new_recursive_definition false list_Axiom `FLAT`
      "(FLAT NIL = NIL:(*)list) /\
       (!h t. FLAT (CONS h t) = APPEND h (FLAT t))";;

%----------------------------------------------------------------%
%- Concatenation of a list of lists   				-%
%- Spec:    	    	    	    				-%
%-  LENGTH [x0;...;xn-1] = n	    				-%
%----------------------------------------------------------------%
let LENGTH = 
    new_recursive_definition false list_Axiom `LENGTH`
     "(LENGTH NIL = 0) /\
      (!h:*. !t. LENGTH (CONS h t) = SUC (LENGTH t))";;

%----------------------------------------------------------------%
%- Apply a function to all elements of a list 			-%
%- Spec:    	    	    	    				-%
%-  MAP f [x0;...;xn-1] = [f x0;...; f xn-1]			-%
%----------------------------------------------------------------%
let MAP = 
    new_recursive_definition false list_Axiom `MAP`
      "(!f. MAP f NIL = NIL) /\
       (!f h t. MAP f (CONS (h:*) t) = CONS (f h:**) (MAP f t))";;

% --------------------------------------------------------------------- %
% Definition of a function 						%
%									%
%   MAP2 : (*->**->***) -> (*)list -> (**)list -> (***)list		%
% 									%
% for mapping a curried binary function down a pair of lists:		%
% 									%
% |- (!f. MAP2 f[][] = []) /\						%
%    (!f h1 t1 h2 t2.							%
%      MAP2 f(CONS h1 t1)(CONS h2 t2) = CONS(f h1 h2)(MAP2 f t1 t2))	%
% 									%
% [TFM 92.04.21]							%
% --------------------------------------------------------------------- %

let MAP2 =
    let lemma =
        PROVE
        ("?fn. 
          (!f:*->**->***. fn f [] [] = []) /\
          (!f h1 t1 h2 t2.
            fn f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (fn f t1 t2))",
         let th = prove_rec_fn_exists list_Axiom
             "(fn (f:*->**->***) [] l = []) /\
              (fn f (CONS h t) l = CONS (f h (HD l)) (fn f t (TL l)))" in
         STRIP_ASSUME_TAC th THEN
         EXISTS_TAC "fn:(*->**->***)->(*)list->(**)list->(***)list" THEN
         ASM_REWRITE_TAC [HD;TL]) in
     new_specification `MAP2` [`constant`,`MAP2`] lemma;;


% changed to ALL_EL
let EVERY_DEF = 
    new_recursive_definition false list_Axiom `EVERY_DEF`
      "(!P:*->bool. EVERY P NIL = T)  /\
       (!P h t. EVERY P (CONS h t) = (P(h) /\ EVERY P t))";; %

%----------------------------------------------------------------%
%- Predicates	    	    	    				-%
%- Spec:    	    	    	    				-%
%-   ALL_EL P [x0;...;xn-1] = T, iff P xi = T for i=0,...,n-1   -%
%- 			      F, otherwise			-%
%----------------------------------------------------------------%
let ALL_EL = new_list_rec_definition(`ALL_EL`,
    "(!P. ALL_EL P [] = T) /\
     (!(P:*->bool) x l. ALL_EL P (CONS x l) = P x /\ (ALL_EL P l))");;

%----------------------------------------------------------------%
%- Spec:    	    	    	    				-%
%-   SOME_EL P [x0;...;xn-1] = T, iff P xi = T for some i       -%
%-			       F, otherwise			-%
%----------------------------------------------------------------%
let SOME_EL = new_list_rec_definition(`SOME_EL`,
    "(!P. SOME_EL P [] = F) /\
     (!(P:*->bool) x l. SOME_EL P (CONS x l) = P x \/ (SOME_EL P l))");;

%----------------------------------------------------------------%
%- Spec:    	    	    	    				-%
%-   IS_EL x [x0;...;xn-1] = T, iff ?xi. x = xi for i=0,...,n-1 -%
%-  	    	    	      F, otherwise			-%
%----------------------------------------------------------------%
let IS_EL_DEF = new_definition(`IS_EL_DEF`,
    "!(x:*) l. IS_EL x l = SOME_EL ($= x) l");;

let AND_EL_DEF = new_definition(`AND_EL_DEF`,
    "AND_EL = ALL_EL I");;

let OR_EL_DEF = new_definition(`OR_EL_DEF`,
    "OR_EL = SOME_EL I");;

%----------------------------------------------------------------%
%- Segments 	    	    	    				-%
%- Spec:    	    	    	    				-%
%-	FIRSTN m [x0;...;xn-1] = [x0;...;xm-1]			-%
%-	BUTFIRSTN m [x0;...;xn-1] = [xm;...;xn-1]		-%
%-	LASTN m [x0;...;xn-1] = [xn-m;...;xn-1]			-%
%-	BUTLASTN m [x0;...;xn-1] = [x0;...;xn-m]		-%
%-	BUTLAST [x0;...;xn-1] = [x0;...;xn-2]			-%
%-	LAST [x0;...;xn-1] = [xn-1] 				-%
%----------------------------------------------------------------%
let FIRSTN =
    let thm1 = prove_rec_fn_exists num_Axiom
    	"(firstn 0 (l:* list) = []) /\
         (firstn (SUC k) l = CONS (HD l) (firstn k (TL l)))" in
    let thm = PROVE(
       "?firstn. (!l:* list. firstn 0 l = []) /\
         (!n x (l:* list). firstn (SUC n) (CONS x l) = CONS x (firstn n l))",
    	STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC "firstn:num->(*)list->(*)list"
    	THEN ASM_REWRITE_TAC[HD;TL]) in
    new_specification `FIRSTN` [`constant`,`FIRSTN`] thm;;

let BUTFIRSTN =
    let thm2 = prove_rec_fn_exists num_Axiom
    	"(butfirstn 0 (l:* list) = l) /\
         (butfirstn (SUC k) l = butfirstn k (TL l))" in
    let thm = PROVE(
       "?butfirstn. (!l:* list. butfirstn 0 l = l) /\
         (!n x (l:* list). butfirstn (SUC n) (CONS x l) = butfirstn n l)",
    	STRIP_ASSUME_TAC thm2 THEN EXISTS_TAC "butfirstn:num->(*)list->(*)list"
    	THEN ASM_REWRITE_TAC[HD;TL]) in
    new_specification `BUTFIRSTN` [`constant`,`BUTFIRSTN`] thm;;

%----------------------------------------------------------------%
%- Segment  	    	    	    				-%
%- Spec:    	    	    	    				-%
%- 	SEG m k [x0;...xk;...xk+m-1;...;xn] = [xk;...;xk+m-1]   -%
%----------------------------------------------------------------%
let SEG = 
    let SEG_exists = PROVE(
    "?SEG. (!k (l:* list). SEG 0 k l = []) /\
       (!m x l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
       (!m k x l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)",
    EXISTS_TAC "\m k (l:* list). (FIRSTN:num -> * list -> * list) m
    	((BUTFIRSTN:num -> * list -> * list) k l)"
    THEN BETA_TAC THEN REWRITE_TAC[FIRSTN;BUTFIRSTN]) in
    new_specification `SEG` [(`constant`,`SEG`)] SEG_exists;;

%----------------------------------------------------------------%
%- LAST and BUTLAST is analogous to HD and TL at the end of list-%
%----------------------------------------------------------------%
let LAST_DEF = new_definition(`LAST_DEF`,
    "!l:* list. LAST l = HD (SEG 1 (PRE(LENGTH l)) l)");;

let BUTLAST_DEF = new_definition(`BUTLAST_DEF`,
    "!l:* list. BUTLAST l = SEG (PRE(LENGTH l)) 0 l");;

let LENGTH_SNOC = PROVE(
    "!(x:*) l. LENGTH (SNOC x l) = SUC (LENGTH l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;SNOC]);;

let LAST =     % "!(x:*) l. LAST (SNOC x l) = x", %
    let lem = PROVE(
    "!x (l:* list).  (SEG 1 (PRE(LENGTH (SNOC x l))) (SNOC x l)) = [x]",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[SNOC;SEG]
    THEN FIRST_ASSUM ACCEPT_TAC) in
    GEN_ALL(REWRITE_RULE[lem;HD](SPEC "SNOC (x:*) l" LAST_DEF));;

let BUTLAST =     % "!x l. BUTLAST (SNOC x l) = l", %
    let lem = PROVE(
    "!x:*. !l. SEG (PRE(LENGTH (SNOC x l))) 0 (SNOC x l) = l",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN ASM_REWRITE_TAC[SNOC;SEG]) in
    GEN_ALL(REWRITE_RULE[lem](SPEC "SNOC (x:*) l" BUTLAST_DEF));;

let LASTN =
    let thm1 = prove_rec_fn_exists num_Axiom
        "(lastn 0 (l:(*)list) = []) /\
    	 (lastn (SUC n) l = SNOC (LAST l) (lastn n (BUTLAST l)))" in
    let thm = PROVE(
    	"?lastn. (!l:* list. lastn 0 l = []) /\
    	 (!n (x:*) l. lastn (SUC n) (SNOC x l) = SNOC x (lastn n l))",
    	STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC "lastn:num->(*)list->(*)list"
    	THEN ASM_REWRITE_TAC[LAST;BUTLAST]) in
    new_specification `LASTN` [`constant`,`LASTN`] thm;;

let BUTLASTN = 
    let thm1 = prove_rec_fn_exists num_Axiom
    	"(butlastn 0 l = (l:(*)list)) /\
         (butlastn (SUC n) l = butlastn n (BUTLAST l))" in
    let thm = PROVE(
    	"?butlastn. (!l:* list. butlastn 0 l = l) /\
    	 (!n (x:*) l. butlastn (SUC n) (SNOC x l) = butlastn n l)",
    	STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC "butlastn:num->(*)list->(*)list"
    	THEN ASM_REWRITE_TAC[BUTLAST]) in
    new_specification `BUTLASTN` [`constant`,`BUTLASTN`] thm;;

%----------------------------------------------------------------%
%- Index of elements	    	    				-%
%- Spec:    	    	    	    				-%
%-	EL k [x0;...xk;...;xn-1] = xk				-%
%-	ELL k [xn-1;...xk;...;x0] = xk				-%
%----------------------------------------------------------------%
let EL = 
    new_recursive_definition false num_Axiom `EL`
      "(!l. EL 0 l = (HD l:*)) /\ 
       (!l:(*)list. !n. EL (SUC n) l = EL n (TL l))";; 

let ELL = new_recursive_definition false num_Axiom `ELL`
    "(!l:* list. ELL 0 (l:* list) = LAST l) /\
     (!l:* list. ELL (SUC n) l = ELL n (BUTLAST l))";;

%----------------------------------------------------------------%
%- Predicates between lists 	    				-%
%- Spec:    	    	    	    				-%
%-	IS_PREFIX l1 l2 = T, iff ?l. l1 = APPEND l2 l		-%
%-	IS_SUFFIX l1 l2 = T, iff ?l. l1 = APPEND l l2		-%
%-	IS_SUBLIST l1 l2 = T, 	    				-%
%-  	    	    iff ?l l'. l1 = APPEND l (APPEND l2 l')	-%
%-  	    	    	    	    				-%
%-	SPLITP P [x0;...xk;...;xn-1] =				-%
%-  	     ([x0;...;x(k-1)],[xk;...;xn-1])			-%
%-		where P xi = F for all i < k and P xk = T	-%
%-  	    	    	    	    				-%
%-	PREFIX P [x0;...xk;...;xn-1] = [x0;...xk-1]		-%
%-		where P xk = F and P xi = T for i = 0,...,k-1	-%
%-	SUFFIX P [x0;...xk;...;xn-1] = [xk+1;...xn-1]		-%
%-		where P xk = F and P xi = T for i = k+1,...,n-1 -%
%----------------------------------------------------------------%

let IS_PREFIX =
    let lemma = PROVE(
       "?fn. (!l:* list. fn l [] = T) /\
    	(!x (l:* list). fn [] (CONS x l) = F) /\
        (!(x1:*) l1 (x2:*) l2. fn (CONS x1 l1) (CONS x2 l2) =
	    (x1 = x2) /\ (fn l1 l2))",
        let th = prove_rec_fn_exists list_Axiom
    	    "(fn l [] = T) /\
    	     (fn (l:* list) (CONS x t) = 
    	    	(NULL l) => F | (((HD l) = x) /\ (fn (TL l) t)))" in
    	STRIP_ASSUME_TAC th THEN EXISTS_TAC "fn:* list -> * list -> bool"
    	THEN ASM_REWRITE_TAC[HD;TL;NULL_DEF]) in
    new_specification `IS_PREFIX` [(`constant`,`IS_PREFIX`)] lemma;;

%---------------------------------------------------------------%

let REVERSE_SNOC = PROVE("!(x:*) l. REVERSE (SNOC x l) = CONS x (REVERSE l)",
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC;REVERSE]);;

let REVERSE_REVERSE = PROVE("!l:(*)list. REVERSE (REVERSE l) = l",
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE;REVERSE_SNOC]);;

let forall_REVERSE = TAC_PROOF(([],
    "!P. (!l:(*)list. P(REVERSE l)) = (!l. P l)"),
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[REVERSE_REVERSE]
     o (SPEC "REVERSE l:(*)list"))));;

let f_REVERSE_lemma = TAC_PROOF (([],
    "!f1 f2.
    ((\x. (f1:(*)list->**) (REVERSE x)) = (\x. f2 (REVERSE x))) = (f1 = f2)"),
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL[
      POP_ASSUM (\x.ACCEPT_TAC (EXT (REWRITE_RULE[REVERSE_REVERSE]
      (GEN "x:(*)list" (BETA_RULE (AP_THM x "REVERSE (x:(*)list)"))))));
      ASM_REWRITE_TAC[]]);;

let SNOC_Axiom = PROVE(
    "!(e:**) (f:** -> (* -> ((*)list -> **))).
     ?! fn. (fn[] = e) /\ (!x l. fn(SNOC x l) = f(fn l)x l)",
    let lemma =  CONV_RULE (EXISTS_UNIQUE_CONV)
       (REWRITE_RULE[REVERSE_REVERSE] (BETA_RULE (SPECL
    	 ["e:**";"(\ft h t. f ft h (REVERSE t)):** -> (* -> ((*)list -> **))"]
        (PURE_ONCE_REWRITE_RULE
    	 [SYM (CONJUNCT1 REVERSE);
    	  PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL REVERSE_SNOC)]
    	   (BETA_RULE (SPEC "\l:(*)list.fn(CONS x l) =
    	    	       (f:** -> (* -> ((*)list -> **)))(fn l)x l"
    	     (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) forall_REVERSE)))]
    	    list_Axiom)))) in
    REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
    THEN STRIP_ASSUME_TAC lemma THEN CONJ_TAC THENL[
      EXISTS_TAC "(fn:(*)list->**) o REVERSE"
      THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN POP_ASSUM (ACCEPT_TAC o SPEC_ALL o
    	REWRITE_RULE[REVERSE_REVERSE;f_REVERSE_lemma] o
        BETA_RULE o REWRITE_RULE[o_DEF] o
        SPECL ["(fn' o REVERSE):(*)list->**";"(fn'' o REVERSE):(*)list->**"])
     ]);;

let IS_SUFFIX =
    let LENGTH_SNOC = PROVE("!(x:*) l. LENGTH (SNOC x l) = SUC (LENGTH l)",
        GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;SNOC]) in
    let NOT_NULL_SNOC = PROVE("!(x:*) l. ~NULL(SNOC x l)",
        GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC;NULL_DEF]) in
    let LAST = % "!(x:*) l. LAST (SNOC x l) = x", %
        let lem = PROVE(
    	    "!x (l:* list). (SEG 1 (PRE(LENGTH (SNOC x l))) (SNOC x l)) = [x]",
    	    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    	    THEN PURE_ONCE_REWRITE_TAC[PRE]
    	    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	    THEN LIST_INDUCT_TAC
    	    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[SNOC;SEG]
    	    THEN FIRST_ASSUM ACCEPT_TAC) in
        GEN_ALL(REWRITE_RULE[lem;HD](SPEC "SNOC (x:*) l" LAST_DEF)) in
    let BUTLAST = % "!x l. BUTLAST (SNOC x l) = l", %
        let lem = PROVE(
    	    "!x:*. !l. SEG (PRE(LENGTH (SNOC x l))) 0 (SNOC x l) = l",
    	    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    	    THEN PURE_ONCE_REWRITE_TAC[PRE] THEN LIST_INDUCT_TAC
    	    THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	    THEN ASM_REWRITE_TAC[SNOC;SEG]) in
        GEN_ALL(REWRITE_RULE[lem](SPEC "SNOC (x:*) l" BUTLAST_DEF)) in
    let lemma = PROVE(
       "?fn. (!l. fn l [] = T) /\
    	(!(x:*) l. fn [] (SNOC x l) = F) /\
    	(!(x1:*) l1 (x2:*) l2. fn (SNOC x1 l1) (SNOC x2 l2) =
	    (x1 = x2) /\ (fn l1 l2))",
    	let th = prove_rec_fn_exists SNOC_Axiom
    	    "(fn l [] = T) /\
    	     (fn l (SNOC (x:*) t) =
    	    	(NULL l) => F | ((LAST l) = x) /\ (fn (BUTLAST l) t))" in
    	STRIP_ASSUME_TAC th THEN EXISTS_TAC "fn:* list -> * list -> bool"
    	THEN ASM_REWRITE_TAC[BUTLAST;LAST;NULL_DEF;NOT_NULL_SNOC]) in
    new_specification `IS_SUFFIX` [(`constant`,`IS_SUFFIX`)] lemma;;

let IS_SUBLIST =
    let lemma = PROVE(
        "?fn. (!l:* list. fn l [] = T) /\
    	  (!(x:*) l. fn [] (CONS x l) = F) /\
          (!x1 l1 x2 l2. fn (CONS x1 l1) (CONS x2 l2) =
    	   ((x1 = x2) /\ (IS_PREFIX l1 l2)) \/ (fn l1 (CONS x2 l2)))",
    	let th = prove_rec_fn_exists list_Axiom
    	    "(fn [] (l:* list) = NULL l => T | F) /\
    	     (fn (CONS x t) l =
    	    	(NULL l) => T |
    	    	 (((x = (HD l)) /\ (IS_PREFIX t (TL l))) \/ (fn t l)))" in
    	STRIP_ASSUME_TAC th THEN EXISTS_TAC "fn:* list -> * list -> bool"
    	THEN ASM_REWRITE_TAC[HD;TL;NULL_DEF]
    	THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HD;TL;NULL_DEF]) in
    new_specification `IS_SUBLIST` [(`constant`,`IS_SUBLIST`)] lemma;;

let SPLITP = new_list_rec_definition(`SPLITP`,
    "(SPLITP P [] = ([],[])) /\
     (SPLITP P (CONS (x:*) l) =
    	P x => ([], CONS x l) |
    	       ((CONS x (FST(SPLITP P l))), (SND (SPLITP P l))))");;

let PREFIX_DEF = new_definition(`PREFIX_DEF`,
    "PREFIX P (l:* list) = FST (SPLITP ($~ o P) l)");;

let SUFFIX_DEF = new_definition(`SUFFIX_DEF`,
    "!P (l:* list). SUFFIX P l = FOLDL (\l' x. P x => SNOC x l' | []) [] l");;

%----------------------------------------------------------------%
%- List of pairs    	    	    				-%
%- Spec:    	    	    	    				-%
%-  ZIP([x0;...;xn-1],[y0;...;yn-1]) = [(x0,y0;...;(xn-1,yn-1)] -%
%-  UNZIP[(x0,y0;...;(xn-1,yn-1)]=([x0;...;xn-1],[y0;...;yn-1]) -%
%-  UNZIP_FST [(x0,y0;...;(xn-1,yn-1)] = [x0;...;xn-1]		-%
%-  UNZIP_SND [(x0,y0;...;(xn-1,yn-1)] = [y0;...;yn-1] 		-%
%----------------------------------------------------------------%
let ZIP = 
    let lemma = PROVE(
    "?ZIP. (ZIP ([],[]) = []) /\
       (!(x1:*) l1 (x2:**) l2.
	ZIP ((CONS x1 l1),(CONS x2 l2)) = CONS (x1,x2)(ZIP (l1,l2)))",
    let th = prove_rec_fn_exists list_Axiom
        "(fn [] l = []) /\
         (fn (CONS (h:*) t) (l:** list) = CONS (h, (HD l)) (fn  t (TL l)))"
        in
    STRIP_ASSUME_TAC th
    THEN EXISTS_TAC "UNCURRY (fn:(*)list -> ((**)list -> (* # **)list))"
    THEN ASM_REWRITE_TAC[UNCURRY_DEF;HD;TL]) in
    new_specification `ZIP` [(`constant`,`ZIP`)] lemma;;

let UNZIP = new_list_rec_definition(`UNZIP`,
    "(UNZIP [] = ([], [])) /\
     (UNZIP (CONS (x:* # **) l) = 
      ((CONS (FST x) (FST(UNZIP l))), (CONS (SND x) (SND(UNZIP l)))))");;

let UNZIP_FST_DEF = new_definition(`UNZIP_FST_DEF`,
    "!l:(*#**)list. UNZIP_FST l = FST(UNZIP l)");;

let UNZIP_SND_DEF = new_definition(`UNZIP_SND_DEF`,
    "!l:(*#**)list. UNZIP_SND l = SND(UNZIP l)");;

%----------------------------------------------------------------%
%- List of natural numbers    	    	    			-%
%- Spec:    	    	    	    				-%
%-  SUM [x0;...;xn-1] = x0 + ... + xn-1				-%
%----------------------------------------------------------------%
let SUM = 
    new_recursive_definition false list_Axiom `SUM`
      "(SUM NIL = 0) /\ (!h t. SUM (CONS h t) = h + (SUM t))";;

%----------------------------------------------------------------%
%- List generator    	    	    				-%
%- Spec:    	    	    	    				-%
%-  GENLIST f n = [f 0;...; f(n-1)] 				-%
%-  REPLICATE n x = [x;....;x] (n repeate elements)             -%
%----------------------------------------------------------------%
let GENLIST = new_recursive_definition false num_Axiom `GENLIST`
    "(GENLIST (f:num->*) 0 = []) /\
     (GENLIST f (SUC n) = SNOC (f n) (GENLIST f n))";;

let REPLICATE = new_recursive_definition false num_Axiom `REPLICATE`
    "(REPLICATE 0 (x:*) = []) /\
     (REPLICATE (SUC n) x = CONS x (REPLICATE n x))";;

close_theory();;

quit();;
