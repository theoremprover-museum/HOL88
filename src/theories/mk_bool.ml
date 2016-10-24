%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_bool.ml                                            %
%                                                                             %
%     DESCRIPTION:      Definition of HOL (Higher-Order Logic) in PPLAMBDA.   %
%                       HOL only has terms - formulae are not a separate type %
%                       but just boolean terms. Load into hol-lcf after       %
%                       deleting bool.th.                                     %
%                                                                             %
%                       We represent an HOL theorem:                          %
%                                                                             %
%                         t1, ... ,tn |- t                                    %
%                                                                             %
%                       as the PPLAMBDA theorem:                              %
%                                                                             %
%                         HOL_ASSERT(t1), ... ,HOL_ASSERT(tn) |- HOL_ASSERT(t)%
%                                                                             %
%                       where HOL_ASSERT is a predicate of type ":bool".      %
%                                                                             %
%                       We provide conventional syntactic sugar for various   %
%                       terms of HOL. The parser translates as follows:       %
%                                                                             %
%                         "!x.t"        --> "!(\x.t)"                         %
%                         "?x.t"        --> "?(\x.t)"                         %
%                         "@x.t"        --> "@(\x.t)"                         %
%                         "t1 /\ t2"    --> "/\ t1 t2"                        %
%                         "t1 \/ t2"    --> "\/ t1 t2"                        %
%                         "t1 ==> t2"   --> "==> t1 t2"                       %
%                         "t1 <=> t2"   --> "<=> t1 t2"                       %
%                         "t1 = t2"     --> "= t1 t2"                         %
%                         "~ t"         --> "~ t"                             %
%                         "t1,t2"       --> ", t1 t2"                         %
%                         "(t=>t1|t2)"  --> "COND t t1 t2"                    %
%                                                                             %
%                       Other terms are represented by themselves. Predicates %
%                       are just functions with types of the form ":ty->bool".%
%                                                                             %
%                       Note that the only reason we need the translation     %
%                       given above is to provide a nicer syntax. Thus, for   %
%                       example, instead of:                                  %
%                                                                             %
%                         "!x.?y. P(x,y)"                                     %
%                                                                             %
%                       we could use:                                         %
%                                                                             %
%                         "!(\x. ?(\y. P(x,y)))"                              %
%                                                                             %
%                       In HOL things like "P(x, !x.Q x)" are allowed. This   %
%                       would be represented in PPLAMBDA by the formula:      %
%                                                                             %
%                         "HOL_ASSERT(P(x, !(\x.Q x)))"                       %
%                                                                             %
%                       The function Q would have to be a predicate (i.e.     %
%                       have a type of the form ":ty->bool") for this to      %
%                       typecheck.                                            %
%                                                                             %
%                       Other syntactic sugar is:                             %
%                                                                             %
%                         "let x=t1 in t2"  --> "LET (\x.t2) t1"              %
%                                                                             %
%                         "\(x,y).t"        --> "UNCURRY \x.\y.t"             %
%                                                                             %
%                         "\(x1,x2,...xn).t" --> "UNCURRY \x1.\(x2,...,xn).t" %
%                                                                             %
%                       and in HOL88 (MJCG 26/1/89):                          %
%                                                                             %
%                         "let f v1 ... vn = t1 in t2"                        %
%                                --> "LET (\f.t2) (\v1 ... vn.t1)"            %
%                                                                             %
%                         "let (x1,...,xn) = t1 in t2"                        %
%                                --> "LET (\(x1,...,xn).t2) t1"               %
%                                                                             %
%                        "let x1=t1 and ... and xn=tn in t"                   %
%                                --> "LET ( ... (LET(LET (\x1...xn.t)         %
%                                                        t1)t2) ... ) tn"     %
%                                                                             %
%     PARENTS:          PPLAMB.th                                             %
%     WRITES FILES:     bool.th                                               %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

new_theory `bool`;;

new_parent `PPLAMB`;;

paired_new_type(0, `bool`);;

new_infix(`=`, ":*->*->bool");;

new_predicate(`HOL_ASSERT`, ":bool");;

% The axiom below is a a hack to create an arbitrary theorem 	%
% for use in the file ml/hol-syn.ml 				%

new_open_axiom(`ARB_THM`, "HOL_ASSERT(($=:*->*->bool) = ($=:*->*->bool))");;

% loads HOL parser and printer for inputting axioms		%
loadt (concat ml_dir_pathname `hol-in-out`);;   

new_infix(`==>` , ":bool->bool->bool");;

new_predicate(`BINDERS`, ":*");;  %Hack for storing binders%

new_predicate(`HOL_DEFINITION`, ":bool");;

new_binder(`@` , ":(*->bool)->*");;

% Definitions 							%

% MJCG for HOL88:
  Type of x changed to ":bool" to prevent unbound free type variable %


% Very temporary hack to get the system to build whilst MJCG thinks
  about definitions. ? declared as a constant
%

% new_constant changed to new_binder [TFM 92.01.12]			%
% new_constant(`?`, ":(*->bool)->bool");;				%
new_binder(`?`, ":(*->bool)->bool");;

new_definition(`T_DEF`, "T = ((\x:bool.x) = (\x:bool.x))");;

lisp`(remprop forall-tok 'syn-const)`;; % make ! parse as a variable %

new_binder_definition(`FORALL_DEF` , "$! = \P:*->bool. P=(\x.T)");;

% Very temporary hack to get the system to build whilst MJCG thinks
  about definitions. Old code below commented out and replaced by
  a mk_thm horror.

lisp`(remprop exists-tok 'syn-const)`;;  make ? parse as a variable 

new_binder_definition(`EXISTS_DEF` , "$? = \P:*->bool. P($@ P)");;
%

store_definition(`EXISTS_DEF` , "$? = \P:*->bool. P($@ P)");;

lisp`(remprop conj-tok 'syn-const)`;; % make /\ parse as a variable %

new_infix_definition(`AND_DEF` , "$/\ = \t1 t2.!t. (t1==>t2==>t)==>t");;

lisp`(remprop disj-tok 'syn-const)`;; % make \/ parse as a variable %

new_infix_definition(`OR_DEF` , "$\/ = \t1 t2.!t. (t1==>t)==>(t2==>t)==>t");;



% --------------------------------------------------------------------- %
% IFF deleted: boolean = can be used instead.		 [TFM 91.01.20]	%
%									%
% lisp`(remprop iff-tok 'syn-const)`;;  make <=> parse as a variable    %
% new_infix_definition(`IFF_DEF` ,					%
%   "$<=> = \t1 t2. (t1==>t2)/\(t2==>t1)");;				%
% --------------------------------------------------------------------- %

new_definition(`F_DEF` , "F = !t.t");;

lisp`(remprop neg-tok 'syn-const)`;; % make ~ parse as a variable %

new_definition(`NOT_DEF` , "$~ = \t. t ==> F");;

lisp`(remprop '|?!| 'syn-const)`;; % make ?! parse as a variable %

new_binder_definition
 (`EXISTS_UNIQUE_DEF`,
  "$?! = \P:(*->bool). ($? P) /\ (!x y. ((P x) /\ (P y)) ==> (x=y))");;

new_definition(`LET_DEF` , "LET = \f:*->**.\x:*. f x");;

new_definition
 (`COND_DEF` , "COND = \t t1 t2.@x:*.((t=T)==>(x=t1))/\((t=F)==>(x=t2))");;

% --------------------------------------------------------------------- %
% Definitions to support restricted abstractions and quantifications    %
% --------------------------------------------------------------------- %

new_definition
 (`RES_FORALL`, "RES_FORALL P B = !x:*. P x ==> B x");;

new_definition
 (`RES_EXISTS`, "RES_EXISTS P B = ?x:*. P x /\ B x");;

new_definition
 (`RES_SELECT`, "RES_SELECT P B = @x:*. P x /\ B x");;

new_definition
 (`ARB`, "ARB = @x:*.T");;

new_definition
 (`RES_ABSTRACT`, "RES_ABSTRACT P B = \x:*. (P x => B x | ARB:**)");;


% --------------------------------------------------------------------- %
% Relic from LCF_LSM. Deleted.			         [TFM 91.01.20]	%
% new_definition							%
% (`FCOND_DEF` ,							%
%   "FCOND = \f.\f1:*->**.\f2:*->**.\x. COND(f x)(f1 x)(f2 x)");;	%
% --------------------------------------------------------------------- %

new_definition
 (`ONE_ONE_DEF`, "ONE_ONE(f:*->**) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)");;

new_definition
 (`ONTO_DEF`, "ONTO(f:*->**) = !y.?x. y = f x");;

% Having "o" as a constant precludes it being used as a variable
  (e.g. for outputs)
  new_infix_definition
    (`o_DEF`, "$o (f:**->***) (g:*->**) x = f(g x)");;
%

% AXIOMS %

map
 new_axiom
 [`BOOL_CASES_AX`  , "!t:bool. (t=T) \/ (t=F)";
  `IMP_ANTISYM_AX` , "!t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 = t2)";
  `ETA_AX`         , "!t:*->**. (\x. t x) = t";
  `SELECT_AX`      , "!P:*->bool.!x. P x ==> P($@ P)"];;

% --------------------------------------------------------------------- %
% version of ==> for coding assumptions of theorems for storing in theories %
% DELETED: TFM 90.12.01							%
% RESTORED: TFM 90.04.27						%

new_infix_definition
 (`IS_ASSUMPTION_OF`,
  "!t1 t2. $IS_ASSUMPTION_OF t1 t2 = (t1 ==> t2)");;

% Now we set up the theory of pairs. Unfortunately we have to include
  pairs in the theory bool because new_theory and close_theory use
  pairing for writing out lists of binders %

new_definition
 (`TYPE_DEFINITION`,
  "TYPE_DEFINITION (P:*->bool) (rep:**->*) =
       (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\	
                 (!x. P x = (?x'. x = rep x'))");;

% Definitions of abbrev_ty_def and new_type_definition used to be	%
% inserted here, but are no longer needed here (TFM 90.04.10)    	%

let MK_PAIR_DEF =
 new_definition(`MK_PAIR_DEF`, "MK_PAIR(x:*)(y:**) = \a b.(a=x)/\(b=y)");;

let IS_PAIR_DEF =
 new_definition(`IS_PAIR_DEF`, "IS_PAIR p = ?x:*.?y:**. p = MK_PAIR x y");;

% We now load in theorem proving infrastructure (that was not already loaded
  via ml/hol-in-out.ml) as we need to prove that:

     |- ?p:*->**->bool. IS_PAIR p

lisp (concat (concat `(load "` lisp_dir_pathname) `genmacs")`);;

loadt (concat ml_dir_pathname `hol-rules`);;
loadt (concat ml_dir_pathname `hol-drules`);;
loadt (concat ml_dir_pathname `drul`);;
loadt (concat ml_dir_pathname `hol-thyfns`);;
loadt (concat ml_dir_pathname `tacticals`);;
loadt (concat ml_dir_pathname `tacont`);;
loadt (concat ml_dir_pathname `tactics`);;
loadt (concat ml_dir_pathname `conv`);;
loadt (concat ml_dir_pathname `hol-net`);;
loadt (concat ml_dir_pathname `rewrite`);;
loadt (concat ml_dir_pathname `resolve`);;
loadt (concat ml_dir_pathname `goals`);;
loadt (concat ml_dir_pathname `stack`);;

let PAIR_EXISTS =
 prove_thm
  (`PAIR_EXISTS`,
   "?p:*->**->bool. IS_PAIR p",
   EXISTS_TAC "MK_PAIR (x:*) (y:**)"
    THEN REWRITE_TAC[MK_PAIR;IS_PAIR]
    THEN EXISTS_TAC "x:*"
    THEN EXISTS_TAC "y:**"
    THEN REWRITE_TAC[]);;
%

% Since the theorem proving infrastructure won't load (because "arb"
  gets bound into various things rather than "F") the following expedient
  is resorted to. I am working on cleaning this up ... %

% save_open_thm renamed to save_thm [TFM 90.12.01]			%

let PAIR_EXISTS =
 save_thm(`PAIR_EXISTS`,mk_thm([], "?p:*->**->bool. IS_PAIR p"));;


new_type_definition
 (`prod`, "IS_PAIR:(*->**->bool)->bool", PAIR_EXISTS);;

% Added TFM 88.03.31							%
%									%
% needs to be added because new_type_definition now does not define 	%
% REP_prod.								%
new_definition
  (`REP_prod`,
   "REP_prod  = 
     @rep:(*,**)prod->(*->**->bool). 
           (!p' p''. (rep p' = rep p'') ==> (p' = p'')) /\ 
           (!p. IS_PAIR (p:*->**->bool)  = (?p'. p = rep p'))");;

lisp`(remprop pair-tok 'syn-const)`;; % make , parse as a variable %

new_infix_definition
 (`COMMA_DEF`, "$, (x:*) (y:**) = @p. REP_prod p = MK_PAIR x y");;

new_definition
 (`FST_DEF`, "FST(p:(*,**)prod) = @x.?y. MK_PAIR x y = REP_prod p");;

new_definition
 (`SND_DEF`, "SND(p:(*,**)prod) = @y.?x. MK_PAIR x y = REP_prod p");;

% --------------------------------------------------------------------- %
% The following can be proved, but out of laziness we make them axioms  %
% save_open_thm renamed to save_thm [TFM 90.12.01]			%
% --------------------------------------------------------------------- %
map 
 (\(tok,t). save_thm(tok, mk_thm([],t)))
 [`PAIR`  , "!x:*#**. (FST x, SND x) = x";
  `FST`   , "!x:*.!y:**. FST(x,y) = x";
  `SND`   , "!x:*.!y:**. SND(x,y) = y"];;

% The following theorem follows from the above "axioms" for pairs,	%
% but it's not clear exactly where it ought to be proved.  So it's	%
% added here as an axiom.  The proof is:		        	%
%									%
% let PAIR_EQ = 							%
%    prove_thm 								%
%    (`PAIR_EQ`,							%
%     "(x:*,(y:**) = a,b) = ((x=a) /\ (y=b))",				%
%     EQ_TAC THENL							%
%     [DISCH_THEN \th. 							%
%      REWRITE_TAC [REWRITE_RULE [FST] (AP_TERM "FST:*#**->*" th);	%
%	          REWRITE_RULE [SND] (AP_TERM "SND:*#**->**" th)];	%
%      STRIP_TAC THEN ASM_REWRITE_TAC[]]);;				%
%									%
% But, of course, a proof can't be run here since tactics etc are not	%
% yet defined.  The whole "pairs" problem (i.e. when to define them)    %
% needs to be reconsidered.  I have a sound definitional theory of 	%
% pairs that can be added when this is done (TFM 88.03.31)		%
%									%
% Meanwhile, we just add a theorem.					%
% 									%
% save_open_thm renamed to save_thm [TFM 90.12.01]			%
% --------------------------------------------------------------------- %

let PAIR_EQ = 
    save_thm
    (`PAIR_EQ`,
      (mk_thm([],"!x y a b.(x:*,(y:**) = a,b) = ((x=a) /\ (y=b))")));;

% UNCURRY is needed for terms of the form "\(x,y).t" (see above) %

new_definition
 (`UNCURRY_DEF`, "UNCURRY(f:* -> **->***)(x,y) = f x y");;

new_definition
 (`CURRY_DEF`, "CURRY (f:*#** -> ***) x y = f(x,y)");;

close_theory();;

quit();;

