%============================================================================%
% Definition to support schemas.                                             %
%============================================================================%

force_new_theory `Z`;;

%----------------------------------------------------------------------------%
% Load ELIMINATE_TACS from contrib/smarttacs                                 %
%----------------------------------------------------------------------------%

load_contrib `smarttacs/ELIMINATE_TACS`;;

load_library `sets`;;
load_library `string`;;
load_library `taut`;;
load_library `reduce`;;
load_library `arith`;;

loadf `arith-tools`;;

%----------------------------------------------------------------------------%
% Rule and Tactic for simplifying terms of the form "x IN {...|...}"         %
%----------------------------------------------------------------------------%

let SET_SPEC_RULE = CONV_RULE(DEPTH_CONV SET_SPEC_CONV)
and SET_SPEC_TAC  = CONV_TAC(DEPTH_CONV SET_SPEC_CONV);;

%----------------------------------------------------------------------------%
% Some proof utilities.                                                      %
%----------------------------------------------------------------------------%

let APPLY_ASMS_TAC f =
 POP_ASSUM_LIST
  (\assums. MAP_EVERY ASSUME_TAC (rev (map f assums)));;

let REWRITE_ASMS_TAC = APPLY_ASMS_TAC o REWRITE_RULE;;

let REWRITE_ALL_TAC thl = 
 REWRITE_ASMS_TAC thl THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC thl;;

%----------------------------------------------------------------------------%
% RW_ASM_THEN ttac [f1;...;fn] f =                                           %
%  ASSUM_LIST(\thl. ttac(REWRITE_RULE[f1 thl;...;fn thl](f thl)))            %
%----------------------------------------------------------------------------%

let RW_ASM_THEN ttac fl f =
 ASSUM_LIST(\thl. ttac(REWRITE_RULE(map (\f. f thl) fl)(f thl)));;

%----------------------------------------------------------------------------%
% POP_ASSUMS n f = f[a1;...;an],                                             %
%                                                                            %
% where a1,...,an are the last n assumptions, which are popped.              %
%----------------------------------------------------------------------------%

letrec POP_ASSUMS n f =
 if n=0
 then ALL_TAC
 if n=1
 then POP_ASSUM(\th. f[th])
 else POP_ASSUM(\th. POP_ASSUMS (n-1) (\l. f (th.l)));;

letrec ITER n (tac:tactic)  = 
 if n < 0 then failwith `ITER`
 if n = 0 then ALL_TAC 
          else tac THEN ITER (n-1) tac;;

%----------------------------------------------------------------------------%
%  Resolution with filters.                                                  %
%  Code written for HOL90 by chou@cs.ucla.edu. Ported to HOL88 by MJCG.      %
%----------------------------------------------------------------------------%

let FILTER_STRIP_ASSUME_TAC (f : term -> bool) th =
  if (f (concl th)) then (STRIP_ASSUME_TAC th) else (ALL_TAC) ;;

let FILTER_IMP_RES_TAC (f : term -> bool) th g =
  IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN (FILTER_STRIP_ASSUME_TAC f)) th g
  ? ALL_TAC g ;;

let FILTER_RES_TAC (f : term -> bool) g =
  RES_THEN (REPEAT_GTCL IMP_RES_THEN (FILTER_STRIP_ASSUME_TAC f)) g
  ? ALL_TAC g ;;

let no_imp (tm) = not (free_in "==>" tm) ;;

let LITE_IMP_RES_TAC = FILTER_IMP_RES_TAC no_imp;;

%----------------------------------------------------------------------------%
% The following constants are not defined in the logic,                      %
% but are translated away by the Z preprocessor. There are declared as       %
% constants here to prevent them being defined in descendents of `Z`.        %
%----------------------------------------------------------------------------%


new_constant(`NOT`,    ":bool->bool");;

new_infix(`AND`,       ":bool->bool->bool");;
new_infix(`OR`,        ":bool->bool->bool");;
new_infix(`IMPLIES`,   ":bool->bool->bool");;

new_constant(`FORALL`, ":*->bool->bool");;
new_constant(`EXISTS`, ":*->bool->bool");;

new_constant(`SCHEMA_FORALL`, ":bool->bool->bool");;
new_constant(`SCHEMA_EXISTS`, ":bool->bool->bool");;

new_infix(`HIDE`,      ":bool->*->bool");;
new_infix(`SEQ`,       ":bool->bool->bool");;
new_constant(`DELTA`,  ":bool->bool");;
new_constant(`XI`,     ":bool->bool");;
new_constant(`theta`,  ":bool->*");;
new_constant(`pre`,    ":bool->bool");;
new_constant(`dash`,   ":bool->bool");;
new_constant(`sig`,    ":bool->bool");;
new_constant(`pred`,   ":bool->bool");;

hide_constant `S`;; %< So "S" can be used as a set variable, as in ZRM >%

load_library `sets`;;

%----------------------------------------------------------------------------%
% Some additional set theory theorems.                                       %
%----------------------------------------------------------------------------%

prove_theorem
 (`DIFF_UNION`,
  "! s t u:* set. s DIFF (t UNION u) = (s DIFF t) DIFF u",
  REPEAT STRIP_TAC
   THEN REWRITE_TAC[EXTENSION;IN_DIFF;IN_UNION]
   THEN GEN_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THEN RES_TAC);;

%----------------------------------------------------------------------------%
% Definitions for Z.                                                         %
%----------------------------------------------------------------------------%

rec_define
 list_Axiom
 "(CONJL [] = T) /\
  (CONJL(CONS b bl) = b /\ CONJL bl)";;

define "SCHEMA decs body = CONJL decs /\ CONJL body";;

new_definition(`true_DEF`, "true = T");;

hide_constant `T`;; %< So "T" can be used as a set variable, as in ZRM >%

new_special_symbol `|-?`;;

define_infix "|-? assumptions conclusion = CONJL assumptions ==> conclusion";;

%----------------------------------------------------------------------------%
% Synonym for IN for use in schema variable declarations.                    %
%----------------------------------------------------------------------------%

new_special_symbol `::`;;

define_infix ":: x (s:* set) = x IN s";;

new_special_symbol `=/=`;;

define_infix "$=/= (x:*) (y:*) = ~(x = y)";;

prove_theorem
 (`CHOICE`,
  "!s:* set. (s =/= {}) = CHOICE s IN s",
  GEN_TAC
   THEN REWRITE_TAC[=/=]
   THEN EQ_TAC
   THEN REWRITE_TAC[CHOICE_DEF]
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC MEMBER_NOT_EMPTY);;

define_infix "$NOT_IN (x:*) s = ~(x IN s)";;

%----------------------------------------------------------------------------%
% Constants for restricting quantifiers to sets.                             %
%----------------------------------------------------------------------------%

define "FORALL_RESTRICT s b = !x:*. (x IN s) ==> (b x)";;

define "EXISTS_RESTRICT s b = ?x:*. (x IN s) /\ (b x)";;

associate_restriction(`!`, `FORALL_RESTRICT`);;
associate_restriction(`?`, `EXISTS_RESTRICT`);;

load_definition `bool` `RES_FORALL`;;
load_definition `bool` `RES_EXISTS`;;

new_special_symbol `|->`;;

define_infix "|-> (x:*) (y:**) = (x,y)";;

define "dom(R:(*#**)set) = {x | ?y. (x|->y) IN R}";;

prove_theorem
 (`dom_UNION`,
  "!X Y:(*#**)set. dom(X UNION Y) = dom X UNION dom Y",
  REWRITE_TAC[dom;EXTENSION;IN_UNION]
   THEN REPEAT GEN_TAC
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL
    [DISJ1_TAC;
     DISJ2_TAC;
     ALL_TAC;
     ALL_TAC]
   THEN EXISTS_TAC "y:**"
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`dom_EMPTY`,
  "dom({}:(*#**)set) = {}",
  REWRITE_TAC[dom;NOT_IN_EMPTY;EXTENSION]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[]);;

prove_theorem
 (`dom_SING`,
  "!(x:*)(y:**). dom{x |-> y} = {x}",
  REWRITE_TAC[dom;EXTENSION;IN_UNION;IN_SING;|->]
   THEN REPEAT GEN_TAC
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN REWRITE_TAC[PAIR_EQ]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC "y:**"
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`dom_SING_Cor`,
  "!(x:*)(y:**). x IN dom{x |-> y}",
  REWRITE_TAC[dom_SING;IN_SING]);;

define "ran(R:(*#**)set) = {y | ?x. (x|->y) IN R}";;

prove_theorem
 (`ran_EMPTY`,
  "ran({}:(*#**)set) = {}",
  REWRITE_TAC[ran;NOT_IN_EMPTY;EXTENSION]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[]);;

prove_theorem
 (`ran_SING`,
  "!(x:*)(y:**). ran{x |-> y} = {y}",
  REWRITE_TAC[ran;EXTENSION;IN_UNION;IN_SING;|->]
   THEN REPEAT GEN_TAC
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN REWRITE_TAC[PAIR_EQ]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC "x:*"
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`ran_UNION`,
  "!X Y:(*#**)set. ran(X UNION Y) = ran X UNION ran Y",
  REWRITE_TAC[ran;EXTENSION;IN_UNION]
   THEN REPEAT GEN_TAC
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL
    [DISJ1_TAC;
     DISJ2_TAC;
     ALL_TAC;
     ALL_TAC]
   THEN EXISTS_TAC "x':*"
   THEN ASM_REWRITE_TAC[]);;

define "P(X:* set) = {Y | Y SUBSET X}";;

prove_theorem
 (`DIFF_IN_P`,
  "! s t:* set. (s DIFF t) IN P s",
  REPEAT STRIP_TAC
   THEN REWRITE_TAC[IN_DIFF;IN_UNION;P;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN ASM_REWRITE_TAC[IN_DIFF]
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]);;

new_special_symbol `><`;;

define_infix ">< (X:* set) (Y:** set) = {(x,y) | x IN X /\ y IN Y}";;

new_special_symbol `<->`;;

define_infix "<-> (X:* set) (Y:** set) = P(X >< Y)";;

new_special_symbol `-+>`;;

define_infix 
 "-+> (X:* set) (Y:** set) = 
  {f | f IN (X <-> Y) /\ 
       !x y1 y2. (x|->y1) IN f /\ (x|->y2) IN f ==> (y1=y2)}";;

new_special_symbol `-->`;;

%< Old version
define_infix 
 "--> (X:* set) (Y:** set) = 
  {f | f IN (X -+> Y) /\ !x::X. ?y::Y. (x,y) IN f}";;
>%

define_infix 
 "--> (X:* set) (Y:** set) = 
  {f | f IN (X -+> Y) /\ (dom f = X)}";;

prove_theorem
 (`domPfun`,
  "!f (X:* set) (Y:** set) x. f IN (X -+> Y) /\ x IN dom f ==> x IN X",
  REWRITE_TAC[|->;dom;-+>;<->;P;><;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
   THEN SMART_ELIMINATE_TAC
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`domPfunIN`,
  "!f (X:* set) (Y:** set). f IN (X -+> Y)  ==> dom f IN P X",
  REWRITE_TAC[P;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC domPfun);;

prove_theorem
 (`SING_Pfun`,
  "!(x:*) (y:**) X Y. x IN X /\ y IN Y ==> {x |-> y} IN (X -+> Y)",
  REWRITE_TAC[|->;-+>;<->;P;><;SUBSET_DEF;IN_SING]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN REWRITE_ASMS_TAC[IN_SING;PAIR_EQ]
   THEN ASM_REWRITE_TAC[]
   THEN EXISTS_TAC "x:*"
   THEN EXISTS_TAC "y:**"
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`UNION_SING_Pfun`,
  "!f (X:* set) (Y:** set) x y.
    f IN (X -+> Y) /\ x IN X /\ y IN Y /\ ~(x IN dom f) 
    ==> 
    (f UNION {x |-> y}) IN (X -+> Y)",
  REWRITE_TAC[dom;-+>;<->;P;><;SUBSET_DEF;|->]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[IN_UNION;IN_SING;PAIR_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THENL
    [EXISTS_TAC "x'':*"
      THEN EXISTS_TAC "y':**"
      THEN ASM_REWRITE_TAC[];
     EXISTS_TAC "x:*"
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[];
     SMART_ELIMINATE_TAC
      THEN RES_TAC;
     SMART_ELIMINATE_TAC
      THEN RES_TAC;
     ASM_REWRITE_TAC[]]);;

prove_theorem
 (`UNION_SING_IN_P`,
  "!f (X:* set) (Y:** set) x y.
    f IN (X -+> Y) /\ x IN X /\ y IN Y
    ==> 
    dom(f UNION {x |-> y}) IN P X",
  REWRITE_TAC[dom;-+>;<->;P;><;SUBSET_DEF;|->]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[IN_UNION;IN_SING;PAIR_EQ]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASM_REWRITE_TAC[]
   THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`domTotalFun`,
  "!f (X:* set) (Y : ** set). f IN (X --> Y) ==> (dom f = X)",
  REWRITE_TAC
   [-->;-+>;<->;><;|->;dom;P;RES_FORALL;RES_EXISTS;SUBSET_DEF;EXTENSION;
    FORALL_RESTRICT;EXISTS_RESTRICT]
   THEN BETA_TAC
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN REPEAT STRIP_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC);;

prove_theorem
 (`IN_Fun_Pfun`,
  "!f (X:* set) (Y:** set). f IN (X --> Y) ==> f IN (X -+> Y)",
  REWRITE_TAC[-->]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`ranPfun`,
  "!f (X:* set) (Y:** set) y. f IN (X -+> Y) /\ y IN ran f ==> y IN Y",
  REWRITE_TAC[|->;ran;-+>;<->;P;><;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
   THEN SMART_ELIMINATE_TAC
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`ranPfunIN`,
  "!f (X:* set) (Y:** set). f IN (X -+> Y)  ==> ran f IN P Y",
  REWRITE_TAC[ran;P;|->;-+>;<->;><;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN IMP_RES_TAC PAIR_EQ
   THEN SMART_ELIMINATE_TAC
   THEN ASM_REWRITE_TAC[]);;

define "Ap(f:(*#**)set)x = @y. (x,y) IN f";;

new_special_symbol `^^`;;

define_infix "^^ = (Ap: (*#**)set -> * -> **)";;

prove_theorem
 (`Ap_UNION1`,
  "!(x1 x2:*) (v:**) X.
    ~(x1 = x2) ==> ((X UNION {x1|->v}) ^^ x2 = X^^x2)",
  REWRITE_TAC[^^;dom;|->;Ap;IN_UNION;IN_SING;PAIR_EQ]
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
   THEN REPEAT STRIP_TAC
   THEN POP_ASSUM(ASSUME_TAC o GSYM)
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`Ap_UNION2`,
  "!(x:*) (v:**) X.
    ~(x IN dom X) ==> ((X UNION {x|->v}) ^^ x = v)",
  REWRITE_TAC[^^;dom;|->;Ap;IN_UNION;IN_SING;PAIR_EQ]
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[SELECT_REFL]);;

prove_theorem
 (`Ap_SING`,
  "!(x:*) (v:**). {x|->v}^^x = v",
  REWRITE_TAC[^^;dom;|->;Ap;IN_UNION;IN_SING;PAIR_EQ]
   THEN CONV_TAC(DEPTH_CONV SET_SPEC_CONV)
   THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[SELECT_REFL]);;

prove_theorem
 (`ApFun`,
  "!f (X:* set) (Y:** set) x.
    (f IN (X -+> Y)) /\
    (x IN dom f)
    ==> 
    !y. (f^^x = y) = (x,y) IN f",
  REWRITE_TAC[^^;Ap;|->;dom;-+>;<->;P;><;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL
    [SMART_ELIMINATE_TAC
      THEN ASSUM_LIST
            (\thl. ASSUME_TAC(EXISTS("?y.(x:*,y:**) IN f","y:**")(el 1 thl)))
      THEN POP_ASSUM(ASSUME_TAC o SELECT_RULE)
      THEN RES_TAC
      THEN ASM_REWRITE_TAC[];
     ASSUM_LIST
            (\thl. ASSUME_TAC(EXISTS("?y.(x:*,y:**) IN f","y:**")(el 2 thl)))
      THEN POP_ASSUM(ASSUME_TAC o SELECT_RULE)
      THEN RES_TAC]);;

prove_theorem
 (`domFun`,
  "!f (x:*) (y:**). (x,y) IN f ==> x IN dom f",
  REWRITE_TAC[dom;|->]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC "y:**"
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`ApFunCor`,
  "!f (X:* set) (Y:** set) x y.
    (f IN (X -+> Y)) /\ (x,y) IN f ==> (f^^x = y)",
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC domFun
   THEN IMP_RES_TAC ApFun);;

prove_theorem
 (`ApIN`,
  "!(X:* set) (Y:** set) f x. f IN (X -+> Y)  /\ x IN dom f ==> (f^^x) IN Y",
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC ApFun
   THEN ASSUM_LIST
         (ASSUME_TAC o REWRITE_RULE[] o SPEC "(f:(*#**)set)^^x" o el 2)
   THEN ASSUM_LIST(MAP_EVERY(UNDISCH_TAC o concl))
   THEN REWRITE_TAC[dom;P;><;<->;-+>;|->;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN REWRITE_ASMS_TAC[PAIR_EQ]
   THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 6)
   THEN SMART_ELIMINATE_TAC
   THEN ASSUM_LIST(ACCEPT_TAC o el 4));;

prove_theorem
 (`IN_dom_ran`,
  "!f (X:* set) (Y:** set) x y.
    f IN (X -+> Y) /\ (x,y) IN f ==> x IN X /\ y IN Y",
  REWRITE_TAC[P;><;<->;-+>;|->;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN REWRITE_ASMS_TAC[PAIR_EQ]
   THEN ASSUM_LIST(\thl. REWRITE_TAC(delete thl (el 4 thl))));;

prove_theorem
 (`IN_P`,
  "!x f (X:* set) (Y:** set). x IN dom f /\ f IN (X -+> Y) ==> x IN X",
  REWRITE_TAC[dom;-+>;<->;><;P;|->;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN ASSUM_LIST(ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
   THEN ASM_REWRITE_TAC[]);;

prove_theorem
 (`domAp`,
  "!(X:* set) (Y:** set) f. 
   (f IN (X -+> Y)) ==> !x. x IN dom f = (x, f^^x) IN f",
  REWRITE_TAC[^^;Ap;|->;dom;-+>;<->;P;><;SUBSET_DEF]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL
    [ASSUM_LIST
      (\thl. ASSUME_TAC(EXISTS("?y.(x:*,y:**) IN f","y:**")(el 1 thl)))
      THEN POP_ASSUM(ASSUME_TAC o SELECT_RULE)
      THEN RES_TAC
      THEN ASM_REWRITE_TAC[];
     EXISTS_TAC "(@y. (x:*,y:**) IN f)"
      THEN ASM_REWRITE_TAC[]]);;

new_special_symbol `<+`;;

define_infix
 "<+ (S:* set) (R:(*#**)set) = {(x|->y) | ~(x IN S) /\ (x|->y) IN R}";;

new_special_symbol `+>`;;

define_infix
 "+> (R:(*#**)set)  (T:** set) = {(x|->y) | (x|->y) IN R /\ ~(y IN T)}";;

prove_theorem
 (`RangeAntiResSING`,
  "!(x:*) (y:**). {x |-> y} +> {y} = {}",
  REPEAT GEN_TAC
   THEN REWRITE_TAC[+>;|->;IN_SING;EXTENSION;NOT_IN_EMPTY]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC);;

prove_theorem
 (`RangeAntiResPfun`,
  "!(X:* set) (Y:** set) f (y:**). f IN (X -+> Y) ==> (f +> {y}) IN (X -+> Y)",
  REPEAT GEN_TAC
   THEN REWRITE_TAC[-+>;<->;><;P;+>;|->;NOT_IN_EMPTY;SUBSET_DEF;IN_SING]
   THEN SET_SPEC_TAC
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN SMART_ELIMINATE_TAC
   THENL
    [EXISTS_TAC "x'':*"
      THEN EXISTS_TAC "y'':**"
      THEN ASM_REWRITE_TAC[];
     SMART_ELIMINATE_TAC
      THEN RES_TAC]);;

prove_theorem
 (`domRangeAntiResPfun`,
  "!(X:* set) (Y:** set) f (y:**). f IN (X -+> Y) ==> dom(f +> {y}) IN P X",
  REPEAT GEN_TAC
   THEN REWRITE_TAC[dom;-+>;<->;><;P;+>;|->;NOT_IN_EMPTY;SUBSET_DEF;IN_SING]
   THEN SET_SPEC_TAC
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[PAIR_EQ]
   THEN REPEAT STRIP_TAC
   THEN RES_TAC
   THEN SMART_ELIMINATE_TAC
   THEN ASSUM_LIST(ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
   THEN ASM_REWRITE_TAC[]);;
   
new_special_symbol `(+)`;;

define_infix "(+) (f:(*#**)set) (g:(*#**)set) = (dom g <+ f) UNION g";;

prove_theorem
 (`OverrideIsFun`,
  "!(X:* set) (Y:** set) f g.
    (f IN (X --> Y)) /\
    (g IN (X --> Y))
    ==> 
    ((f (+) g) IN (X --> Y))",
  REWRITE_TAC[dom;|->;(+);<+;-->;-+>;<->;P;><;SUBSET_DEF]  
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[IN_UNION]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN (SMART_ELIMINATE_TAC ORELSE ALL_TAC)
   THEN ASM_REWRITE_TAC[PAIR_EQ]
   THENL
    [EXISTS_TAC "x':*"
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[]
      THEN RES_TAC
      THEN IMP_RES_TAC PAIR_EQ
      THEN SMART_ELIMINATE_TAC
      THEN ASM_REWRITE_TAC[];
     RES_TAC
      THEN SMART_ELIMINATE_TAC
      THEN ASM_REWRITE_TAC[PAIR_EQ]
      THEN EXISTS_TAC "x':*"
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[];
     ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 6)
      THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 5)
      THEN ASSUM_LIST
            (\thl. (STRIP_ASSUME_TAC o 
                    REWRITE_RULE[SYM(el 4 thl);SYM(el 3 thl)])
                   (el 8 thl))
      THEN ASSUM_LIST
            (\thl. (STRIP_ASSUME_TAC o 
                    REWRITE_RULE[SYM(el 3 thl);SYM(el 2 thl)])
                   (el 6 thl))
      THEN RES_TAC;
     ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 4)
      THEN SMART_ELIMINATE_TAC
      THEN ASSUM_LIST
            (STRIP_ASSUME_TAC          o 
             CONV_RULE NOT_EXISTS_CONV o
             SET_SPEC_RULE             o 
             REWRITE_RULE[dom]         o 
             el 3)
      THEN RES_TAC;
     ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
      THEN SMART_ELIMINATE_TAC
      THEN ASSUM_LIST
            (STRIP_ASSUME_TAC          o 
             CONV_RULE NOT_EXISTS_CONV o
             SET_SPEC_RULE             o 
             REWRITE_RULE[dom]         o 
             el 2)
      THEN RES_TAC;
     RES_TAC;
     REWRITE_TAC[EXTENSION]
      THEN SET_SPEC_TAC
      THEN GEN_TAC
      THEN EQ_TAC
      THEN REPEAT STRIP_TAC
      THENL
       [SMART_ELIMINATE_TAC
         THEN ASSUM_LIST(ASSUME_TAC o GSYM o SET_SPEC_RULE o REWRITE_RULE[EXTENSION] o el 5)
         THEN ASM_REWRITE_TAC[]
         THEN EXISTS_TAC "y':**"
         THEN ASM_REWRITE_TAC[];
        EXISTS_TAC "y:**"
         THEN ASM_REWRITE_TAC[];
        EXISTS_TAC "y:**"
         THEN ASM_REWRITE_TAC[]]]);;

prove_theorem
 (`OverrideIsPfun`,
  "!(X:* set) (Y:** set) f g.
    (f IN (X -+> Y)) /\
    (g IN (X -+> Y))
    ==> 
    ((f (+) g) IN (X -+> Y))",
  REWRITE_TAC[dom;|->;(+);<+;-+>;<->;P;><;SUBSET_DEF]  
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[IN_UNION]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN (SMART_ELIMINATE_TAC ORELSE ALL_TAC)
   THEN ASM_REWRITE_TAC[PAIR_EQ]
   THENL
    [EXISTS_TAC "x':*"
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[]
      THEN RES_TAC
      THEN IMP_RES_TAC PAIR_EQ
      THEN SMART_ELIMINATE_TAC
      THEN ASM_REWRITE_TAC[];
     RES_TAC
      THEN SMART_ELIMINATE_TAC
      THEN ASM_REWRITE_TAC[PAIR_EQ]
      THEN EXISTS_TAC "x':*"
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[];
     ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 6)
      THEN ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 5)
      THEN ASSUM_LIST
            (\thl. (STRIP_ASSUME_TAC o 
                    REWRITE_RULE[SYM(el 4 thl);SYM(el 3 thl)])
                   (el 8 thl))
      THEN ASSUM_LIST
            (\thl. (STRIP_ASSUME_TAC o 
                    REWRITE_RULE[SYM(el 3 thl);SYM(el 2 thl)])
                   (el 6 thl))
      THEN RES_TAC;
     ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 4)
      THEN SMART_ELIMINATE_TAC
      THEN ASSUM_LIST
            (STRIP_ASSUME_TAC          o 
             CONV_RULE NOT_EXISTS_CONV o
             SET_SPEC_RULE             o 
             REWRITE_RULE[dom]         o 
             el 3)
      THEN RES_TAC;
     ASSUM_LIST(STRIP_ASSUME_TAC o REWRITE_RULE[PAIR_EQ] o el 3)
      THEN SMART_ELIMINATE_TAC
      THEN ASSUM_LIST
            (STRIP_ASSUME_TAC          o 
             CONV_RULE NOT_EXISTS_CONV o
             SET_SPEC_RULE             o 
             REWRITE_RULE[dom]         o 
             el 2)
      THEN RES_TAC;
     RES_TAC]);;
     
prove_theorem
 (`domOverride`,
  "!(X:* set) (Y:** set) f g.
    (f IN (X -+> Y)) /\
    (g IN (X -+> Y))
    ==> 
    (dom(f (+) g) = dom f UNION dom g)",
  REWRITE_TAC[|->;dom;(+);<+;-+>;<->;P;><;SUBSET_DEF]  
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[EXTENSION;IN_UNION]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[PAIR_EQ]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC
   THENL
    [DISJ1_TAC
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[];
     DISJ2_TAC
      THEN EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[];
     ASM_CASES_TAC "?y.(x:*,y:**) IN g"
      THENL
       [POP_ASSUM STRIP_ASSUME_TAC
         THEN EXISTS_TAC "y':**"
         THEN ASM_REWRITE_TAC[];
        EXISTS_TAC "y:**"
         THEN DISJ1_TAC
         THEN EXISTS_TAC "x:*"
         THEN EXISTS_TAC "y:**"
         THEN ASM_REWRITE_TAC[]];
     EXISTS_TAC "y:**"
      THEN ASM_REWRITE_TAC[]]);;

prove_theorem
 (`ApOverride1`,
  "!f g (X:* set) (Y:** set) x.
    (f IN (X -+> Y)) /\
    (g IN (X -+> Y)) /\
    (x IN (dom f DIFF dom g))
    ==> 
    ((f (+) g)^^x = f^^x)",
  REWRITE_TAC[|->;dom;IN_DIFF]
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC domOverride
   THEN REWRITE_ASMS_TAC[GSYM(REWRITE_RULE[|->]dom)]
   THEN ASSUM_LIST
        (\thl. (ASSUME_TAC                      o 
                REWRITE_RULE[IN_UNION;el 6 thl] o
                SPEC_ALL                        o
                REWRITE_RULE[EXTENSION])
               (el 2 thl))
   THEN ASSUM_LIST(\thl. ASSUME_TAC(REWRITE_RULE thl (SPEC_ALL OverrideIsPfun)))
   THEN ASSUM_LIST
         (\thl. ASSUME_TAC(REWRITE_RULE(thl@[|->;dom]) (SPEC_ALL ApFun)))
   THEN ASSUM_LIST
         (\thl. ASSUME_TAC
                 (REWRITE_RULE thl 
                   (SPEC_ALL(SPEC "(f:(*#**)set) (+) g" ApFun))))
   THEN ASM_REWRITE_TAC[(+);<+;IN_UNION]
   THEN REWRITE_TAC[|->] % Needed because of bug in ASM_REWRITE_TAC %
   THEN SET_SPEC_TAC
   THEN DISJ1_TAC
   THEN ASSUM_LIST
         (STRIP_ASSUME_TAC o SET_SPEC_RULE o REWRITE_RULE[dom] o el 10)
   THEN EXISTS_TAC "x:*"
   THEN EXISTS_TAC "y:**"
   THEN ASM_REWRITE_TAC[GSYM |->;PAIR_EQ]);;

prove_theorem
 (`ApOverride2`,
  "!f g (X:* set) (Y:** set) x.
    (f IN (X -+> Y)) /\
    (g IN (X -+> Y)) /\
    (x IN dom g)
    ==> 
    ((f (+) g)^^x = g^^x)",
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC domOverride
   THEN ASSUM_LIST
        (\thl. (ASSUME_TAC                      o 
                REWRITE_RULE[IN_UNION;el 5 thl] o
                SPEC_ALL                        o
                REWRITE_RULE[EXTENSION])
               (el 2 thl))
   THEN ASSUM_LIST(\thl. ASSUME_TAC(REWRITE_RULE thl (SPEC_ALL OverrideIsPfun)))
   THEN ASSUM_LIST
         (\thl. 
           ASSUME_TAC(REWRITE_RULE thl (SPEC_ALL(SPEC "g:(*#**)set" ApFun))))
   THEN ASSUM_LIST
         (\thl. ASSUME_TAC
                 (REWRITE_RULE thl 
                   (SPEC_ALL(SPEC "(f:(*#**)set) (+) g" ApFun))))
   THEN ASM_REWRITE_TAC[(+);<+;IN_UNION]
   THEN SET_SPEC_TAC
   THEN DISJ2_TAC
   THEN IMP_RES_TAC domAp);;

new_special_symbol `|\\/|`;;

define_infix "|\/| f1 f2 (x:*) = (f1 x) \/ (f2 x)";;

new_special_symbol `|/\\|`;;

define_infix "|/\| f1 f2 (x:*) = (f1 x) /\ (f2 x)";;

new_special_symbol `|==>|`;;

define_infix "|==>| f1 f2 (x:*) = (f1 x) ==> (f2 x)";;

new_special_symbol `|~|`;;

define "|~| f (x:*) = ~(f x)";;

define "NN = {n | n >= 0}";;

define "NN_1 = {n | n > 0}";;

define_infix "to m n i = m <= i /\ i <= n";;

new_special_symbol `..`;;

define_infix ".. m n = {i | m <= i /\ i <= n}";;

prove_theorem
 (`Interval_to`,
  "!m n. (FORALL_RESTRICT (m..n) = RES_FORALL (m to n)) /\
         (EXISTS_RESTRICT (m..n) = RES_EXISTS (m to n))",
  CONV_TAC(TOP_DEPTH_CONV FUN_EQ_CONV)
   THEN REWRITE_TAC
         [RES_FORALL;FORALL_RESTRICT;RES_EXISTS;EXISTS_RESTRICT;..;to]
   THEN SET_SPEC_TAC
   THEN REWRITE_TAC[]);;

prove_theorem
 (`IncInterval`,
  "(1 to (n+1)) = (1 to n) |\/| ((n+1) to (n+1))",
  CONV_TAC(FUN_EQ_CONV)
   THEN REPEAT GEN_TAC
   THEN REWRITE_TAC[to;|\/|]
   THEN ARITH_TAC);;

prove_theorem
 (`UnitInterval`,
  "(n to n) x = (x = n)",
  REWRITE_TAC[to]
   THEN ARITH_TAC);;

prove_theorem
 (`IntervalDIFFLemma`,
  "!f (X:* set) n x (v:*).
    (f IN (NN_1 --> X) /\ (1 to n)x 
    ==> x IN (dom f) DIFF dom {(n+1) |-> v})",
  REWRITE_TAC
   [|->;dom;NN_1;to;IN_DIFF;IN_SING;dom_SING;
    -->;-+>;P;><;<->;SUBSET_DEF;
    RES_EXISTS;RES_FORALL;EXISTS_RESTRICT;FORALL_RESTRICT;EXTENSION;EQ_IMP_THM]
   THEN BETA_TAC
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN REWRITE_ASMS_TAC[ARITH_PROVE "(1 <= n) = (n > 0)"]
   THEN RES_TAC
   THENL
    [EXISTS_TAC "y:*"
      THEN ASM_REWRITE_TAC[];
     SMART_ELIMINATE_TAC
      THEN IMP_RES_TAC(ARITH_PROVE "((n+1) <= n) ==> F")]);;

prove_theorem
 (`IN_NN`,
  "!n. n IN NN",
  REWRITE_TAC[NN]
   THEN SET_SPEC_TAC
   THEN ARITH_TAC);;

prove_theorem
 (`IN_NN_1`,
  "!n. (n+1) IN NN_1",
  REWRITE_TAC[NN_1]
   THEN SET_SPEC_TAC
   THEN ARITH_TAC);;

prove_theorem
 (`IntervalApLemma1`,
  "!f (X:* set) n x v.
    f IN (NN_1 --> X) /\ (1 to n)x  /\ v IN X 
    ==> 
    ((f (+) {(n+1) |-> v}) ^^ x = f ^^ x)",
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC IntervalDIFFLemma
   THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
   THEN ASSUME_TAC(SPEC "n:num" IN_NN_1)
   THEN IMP_RES_TAC SING_Pfun
   THEN IMP_RES_TAC IN_Fun_Pfun
   THEN IMP_RES_TAC ApOverride1);;

prove_theorem
 (`IntervalApLemma2`,
  "!f (X:* set) n v.
    f IN (NN_1 --> X) /\ v IN X 
    ==> 
    ((f (+) {(n+1) |-> v}) ^^ (n+1) = v)",
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC IntervalDIFFLemma
   THEN POP_ASSUM(ASSUME_TAC o SPEC_ALL)
   THEN ASSUME_TAC(SPEC "n:num" IN_NN_1)
   THEN ASSUME_TAC(ISPECL["n+1";"v:*"]dom_SING_Cor)
   THEN LITE_IMP_RES_TAC SING_Pfun
   THEN LITE_IMP_RES_TAC IN_Fun_Pfun
   THEN LITE_IMP_RES_TAC ApOverride2
   THEN ASSUM_LIST(ACCEPT_TAC o REWRITE_RULE[Ap_SING] o el 2));;

prove_theorem
 (`IntervalSINGLemma`,
  "!n x (v:*). (1 to n)x  ==> ~(x IN (dom {(n+1) |-> v}))",
  REWRITE_TAC[|->;dom;to;IN_SING;dom_SING]
   THEN ARITH_TAC);;

prove_theorem
 (`IncINTERVAL`,
  "(1..(n+1)) = (1..n) UNION ((n+1)..(n+1))",
  REWRITE_TAC[EXTENSION;..;IN_UNION]
   THEN SET_SPEC_TAC
   THEN ARITH_TAC);;

prove_theorem
 (`UnitINTERVAL`,
  "x IN (n..n) = (x = n)",
  REWRITE_TAC[..]
   THEN SET_SPEC_TAC
   THEN ARITH_TAC);;

prove_theorem
 (`IN_INTERVAL`,
  "x IN (m..n) = m <= x /\ x <= n",
  REWRITE_TAC[..]
   THEN SET_SPEC_TAC
   THEN ARITH_TAC);;

prove_theorem
 (`IN_Interval`,
  "!i m n. i IN (m..n) = (m to n) i",
  REWRITE_TAC[..;to]
   THEN SET_SPEC_TAC
   THEN BETA_TAC
   THEN REWRITE_TAC[]);;

prove_theorem
 (`OverrideSingPfun`,
  "!(X:* set) f x.
    (f IN (NN_1 -+> X)) /\ x IN X
    ==> 
    ((f (+) {(n+1) |-> x}) IN (NN_1 -+> X))",
  REPEAT STRIP_TAC
   THEN ASSUME_TAC(SPEC "n:num" IN_NN_1)
   THEN IMP_RES_TAC SING_Pfun
   THEN IMP_RES_TAC OverrideIsPfun);;

prove_theorem
 (`UNION_NN_1_SUC`,
  "!n. NN_1 UNION {n+1} = NN_1",
  GEN_TAC
   THEN REWRITE_TAC[EXTENSION;IN_UNION;NN_1;IN_SING]
   THEN SET_SPEC_TAC
   THEN ARITH_TAC);;

prove_theorem
 (`OverrideSingFun`,
  "!(X:* set) f x.
    (f IN (NN_1 --> X)) /\ x IN X
    ==> 
    ((f (+) {(n+1) |-> x}) IN (NN_1 --> X))",
  REWRITE_TAC[-->]
   THEN SET_SPEC_TAC
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC OverrideSingPfun
   THEN ASM_REWRITE_TAC[]
   THEN ASSUME_TAC(SPEC "n:num" IN_NN_1)
   THEN IMP_RES_TAC SING_Pfun
   THEN IMP_RES_TAC domOverride
   THEN ASM_REWRITE_TAC[dom_SING;UNION_NN_1_SUC]);;
