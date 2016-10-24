%----------------------------------------------------------------------------%
%
  File name: predicate.ml
  Author:    Wishnu Prasetya
             wishnu@cs.ruu.nl
             Dept. of Comp. Science, Utrect University, the Netherlands
  Date:      Sept 1992

  Predicate (on *) is anything of type *->bool. Lifted bool operators are
  defined:
  
      FF, TT, IMP, ==, AND, OR, !!, and ??

  Also a lifted Sequent Operator is defined:

      P |== Q, which means (!s. P s ==> Q s)

  This follows the definition by Ching Tsun Chou in "A Sequent Formulation
  of the Proposiotional Logic of Predicates in HOL" in HOL Workshop 92 
  proceeding. A package by him is also available in the Contrib of HOL 2.1.

  Further, instead of !! and ?? as the lifted ! and ? for predicates as Chou
  did, we choose another approach, benefitting the RESTRICTION notation. Let
  W be a set of indices, represented as charasteristic function, ie W i means
  i is in W. We will use the same !! and ?? symbols: 

     (!! i:: W. P i) to denote (/\ i: i in W: P i)
     (?? i:: W. P i) to denote (\/ i: i in W: P i)

  If W is a set of predicates instead, then /\W and \/W can be denoted as,
  respectively:

     (!! i:: W. i)
     (??  i:: W. i)
  
  And further, let P maps ** to predicate over *, we can denote the Chou's 
  !!s:**. P s and ??s:**. P s respectively as follows:

     (!! i::(TT:**->bool). P i)
     (??  i::(TT:**->bool). P i)

  i.e. the quatification is over the whole domain **.

%
%----------------------------------------------------------------------------%

new_theory `predicate` ;;
loadf `MYTACTICS` ;;

let FF_DEF = new_definition (`FF_DEF`, "(FF:*->bool) = \s:*.F");;

let TT_DEF = new_definition (`TT_DEF`, "(TT:*->bool) = \s:*.T");;

let p_NOT_DEF = new_definition (`p_NOT_DEF`, 
    "NOT (p:*->bool) = \s:*. ~p s");;

let p_AND_DEF = new_infix_definition (`p_AND_DEF`, 
    "AND (p:*->bool) (q:*->bool) = \s:*. (p s) /\ (q s)");;

let p_OR_DEF = new_infix_definition (`p_OR_DEF`, 
    "OR (p:*->bool) (q:*->bool) = \s:*. (p s) \/ (q s)");;

let p_IMP_DEF = new_infix_definition (`p_IMP_DEF`, 
    "IMP (p:*->bool) (q:*->bool) = \s:*. (p s) ==> (q s)");;

let EQUAL_DEF = new_infix_definition (`==_DEF`, 
    "== (p:*->bool) (q:*->bool) = \s:*. (p s) = (q s)");;

%-----------------------------------------------------------------------------------
 The definition for !! and ?? are included bellow for the sake of completeness
-----------------------------------------------------------------------------------%
 
new_binder_definition
  (`!!_DEF`, "!! = \R:**->(*->bool). \s:*. !i:**. (R i) s ");;

new_binder_definition
  (`??_DEF`, "?? = \R:**->(*->bool). \s:*. ?i:**. (R i) s ");;

%-----------------------------------------------------------------------------------
 Here follows the definition of quatified AND and OR
-----------------------------------------------------------------------------------%

let RES_qOR = new_definition (`RES_qOR`, 
    "RES_qOR (W:**->bool) (P:**->(*->bool)) = (\s. ?i. W i /\  P i s)") ;;

associate_restriction (`??`, `RES_qOR`) ;;

let RES_qAND = new_definition (`RES_qAND`,
    "RES_qAND (W:**->bool) (P:**->(*->bool)) = (\s. (!i. W i ==> P i s))") ;;

associate_restriction (`!!`, `RES_qAND`) ;;

%-----------------------------------------------------------------------------------
 Here follows the definition of lifted sequent |-- for predicates
-----------------------------------------------------------------------------------%

new_special_symbol `|==` ;;

new_infix_definition
  (`|==_DEF`, "|== (p:*->bool) (q:*->bool) = !s:*. (p s) ==> (q s)") ;;


loadf `predicate_LIB` ;;

%-----------------------------------------------------------------------------------
  Here are some theorems about predicates
  First few useful tactics:
-----------------------------------------------------------------------------------%

let SUBST2_ASM_TAC =  EVERY_ASSUM (\thm. SUBST1_TAC (SYM thm) ? ALL_TAC) ;;
 
let REW_SPEC_ASM_TAC trm = EVERY_ASSUM 
    (\thm. REWRITE_TAC [REWRITE_RULE [] (SPEC trm  thm)] ? ALL_TAC) ;;

%-----------------------------------------------------------------------------------
   EXT_lemma: |- !f g. (f = g) = (!x. f x = g x)

   this lemma is a stronger form of EQ_EXT, which is often more handy than EQ_EXT.
-----------------------------------------------------------------------------------%

let EXT_lemma = prove_thm
  (`EXT_lemma`,
   "!(f:*->**) g. (f = g) = (!x. f x = g x)",
    REPEAT GEN_TAC THEN EQ_TAC 
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC []
    THEN IMP_RES_TAC EQ_EXT) ;;

%-----------------------------------------------------------------------------------
  NOT_FF_lemma: |- !P. ~(P = FF) ==> (?a. P a)
-----------------------------------------------------------------------------------%

let NOT_FF_lemma = prove_thm
  (`NOT_FF_lemma`,
   "!P:*->bool. ~(P=FF) ==> ?a. P a",
    REWRITE_TAC [FF_DEF] THEN BETA_TAC
    THEN REWRITE_TAC [EXT_lemma]
    THEN REWRITE_TAC [NOT_FORALL_CONV "~(!x:*. ~P x)"]) ;;

%-----------------------------------------------------------------------------------
  Reflexivity of AND and OR
-----------------------------------------------------------------------------------%

let p_AND_REFL = prove_thm (`p_AND_REFL`,
    "!p:*->bool. (p AND p) = p",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let p_OR_REFL = prove_thm (`p_OR_REFL`,
    "!p:*->bool. (p OR p) = p",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

%-----------------------------------------------------------------------------------
  Commutativity of AND and OR
-----------------------------------------------------------------------------------%

let p_AND_SYM = prove_thm (`p_AND_SYM`,
    "!(p:*->bool) q. (p AND q) = (q AND p)",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let p_OR_SYM = prove_thm (`p_OR_SYM`,
    "!(p:*->bool) q. (p OR q) = (q OR p)",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

%-----------------------------------------------------------------------------------
  Zero and Unit element of AND and OR
-----------------------------------------------------------------------------------%

let p_AND_ZERO = prove_thm (`p_AND_ZERO`,
    "!p:*->bool. (FF AND p) = FF",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let p_AND_UNIT = prove_thm (`p_AND_UNIT`,
    "!p:*->bool. (TT AND p) = p",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let p_OR_ZERO = prove_thm (`p_OR_ZERO`,
    "!p:*->bool. (TT OR p) = TT",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let p_OR_UNIT = prove_thm (`p_OR_UNIT`,
    "!p:*->bool. (FF OR p) = p",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

%-----------------------------------------------------------------------------------
  De Morgan Laws
-----------------------------------------------------------------------------------%

let p_DEMORGAN1 = prove_thm (`p_DEMORGAN1`,
    "!(p:*->bool) q. (NOT (p AND q)) = ((NOT p) OR (NOT q))",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let p_DEMORGAN2 = prove_thm (`p_DEMORGAN2`,
    "!(p:*->bool) q. (NOT (p OR q)) = ((NOT p) AND (NOT q))",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

%-----------------------------------------------------------------------------------
  Let => be an ordering defined as follows:

      p => q   =   TT |== p IMP q

  then in this ordering FF is bottom element and TT is the top element.
-----------------------------------------------------------------------------------%
 
let FF_BOTTOM = prove_thm(`FF_BOTTOM`,
    "!p:*->bool. TT |== (FF IMP p)",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

let TT_TOP = prove_thm(`TT_TOP`,
    "!p:*->bool. TT |== (p IMP TT)",
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN EXT_TAC THEN TAUT_TAC) ;;

%-----------------------------------------------------------------------------%
%
 With respect to the IMP-ordering, see above, we will show that (??j::W. P j) 
 and (!!j::W. P j) are respectively the Least Upper Bound and Greatest Lower 
 Bound of {P j | W j}. These consists of the following 4 theorems: 

   Let W:**->bool and P:**->(*->bool)

   qOR_LUB1: says that (??j::W. P j) is an upper bound of {P j | W j}
            
   qOR_LUB2: says that (??j::W. P j) is less than any upper bound of {P j | W j}

   qAND_LUB1: says that (!!j::W. P j) is an lower bound of {P j | W j}
            
   qAND_LUB2: says that (!!j::W. P j) is greater than any lower bound of {P j | W j}

%
%-----------------------------------------------------------------------------%

let qOR_LUB1 = prove_thm(`qOR_LUB1`,
  "!(W:**->bool) (P:**->(*->bool)).
       !i:: W. (TT |== ((P i) IMP (?? j:: W. P j)))",
  REWRITE_TAC pred_defs 
  THEN RESTRICT_DEF_TAC
  THEN (REPEAT STRIP_TAC) 
  THEN EXISTS_TAC "x:**"
  THEN ASM_REWRITE_TAC[] ) ;;

let qOR_LUB2 = prove_thm(`qOR_LUB2`,
  "!(W:**->bool) (P:**->(*->bool)) (q:*->bool).
       (!i:: W. TT |== ((P i) IMP q)) ==>
       (TT |== ((?? j:: W. P j) IMP q))",
  REWRITE_TAC pred_defs 
  THEN RESTRICT_DEF_TAC
  THEN (REPEAT STRIP_TAC) 
  THEN RES_TAC) ;;

let qAND_GLB1 = prove_thm(`qAND_GLB1`,
  "!(W:**->bool) (P:**->(*->bool)).
       !i:: W. TT |== ((!! j:: W. P j) IMP (P i))",
  REWRITE_TAC pred_defs 
  THEN RESTRICT_DEF_TAC
  THEN (REPEAT STRIP_TAC)
  THEN RES_TAC) ;;

let qAND_GLB2 = prove_thm(`qAND_GLB2`,
  "!(W:**->bool) (P:**->(*->bool)) (q:*->bool).
       (!i:: W. TT |== (q IMP (P i))) ==>
       (TT |== (q IMP (!! j:: W. P j)))",
  REWRITE_TAC pred_defs 
  THEN RESTRICT_DEF_TAC
  THEN (REPEAT STRIP_TAC) 
  THEN RES_TAC) ;;


%------------------------------------------------------------------------------

 Quatified OR and AND over empty domain:

 qAND_EMPTY: (!!i:: FF. P i) = TT

 qOR_EMPTY:  (??i:: TT. P i) = FF

------------------------------------------------------------------------------%

let qAND_EMPTY = prove_thm (`qAND_EMPTY`,
    "!P:**->(*->bool). (!!i:: FF. P i) = TT",
    EXT_TAC 
    THEN REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN (REPEAT STRIP_TAC)) ;;

let qOR_EMPTY = prove_thm (`qOR_EMPTY`,
    "!P:**->(*->bool). (??i:: FF. P i) = FF",
    EXT_TAC 
    THEN REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN (REPEAT STRIP_TAC)) ;;

%------------------------------------------------------------------------------

 Singletons Lemmas:

 qOR_SINGLETON:  (??i::(\j. a=j). P i) = P a

 qAND_SINGLETON: (!!i::(\j. a=j). P i) = P a

------------------------------------------------------------------------------%

let qOR_SINGLETON = prove_thm(`qOR_SINGLETON`,
    "!(P:**->(*->bool)) a. (??i:: (\j. a=j). P i) = (P a)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC)
    THENL [ ASM_REWRITE_TAC[] ;
            EXISTS_TAC "a:**" THEN ASM_REWRITE_TAC[] ] ) ;;


let qAND_SINGLETON = prove_thm(`qAND_SINGLETON`,
    "!(P:**->(*->bool)) a. (!!i:: (\j. a=j). P i) = (P a)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC)
    THENL [ REW_SPEC_ASM_TAC "a:**" ;
            SUBST2_ASM_TAC THEN ASM_REWRITE_TAC [] ] ) ;;


%------------------------------------------------------------------------------

 We prove that AND and OR are special cases of quantified AND and OR:

 qOR_OR:   (??i::(\j. (p=j) \/ (q=j)). i) = (p OR q)

 qAND_AND: (!!i::(\j. (p=j) \/ (q=j)). i) = (p AND q)

------------------------------------------------------------------------------%

let qOR_OR = prove_thm(`qOR_OR`,
    "!(p:*->bool) q. (??i:: (\j. (p=j) \/ (q=j)). i) = (p OR q)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC)
    THEN SUBST2_ASM_TAC THEN ASM_REWRITE_TAC[]
    THENL [ EXISTS_TAC "p:*->bool" THEN ASM_REWRITE_TAC [] ;
            EXISTS_TAC "q:*->bool" THEN ASM_REWRITE_TAC [] ] ) ;;


let qAND_AND = prove_thm(`qAND_AND`,
    "!(p:*->bool) q. (!!i:: (\j. (p=j) \/ (q=j)). i) = (p AND q)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC)
    THEN SUBST2_ASM_TAC THEN ASM_REWRITE_TAC[]
    THENL 
    [ REW_SPEC_ASM_TAC "p:*->bool" ;
      REW_SPEC_ASM_TAC "q:*->bool" ] ) ;;


%------------------------------------------------------------------------------

 Domain Splits lemmas:

 qOR_DOM_SPLIT:  (??i::W. P i) OR P a = (??i::(\j. W j \/ a=j). P i)

 qAND_DOM_SPLIT: (!!i::W. P i) AND P a = (!!i::(\j. W j \/ a=j). P i)

------------------------------------------------------------------------------%

let qOR_DOM_SPLIT = prove_thm (`qOR_DOM_SPLIT`,
    "!W (P:**->(*->bool)) a. 
     ((??i:: W. P i) OR (P a)) = (??i::(\j. (W j) \/ (a=j)). P i)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC)
    THENL [ EXISTS_TAC "i:**" THEN ASM_REWRITE_TAC[] ;
            EXISTS_TAC "a:**" THEN ASM_REWRITE_TAC[] ;
            DISJ1_TAC THEN EXISTS_TAC "i:**" THEN ASM_REWRITE_TAC[] ;
            ASM_REWRITE_TAC[] ] ) ;;


let qAND_DOM_SPLIT = prove_thm (`qAND_DOM_SPLIT`,
    "!W (P:**->(*->bool)) a. 
     ((!!i:: W. P i) AND (P a)) = (!!i::(\j. (W j) \/ (a=j)). P i)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC)
    THEN RES_TAC 
    THENL [ SUBST2_ASM_TAC THEN ASM_REWRITE_TAC[] ;
            REW_SPEC_ASM_TAC "a:**" ] ) ;;

%------------------------------------------------------------------------------

 AND and OR left and right distribute over quatified OR:

 qAND_LEFT_DISTR_OR:  p AND (??i::W. P i) = (??i::W. p AND P i)

 qAND_RIGHT_DISTR_OR: (??i::W. P i) AND p = (??i::W. P i AND p)

NOTE: the same also holds fot quantified AND, provided the quantification 
      domain is non-empty. This part still left out.
------------------------------------------------------------------------------%

let qAND_LEFT_DISTR_OR = prove_thm (`qAND_LEFT_DISTR_OR`,
    "!W (P:**->(*->bool)) p. (p AND (??i::W. P i)) = (??i::W. p AND P i)",
    REWRITE_TAC pred_defs 
    THEN RESTRICT_DEF_TAC
    THEN EXT_TAC THEN EQ_TAC
    THEN (REPEAT STRIP_TAC) 
    THEN ASM_REWRITE_TAC []
    THEN EXISTS_TAC "i:**" THEN ASM_REWRITE_TAC []) ;;

let qAND_RIGHT_DISTR_OR = prove_thm (`qAND_RIGHT_DISTR_OR`,
    "!W (P:**->(*->bool)) p. ((??i::W. P i) AND p) = (??i::W. (P i) AND p)",
    ONCE_REWRITE_TAC [p_AND_SYM]
    THEN ACCEPT_TAC qAND_LEFT_DISTR_OR) ;;

%
set_goal([],
    "!Prop (W:**->bool) (f:**->(*->bool)).
    (!i. W i  ==>  (Prop (f i)))  =  (!p. (MAP_S W f) p ==>  (Prop p))") ;;
   
    e (REWRITE_TAC pred_defs THEN BETA_TAC) ;;
    e ((REPEAT STRIP_TAC) THEN EQ_TAC) ;;
    e (REPEAT STRIP_TAC) ;;
    e  RES_TAC ;;
    e (FILTER_REWRITE_ASM_TAC 
          "(f:**->(*->bool)) i = p"
          "(Prop:(*->bool)->bool) (f (i:**))") ;;
    e (ASM_REWRITE_TAC []) ;;
    e (REPEAT STRIP_TAC) ;;
    e (FILTER_INFER_ASM_TAC 
          "!p:*->bool. (?i:**. W i /\ (f i = p)) ==> Prop p"
          (SPEC "(f:**->(*->bool)) i")) ;;
    e (IMP_RES_TAC lemma THEN RES_TAC) ;;
    e (FILTER_INFER_ASM_TAC
          "((f:**->(*->bool)) i = f i) ==> Prop(f i)"
           (REWRITE_RULE [])) ;;
    e (ASM_REWRITE_TAC[]) ;;

let MAP_S_LEMMA2 = save_top_thm `MAP_S_LEMMA2` ;;
%
   
close_theory ();;
