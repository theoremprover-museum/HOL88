%-----------------------------------------------------------------------------------

  This library contains some basic theorems about well-founded set. 

  Well foundedness is defined as follows. A relation R is called well founded
  iff it satisfies:

        !V. (!y. y IN V ==> (?x. R x y /\ x IN V)) ==> (V = {})

  That is, any non-empty set must have a minimal element m. This is an equivalent
  definition with the more classical definition in term of chains.

  The main results of this library is as follows:

     - WELL_FOUNDED
       The definition for well-foundedness.
     
     - ADMIT_WF_INDUCTION
       Define the well-founded induction.

     - WF_EQU_IND
       States that well-foundedness is equivalent with admiting the WF induction.
 
     - FIN_ADMIT_WF_IND        
       States that a transitive and anti-reflexive relation on finite domain will
       admit WF induction.

     - NUM_ADMIT_WF_INDUCTION
       States that the relation < on natural number admits WF induction.

     - REL_JOINT_ADMIT_WF_IND
       States that the conjunction of two relations preserves WF induction.

     - REL_PROD_ADMIT_WF_IND
       States that the product of two relations preserves WF induction.

     - REL_LEXI_ADMIT_WF_IND
       States that the lexicographic product of two relations preserves WF 
       induction.

     - FPROD_ADMIT_WF_IND
       States that the finite product of two relations preserves WF induction.

      - FLEXI_ADMIT_WF_IND
        States that the finite lexicographic product of two relations preserves 
        WF induction.

Hope this help.

  Lib name: WF
  Date    : Dec. 2 1992
  Author  : Wishnu Prasetya
            Dept. of Comp. Science
            University of Utrecht, the Netherlands
  EMail   : wishnu@cs.ruu.nl

---------------------------------------------------------------------------------%

new_theory`WF`;;

load_library `taut` ;;
load_library `sets` ;;
new_parent `arithmetic` ;;
new_parent `predicate` ;;
loadf `MYTACTICS` ;;
loadf `OLD_RES` ;;
loadf `predicate_LIB`;;

let autoload_defs_and_thms thy =
 map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
 map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy));
     () ;;

autoload_defs_and_thms `arithmetic`;;
autoload_defs_and_thms `prim_rec`;;
autoload_defs_and_thms `num`;;
autoload_defs_and_thms `predicate`;;

let Rel = ":*->*->bool" ;;
let Rel1 = ":*->*->bool" ;;
let Rel2 = ":**->**->bool" ;;
let Pred = ":*->bool" ;;

let ADMIT_WF_INDUCTION = new_definition
  (`ADMIT_WF_INDUCTION`,
   "ADMIT_WF_INDUCTION (R:^Rel) =
    !P. (!y. (!x. R x y ==> P x) ==> P y) ==> (!x. P x)") ;;

let CHF_WELL_FOUNDED = new_definition
  (`CHF_WELL_FOUNDED`,
   "WELL_FOUNDED (R:^Rel) = 
    (!P. (!y. P y ==> (?x. R x y /\ P x)) ==> (P=FF))") ;;

%----------------------------------------------------------------------------------
  CONTRA_lemma: |- !p. p /\ ~p ==> F
  The lemma is useful in proofs using contradiction
----------------------------------------------------------------------------------%

let CONTRA_lemma = prove_thm
  (`CONTRA_lemma`,"!p. (p /\ ~p) ==> F", TAUT_TAC) ;;

%----------------------------------------------------------------------------------
  IN_GSPEC_lemma: |- !P x. x IN {s | P s} = P x
----------------------------------------------------------------------------------%

let IN_GSPEC_lemma = prove_thm
  (`IN_GSPEC_lemma`,
   "!P x. (x IN {s:* | P s}) = P x",
    REWRITE_TAC [GSPECIFICATION]
    THEN REPEAT GEN_TAC THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [ XRULE_ASSUM_TAC (REWRITE_RULE [PAIR_EQ] o BETA_RULE)
            THEN ASM_REWRITE_TAC [] ;
            EXISTS_TAC "x:*" THEN BETA_TAC
            THEN ASM_REWRITE_TAC[] ]) ;;

%----------------------------------------------------------------------------------
   WELL_FOUNDED:
   The set version of WELL_FOUNDED definition.

   WELL_FOUNDED R = (!V. (!y. y IN V ==> (?x. R x y /\ x IN V)) ==> V = {}
----------------------------------------------------------------------------------%

let WELL_FOUNDED = prove_thm
  (`WELL_FOUNDED`,
   "!R:^Rel. WELL_FOUNDED R =
       (!V. (!y. y IN V ==> (?x. R x y /\ x IN V)) ==> (V={}))",
    REWRITE_TAC [CHF_WELL_FOUNDED] 
    THEN GEN_TAC THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [ XRULE_ASSUM_TAC (BETA_RULE o SPEC "\s:*. s IN V")
            THEN RES_TAC
            THEN XRULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE [FF_DEF; EXT_lemma])
            THEN REWRITE_TAC [EXTENSION ; NOT_IN_EMPTY]
            THEN ASM_REWRITE_TAC [] ;
            XRULE_ASSUM_TAC (SPEC "{s:* | P s}")
            THEN XRULE_ASSUM_TAC (REWRITE_RULE [IN_GSPEC_lemma])
            THEN RES_TAC
            THEN XRULE_ASSUM_TAC (REWRITE_RULE [EXTENSION ; NOT_IN_EMPTY])
            THEN XRULE_ASSUM_TAC (REWRITE_RULE [IN_GSPEC_lemma])
            THEN REWRITE_TAC [FF_DEF; EXT_lemma] THEN BETA_TAC
            THEN ASM_REWRITE_TAC[] ]) ;;

%----------------------------------------------------------------------------------
  NOT_WF: 
  ~WELL_FOUNDED R = (?P. (!y. P y ==> (?x. R x y /\ P x)) /\ ~(P = FF))
----------------------------------------------------------------------------------%

let NOT_WF = prove_thm
  (`NOT_WF`,
   "!R:^Rel. ~(WELL_FOUNDED R) =
      (?P. (!y. P y ==> (?x. R x y /\ P x)) /\ ~(P=FF))",
    REWRITE_TAC [CHF_WELL_FOUNDED]
    THEN REWRITE_TAC [NOT_FORALL_CONV 
         "~(!P. (!y. P y ==> (?x. (R:^Rel) x y /\ P x)) ==> (P = FF))"]
    THEN REWRITE_TAC [prove("!p q. ~(p ==> q) = (p /\ ~q)", TAUT_TAC)]) ;;

%----------------------------------------------------------------------------------
  WELL_FOUNDED_CONTRA:
  The contra position version of WELL_FOUNDED definition.
----------------------------------------------------------------------------------%

let WELL_FOUNDED_CONTRA = prove_thm
  (`WELL_FOUNDED_CONTRA`,
   "!R:^Rel. WELL_FOUNDED R =
      (!P. ~(P=FF) ==> ?y. P y /\ (!x. P x ==> ~(R x y)))",
   REWRITE_TAC [CHF_WELL_FOUNDED]
   THEN REWRITE_TAC [CONTRAPOS_CONV 
        "(!y. P y ==> (?x. (R:^Rel) x y /\ P x)) ==> (P = FF)"]
   THEN REWRITE_TAC [NOT_FORALL_CONV
        "~(!y. P y ==> (?x. (R:^Rel) x y /\ P x))" ]
   THEN REWRITE_TAC [prove("!p q. ~(p ==> q) = (p /\ ~q)", TAUT_TAC)] 
   THEN REWRITE_TAC [NOT_EXISTS_CONV "~(?x. (R:^Rel) x y /\ P x)"]
   THEN REWRITE_TAC [prove("!p q. ~(p /\ q) = (q ==> ~p)", TAUT_TAC)]) ;;

%---------------------------------------------------------------------------------
  FF_lemma: |- !P. (P = FF) = (!x. ~P x)
---------------------------------------------------------------------------------%

let FF_lemma = prove_thm
  (`FF_lemma`, 
   "!P:^Pred. (P=FF) = (!x. ~P x)", 
    REWRITE_TAC pred_defs
    THEN GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
    THENL [RULE_ASSUM_TAC 
                (\thm. (BETA_RULE o SUBS [ASSUME "(P:^Pred)=(\s. F)"]) thm 
                       ? thm)
           THEN ASM_REWRITE_TAC[] ;
           EXT_TAC THEN ASM_REWRITE_TAC[] ]) ;;

%---------------------------------------------------------------------------------
  Now we are going to prove that well foundedness is equal with admiting WF
  induction.
---------------------------------------------------------------------------------%

let lemma1 = prove
  ("!(R:^Rel) P.
    (!y. (!x. R x y ==> ~P x) ==> ~P y) = (!y. P y ==> (?x. R x y /\ P x))",
    REWRITE_TAC [CONTRAPOS_CONV "(!x. (R:^Rel) x y ==> ~P x) ==> ~P y"]
    THEN REWRITE_TAC [NOT_FORALL_CONV "~(!x. (R:^Rel) x y ==> ~P x)"]
    THEN REWRITE_TAC [prove("!p q. ~(p ==> ~q) = (p /\ q)", TAUT_TAC)]) ;;

let lemma2 = prove
  ("!(R:^Rel) P.
    (!y. ~P y ==> (?x. R x y /\ ~P x)) = (!y. (!x. R x y ==> P x) ==> P y)",
    REWRITE_TAC [CONTRAPOS_CONV "(!x. (R:^Rel) x y ==> P x) ==> P y"]
    THEN REWRITE_TAC [NOT_FORALL_CONV "~(!x. (R:^Rel) x y ==> P x)"]
    THEN REWRITE_TAC [prove("!p q. ~(p ==> q) = (p /\ ~q)", TAUT_TAC)]) ;;

%--------------------------------------------------------------------------------
  WF_EQU_IND = |- !R. WELL_FOUNDED R = ADMIT_WF_INDUCTION R
--------------------------------------------------------------------------------%

let WF_EQU_IND = prove_thm
  (`WF_EQU_IND`,
   "!R:^Rel. (WELL_FOUNDED R) = (ADMIT_WF_INDUCTION R)",
    REWRITE_TAC [CHF_WELL_FOUNDED; ADMIT_WF_INDUCTION; FF_lemma]
    THEN GEN_TAC THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RULE_ASSUM_TAC 
         (\thm. (BETA_RULE o REWRITE_RULE [p_NOT_DEF] o 
                 SPEC "NOT (P:^Pred)") thm ? thm)
    THENL [ RULE_ASSUM_TAC (\thm. REWRITE_RULE[lemma2] thm ? thm)
            THEN RES_TAC THEN ASM_REWRITE_TAC[] ;
            RULE_ASSUM_TAC (\thm. REWRITE_RULE[lemma1] thm ? thm)
            THEN RES_TAC ]) ;;

%--------------------------------------------------------------------------------
  now we will prove that a transitive and anti-reflexive relation on a finite
  domain will admit WF induction.

  This is proved using induction, as finiteness implies induction. Let ALL_WF be
  defined as follows:

      ALL_WF R V =   !W. W SUBSET V ==> WF R W
      WF R V     =  (!y:*. y IN V ==> ?x. R x y /\ x IN V) ==> (V={})

  The proof is based on three lemmas:

      FIN_WF_lemma1: States that ALL_WF UNV implies well foundedness, hence 
                     also the WF induction.
      
      FIN_WF_lemma2: States that ALL_WF R holds for empty set.
      
      FIN_WF_lemma3: States that if ALL_WF R holds for set V, then it also
                     holds for a INSERT V.

--------------------------------------------------------------------------------%

let REL_TRANS = new_definition
  (`REL_TRANS`,
   "REL_TRANS (R:^Rel) = !x y z. R x y /\ R y z ==> R x z") ;;

let REL_ANTI_REFL = new_definition
  (`REL_ANTI_REFL`,
   "REL_ANTI_REFL (R:^Rel) = !x. ~(R x x)") ;;
            

let WF = "\R V. (!y:*. y IN V ==> ?x. R x y /\ x IN V) ==> (V={})" ;;

let ALL_WF = "\R V. !W. W SUBSET V ==> ^WF R W" ;;

let FIN_WF_lemma1 = (BETA_RULE o prove)
  ("!R:^Rel. ^ALL_WF R UNIV ==> WELL_FOUNDED R",
    REWRITE_TAC [WELL_FOUNDED] THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN ASSUME_TAC (SPEC "V:(*)set" SUBSET_UNIV)
    THEN RES_TAC) ;;

let FIN_WF_lemma2 = (BETA_RULE o prove)
  ("!R:^Rel. ^ALL_WF R {}",
   BETA_TAC 
   THEN REWRITE_TAC [SUBSET_EMPTY]
   THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]) ;;

let FIN_WF_lemma3_1 = prove
  ("!(R:^Rel) W. 
       ((!y. y IN W ==> (?x'. R x' y /\ x' IN W)) ==> (W = {})) =
       (~(W = {}) ==> (?y. y IN W /\ (!x'. x' IN W ==> ~R x' y)))",
    REWRITE_TAC [CONTRAPOS_CONV 
         "~(W = {}) ==> (?y. y IN W /\ (!x'. x' IN W ==> ~(R:^Rel) x' y))"]
    THEN REWRITE_TAC [NOT_EXISTS_CONV
         "~(?y. y IN W /\ (!x'. x' IN W ==> ~(R:^Rel) x' y))"]
    THEN REWRITE_TAC [prove("!p q. ~(p /\ q) = (p ==> ~q)", TAUT_TAC)]
    THEN REWRITE_TAC [NOT_FORALL_CONV "~(!x'. x' IN W ==> ~(R:^Rel) x' y)"]
    THEN REWRITE_TAC [prove("!p q. ~(p ==> ~q) = (q /\ p)", TAUT_TAC)] );;

let FIN_WF_lemma3_2 = prove
  ("!(R:^Rel) W x.
       (?y. (y = x) /\ (!x'. (x' = x) \/ x' IN (W DELETE x) ==> ~R x' y)) =
       ((!x'. x' IN (W DELETE x) ==> ~R x' x) /\ ~R x x)",
    REPEAT GEN_TAC THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [ XRULE_ASSUM_TAC (SPEC "x':*")
            THEN XRULE_ASSUM_TAC (REWRITE_RULE[ASSUME "y=(x:*)"])
            THEN RES_TAC ;
            XRULE_ASSUM_TAC (REWRITE_RULE [] o SPEC "x:*") 
            THEN XRULE_ASSUM_TAC (REWRITE_RULE[ASSUME "y=(x:*)"])
            THEN RES_TAC ;
            EXISTS_TAC "x:*" THEN REWRITE_TAC[]
            THEN REPEAT STRIP_TAC
            THENL [ XRULE_ASSUM_TAC (REWRITE_RULE[ASSUME "x'=(x:*)"])
                    THEN IMP_RES_TAC CONTRA_lemma ;
                    RES_TAC ] ]) ;;

let FIN_WF_lemma3_3 = prove
  ("!(R:^Rel) W x. 
         ~(!x'. x' IN (W DELETE x) ==> ~R x' x) = 
          (?x'. x' IN (W DELETE x) /\  R x' x)",
    REWRITE_TAC [NOT_FORALL_CONV "~(!x'. x' IN (W DELETE x) ==> ~(R:^Rel) x' x)"]
    THEN REWRITE_TAC [prove("!p q. ~(p ==> ~q) = (p /\ q)", TAUT_TAC)] );;

let FIN_WF_lemma3 = (BETA_RULE o prove)
  ("!(R:^Rel) V x. 
    REL_TRANS R /\ REL_ANTI_REFL R /\ ^ALL_WF R V ==> ^ALL_WF R (x INSERT V)",
    BETA_TAC THEN REWRITE_TAC [REL_TRANS; REL_ANTI_REFL; FIN_WF_lemma3_1]
    THEN REPEAT STRIP_TAC
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [SUBSET_INSERT_DELETE])
    THEN ASM_CASES_TAC "(x:*) IN W"
    THENL 
      [IMP_RES_TAC INSERT_DELETE
       THEN XRULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ])
       THEN ONCE_ASM_REWRITE_TAC[]
       THEN XRULE_ASSUM_TAC (ONCE_REWRITE_RULE [EQ_SYM_EQ])
       THEN REWRITE_TAC [IN_INSERT; RIGHT_AND_OVER_OR]
       THEN CONV_TAC EXISTS_OR_CONV
       THEN REWRITE_TAC [FIN_WF_lemma3_2]
       THEN ASM_REWRITE_TAC[]
       THEN ASM_CASES_TAC "!x'. x' IN (W DELETE x) ==> ~(R:^Rel) x' x"
       THEN ASM_REWRITE_TAC []
       THEN XRULE_ASSUM_TAC (REWRITE_RULE [FIN_WF_lemma3_3])
       THEN UNDISCH_ALL_TAC THEN REPEAT STRIP_TAC
       THEN ASM_TAC (EXISTS ("?y:*. y IN (W DELETE x)","x':*"))
       THEN XRULE_ASSUM_TAC (REWRITE_RULE [MEMBER_NOT_EMPTY])
       THEN RES_TAC
       THEN EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[]
       THEN REPEAT STRIP_TAC
       THENL
         [ XRULE_ASSUM_TAC (REWRITE_RULE [ASSUME "x''=(x:*)"])
           THEN REPEAT RES_TAC ;
           RES_TAC ] ;
       
       XRULE_ASSUM_TAC (REWRITE_RULE [DELETE_NON_ELEMENT])
       THEN XRULE_ASSUM_TAC (REWRITE_RULE [ASSUME "W DELETE (x:*) = W"])
       THEN OLD_RES_TAC ] ) ;;

%--------------------------------------------------------------------------------
  FIN_ADMIT_WF_IND: 
  States that a transitive and anti reflexive relation on a finite domain will
  admit WF induction.
--------------------------------------------------------------------------------%

let FIN_ADMIT_WF_IND = prove_thm
  (`FIN_ADMIT_WF_IND`,
   "!R:^Rel.
        REL_TRANS R  /\  REL_ANTI_REFL R  /\  FINITE (UNIV:(*)set)
        ==>
        ADMIT_WF_INDUCTION R",
    REWRITE_TAC [(SYM o SPEC_ALL) WF_EQU_IND]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FIN_WF_lemma1
    THEN MATCH_MP_TAC 
         ((BETA_RULE o SPEC "^ALL_WF (R:^Rel)" o REWRITE_RULE [FINITE_DEF] o 
           ASSUME) "FINITE (UNIV:(*)set)")
    THEN REPEAT STRIP_TAC
    THENL [ IMP_RES_TAC FIN_WF_lemma2 ;
            IMP_RES_TAC FIN_WF_lemma3 ] ) ;;

%--------------------------------------------------------------------------------
  ADMIT_WF_ANTI_REFL = |- !R. ADMIT_WF_INDUCTION R ==> REL_ANTI_REFL R
--------------------------------------------------------------------------------%

let ADMIT_WF_ANTI_REFL = prove_thm
  (`ADMIT_WF_ANTI_REFL`,
   "!R:^Rel. ADMIT_WF_INDUCTION R ==> REL_ANTI_REFL R",
    REWRITE_TAC [REL_ANTI_REFL]
    THEN GEN_TAC THEN STRIP_TAC
    THEN MATCH_MP_TAC ((BETA_RULE o
                        SPEC "\x:*. ~R x x" o
                        REWRITE_RULE [ADMIT_WF_INDUCTION] o 
                        ASSUME) "ADMIT_WF_INDUCTION (R:^Rel)")
    THEN REPEAT STRIP_TAC
    THEN RES_TAC) ;;

%--------------------------------------------------------------------------------
   Prove that < on natural number admits WF_INDUCTION. Therefore we need the
   following lemma about natural numbers:

   LESS_EQ__EQ_LESS_SUC = |- !x y. x <= y = x < (SUC y)
--------------------------------------------------------------------------------%

let LESS_EQ__EQ_LESS_SUC = prove_thm
  (`LESS_EQ__EQ_LESS_SUC`,
   "!x y. (x <= y) = (x < (SUC y))",
    REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC
    THENL [IMP_RES_TAC LESS_EQ_IMP_LESS_SUC ; 
           REWRITE_TAC [LESS_OR_EQ] 
           THEN IMP_RES_TAC LESS_LEMMA1 
           THEN ASM_REWRITE_TAC[] ] ) ;;

let NUM_ADMIT_lemma1 = prove
  ("!P z. (!y. (!x. x<y ==> P x) ==> P y)  /\  (!x. x<=z ==> P x)
          ==> (!x. x <= (SUC z) ==> P x)",
    REPEAT GEN_TAC THEN STRIP_TAC 
    THEN RULE_ASSUM_TAC (REWRITE_RULE [LESS_EQ__EQ_LESS_SUC])
    THEN REWRITE_TAC [LESS_OR_EQ] 
    THEN REPEAT STRIP_TAC
    THEN RES_TAC THEN ASM_REWRITE_TAC[]) ;;

let NUM_ADMIT_lemma2 = prove
  ("!P. (!y. (!x. x<y ==> P x) ==> P y) ==> (!x. x <= 0 ==> P x)",
    REPEAT GEN_TAC THEN STRIP_TAC
    THEN REWRITE_TAC [LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THENL [ RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_0]) 
            THEN CONTR_TAC (ASSUME "F") ;
            ASM_TAC (SPEC "0")
            THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS_0]) 
            THEN ASM_REWRITE_TAC[] ]) ;;

%--------------------------------------------------------------------------------
  NUM_ADMIT_WF_INDUCTION: states that < on num admits WF_INDUCTION
--------------------------------------------------------------------------------%

let NUM_ADMIT_WF_INDUCTION = prove_thm
  (`NUM_ADMIT_WF_INDUCTION`,
   "ADMIT_WF_INDUCTION $<",
    REWRITE_TAC [ADMIT_WF_INDUCTION]
    THEN REPEAT STRIP_TAC
    THEN ASSUME_TAC ((BETA_RULE o SPEC "\y. (!x. x<=y ==> P x)") INDUCTION)
    THEN IMP_RES_TAC NUM_ADMIT_lemma1
    THEN IMP_RES_TAC NUM_ADMIT_lemma2
    THEN RES_TAC 
    THEN RULE_ASSUM_TAC (REWRITE_RULE [LESS_OR_EQ])
    THEN ASM_TAC (REWRITE_RULE[] o SPECL ["x:num" ; "x:num"])
    THEN ASM_REWRITE_TAC[]) ;;

%-------------------------------------------------------------------------------%

let REL_JOINT = new_infix_definition
  (`REL_JOINT`, "REL_JOINT (U:^Rel) V = \x y. U x y /\ V x y") ;;

let REL_JOINT_ADMIT_lemma = prove
  ("!P. (!y:*. (!x. U x y /\ V x y ==> P x) ==> P y) ==>
        (!y. (!x. U x y ==> P x) ==> P y)",
    REPEAT STRIP_TAC
    THEN (MATCH_MP_TAC o ASSUME) "(!y:*. (!x. U x y /\ V x y ==> P x) ==> P y)"
    THEN REPEAT STRIP_TAC
    THEN RES_TAC) ;;

%--------------------------------------------------------------------------------
  REL_JOINT_ADMIT_WF_INDUCTION: 
  states that the joint (intersection) of two relations preserves WF_INDUCTION
--------------------------------------------------------------------------------%

let REL_JOINT_ADMIT_WF_IND = prove_thm
  (`REL_JOINT_ADMIT_WF_IND`,
   "!U (V:^Rel). ADMIT_WF_INDUCTION U /\ ADMIT_WF_INDUCTION V ==>
                 ADMIT_WF_INDUCTION (U REL_JOINT V)",
    REWRITE_TAC [REL_JOINT; ADMIT_WF_INDUCTION]
    THEN BETA_TAC THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC REL_JOINT_ADMIT_lemma
    THEN RES_TAC THEN ASM_REWRITE_TAC[]) ;;

%-------------------------------------------------------------------------------%

let REL_PROD = new_infix_definition
  (`REL_PROD`, 
   "REL_PROD (U:^Rel1) (V:^Rel2) = 
    (\x y. U (FST x) (FST y) /\ V (SND x) (SND y))") ;;

let PROD_ADMIT_lemma = prove
  ("!P. 
    (!Y. (!X. U(FST X)(FST Y) /\ V(SND X)(SND Y) ==> P X) ==> P Y) ==>
         (!b:*. (!a. U a b ==> (!x:**. P(a,x))) ==> (!x. P(b,x)))",
    REPEAT STRIP_TAC
    THEN ASM_TAC (SPEC "b:*, x:**")
    THEN (MATCH_MP_TAC o ASSUME)
         "(!X:(*#**). U(FST X)(FST(b,x)) /\ V(SND X)(SND(b,x)) ==> P X) ==> P(b,x)"
    THEN REWRITE_TAC [FST] THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_TAC (REWRITE_RULE [PAIR] o SPEC "SND (X:(*#**))")
    THEN ASM_REWRITE_TAC[]) ;;

%--------------------------------------------------------------------------------
  REL_PROD_ADMIT_WF_INDUCTION: 
  states that the product of two relations preserves WF_INDUCTION
--------------------------------------------------------------------------------%

let REL_PROD_ADMIT_WF_IND = prove_thm
  (`REL_PROD_ADMIT_WF_IND`,
   "!(U:^Rel1) (V:^Rel2). 
         ADMIT_WF_INDUCTION U /\ ADMIT_WF_INDUCTION V ==>
         ADMIT_WF_INDUCTION (U REL_PROD V)",
    REWRITE_TAC [REL_PROD; ADMIT_WF_INDUCTION]
    THEN BETA_TAC THEN REPEAT STRIP_TAC
    THEN ASM_TAC (BETA_RULE o SPEC "\a:*. !x:**. P(a,x)")
    THEN IMP_RES_TAC PROD_ADMIT_lemma
    THEN RES_TAC
    THEN ONCE_REWRITE_TAC [(SYM o SPEC_ALL) PAIR] THEN ASM_REWRITE_TAC []) ;;
    
%-------------------------------------------------------------------------------%

let REL_LEXI = new_infix_definition
  (`REL_LEXI`, 
   "REL_LEXI (U:^Rel1) (V:^Rel2) = 
    (\x y. U (FST x) (FST y) \/ (((FST x)=(FST y)) /\ V (SND x) (SND y)))") ;;

let Dpred = ":(*#**)->bool" ;;
let FIRST  = "\P:^Dpred. \x. ?y. P(x,y)" ;;
let SECOND = "\(P:^Dpred) m. \y. P(m,y)" ;;

%--------------------------------------------------------------------------------
  Now we are going to prove that lexicographic product preserve the WF 
  induction.
--------------------------------------------------------------------------------%

let LEXI_lemma1 = (BETA_RULE o prove)
  ("!P:^Dpred. ~(P=FF) ==> ~((^FIRST P)=FF)",
    REWRITE_TAC [FF_DEF] THEN BETA_TAC
    THEN REWRITE_TAC [EXT_lemma] THEN BETA_TAC
    THEN REWRITE_TAC [NOT_EXISTS_CONV "~(?y. (P:^Dpred)(x,y))"]
    THEN REWRITE_TAC [NOT_FORALL_CONV "~(!x. ~(P:^Dpred) x)"]
    THEN REPEAT STRIP_TAC
    THEN XRULE_ASSUM_TAC (SPECL ["FST (x:*#**)"; "SND (x:*#**)"])
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [PAIR])
    THEN IMP_RES_TAC CONTRA_lemma) ;;

let LEXI_lemma2 = (BETA_RULE o prove)
  ("!(P:^Dpred) (R:^Rel1). 
        ~(P=FF) /\ WELL_FOUNDED R ==>
        (?a. (^FIRST P)a /\ (!b. (^FIRST P)b ==> ~(R b a)))",
    REWRITE_TAC [WELL_FOUNDED_CONTRA] THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LEXI_lemma1
    THEN RES_TAC
    THEN XRULE_ASSUM_TAC BETA_RULE
    THEN EXISTS_TAC "y:*"
    THEN ASM_REWRITE_TAC[]) ;;

let LEXI_lemma3 = (BETA_RULE o prove)
  ("!(P:^Dpred) m. 
        ~(P=FF) /\ (^FIRST P)m ==> ~((^SECOND P m)=FF)",
    BETA_TAC THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LEXI_lemma1
    THEN XRULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE [FF_DEF; EXT_lemma])
    THEN XRULE_ASSUM_TAC (SPEC "y:**")
    THEN IMP_RES_TAC CONTRA_lemma) ;;

let MYRULE1 thm =
    let th1 = ASSUME "(P:^Dpred) X" in
    let th2 = ONCE_REWRITE_RULE [(SYM o SPEC_ALL) PAIR] th1 in
    let th3 = EXISTS ("?y:**. P(FST (X:*#**),y)","SND (X:*#**)") th2 in
    MP (SPEC "FST (X:*#**)" thm) th3 ;;

let LEXI_lemma4 = (BETA_RULE o prove)
  ("!(P:^Dpred) (U:^Rel1) (V:^Rel2) m.
         ~(P=FF) /\ (!Y. P Y ==> (?X. (U REL_LEXI V) X Y  /\  P X))  /\
         (!a. (^FIRST P)a ==> ~(U a m))
         ==>
         (!v. (^SECOND P m)v ==> (?u. V u v /\ (^SECOND P m)u))",
    REWRITE_TAC [REL_LEXI] THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THENL [ XRULE_ASSUM_TAC MYRULE1
            THEN XRULE_ASSUM_TAC (REWRITE_RULE [SND])
            THEN IMP_RES_TAC CONTRA_lemma ;
            EXISTS_TAC "SND (X:*#**)"
            THEN XRULE_ASSUM_TAC (REWRITE_RULE [FST; SND])
            THEN UNDISCH_TAC "(P:^Dpred) X"
            THEN ONCE_REWRITE_TAC [(SYM o SPEC_ALL) PAIR]
            THEN SUBST1_TAC (ASSUME "FST (X:*#**) = m")
            THEN ASM_REWRITE_TAC [FST; SND] ]) ;;            

let LEXI_lemma5 = prove
  ("!(U:^Rel1) (V:^Rel2).
         ~(WELL_FOUNDED (U REL_LEXI V)) /\ WELL_FOUNDED U 
         ==>
         (?P. ~(P=FF) /\ (!v. P v ==> (?u. V u v /\ P u)))",
    REWRITE_TAC [NOT_WF] THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN OLD_IMP_RES_TAC LEXI_lemma2
    THEN UNDISCH_ALL_TAC THEN REPEAT STRIP_TAC
    THEN XRULE_ASSUM_TAC (EXISTS ("?y. (P:^Dpred)(a,y)", "y:**"))
    THEN OLD_IMP_RES_TAC (SPECL ["P:^Dpred"; "a:*"] LEXI_lemma3)
    THEN OLD_IMP_RES_TAC LEXI_lemma4
    THEN EXISTS_TAC "^SECOND (P:^Dpred) (a:*)"
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[]) ;;

%----------------------------------------------------------------------------------
  REL_LEXI_ADMIT_WF_IND:
  States that lexicographic product does preserve the WF induction.
----------------------------------------------------------------------------------%

let REL_LEXI_ADMIT_WF_IND = prove_thm
  (`REL_LEXI_ADMIT_WF_IND`,
   "!(U:^Rel1) (V:^Rel2).
        ADMIT_WF_INDUCTION U  /\  ADMIT_WF_INDUCTION V
        ==>
        ADMIT_WF_INDUCTION (U REL_LEXI V)",
    REWRITE_TAC [(SYM o SPEC_ALL) WF_EQU_IND]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC "WELL_FOUNDED ((U:^Rel1) REL_LEXI (V:^Rel2))"
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC LEXI_lemma5
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [WELL_FOUNDED_CONTRA])
    THEN REPEAT RES_TAC) ;;

%----------------------------------------------------------------------------------
  Now we are going to define what is a finite product on relations, then proves
  that this preserves WF induction. 

  Due to the chosen representation, the relations are required to be all on the 
  same domain.
----------------------------------------------------------------------------------%

let Rel_Vec = ":num->^Rel";;
let Vector = ":num->*" ;;

let TAIL = new_definition
  (`TAIL`, "TAIL (s:^Vector) = (\i. s(SUC i))") ;;

let REL_FPROD = new_prim_rec_definition
  (`REL_FPROD`,
   "(REL_FPROD 0 (R:^Rel_Vec) (s:^Vector) (t:^Vector) = (R 0) (s 0) (t 0)) /\
    (REL_FPROD (SUC n) R s t = 
       (R 0) (s 0) (t 0)  /\  REL_FPROD n (TAIL R) (TAIL s) (TAIL t))") ;;

let FPROD_lemma1_1 = prove
  ("!V:(^Vector)set. ({a | (\x. ?s. s IN V /\ (x = s 0)) a} = {}) ==> (V={})",
    REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_GSPEC_lemma]
    THEN BETA_TAC THEN REPEAT STRIP_TAC
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [NOT_EXISTS_CONV
          "~(?s:^Vector. s IN V /\ (x = s 0))"])
    THEN RES_TAC
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [] o SPEC "(x:^Vector) 0")
    THEN ASM_REWRITE_TAC[]) ;;

let FPROD_lemma1_2 =
    (SPEC "{a | (\x. ?s. s IN (V:(^Vector)set) /\ (x = s 0)) a}" o
     REWRITE_RULE [WELL_FOUNDED] o
     ASSUME) "WELL_FOUNDED ((R:^Rel_Vec) 0)" ;;
        
let FPROD_lemma1 = prove
   ("!(R:^Rel_Vec) n. WELL_FOUNDED (R 0) ==> WELL_FOUNDED (REL_FPROD n R)",
    REPEAT GEN_TAC 
    THEN DISJ_CASES_TAC (SPEC "n:num" num_CASES)
    THEN UNDISCH_ALL_TAC THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC [WELL_FOUNDED; REL_FPROD]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FPROD_lemma1_1 
    THEN MATCH_MP_TAC FPROD_lemma1_2
    THEN REWRITE_TAC [IN_GSPEC_lemma] THEN BETA_TAC
    THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN EXISTS_TAC "(x:^Vector) 0" THEN ASM_REWRITE_TAC []
    THEN EXISTS_TAC "x:^Vector" THEN ASM_REWRITE_TAC []) ;;

%----------------------------------------------------------------------------------
  FPROD_ADMIT_WF_IND
  States that finite product of N relations preserves WF induction.
----------------------------------------------------------------------------------%

let FPROD_ADMIT_WF_IND = prove_thm
  (`FPROD_ADMIT_WF_IND`,
   "!(R:^Rel_Vec) n. 
          (!i. (i<=n) ==> ADMIT_WF_INDUCTION (R i))  ==>  
           ADMIT_WF_INDUCTION (REL_FPROD n R)",
    REWRITE_TAC [(SYM o SPEC_ALL) WF_EQU_IND]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FPROD_lemma1
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [LESS_OR_EQ] o SPEC "0")
    THEN XRULE_ASSUM_TAC (ONCE_REWRITE_RULE [DISJ_SYM])
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [LESS_0_CASES])
    THEN ASM_REWRITE_TAC[]) ;;

%----------------------------------------------------------------------------------
  Now we are going to define what is a finite lexicographic product of relations, 
  then proves that this preserves WF induction. 

  Due to the chosen representation, the relations are required to be all on the 
  same domain.
----------------------------------------------------------------------------------%

let REL_FLEXI = new_prim_rec_definition
  (`REL_FLEXI`,
   "(REL_FLEXI 0 (R:^Rel_Vec) (s:^Vector) (t:^Vector) = (R 0) (s 0) (t 0)) /\
    (REL_FLEXI (SUC n) R s t = 
       (R 0) (s 0) (t 0)  \/
       ((s 0 = t 0) /\ REL_FLEXI n (TAIL R) (TAIL s) (TAIL t)))") ;;

let FLEXI_lemma = prove_thm
  (`FLEXI_lemma`,
   "!(R:^Rel_Vec) n s t. 
        REL_FLEXI (SUC n) R s t = 
        ((R 0) REL_LEXI (REL_FLEXI n (TAIL R))) ((s 0),(TAIL s)) ((t 0),(TAIL t))",
    REWRITE_TAC [REL_FLEXI; REL_LEXI] THEN BETA_TAC
    THEN REWRITE_TAC [FST; SND]) ;;

let FLEXI_lemma1 = prove
   ("!R:^Rel_Vec. WELL_FOUNDED (R 0) ==> WELL_FOUNDED (REL_FLEXI 0 R)",
    REPEAT STRIP_TAC
    THEN REWRITE_TAC [WELL_FOUNDED; REL_FLEXI]
    THEN REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FPROD_lemma1_1 
    THEN MATCH_MP_TAC FPROD_lemma1_2
    THEN REWRITE_TAC [IN_GSPEC_lemma] THEN BETA_TAC
    THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN EXISTS_TAC "(x:^Vector) 0" THEN ASM_REWRITE_TAC []
    THEN EXISTS_TAC "x:^Vector" THEN ASM_REWRITE_TAC []) ;;


let FLEXI_lemma2_1 = prove
  ("!V:(^Vector)set.
       ({z | (\x. ?s. s IN V /\ (FST x = s 0) /\ (SND x = TAIL s))z } = {}) ==>
       (V={})",
    REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_GSPEC_lemma]
    THEN BETA_TAC THEN REPEAT STRIP_TAC
    THEN RES_TAC 
    THEN XRULE_ASSUM_TAC (SPEC "((x:^Vector) 0, TAIL x)")
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [FST; SND])
    THEN ASM_REWRITE_TAC[]) ;;

let FLEXI_lemma2 = prove
  ("!(U:^Rel_Vec) n. 
       WELL_FOUNDED ((U 0) REL_LEXI (REL_FLEXI n (TAIL U))) ==>
       WELL_FOUNDED (REL_FLEXI (SUC n) U)",
    REWRITE_TAC [WELL_FOUNDED; FLEXI_lemma]
    THEN REPEAT STRIP_TAC
    THEN XRULE_ASSUM_TAC (SPEC 
         "{z | (\x. ?s. (s:^Vector) IN V /\ (FST x = s 0) /\ (SND x = TAIL s))z}")
    THEN XRULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE [IN_GSPEC_lemma])
    THEN MATCH_MP_TAC FLEXI_lemma2_1 THEN BETA_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN EXISTS_TAC "((x:^Vector) 0, TAIL x)"
    THEN (SUBST1_TAC o SYM o ISPEC "y:*#^Vector") PAIR
    THEN SUBST1_TAC (ASSUME "FST (y:*#^Vector) = s 0")
    THEN SUBST1_TAC (ASSUME "SND (y:*#^Vector) = TAIL s")
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC "x:^Vector"
    THEN ASM_REWRITE_TAC[]) ;;
 
let FLEXI_lemma3 = prove
  ("!(U:^Rel_Vec) n. 
       WELL_FOUNDED (U 0) /\
       WELL_FOUNDED (REL_FLEXI n (TAIL U)) ==>
       WELL_FOUNDED (REL_FLEXI (SUC n) U)",
    REPEAT STRIP_TAC
    THEN MATCH_MP_TAC FLEXI_lemma2
    THEN IMP_RES_TAC (REWRITE_RULE [(SYM o SPEC_ALL) WF_EQU_IND]
                      REL_LEXI_ADMIT_WF_IND)) ;;

let SUC_MONO = prove
  ("!n m. (n<=m) ==> ((SUC n)<=(SUC m))",
    REWRITE_TAC [LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THENL [IMP_RES_TAC LESS_MONO
           THEN ASM_REWRITE_TAC[] ;
           ASM_REWRITE_TAC[] ]) ;;

%----------------------------------------------------------------------------------
  FLEXI_ADMIT_WF_IND
  States that finite lexicographic product of N relations preserves WF induction.
----------------------------------------------------------------------------------%

let FLEXI_WF = 
    "\n. !R:^Rel_Vec. 
             (!i. (i<=n) ==> WELL_FOUNDED (R i)) ==>
              WELL_FOUNDED (REL_FLEXI n R)" ;;

let FLEXI_ADMIT_WF_IND  = save_thm
  (`FLEXI_ADMIT_WF_IND`,
   (BETA_RULE o prove)("!n. ^FLEXI_WF n",
    BETA_TAC THEN (MATCH_MP_TAC o BETA_RULE o SPEC "^FLEXI_WF") INDUCTION
    THEN REPEAT STRIP_TAC
    THENL [ MATCH_MP_TAC FLEXI_lemma1
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN REWRITE_TAC [LESS_OR_EQ; LESS_0_CASES] ;
            MATCH_MP_TAC FLEXI_lemma3 THEN CONJ_TAC 
            THENL [ FIRST_ASSUM MATCH_MP_TAC
                    THEN REWRITE_TAC [LESS_OR_EQ; LESS_0] ;
                    FIRST_ASSUM MATCH_MP_TAC
                    THEN REPEAT STRIP_TAC 
                    THEN REWRITE_TAC [TAIL] THEN BETA_TAC
                    THEN FIRST_ASSUM MATCH_MP_TAC
                    THEN IMP_RES_TAC SUC_MONO ] ])) ;;


close_theory() ;;

%---- DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG DCG ----%

