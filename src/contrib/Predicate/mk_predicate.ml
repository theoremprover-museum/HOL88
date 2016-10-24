new_theory `predicate`;;
load_library `taut` ;;
load_library `sets` ;;
loadf `my_misc`;;
loadf `OLD_RES` ;;

let TT_DEF = new_definition (`TT_DEF`, "(TT:*->bool) = \s:*.T");;

let FF_DEF = new_definition (`FF_DEF`, "(FF:*->bool) = \s:*.F");;

let pNOT_DEF = new_definition (`pNOT_DEF`, "NOT (p:*->bool) = \s:*. ~p s");;

let pAND_DEF = new_infix_definition (`pAND_DEF`, 
    "AND (p:*->bool) (q:*->bool) = \s:*. (p s) /\ (q s)");;

let pOR_DEF = new_infix_definition (`pOR_DEF`, 
    "OR (p:*->bool) (q:*->bool) = \s:*. (p s) \/ (q s)");;

let pIMP_DEF = new_infix_definition (`pIMP_DEF`, 
    "IMP (p:*->bool) (q:*->bool) = \s:*. (p s) ==> (q s)");;

let EQUAL_DEF = new_infix_definition (`EQUAL_DEF`, 
    "EQUAL (p:*->bool) (q:*->bool) = \s:*. (p s) = (q s)");;
new_binder_definition(`qAND`,"!! P = (\s:*. !i:**. P i)") ;;
new_binder_definition(`qOR`,"?? P = (\s:*. ?i:**. P i)") ;;

let RES_qAND = new_definition (`RES_qAND`,
   "RES_qAND (W:**->bool) (P:**->(*->bool)) = (\s. (!i. W i ==> P i s))") ;;

let RES_qOR = new_definition (`RES_qOR`, 
   "RES_qOR (W:**->bool) (P:**->(*->bool)) = (\s. ?i. W i /\  P i s)") ;;

associate_restriction (`!!`, `RES_qAND`) ;;
associate_restriction (`??`, `RES_qOR`) ;;
new_special_symbol `|==` ;;

let pSEQ_DEF = new_definition
  (`pSEQ_DEF`, "|== (p:*->bool) = !s:*. (p s)") ;;
let pred_JADE_TAC n =
    REWRITE_TAC (snd(split (definitions `predicate`)))
    THEN RESTRICT_DEF_TAC
    THEN (REPEAT STRIP_TAC)
    THEN (REPEAT_FIN n (ASM_REWRITE_TAC [] THEN RES_TAC)) ;;

let pred_CYAN_TAC =
    REWRITE_TAC (snd(split (definitions `predicate`)))
    THEN RESTRICT_DEF_TAC
    THEN REPEAT GEN_TAC THEN EXT_TAC THEN TAUT_TAC ;;
let pAND_SYM = prove_thm 
  (`pAND_SYM`, "!(p:*->bool) q. (p AND q) = (q AND p)", pred_CYAN_TAC) ;;

let pAND_ASSOC = prove_thm 
  (`pAND_ASSOC`, 
   "!(p:*->bool) q r. (p AND q) AND r = p AND (q AND r)", pred_CYAN_TAC) ;;

let pAND_UNIT = prove_thm 
  (`pAND_UNIT`, "!p:*->bool. (TT AND p) = p", pred_CYAN_TAC) ;;

let pOR_SYM = prove_thm 
  (`pOR_SYM`, "!(p:*->bool) q. (p OR q) = (q OR p)", pred_CYAN_TAC) ;;

let pOR_ASSOC = prove_thm 
  (`pOR_ASSOC`,
   "!(p:*->bool) q r. (p OR q) OR r =  p OR (q OR r)", pred_CYAN_TAC) ;;

let pOR_UNIT = prove_thm 
  (`pOR_UNIT`, "!p:*->bool. (FF OR p) = p", pred_CYAN_TAC) ;;
let pAND_ZERO = prove_thm 
  (`pAND_ZERO`, "!p:*->bool. (FF AND p) = FF", pred_CYAN_TAC) ;;

let pAND_LOVER_OR = prove_thm 
  (`pAND_LOVER_OR`,
   "!(p:*->bool) q r. p AND (q OR r) = (p AND q) OR (p AND r)", 
    pred_CYAN_TAC) ;;

let pAND_ROVER_OR = prove_thm 
  (`pAND_ROVER_OR`,
   "!(p:*->bool) q r. (p OR q) AND r = (p AND r) OR (q AND r)", 
    pred_CYAN_TAC) ;;

let pOR_ZERO = prove_thm 
  (`pOR_ZERO`, "!p:*->bool. (TT OR p) = TT", pred_CYAN_TAC) ;;

let pOR_LOVER_AND = prove_thm 
  (`pOR_LOVER_AND`,
   "!(p:*->bool) q r. p OR (q AND r) = (p OR q) AND (p OR r)", 
    pred_CYAN_TAC) ;;

let pOR_ROVER_AND = prove_thm 
  (`pOR_ROVER_AND`,
   "!(p:*->bool) q r. (p AND q) OR r = (p OR r) AND (q OR r)", 
    pred_CYAN_TAC) ;;
let pAND_REFL = prove_thm 
  (`pAND_REFL`, "!p:*->bool. (p AND p) = p", pred_CYAN_TAC) ;;

let pOR_REFL = prove_thm 
  (`pOR_REFL`, "!p:*->bool. (p OR p) = p", pred_CYAN_TAC) ;;
let pAND_LOVER_AND = prove_thm 
  (`pAND_LOVER_AND`,
   "!(p:*->bool) q r. p AND (q AND r) = (p AND q) AND (p AND r)", 
    pred_CYAN_TAC) ;;

let pOR_LOVER_OR = prove_thm 
  (`pOR_LOVER_OR`,
   "!(p:*->bool) q r. p OR (q OR r) = (p OR q) OR (p OR r)", 
    pred_CYAN_TAC) ;;

let pAND_ROVER_AND = prove_thm 
  (`pAND_ROVER_AND`,
   "!(p:*->bool) q r. (p AND q) AND r = (p AND r) AND (q AND r)", 
    pred_CYAN_TAC) ;;

let pOR_ROVER_OR = prove_thm 
  (`pOR_ROVER_OR`,
   "!(p:*->bool) q r. (p OR q) OR r = (p OR r) OR (q OR r)", 
    pred_CYAN_TAC) ;;
let pIMP_REFL = prove_thm
  (`pIMP_REFL`,
   "!P:*->bool. (|== (P IMP P))", pred_JADE_TAC 5) ;;

let pIMP_TRANS = prove_thm
  (`pIMP_TRANS`,
   "!(P:*->bool) Q R. (|== (P IMP Q)) /\ (|== (Q IMP R)) ==>
                      (|== (P IMP R))",
    pred_JADE_TAC 5) ;;

let pIMP_ANTISYM = prove_thm
  (`pIMP_ANTISYM`,
   "!(P:*->bool) Q. (|== (P IMP Q)) /\ (|== (Q IMP P)) ==>
                      (P=Q)",
    pred_JADE_TAC 1 THEN EXT_TAC
    THEN EQ_TAC THEN pred_JADE_TAC 5) ;;
let qAND_GLB1 = prove_thm(`qAND_GLB1`,
    "!(W:**->bool) (P:**->(*->bool)). 
         !i:: W. |== ((!! j:: W. P j) IMP (P i))",
    pred_JADE_TAC 5) ;;

let qAND_GLB2 = prove_thm(`qAND_GLB2`,
    "!(W:**->bool) (P:**->(*->bool)) (q:*->bool).
         (!i:: W. |== (q IMP (P i))) ==> (|== (q IMP (!! j:: W. P j)))",
    pred_JADE_TAC 5) ;;

let qOR_LUB1 = prove_thm(`qOR_LUB1`,
    "!(W:**->bool) (P:**->(*->bool)).
         !i:: W. (|== ((P i) IMP (?? j:: W. P j)))",
    pred_JADE_TAC 0
    THEN EXISTS_TAC "x:**" THEN ASM_REWRITE_TAC[] ) ;;

let qOR_LUB2 = prove_thm(`qOR_LUB2`,
    "!(W:**->bool) (P:**->(*->bool)) (q:*->bool).
         (!i:: W. |== ((P i) IMP q)) ==> (|== ((?? j:: W. P j) IMP q))",
    pred_JADE_TAC 5) ;;
let FF_TOP = prove_thm(`FF_TOP`,
    "!p:*->bool. |== (FF IMP p)", pred_JADE_TAC 5) ;;

let TT_BOTTOM = prove_thm(`TT_BOTTOM`,
    "!p:*->bool. |== (p IMP TT)", pred_JADE_TAC 5) ;;

let qOR_EMPTY = prove_thm (`qOR_EMPTY`,
    "!P:**->(*->bool). (??i:: FF. P i) = FF",
    EXT_TAC THEN pred_JADE_TAC 0) ;;

let qAND_EMPTY = prove_thm (`qAND_EMPTY`,
    "!P:**->(*->bool). (!!i:: FF. P i) = TT",
    EXT_TAC THEN pred_JADE_TAC 0) ;;
let NOT_TT = prove_thm
  (`NOT_TT`, "NOT (TT:*->bool) = FF", pred_CYAN_TAC) ;;

let NOT_FF = prove_thm
  (`NOT_FF`, "NOT (FF:*->bool) = TT", pred_CYAN_TAC) ;;
let pDEMORGAN1 = prove_thm 
  (`pDEMORGAN1`, 
   "!(p:*->bool) q. (NOT (p AND q)) = ((NOT p) OR (NOT q))",
    pred_CYAN_TAC) ;;

let pDEMORGAN2 = prove_thm 
  (`pDEMORGAN2`, 
   "!(p:*->bool) q. (NOT (p OR q)) = ((NOT p) AND (NOT q))",
    pred_CYAN_TAC) ;;
let pCONTRA_POS = prove_thm
  (`pCONTRA_POS`,
   "!(p:*->bool) q. (p IMP q) = ((NOT q) IMP (NOT p))",
    pred_CYAN_TAC) ;;
let qAND_SINGLETON = prove_thm(`qAND_SINGLETON`,
    "!(P:**->(*->bool)) a. (!!i:: (\j. a=j). P i) = (P a)",
    EXT_TAC THEN EQ_TAC 
    THEN pred_JADE_TAC 0
    THENL [ XRULE_ASSUM_TAC (REWRITE_RULE[] o (SPEC "a:**")) 
            THEN ASM_REWRITE_TAC[] ;
            XRULE_ASSUM_TAC SYM THEN ASM_REWRITE_TAC [] ] ) ;;

let qOR_SINGLETON = prove_thm(`qOR_SINGLETON`,
    "!(P:**->(*->bool)) a. (??i:: (\j. a=j). P i) = (P a)",
    EXT_TAC THEN EQ_TAC
    THEN pred_JADE_TAC 0
    THENL [ALL_TAC ; EXISTS_TAC "a:**"]
    THEN ASM_REWRITE_TAC[] ) ;;
let qAND_AND = prove_thm(`qAND_AND`,
    "!(p:*->bool) q. (!!i:: (\j. (p=j) \/ (q=j)). i) = (p AND q)",
    EXT_TAC THEN EQ_TAC
    THEN pred_JADE_TAC 1
    THEN XRULE_ASSUM_TAC SYM THEN ASM_REWRITE_TAC[]
    THENL 
    [ XRULE_ASSUM_TAC (REWRITE_RULE [] o (SPEC "p:*->bool")) ;
      XRULE_ASSUM_TAC (REWRITE_RULE [] o (SPEC "q:*->bool")) ]
    THEN ASM_REWRITE_TAC []) ;;

let qOR_OR = prove_thm(`qOR_OR`,
    "!(p:*->bool) q. (??i:: (\j. (p=j) \/ (q=j)). i) = (p OR q)",
    EXT_TAC THEN EQ_TAC
    THEN pred_JADE_TAC 1
    THEN XRULE_ASSUM_TAC SYM THEN ASM_REWRITE_TAC[]
    THENL [EXISTS_TAC "p:*->bool" ; EXISTS_TAC "q:*->bool"]
    THEN ASM_REWRITE_TAC []) ;;
let qAND_RIGHT_DISTR_AND = prove_thm
  (`qAND_RIGHT_DISTR_AND`,
   "!W (P:**->(*->bool)) p. 
        ~(W=FF)  ==>  ((!!i::W. P i) AND p = (!!i::W. (P i) AND p))",
    REWRITE_TAC [FUN_EQ_CONV "(f:*->**)=g"]
    THEN pred_JADE_TAC 0
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [NOT_FORALL_CONV "~(!x:**. ~W x)"])
    THEN UNDISCH_ALL_TAC THEN STRIP_TAC
    THEN EQ_TAC THEN pred_JADE_TAC 5) ;;

let qAND_LEFT_DISTR_AND = prove_thm
  (`qAND_LEFT_DISTR_AND`,
   "!W (P:**->(*->bool)) p. 
        ~(W=FF)  ==>  (p AND (!!i::W. P i) = (!!i::W. p AND (P i)))",
    ONCE_REWRITE_TAC [pAND_SYM]
    THEN ACCEPT_TAC qAND_RIGHT_DISTR_AND) ;;

let qAND_LEFT_DISTR_OR = prove_thm (`qAND_LEFT_DISTR_OR`,
    "!W (P:**->(*->bool)) p. (p AND (??i::W. P i)) = (??i::W. p AND P i)",
    EXT_TAC THEN EQ_TAC
    THEN pred_JADE_TAC 1
    THEN EXISTS_TAC "i:**" THEN ASM_REWRITE_TAC []) ;;

let qAND_RIGHT_DISTR_OR = prove_thm (`qAND_RIGHT_DISTR_OR`,
    "!W (P:**->(*->bool)) p. ((??i::W. P i) AND p) = (??i::W. (P i) AND p)",
    ONCE_REWRITE_TAC [pAND_SYM]
    THEN ACCEPT_TAC qAND_LEFT_DISTR_OR) ;;
let qOR_RIGHT_DISTR_AND = prove_thm
  (`qOR_RIGHT_DISTR_AND`,
   "!W (P:**->(*->bool)) p. (!!i::W. P i) OR p = (!!i::W. (P i) OR p)",
   EXT_TAC THEN EQ_TAC 
   THEN pred_JADE_TAC 1
   THEN RES_TAC THEN ASM_REWRITE_TAC[]
   THEN ASM_CASES_TAC "(p:*->bool) x"
   THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
   THEN XRULE_ASSUM_TAC (REWRITE_RULE [ASSUME "~(p:*->bool) x"])
   THEN RES_TAC) ;;

let qOR_LEFT_DISTR_AND = prove_thm
  (`qOR_LEFT_DISTR_AND`,
   "!W (P:**->(*->bool)) p. p OR (!!i::W. P i) = (!!i::W. p OR (P i))",
    ONCE_REWRITE_TAC [pOR_SYM]
    THEN ACCEPT_TAC qOR_RIGHT_DISTR_AND) ;;

let qOR_RIGHT_DISTR_OR = prove_thm (`qOR_RIGHT_DISTR_OR`,
    "!W (P:**->(*->bool)) p. 
        ~(W=FF) ==> (((??i::W. P i) OR p) = (??i::W. (P i) OR p))",
    REWRITE_TAC [FUN_EQ_CONV "(f:*->**)=g"]
    THEN pred_JADE_TAC 0
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [NOT_FORALL_CONV "~(!x:**. ~W x)"])
    THEN UNDISCH_ALL_TAC THEN STRIP_TAC
    THEN EQ_TAC THEN REPEAT STRIP_TAC 
    THENL [ EXISTS_TAC "i:**" ;
            EXISTS_TAC "x':**" ;
            DISJ1_TAC THEN EXISTS_TAC "i:**" ;
            ALL_TAC ]
    THEN ASM_REWRITE_TAC[]) ;;

let qOR_LEFT_DISTR_OR = prove_thm (`qOR_LEFT_DISTR_OR`,
    "!W (P:**->(*->bool)) p. 
        ~(W=FF) ==> ((p OR (??i::W. P i)) = (??i::W. p OR (P i)))",     
    ONCE_REWRITE_TAC [pOR_SYM]
    THEN ACCEPT_TAC qOR_RIGHT_DISTR_OR) ;;
let qAND_DOM_SPLIT = prove_thm (`qAND_DOM_SPLIT`,
    "!W (P:**->(*->bool)) a. 
     ((!!i:: W. P i) AND (P a)) = (!!i::(\j. (W j) \/ (a=j)). P i)",
    EXT_TAC THEN EQ_TAC
    THEN pred_JADE_TAC 1
    THENL [ XRULE_ASSUM_TAC SYM THEN ASM_REWRITE_TAC[] ;
            XRULE_ASSUM_TAC (REWRITE_RULE [] o (SPEC "a:**"))
            THEN ASM_REWRITE_TAC[] ] ) ;;

let qOR_DOM_SPLIT = prove_thm (`qOR_DOM_SPLIT`,
    "!W (P:**->(*->bool)) a. 
        ((??i:: W. P i) OR (P a)) = (??i::(\j. (W j) \/ (a=j)). P i)",
    EXT_TAC THEN EQ_TAC
    THEN pred_JADE_TAC 0
    THENL [ EXISTS_TAC "i:**" ;
            EXISTS_TAC "a:**" ;
            DISJ1_TAC THEN EXISTS_TAC "i:**" ;
            ALL_TAC ]
    THEN ASM_REWRITE_TAC[]) ;;

let CHF_FINITE = new_definition(`CHF_FINITE`, 
   "CHF_FINITE (W:*->bool) = FINITE (SPEC W)" ) ;;
let EMPTY_lemma = prove_thm(`EMPTY_lemma`,"{} = SPEC(FF:*->bool)",
    REWRITE_TAC [EMPTY_DEF ; FF_DEF]) ;;
let CHF_SPEC_lemma = (REWRITE_RULE [] o BETA_RULE o CONJUNCT2) set_ISO_DEF ;;
save_thm (`CHF_SPEC_lemma` , CHF_SPEC_lemma) ;;
let SET_lemma = prove_thm(`SET_lemma`,
   "!(a:*) V. {y| (y=a) \/ (y IN V)} = SPEC(\y.(y=a) \/ ((CHF V) y))",
   REWRITE_TAC [IN_DEF] THEN REWRITE_TAC [GSPEC_DEF]
   THEN BETA_TAC THEN REWRITE_TAC [PAIR_EQ] THEN REPEAT GEN_TAC
   THEN AP_TERM_TAC THEN EXT_TAC
   THEN EQ_TAC THEN REPEAT STRIP_TAC
   THEN ASM_REWRITE_TAC[]
   THENL [ EXISTS_TAC "a:*" THEN ASM_REWRITE_TAC[] ;
           EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[] ] ) ;;
let lemma1 = prove(
   "(!V a. X V ==> X(\x:*. (x=a) \/ (V x))) ==>
    (!s:(*)set. X(CHF s) ==> (!e:*. X(\y. (y=e) \/ (CHF s y))))",
    REPEAT STRIP_TAC
    THEN RES_TAC THEN ASM_REWRITE_TAC[]) ;;
    
let lemma2 = prove(
   "(!s':(*)set. P s' ==> (!e:*. P(SPEC(\y. (y=e) \/ (CHF s' y)))))  ==>
    (!V (a:*). P(SPEC V) ==> P(SPEC(\x:*. (x=a) \/ V x)))",
    REPEAT STRIP_TAC
    THEN RES_TAC 
    THEN XRULE_ASSUM_TAC (REWRITE_RULE [CHF_SPEC_lemma])
    THEN ASM_REWRITE_TAC[]) ;;

let CHF_FINITE_def = prove_thm 
  (`CHF_FINITE_def`,
   "!W:*->bool. (CHF_FINITE W) =
     (!X. (X FF) /\ (!V a. (X V) ==> (X (\x. (x=a) \/ (V x))))  ==> (X W))",
   REWRITE_TAC [CHF_FINITE] THEN GEN_TAC
   THEN REWRITE_TAC [FINITE_DEF; INSERT_DEF]
   THEN REWRITE_TAC [SET_lemma ; EMPTY_lemma]
   THEN EQ_TAC THEN REPEAT STRIP_TAC
   THENL 
   [ IMP_RES_TAC lemma1
     THEN XRULE_ASSUM_TAC  
          ((REWRITE_RULE [CHF_SPEC_lemma]) o  BETA_RULE o (SPEC 
          "\x:(*)set. (X:(*->bool)->bool) (CHF x)"))
     THEN RES_TAC ;
     OLD_IMP_RES_TAC lemma2
     THEN XRULE_ASSUM_TAC 
          (BETA_RULE o (SPEC "\x:*->bool. (P:(*)set->bool)(SPEC x)"))
     THEN RES_TAC ]) ;;
let CHF_INDUCTION = prove_thm (`CHF_INDUCTION`,
   "!(X:(**->bool)->bool). 
    ((X FF) /\ (!V a. (X V) ==> X(\x. (x=a) \/ (V x))))
    ==>
    (!V. (CHF_FINITE  V) ==> X V)",
   REWRITE_TAC [CHF_FINITE_def] THEN REPEAT STRIP_TAC
   THEN RES_TAC) ;;
close_theory();;
