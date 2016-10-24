%--------------------------------------------------------------------------%
%
 File    : MYTACTICS
 Author  : Wishnu Prasetya
           wishnu@cs.ruu.nl
           Dept. of Comp Science, Utrecht University, the Netherlands
 Date    : Sept 92

 Several useful tactics and rules:
   
   RESTRICT_DEF_TAC:          Unfold the definitions of RES_ABSTRACT,
                              RES_EXISTS, RES_FORALL

   UNDISCHN_TAC n:            UNDISCH n-th assumption

   UNDISCH_ALL_TAC:           UNDISCH all assumptions
   
   INFER_ASMN_TAC n Rule:     Apply inference rule Rule to the n-th 
                              assumption, add the result to the asumptions
                              list

   FILTER_INFER_ASM_TAC A R:  As INFER_ASMN_TAC, but the assumption 
                              selected is identified by A

   SEQ_TAC Tac Thml:          apply tactic Tac subsequently, where the i-th 
                              application uses the i-th theorem from the 
                              list Thml    

   ASM_STRIPN_TAC i:          STRIP the i-th assumption and add the result
                              to the assumptions list

   FILTER_ASM_STRIP_TAC:      As ASM_STRIPN_TAC, but assumption selected is
                              identified by Asm

   REWRITE_ASM_TAC m n:       REWRITE n-th assumption using m-th assumption,
                              then add the result to asm list

   FILTER_REWRITE_ASM A1 A2   As REWRITE_ASMN_TAC but assumptions selected
                              are identified by A1 and A2

   SPECSTRIP_ASSUME_TAC thm:  SPEC_ALL thm, then strip it and add the result
                              to the assumptions list

   EXT_TAC:                   transform goal f = g to f x = g x then
                              do BETA reduction

   SUBST2_ASM_TAC

   REW_SPEC_ASM_TAC

   ASM_TAC

   ASM_ASM_TAC

   RESTRICT_DEF_RULE:         Rewrite using the definition of RES_FORALL,
                              RES_EXISTS, RES_ABSTRACT

   RESTRICT_SHIFT:            Rewrite !x::P. !y z... Q to !x y z... P ==> Q

   IMP_LEFT_RULE:             see below
      
%
%--------------------------------------------------------------------------%


let RES_lst = 
    [ definition `bool` `RES_FORALL` ;
      definition `bool` `RES_EXISTS` ;
      definition `bool` `RES_ABSTRACT` ] ;;

let RESTRICT_DEF_TAC  = REWRITE_TAC RES_lst THEN BETA_TAC ;;
let RESTRICT_DEF_RULE thm = BETA_RULE (REWRITE_RULE RES_lst thm) ;;

letrec DISCH_TOP thm = DISCH (hd (hyp thm)) thm ;;

let RESTRICT_SHIFT thm =
    GEN_ALL (DISCH_TOP 
            (SPEC_ALL (UNDISCH (SPEC_ALL (RESTRICT_DEF_RULE thm))))) ;;


let test_term trm1 trm2 = 
    ((\trm. true) (find_term (\t. t=trm1) trm2)) ? false ;;

letrec get_match_term trm1 trml =
    if null trml then failwith `get_match_term: no match found`
    else (if test_term trm1 (hd trml) then (hd trml)
          else get_match_term trm1 (tl trml)) ;;



letrec pick_el x l =
   if (null l) then failwith `pick_el: element not in the list`
   else (if (x = (hd l)) then x else pick_el x (tl l)) ;;


let UNDISCHN_TAC n (asml,g) = UNDISCH_TAC (el n asml) (asml,g) ;;


letrec UNDISCH_ALL_TAC (asml,g) =
    if (asml = []) then ALL_TAC (asml,g)
    else (UNDISCH_TAC (hd asml) THEN UNDISCH_ALL_TAC) (asml,g) ;;


let INFER_ASMN_TAC n inf_rule (asml,g) =
   ASSUME_TAC (inf_rule (ASSUME (el n asml))) (asml,g) ;;
   % apply inference rule inf_rule to n-th assumption, then add the result
     to the asumptions list %

let FILTER_INFER_ASM_TAC trm inf_rule (asml,g) =
   let ASM = ASSUME (pick_el trm asml) in
   ASSUME_TAC (inf_rule ASM) (asml,g) ;;

let F_INFER_ASM_TAC trm inf_rule (asml,g) = 
   let ASM = ASSUME (get_match_term trm asml) in
   ASSUME_TAC (inf_rule ASM) (asml,g) ;;


letrec SEQ_TAC tac thml = if (null  thml) then ALL_TAC else 
  (tac (hd thml) THEN (SEQ_TAC tac (tl thml))) ;;                              

let ASM_STRIPN_TAC i (asml,g) =  
   STRIP_ASSUME_TAC (SPEC_ALL (ASSUME (el i asml))) (asml,g) ;;
   % this strips the i-th assumption and then adds then to the 
     assumption list %

let FILTER_ASM_STRIP_TAC trm (asml,g) =
   let ASM = SPEC_ALL (ASSUME (pick_el trm asml)) in
   STRIP_ASSUME_TAC ASM (asml,g) ;;



let REWRITE_ASM_TAC m n (asml,g) =
   ASSUME_TAC 
      (REWRITE_RULE [ASSUME (el m asml)] (ASSUME (el n asml))) (asml,g) ;;

let FILTER_REWRITE_ASM_TAC trm1 trm2 (asml,g) =
   let ASM1 = ASSUME (pick_el trm1 asml) in
   let ASM2 = ASSUME (pick_el trm2 asml) in
   ASSUME_TAC (REWRITE_RULE [ASM1] ASM2) (asml,g) ;;



let SPECSTRIP_ASSUME_TAC thm = STRIP_ASSUME_TAC (SPEC_ALL thm) ;;

let EXT_TAC  =
    let EXT_SPEC_TAC (asml,g) = 
      (REWRITE_TAC [FUN_EQ_CONV g] 
      THEN BETA_TAC
      THEN GEN_TAC) (asml,g) in
     (REPEAT GEN_TAC) THEN EXT_SPEC_TAC ;;


let SUBST2_ASM_TAC =  EVERY_ASSUM (\thm. SUBST1_TAC (SYM thm) ? ALL_TAC) ;;
 

let REW_SPEC_ASM_TAC trm = EVERY_ASSUM 
    (\thm. REWRITE_TAC [REWRITE_RULE [] (SPEC trm  thm)] ? ALL_TAC) ;;


let ASM_TAC rule = EVERY_ASSUM (\thm. ASSUME_TAC (rule thm) ? ALL_TAC) ;;

letrec ASM_tac rule thm asml =
   if (asml = []) then ALL_TAC
   else (ASSUME_TAC (rule thm (hd asml)) ? ALL_TAC) 
        THEN ASM_tac rule thm (tl asml) ;;

letrec ASM_ASM_tac rule asml1 asml2 =
   if (asml1 = []) then ALL_TAC
   else (ASM_tac rule (hd asml1) asml2) 
        THEN (ASM_ASM_tac rule (tl asml1) asml2) ;;

let ASM_ASM_TAC rule = ASSUM_LIST (\asml. ASM_ASM_tac rule asml asml) ;;

let XRULE_ASSUM_TAC rule = 
    RULE_ASSUM_TAC (\thm. rule thm ? thm) ;;


letrec last l = last (tl l) ? hd l ? failwith `last on empty list` ;;

let IMP_LEFT_RULE trm thm = 
   let th1 = SPEC_ALL thm in
   let th2 = UNDISCH th1 in
   let th3 = CONJUNCT1 th2 in
   let th4 = DISCH (last (hyp th3)) th3  in
   GEN trm th4 ;;

   %   !x. P ==> Q /\ R
      ------------------ IMP_LEFT_RULE "x"
         !x. P ==> Q
   %



