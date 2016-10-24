let RES_lst = 
    [ definition `bool` `RES_FORALL`; definition `bool` `RES_EXISTS`] ;;
let RESTRICT_DEF_RULE thm = BETA_RULE (REWRITE_RULE RES_lst thm) ;;
let RESTRICT_SHIFT thm =
    let th1 = SPEC_ALL (RESTRICT_DEF_RULE thm) in
    let asm = fst(dest_imp(concl th1)) in
    (GEN_ALL o (DISCH asm) o SPEC_ALL o UNDISCH) th1 ;;
let IMP_LEFT_RULE thm =
    let th1 = SPEC_ALL thm in
    let asm = fst(dest_imp(concl th1)) in
    (GEN_ALL o (DISCH asm) o CONJUNCT1 o UNDISCH) th1 ;;
let IMP_RIGHT_RULE thm =
    let th1 = SPEC_ALL thm in
    let asm = fst(dest_imp(concl th1)) in
    (GEN_ALL o (DISCH asm) o CONJUNCT2 o UNDISCH) th1 ;;
let RESTRICT_DEF_TAC  = REWRITE_TAC RES_lst THEN BETA_TAC ;;
letrec REPEAT_FIN n tac =
    if n=0 then ALL_TAC
    else (tac THEN REPEAT_FIN (n-1) tac) ;;
letrec UNDISCH_ALL_TAC (asml,g) =
    if (asml = []) then ALL_TAC (asml,g)
    else (UNDISCH_TAC (hd asml) THEN UNDISCH_ALL_TAC) (asml,g) ;;
let EXT_TAC  =
    let EXT_SPEC_TAC (asml,g) = 
        (REWRITE_TAC [FUN_EQ_CONV g] 
        THEN BETA_TAC THEN GEN_TAC) (asml,g) in
    REPEAT GEN_TAC THEN EXT_SPEC_TAC ;;
let ASM_TAC rule = EVERY_ASSUM (\thm. ASSUME_TAC (rule thm) ? ALL_TAC) ;;
let XRULE_ASSUM_TAC rule = RULE_ASSUM_TAC (\thm. rule thm ? thm) ;;
