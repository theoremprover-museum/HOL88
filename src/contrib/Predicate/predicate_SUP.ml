let pred_JADE_TAC n =
    REWRITE_TAC (snd(split (definitions `predicate`)))
    THEN RESTRICT_DEF_TAC
    THEN (REPEAT STRIP_TAC)
    THEN (REPEAT_FIN n (ASM_REWRITE_TAC [] THEN RES_TAC)) ;;

let pred_CYAN_TAC =
    REWRITE_TAC (snd(split (definitions `predicate`)))
    THEN RESTRICT_DEF_TAC
    THEN REPEAT GEN_TAC THEN EXT_TAC THEN TAUT_TAC ;;
