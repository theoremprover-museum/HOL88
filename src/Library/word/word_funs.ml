let word_CASES_TAC =
    let cthm = (theorem `word_base` `word_cases`) in
  \w. CHOOSE_THEN SUBST1_TAC (ISPEC w cthm) ;;

let word_INDUCT_TAC = 
    let ithm = theorem `word_base` `word_induct` in
    (INDUCT_THEN ithm (\t.ALL_TAC));;

let RESQ_WORDLEN_TAC = 
    (CONV_TAC RESQ_FORALL_CONV THEN word_INDUCT_TAC
     THEN PURE_ONCE_REWRITE_TAC[definition `word_base` `PWORDLEN_DEF`]
     THEN GEN_TAC THEN DISCH_TAC);;

