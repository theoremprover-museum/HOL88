

%----------------------------------------------------------------------------%
% Some tools for use with the `arith` library.                               %
%----------------------------------------------------------------------------%


%----------------------------------------------------------------------------%
% Prove that the assumption imply a given term, and then rewrite with it.    %
%----------------------------------------------------------------------------%

let ASM_ARITH_THEN t ttac =
 ASSUM_LIST
  (\thl. 
    ttac
     (REWRITE_RULE 
       thl 
       (ARITH_CONV
         (mk_imp(list_mk_conj(filter is_presburger (map concl thl)),t)))));;

let ASM_ARITH_REWRITE_TAC t = ASM_ARITH_THEN t (\th. REWRITE_TAC[th]);;

%----------------------------------------------------------------------------%
% Try to prove goal using ARITH_TAC.                                         %
%----------------------------------------------------------------------------%

let ARITH_TAC = CONV_TAC ARITH_CONV;;

let ARITH_PROVE = EQT_ELIM o ARITH_CONV;;

let ASM_ARITH_TAC =
 ASSUM_LIST(\thl. MAP_EVERY UNDISCH_TAC (map concl thl))
  THEN ARITH_TAC;;

