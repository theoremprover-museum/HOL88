
let PURE_REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV []
and REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV ONCE_DEPTH_CONV []
and ONCE_REWRITE_CONV = GEN_REWRITE_CONV ONCE_DEPTH_CONV basic_rewrites;;

let PURE_REWRITE_RULE      = GEN_REWRITE_RULE TOP_DEPTH_CONV [] 
and REWRITE_RULE           = GEN_REWRITE_RULE TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_RULE = GEN_REWRITE_RULE ONCE_DEPTH_CONV []
and ONCE_REWRITE_RULE      = GEN_REWRITE_RULE ONCE_DEPTH_CONV basic_rewrites;;

let PURE_ASM_REWRITE_RULE thl th =
    PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and ASM_REWRITE_RULE thl th = 
    REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and PURE_ONCE_ASM_REWRITE_RULE thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and ONCE_ASM_REWRITE_RULE thl th = 
    ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;

let FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_ASM_REWRITE_RULE f thl th = 
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_ONCE_ASM_REWRITE_RULE f thl th = 
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;

let PURE_REWRITE_TAC      = GEN_REWRITE_TAC TOP_DEPTH_CONV []
and REWRITE_TAC           = GEN_REWRITE_TAC TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_TAC = GEN_REWRITE_TAC ONCE_DEPTH_CONV []
and ONCE_REWRITE_TAC      = GEN_REWRITE_TAC ONCE_DEPTH_CONV basic_rewrites;;

let PURE_ASM_REWRITE_TAC thl = 
    ASSUM_LIST (\asl. PURE_REWRITE_TAC (asl @ thl))
and ASM_REWRITE_TAC thl      = 
    ASSUM_LIST (\asl. REWRITE_TAC (asl @ thl))
and PURE_ONCE_ASM_REWRITE_TAC thl = 
    ASSUM_LIST (\asl. PURE_ONCE_REWRITE_TAC (asl @ thl))
and ONCE_ASM_REWRITE_TAC thl      = 
    ASSUM_LIST (\asl. ONCE_REWRITE_TAC (asl @ thl));;

let FILTER_PURE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. PURE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. PURE_ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl));;
