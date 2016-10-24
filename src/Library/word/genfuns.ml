
%-----------------------------------------------------------------------%
% Derived inference rules   	    					%
%-----------------------------------------------------------------------%

let MATCH_EQ_MP = \eq lh. EQ_MP (PART_MATCH lhs eq (concl lh)) lh;;

let REWRITE1_TAC = \t. REWRITE_TAC[t];;


let ARITH_TAC (asml,gl) =
    let as = filter is_presburger asml in
    (MAP_EVERY (MP_TAC o ASSUME) as THEN CONV_TAC ARITH_CONV)(asml,gl);;

let ARITH_PROVE = EQT_ELIM o ARITH_CONV;;
