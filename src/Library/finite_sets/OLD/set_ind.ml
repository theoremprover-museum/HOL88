% ===================================================================== %
% set_ind.ml : set induction.						%
% ===================================================================== %

% BINDER_CONV conv "B x. tm[x]" applies conv to tm[x]			%
let BINDER_CONV conv =  (RAND_CONV (ABS_CONV conv));;

% DEPTH_FORALL_CONV : BINDER_CONV in depth				%
letrec DEPTH_FORALL_CONV conv tm = 
       if (is_forall tm) then
          BINDER_CONV (DEPTH_FORALL_CONV conv) tm else
	  conv tm;;

let SET_INDUCT_TAC =
    let set_induction = theorem `finite_sets` `set_induction` in
         INDUCT_THEN set_induction ASSUME_TAC;;

%----------------------------------------------------------------
  Taken from T. Melham's INDUCT_THEN 
----------------------------------------------------------------%
let SET_INDUCT_2_TAC  = 
    let th = theorem `finite_sets` `set_induction_2` in
    \(A,t).
     (let x,body = dest_forall t in
      let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
      let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
      let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
      let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in
      let th_tac = ASSUME_TAC in
      let tac = 
      (MATCH_MP_TAC thm THEN
       REPEAT CONJ_TAC THEN
       FIRST [CONV_TAC (DEPTH_FORALL_CONV BETA_CONV);
              CONV_TAC (GEN_ALPHA_CONV x) THEN
              REPEAT GEN_TAC THEN 
              DISCH_TAC THEN
              DISCH_THEN (\th. 
               CONV_TAC (DEPTH_FORALL_CONV BETA_CONV) THEN
               MAP_EVERY (th_tac o (CONV_RULE BETA_CONV)) (CONJUNCTS th))]) in
       (tac (A,t))) ? failwith `SET_INDUCT_2_TAC`;;

