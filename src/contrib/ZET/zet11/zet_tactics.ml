%<
FILE: zet_fns.ml

DESCRIPTION: tactics for integers

AUTHOR: Ton Kalker

DATE: 22-09-89
>%

let ZET_INDUCT0_TAC (A,t) = 
    (let th = ZET_INDUCTION0 in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in
     let tac = 
     (MATCH_MP_TAC thm THEN  
      CONJ_TAC THEN
      FIRST[CONV_TAC (BINDER_CONV((RAND_CONV BETA_CONV) THENC
                                  (LHS_CONV(RAND_CONV BETA_CONV))));
            CONV_TAC (BINDER_CONV(RAND_CONV BETA_CONV))] )in
      tac (A,t));; 

%<The parameter k in the tactic below determines the
  point where induction really starts>%


let ZET_INDUCT1_TAC k (A,t) = 
    (let th = SPEC k ZET_INDUCTION1 in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in 
     let PART_MATCH' partfn th =
              (let pth = GSPEC th  in
               let pat = partfn(concl pth) in
               let matchfn = match pat in
               \tm. INST_TY_TERM (matchfn tm) pth) in  
     let MATCH_MP_TAC' thm:tactic (gl,g) =
              (let imp = ((PART_MATCH' (snd o dest_imp) thm) g) ? 
	       failwith `MATCH_MP_TAC` in
    
               ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl))) in
     let tac = 
     (MATCH_MP_TAC' thm THEN
      REPEAT CONJ_TAC THEN
      GEN_TAC THENL
      [CONV_TAC (RAND_CONV BETA_CONV);
       CONV_TAC ((RAND_CONV BETA_CONV) THENC
                 (LHS_CONV(RAND_CONV BETA_CONV)))] THEN
      REPEAT STRIP_TAC) in
     tac (A,t));;    

%<The parameter k in the tactic below determines the
  point where induction really starts>%

let ZET_INDUCT2_TAC k (A,t) = 
    (let th = SPEC k ZET_INDUCTION2 in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in 
     let PART_MATCH' partfn th =
              (let pth = GSPEC th  in
               let pat = partfn(concl pth) in
               let matchfn = match pat in
               \tm. INST_TY_TERM (matchfn tm) pth) in  
     let MATCH_MP_TAC' thm:tactic (gl,g) =
              (let imp = ((PART_MATCH' (snd o dest_imp) thm) g) ? 
	       failwith `MATCH_MP_TAC` in
    
               ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl))) in
     let tac = 
     (MATCH_MP_TAC' thm THEN
      REPEAT CONJ_TAC THENL
      [ALL_TAC;GEN_TAC;GEN_TAC] THENL
      [CONV_TAC BETA_CONV;
       CONV_TAC ((RAND_CONV BETA_CONV) THENC
                 (LHS_CONV(RAND_CONV BETA_CONV)));
       CONV_TAC ((RAND_CONV BETA_CONV) THENC
                 (LHS_CONV(RAND_CONV BETA_CONV)))] THEN
      REPEAT STRIP_TAC) in
     tac (A,t));; 

