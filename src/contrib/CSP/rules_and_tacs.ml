let SET_SPEC_TAC = CONV_TAC (DEPTH_CONV SET_SPEC_CONV);;
let SET_SPEC_RULE = CONV_RULE (DEPTH_CONV SET_SPEC_CONV);;

let IN_TAC conv = CONV_TAC (DEPTH_CONV (IN_CONV conv));;
let IN_RULE conv = CONV_RULE (DEPTH_CONV (IN_CONV conv));;

let RIGHT_AND_EXISTS_TAC = CONV_TAC (DEPTH_CONV RIGHT_AND_EXISTS_CONV);;
let LEFT_AND_EXISTS_TAC = CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV);;
let RIGHT_OR_EXISTS_TAC = CONV_TAC (DEPTH_CONV RIGHT_OR_EXISTS_CONV);;
let LEFT_OR_EXISTS_TAC = CONV_TAC (DEPTH_CONV LEFT_OR_EXISTS_CONV);;

let ELIM_SELECT_RULE thm1 thm2 =
   (let (vl, tm) =
    dest_select (rhs (snd (strip_forall (concl thm2))))
    and imp = concl thm1
    in
    let (imp', (L, R)) = ((I # dest_eq) o dest_imp) tm
    in
    let Ea = (subst (fst (match imp' imp)) R)
    in
    let th1 =
        DISCH_ALL
         (ADD_ASSUM imp (SPEC Ea (INST_TYPE [(type_of L),":*"] EQ_REFL)))
    in
    ONCE_REWRITE_RULE
     [GEN_ALL (SYM (SPEC_ALL thm2))]
     (MP
      (SELECT_RULE
       (EXISTS
        ((mk_exists (L, (mk_imp (imp, (mk_eq (L, Ea)))))), Ea) th1))
      thm1))
    ? (failwith `ELIM_SELECT_RULE`);;
