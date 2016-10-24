

let PROVE_IN s =
   let dest_insert t = (
      if (is_comb t) & (fst (dest_const (fst (dest_comb (fst (dest_comb t))))) = `INSERT`) then
         (snd(dest_comb(fst(dest_comb t))), snd(dest_comb t))
      else fail
   ) in
   letrec strip_insert t = (
     ( let (e,bs) = dest_insert t in
      let (el,bs') = strip_insert bs in
         (e.el,bs'))
    ? ([],t)
   ) in
   let (inserts, _) = strip_insert s in
   let gls = map (\insert. "^insert IN ^s") inserts in
      map (\gl. PROVE(gl, REWRITE_TAC [IN_INSERT])) gls;;

let PROVE_NOT_IN s =
   let dest_insert t = (
      if (is_comb t) & (fst (dest_const (fst (dest_comb (fst (dest_comb t))))) = `INSERT`) then
         (snd(dest_comb(fst(dest_comb t))), snd(dest_comb t))
      else fail
   ) in
   letrec strip_insert t = (
     ( let (e,bs) = dest_insert t in
      let (el,bs') = strip_insert bs in
         (e.el,bs'))
    ? ([],t)
   ) in
   let (inserts, base) = strip_insert s in
   if (fst(dest_const base) = `EMPTY`) then (
      let var = mk_var(`x`,hd (snd (dest_type (snd (dest_const base))))) in
      if (null inserts)  then 
         NOT_IN_EMPTY
      else 
         let neq_asm = end_itlist (curry mk_conj) (map (\t. "~(^var = ^t)") inserts) in
            PROVE("!^var. ^neq_asm ==> ~(^var IN ^s)", 
                GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT;NOT_IN_EMPTY])
   )
   else failwith `PROVE_NOT_IN - applied to a non-fully defined set`;;


