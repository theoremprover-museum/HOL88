%( 
---------------------------------

  convert library
  
  more_conv.ml
  
  extra conversions
---------------------------------
)%

%( [DES] 27apr89

   distinct_ALPHA_term t renames all binding variables in t
   so that all are distinct.
   
   Very useful when you want to STRIP_TAC nested ?s as HOL
   tends to do ? x . --- ? x' . --- ? x . ---
   causing a CHOOSE to fail
)%

letrec distinct_ALPHA_term t =
   letrec f t used =
   if is_abs t then let bv,body = dest_abs t in
                    let nbv = variant(used)bv in
                    let nbody,nused = f (subst [nbv,bv] body) (nbv.used)in
                        (mk_abs (nbv,nbody),nused)
   else if is_comb t then let rat,ran=dest_comb t in
           let nrat,nused = f rat used in
           let nran,nnused = f ran nused in
                        (mk_comb(nrat,nran),nnused)
   else (t,used)
   in fst(f t []);;

%( [DES] 27apr89

   distinct_ALPHA_CONV does a conversion using above function
)%

let distinct_ALPHA_CONV t = let nt = distinct_ALPHA_term t in ALPHA t nt;;

%( [DES] 27apr89

   UP_CONV and DOWN_CONV. Similar to DEPTH_CONV except only do conversion
   once at each level. UP_CONV is bottom up while DOWN_CONV is top down.
   
   Useful when applying a conversion that loops in DEPTH_CONV causing
   NAMESTACK OVERFLOW
)%

letrec UP_CONV conv t = (SUB_CONV (UP_CONV conv) THENC (conv ORELSEC ALL_CONV)) t;;

letrec DOWN_CONV conv t = ((conv ORELSEC ALL_CONV) THENC SUB_CONV (DOWN_CONV conv)) t;;

%( [DES] 27apr89

   DOWN_CONV_THEN. Applies a conversion like DOWN_CONV but when it fails applies
   another one at that point
)%

letrec DOWN_CONV_THEN c1 c2 t =
    ((c1 THENC SUB_CONV (DOWN_CONV_THEN c1 c2)) ORELSEC c2) t;;

%( [DES] 27apr89

   B_SUB_CONV. B(inder)_SUB_CONV.
   
   Does a SUB_CONV that is more in line with what the user sees as the sub terms.
   
   i.e. subterms of ?x.P(x) is P(x) and not $? and \x.P(x).
)%

let B_SUB_CONV conv t =
   (let t1,t2 = dest_comb t in
    if is_abs t2 then if is_binder(fst(dest_const t1))
                      then (SUB_CONV o SUB_CONV) conv t
                      else SUB_CONV conv t
                 else else SUB_CONV conv t
   ) ? SUB_CONV conv t;;

%( [DES] 27apr89 

   B_ versions of UP DOWN and DOWN_THEN
)%

letrec B_UP_CONV conv t = (B_SUB_CONV (UP_CONV conv) THENC (conv ORELSEC ALL_CONV)) t;;

letrec B_DOWN_CONV conv t = ((conv ORELSEC ALL_CONV) THENC B_SUB_CONV (DOWN_CONV conv)) t;;

letrec B_DOWN_CONV_THEN c1 c2 t =
    ((c1 THENC B_SUB_CONV (B_DOWN_CONV_THEN c1 c2)) ORELSEC c2) t;;

%( example use of B_DOWN_CONV_THEN


   B_DOWN_CONV_THEN SWAP_EXISTS_CONV PRUNE_ONCE_CONV
   
  
   Applied to ? x1 ... xn . bdy 
   
   i)  moves x1 in to ? x1 . bdy where SWAP_EXISTS_CONV fails
   ii) PRUNEs the ? x1.
   
   PRUNE_CONV could have been defined like this but is hand coded to
   be handle cases where PRUNE_ONCE_CONV fails as well.
)%

%( [DES] 27apr89

   unnum_CONV

   SUC n --> |- SUC n = "n+1"
)%

let unnum_CONV t =
   (let suc,n = dest_comb t in
    if not suc="SUC" then fail
    else let nv = int_of_string(fst(dest_const n)) in
    SYM(num_CONV(mk_const(string_of_int(nv+1),":num")))
   ) ? failwith `unnum_CONV`;;

%( [DES] 2may89

   REV
   
   ....(x=y).... --> |- ....(x-y).... = ....(y=x)....
   
   normal use to reverse quantified equates for rewriting
)%

let REV = CONV_RULE (ONCE_DEPTH_CONV SYM_CONV);;

%< these let convs are supercede by hol 1.12 >%

let UNCURRY_AP = 
  prove("! (f:*->**->***) z . UNCURRY f z = f (FST z) (SND z)",
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REV PAIR]
  THEN PURE_REWRITE_TAC[UNCURRY_DEF] THEN REWRITE_TAC[PAIR]);;

let LET_CONV t =
  let (lb,v) = dest_comb t in
  let (_,b) = dest_comb lb in
  let (_,[ty1;ty2]) = dest_type(type_of b) in
  let th1 = RIGHT_CONV_RULE BETA_CONV(AP_THM (INST_TYPE[(ty1,":*");(ty2,":**")]LET_DEF) b) in
  RIGHT_CONV_RULE BETA_CONV(RIGHT_CONV_RULE BETA_CONV(AP_THM th1 v));;

let tuple_LET_CONV t =
  let (lb,v) = dest_comb t in
  let (_,b) = dest_comb lb in
  let (_,f) = dest_comb b in
  let (_,[ty1;ty2]) = dest_type(type_of b) in
  let (_,[ty3;ty]) = dest_type(type_of f) in
  let (_,[ty4;ty5]) = dest_type ty in
  let th1 = RIGHT_CONV_RULE BETA_CONV(AP_THM (INST_TYPE[(ty1,":*");(ty2,":**")]LET_DEF) b) in
  let th2 = SPECL[f;v](INST_TYPE[(ty3,":*");(ty4,":**");(ty5,":***")]UNCURRY_AP) in
  let th3 = RIGHT_CONV_RULE BETA_CONV(AP_THM th1 v)
  in th3 TRANS (RIGHT_CONV_RULE(RATOR_CONV BETA_CONV THENC BETA_CONV)th2);;

% match spec - instance types for a SPEC %
let MATCH_SPEC v tm =
  let (v',tm') = dest_forall (concl tm) in
  let (tml,tyl) = match v' v
  in (SPEC v o INST_TYPE tyl)tm
;;

let UNCURRY_DEF' = (GENL["x:*";"y:**";"f:*->**->***"] o SYM o SPEC_ALL) UNCURRY_DEF;;

%----------------------------------------
 this turned out to be nqwww but still
 could have uses.

 "\z . f z" --> "UNCURRY (\x y. f(x,y)"
----------------------------------------%

let pair_abs_CONV n1 n2 tm =
    let v = (fst o dest_abs) tm in
    let ty = (snd o dest_var) v in
    let [ty1;ty2] = (snd o dest_type) ty in
    let v1 = mk_var(n1,ty1)
    and v2 = mk_var(n2,ty2) in
    let pair_thm = MATCH_SPEC v PAIR in
    let fs,sn = dest_pair(lhs(concl pair_thm)) in
    let tm' = (mk_abs(v1,mk_abs(v2,mk_comb(tm,mk_pair(v1,v2))))) in
    let tyl = snd(match "f:*->**->***" tm') in
    let th1 = (SPEC tm' o SPEC sn o SPEC fs o INST_TYPE tyl)UNCURRY_DEF' in
    let th2 = CONV_RULE((RATOR_CONV o RAND_CONV) ((RATOR_CONV BETA_CONV) THENC BETA_CONV)) th1 in
    let th3 = SUBS[pair_thm]th2 in % could do better with a SUBST ? %
    let th4 = CONV_RULE((RAND_CONV o RATOR_CONV o RAND_CONV o ABS_CONV o ABS_CONV)BETA_CONV)th3
    in (CONV_RULE((RATOR_CONV o RAND_CONV)(ALPHA_CONV v)) o EXT o GEN v)th4;;

let pair_EXISTS_THM =
  prove("! (f:((*#**)->bool)) . (? z . f z) = (?x y . f (x,y))",
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [ EXISTS_TAC "FST(z:*#**)"
	  THEN EXISTS_TAC "SND(z:*#**)"
	  THEN ASM_REWRITE_TAC[PAIR]
	 ;
	  EXISTS_TAC"x:*,y:**"
	  THEN POP_ASSUM ACCEPT_TAC
	]);;

let pair_EXISTS_CONV n1 n2 tm =
    let tm' = (snd o dest_comb)tm in
    let (v,b) = dest_abs tm' in
    let [ty1;ty2] = (snd o dest_type o snd o dest_var) v in
    let v1 = mk_var(n1,ty1)
    and v2 = mk_var(n2,ty2) in
    let th1 = MATCH_SPEC tm' pair_EXISTS_THM in
    CONV_RULE((RATOR_CONV o RAND_CONV o RAND_CONV)(ALPHA_CONV v THENC
               (ABS_CONV BETA_CONV)) THENC
              (RAND_CONV o RAND_CONV)(ALPHA_CONV v1 THENC 
               (ABS_CONV o RAND_CONV)(ALPHA_CONV v2 THENC
                (ABS_CONV BETA_CONV)))) th1;;

%----------------------------------------
 term_EXISTS_CONV tm "? x . f x" --> "? v1 ... vn . f tm"

where v1 ... vn are the variables in tm

used to untuple the internal state in the specs etc
copes with any shape of tm (i.e. untuples nested tuples)
----------------------------------------%

letrec term_EXISTS_CONV tm t =
       if (is_pair tm) 
       then let (tm1,tm2) = dest_pair tm in
            let n1 = (fst o dest_var o genvar)(type_of tm1)
            and n2 = (fst o dest_var o genvar)(type_of tm2) in
            ((pair_EXISTS_CONV n1 n2) THENC
             (RAND_CONV o ABS_CONV)(term_EXISTS_CONV tm2) THENC
             (term_EXISTS_CONV tm1)) t
      else (RAND_CONV (ALPHA_CONV tm) t);;

let pair_FORALL_THM =
  prove("! (f:((*#**)->bool)) . (! z . f z) = (!x y . f (x,y))",
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [ ASM_REWRITE_TAC[]
	 ;
	  GEN_TAC THEN ONCE_REWRITE_TAC[REV PAIR] 
          THEN PURE_ASM_REWRITE_TAC[]
        ]);;

let pair_FORALL_CONV n1 n2 tm =
    let tm' = (snd o dest_comb)tm in
    let (v,b) = dest_abs tm' in
    let [ty1;ty2] = (snd o dest_type o snd o dest_var) v in
    let v1 = mk_var(n1,ty1)
    and v2 = mk_var(n2,ty2) in
    let th1 = MATCH_SPEC tm' pair_FORALL_THM in
    CONV_RULE((RATOR_CONV o RAND_CONV o RAND_CONV)(ALPHA_CONV v THENC
               (ABS_CONV BETA_CONV)) THENC
              (RAND_CONV o RAND_CONV)(ALPHA_CONV v1 THENC 
               (ABS_CONV o RAND_CONV)(ALPHA_CONV v2 THENC
                (ABS_CONV BETA_CONV)))) th1;;

%----------------------------------------
 term_FORALL_CONV tm "! x . f x" --> "! v1 ... vn . f tm"

where v1 ... vn are the variables in tm

used to untuple the internal state in the specs etc
copes with any shape of tm (i.e. untuples nested tuples)
----------------------------------------%

letrec term_FORALL_CONV tm t =
       if (is_pair tm) 
       then let (tm1,tm2) = dest_pair tm in
            let n1 = (fst o dest_var o genvar)(type_of tm1)
            and n2 = (fst o dest_var o genvar)(type_of tm2) in
            ((pair_FORALL_CONV n1 n2) THENC
             (RAND_CONV o ABS_CONV)(term_FORALL_CONV tm2) THENC
             (term_FORALL_CONV tm1)) t
      else (RAND_CONV (ALPHA_CONV tm) t);;

