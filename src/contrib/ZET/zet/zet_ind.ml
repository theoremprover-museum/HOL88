%<
FILE: zet_ind.ml

DESCRIPTION: induction for integers

AUTHOR: Ton Kalker

DATE: 22-09-89
>%

let zet_derive_existence_thm k tml = 
    (let th = SPEC k zet_Axiom in
     let vars = map(genvar o type_of) (fst(strip_forall(concl th))) in 
     let exists = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV (SPECL vars th)) in
     let e_fn = fst(dest_exists (concl exists)) in
     letrec splt l = 
	    if (is_var (hd l)) then 
	       (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	    if (is_const (hd l) or (is_comb (hd l))) then
	       [],(hd l),(tl l) else fail in
     let bv,Con,av =splt(snd(strip_comb(lhs(snd(strip_forall(hd tml)))))) in
     let rhsfn = let cv = genvar(type_of Con) in
                 let r = rhs(snd(strip_forall(hd tml))) in
                 list_mk_abs(cv. (bv @ av),r) in
     let th_inst = INST_TYPE (snd(match e_fn rhsfn)) exists in
     let get_c t = 
         let args = snd(strip_comb(lhs(snd(strip_forall t)))) in
	 let c = fst(strip_comb(find (\t.is_const t or is_comb t) args)) in
	 (if (is_const c) then c else fail) in
     let cs = map get_c tml in
     let exl = CONJUNCTS (SELECT_RULE th_inst) in
     let fn = fst(dest_exists(concl th_inst)) in
     let same_c c cl = 
	(
         (c = fst(strip_comb(rand(lhs(snd(dest_imp(snd(strip_forall(concl cl))))))))) ?
         (c = fst(strip_comb(rand(lhs(snd(strip_forall(concl cl)))))))
        ) in
     letrec get_ths cs exl = 
            if (null cs) then [] else
	       (let (c,ex) = remove (same_c(hd cs)) exl in
	         (c.(get_ths (tl cs) ex))) in
     let ths = (get_ths cs exl) in
     let argvars = map (genvar o type_of) (bv @ av) in
     let ap_ths th = 
         let v = map (genvar o type_of) (fst(strip_forall(concl th))) in
         let th1 = SPECL v th in 
         let th2 = (if (is_imp (concl th1)) then
                       (let as,_= dest_imp (concl th1) in
                        let th3 = UNDISCH th1 in
                        let th4 = rev_itlist (C AP_THM) argvars th3 in
                        DISCH as th4)
                     else (rev_itlist (C AP_THM) argvars th1) 
                    ) in
	     (GENL (v @ argvars) th2) in
     let th1 = LIST_CONJ (map ap_ths ths) in
     let sel = mk_select(dest_exists (concl th_inst)) in
     GEN_ALL(EXISTS(mk_exists(fn,subst [fn,sel](concl th1)),sel)th1))?
     failwith `Can't derive existence theorem`;;

let zet_instantiate_existence_thm eth tml = 
   (let cls = map (snd o strip_forall) tml in
    letrec splt l = 
	   if (is_var (hd l)) then 
	      (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	   if (is_const (hd l) or (is_comb (hd l))) then
	      [],(hd l),(tl l) else fail in
    let dest tm = 
	let ((Fn,(bv,C,av)),r)=(((I # splt) o strip_comb) # I)(dest_eq tm) in
	    (Fn,bv,C,av,r) in
    let destcl = (map dest cls) in 
    let prep_tm tm = (if (is_imp (snd(strip_forall tm))) then
                     (let vl,body = strip_forall tm in
                      list_mk_forall(vl,snd(dest_imp body))) else tm) in
    let ecls = map prep_tm (conjuncts(snd(dest_exists(snd(strip_forall(concl eth)))))) in
    let fns,spec,beta = (I # split)
			(split(map mk_fn (combine(ecls,destcl)))) in
    let ethsp = SPECL fns eth in
    let conjs = map (uncurry SPECL)
    		    (combine(spec,CONJUNCTS(SELECT_RULE ethsp))) in
    let rule (th1,th2) = ((CONV_RULE (RAND_CONV (REWRITE_CONV th1)) th2) ?
                          (CONV_RULE (RAND_CONV(RAND_CONV(REWRITE_CONV th1))) th2)) in
    let th = LIST_CONJ (map (GEN_ALL o rule) (combine(beta,conjs))) in
    let fn = fst(dest_exists (concl ethsp)) and
        fsel = mk_select(dest_exists(concl ethsp)) in
        (EXISTS (mk_exists(fn,subst [fn,fsel] (concl th)),fsel) th))?
    failwith `Can't instantiate existence theorem`;;
                                    
let prepare_goal k tml = 
    letrec splt l = 
	    if (is_var (hd l)) then 
	       (let bv,C,av = splt (tl l) in ((hd l).bv,C,av)) else
	    if (is_const (hd l) or (is_comb (hd l))) then
	       [],(hd l),(tl l) else fail in
    let term_type tm =fst(snd(splt(snd(strip_comb(lhs(snd(strip_forall tm))))))) in 
    let mk_term tm = 
            (let strip_term = snd(strip_forall tm) in
             let Con = term_type tm in
             let con = fst(strip_comb Con) in
             let y = hd(frees Con) ? "zero" in 
              (if y = "zero" then strip_term 
               if con = "$plus" then "(^k leq ^y) ==> ^strip_term"
               if con = "$minus" then "(^y leq ^k) ==> ^strip_term"
               else fail)) in 
     let lvars t = subtract
		    (freesl(snd(strip_comb(lhs(snd (strip_forall t))))))
    		    (fst(strip_forall t)) in
     list_mk_conj(map (\tm.list_mk_forall(lvars tm,mk_term tm)) tml);;


let zet_prove_rec_fn_exists k tml = 
   (let eth = zet_derive_existence_thm k tml in
    let ith = zet_instantiate_existence_thm eth tml in
    letrec get_avars tm  = 
	   if (is_var (rand tm)) then (get_avars (rator tm)) else
	      (snd(strip_comb (rator tm)),rand tm) in
    let cl = snd(strip_forall(hd tml)) in
    let fn = fst(strip_comb(lhs cl)) and
        av,tv = (map (genvar o type_of) # (genvar o type_of))
	        (get_avars (lhs cl)) in 
    let prep_tm tm = (if (is_imp (snd(strip_forall tm))) then
                     (let vl,body = strip_forall tm in
                      list_mk_forall(vl,snd(dest_imp body))) else tm) in
    if is_const fn
     then failwith(fst(dest_const fn)^` previously defined`)
     else
      let goal = ([],mk_exists(fn,prepare_goal k tml)) in 
      let etac th = 
	  let efn = fst(strip_comb(lhs(snd(strip_forall(prep_tm(concl th)))))) in
          EXISTS_TAC (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
      let fn_beta th (A,gl) = 
 	   let efn = fst(strip_comb(lhs(snd(strip_forall(prep_tm(concl th)))))) in
           let eabs = (list_mk_abs(av@[tv],list_mk_comb(efn,tv.av))) in 
	   let epat = list_mk_comb(eabs, map (genvar o type_of) (av @ [tv])) in
	   let tms = find_terms (\tm. can (match epat) tm) gl in
	   PURE_ONCE_REWRITE_TAC (map LIST_BETA_CONV tms) (A,gl) in
      GEN_ALL(TAC_PROOF(goal,
              STRIP_ASSUME_TAC ith THEN FIRST_ASSUM etac THEN
              REPEAT STRIP_TAC THEN FIRST_ASSUM fn_beta THEN
              RES_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC)))?\tok
    failwith(`Can't solve recursion equation: `^tok);;

let zet_recursive_definition k infix_flag name tml = 
 let thm = zet_prove_rec_fn_exists k tml
 in
 new_specification
  name
  [(infix_flag=>`infix`|`constant`),
  ((fst o dest_var o fst o dest_exists o concl) thm)]
  thm;; 

let zet_zero_definition = zet_recursive_definition "zero";;

let zet_one_definition = zet_recursive_definition "een";;

