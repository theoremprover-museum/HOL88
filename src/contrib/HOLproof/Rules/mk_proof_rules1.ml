% mk_proof_rules.ml

  ml-functions that prove things: preliminaries %


% --- general ml functions --- %

% position finds the position of an element x in a list xl %
letrec position x xl =
 if xl = [] then 0
 else if x = hd xl then 1
 else 1 + position x (tl xl);;

% rcorr_tyinst find pair in xyl with first component x (a type) with type instantiation %
letrec rcorr_tyinst x xyl =
 if xyl = [] then failwith `rcorr_tyinst: no such alternative`
 else 
  let (h1,h2).t = xyl in
  let instl = snd(match (mk_var(`x`,h1)) (mk_var(`x`,x))) ? [] in
  if x = inst_type instl h1 ? false then h2
  else rcorr_tyinst x t;;

% rcorr_tminst find pair in xyl with first component x (a term) with type instantiation %
letrec rcorr_tminst x xyl =
 if xyl = [] then failwith `rcorr_tyinst: no such alternative`
 else 
  let (h1,h2).t = xyl in
  let instl = snd(match h1 x) ? [] in
  if x = inst [] instl h1 ? false then h2
  else rcorr_tminst x t;;


% --- additional inference rules --- %

% AP_TERM_LIST - AP_TERM for n-ary function over a reversed list of theorems %
letrec AP_TERM_LIST tm thl =
 if thl = [] then REFL tm
 else
  let h.t = thl in
  let th = AP_TERM_LIST tm t in
  TRANS (AP_THM th (lhs(concl h)))
        (AP_TERM (rhs(concl th)) h);;

% AP_TERM_LIST2 - AP_TERM for n-ary function over a nonreversed list of theorems %
letrec AP_TERM_LIST2 tm thl =
 if thl = [] then REFL tm
 else
  let h,t = last thl,butlast thl in
  let th = AP_TERM_LIST2 tm t in
  TRANS (AP_THM th (lhs(concl h)))
        (AP_TERM (rhs(concl th)) h);;

% --- set up global variable for equality rules --- %

letref Reqs = ([]:(type#(term list -> thm))list);;
letref RReqs = ([]:(type#proof)list);;

% --- rules for the type :bool --- %

let bool_distinct = CONJUNCT1 BOOL_EQ_DISTINCT;;
let bool_conl = ["T";"F"];;

% equality %
let Rbool_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else
    let th = EQF_INTRO bool_distinct in
    if t1 = "T" then th
    else TRANS (SYM(SYM_CONV(lhs(concl th)))) th )
 ? REFL(mk_eq(t1,t2));;
let RRbool_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM (mk_comb("$=:bool->bool->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:bool->bool->bool" th1) t2b)
              (Rbool_eq [t1b;t2b]) )
 ? AP_TERM_LIST  "$=:bool->bool->bool" [th2;th1] ;;
Reqs := (":bool",Rbool_eq).Reqs;;
RReqs := (":bool",RRbool_eq).RReqs;;

% negation %
let NOT_CONJS = 
 [CONJUNCT1(CONJUNCT2 NOT_CLAUSES)
 ;CONJUNCT2(CONJUNCT2 NOT_CLAUSES)] ;;
let Rnot [t1] =
  if t1 = "T" then hd NOT_CONJS
  else if t1 = "F" then hd(tl NOT_CONJS)
  else REFL(mk_neg t1);;
let RRnot [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 TRANS (AP_TERM "$~"  th1) (Rnot [t1b])
 ? AP_TERM "$~" th1;;

% conjunction (special case) %
let AND_CONJS =
 let th = SPEC_ALL AND_CLAUSES in
 [GEN_ALL(CONJUNCT1(CONJUNCT2 th))
 ;GEN_ALL(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))
 ;GEN_ALL(CONJUNCT1 th)
 ;GEN_ALL(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))];;
let Rand [t1;t2] =
  if t2 = "T" then SPEC t1 (hd AND_CONJS)
  else if t2 = "F" then SPEC t1 (hd(tl AND_CONJS))
  else if t1 = "T" then SPEC t2 (el 3 AND_CONJS)
  else if t1 = "F" then SPEC t2 (el 4 AND_CONJS)
  else REFL(mk_conj(t1,t2));;
let RRand [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "$/\" [th2;th1]) (Rand [t1b;t2b])
  ? AP_TERM_LIST "$/\" [th2;th1];;

% disjunction (special case) %
let OR_CONJS =
 let th = SPEC_ALL OR_CLAUSES in
 [GEN_ALL(CONJUNCT1(CONJUNCT2  th))
 ;GEN_ALL(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))
 ;GEN_ALL(CONJUNCT1 th)
 ;GEN_ALL(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))];;
let Ror [t1;t2] =
  if t2 = "T" then SPEC t1 (hd OR_CONJS)
  else if t2 = "F" then SPEC t1 (hd(tl OR_CONJS))
  else if t1 = "T" then SPEC t2 (el 3 OR_CONJS)
  else if t1 = "F" then SPEC t2 (el 4 OR_CONJS)
  else REFL(mk_disj(t1,t2));;
let RRor [th1;th2] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  TRANS (AP_TERM_LIST "$\/" [th2;th1]) (Ror [t1b;t2b])
  ? AP_TERM_LIST "$\/" [th2;th1];;

% conditional %
let COND_CONJS =
 let th = SPEC_ALL COND_CLAUSES in
 [GEN_ALL(CONJUNCT1 th)
 ;GEN_ALL(CONJUNCT2 th)];;
let Rcond [t1;t2;t3] =
  if t1 = "T" then ISPECL [t2;t3] (hd COND_CONJS)
  else if t1 = "F" then ISPECL [t2;t3] (hd(tl COND_CONJS))
  else REFL(mk_cond(t1,t2,t3));;
let RRcond [th1;th2;th3] =
  let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let t3a,t3b = dest_eq(concl th3) in
  let ty2 = type_of t2b in
  TRANS (AP_TERM_LIST "COND:bool->^ty2->^ty2->^ty2" [th3;th2;th1])
        (Rcond [t1b;t2b;t3b])
  ? AP_TERM_LIST "COND:bool->^ty2->^ty2->^ty2" [th3;th2;th1];;


% --- rules for the type :num %

% equality %
let Rnum_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else num_EQ_CONV (mk_eq(t1,t2)) )
 ? REFL(mk_eq(t1,t2));;
let RRnum_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM (mk_comb("$=:num->num->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:num->num->bool" th1) t2b)
              (Rnum_eq [t1b;t2b]) )
 ? AP_TERM_LIST  "$=:num->num->bool" [th2;th1];;
Reqs := (":num",Rnum_eq).Reqs;;
RReqs := (":num",RRnum_eq).RReqs;;


% --- rules for the type :string %

% equality %
let Rstring_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else string_EQ_CONV (mk_eq(t1,t2)) )
 ? REFL(mk_eq(t1,t2));;
let RRstring_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 TRANS (AP_TERM (mk_comb("$=:string->string->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:string->string->bool" th1) t2b)
       (Rstring_eq [t1b;t2b]) )
 ? AP_TERM_LIST  "$=:string->string->bool" [th2;th1];;
Reqs := (":string",Rstring_eq).Reqs;;
RReqs := (":string",RRstring_eq).RReqs;;


% -- rules for paired types --- %

let prod_11 = PAIR_EQ;;
let prod_conl = [",:*->**->*#**"];;

% equality %
let Rprod_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else
    let t1x,t1y = dest_pair t1 in
    let t2x,t2y = dest_pair t2 in
    let [tyx;tyy] = snd(dest_type(type_of t1)) in
    TRANS (ISPECL[t1x;t1y;t2x;t2y] prod_11)
          (RRand [(rcorr_tyinst tyx Reqs ? (\[t1;t2].REFL "^t1 = ^t2"))[t1x;t2x]
                 ;(rcorr_tyinst tyy Reqs ? (\[t1;t2].REFL "^t1 = ^t2"))[t1y;t2y]
                 ] ) )
 ? REFL(mk_eq(t1,t2));;
let RRprod_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [tyx;tyy] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM (mk_comb("$=:^tyx#^tyy->^tyx#^tyy->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:^tyx#^tyy->^tyx#^tyy->bool" th1) t2b)
              (Rprod_eq [t1b;t2b]) )
 ? AP_TERM_LIST "$=:^tyx#^tyy->^tyx#^tyy->bool" [th2;th1] ;;
Reqs := (":*#**",Rprod_eq).Reqs;;
RReqs := (":*#**",RRprod_eq).RReqs;;

% FST %
let Rfst [t1] =
  let [tyx;tyy] = snd(dest_type(type_of t1)) in
  let x,y = dest_pair t1 in
  ISPECL[x;y] FST
  ? REFL(mk_comb("FST:^tyx#^tyy->^tyx",t1));;
let RRfst [th1] =
  let t1a,t1b = dest_eq(concl th1) in
  let [tyx;tyy] = snd(dest_type(type_of t1b)) in
  TRANS (AP_TERM "FST:^tyx#^tyy->^tyx"  th1) (Rfst [t1b])
  ? AP_TERM "FST:^tyx#^tyy->^tyx" th1;;

% SND %
let Rsnd [t1] =
  let [tyx;tyy] = snd(dest_type(type_of t1)) in
  let x,y = dest_pair t1 in
  ISPECL[x;y] SND
  ? REFL(mk_comb("SND:^tyx#^tyy->^tyy",t1));;
let RRsnd [th1] =
  let t1a,t1b = dest_eq(concl th1) in
  let [tyx;tyy] = snd(dest_type(type_of t1b)) in
  TRANS (AP_TERM "SND:^tyx#^tyy->^tyy"  th1) (Rsnd [t1b])
  ? AP_TERM "SND:^tyx#^tyy->^tyy" th1;;

% SND o SND %
let Rsndsnd [t1] =
  let ty0 = type_of t1 in
  let [tyx;ty] = snd(dest_type ty0) in
  let [tyy;tyz] = snd(dest_type ty) in
  (let x,yz = dest_pair t1 in
   let y,z = dest_pair yz in
   let thm1 = ISPECL["SND:^ty->^tyz";"SND:^ty0->^ty"] o_DEF in
   let thm2 = TRANS (AP_TERM "SND:^ty->^tyz" (ISPECL[x;yz] SND))
                    (ISPECL[y;z] SND) in
   TRANS (BETA_RULE (AP_THM thm1 t1)) thm2 )
  ? REFL(mk_comb("(SND o SND):^tyx#^tyy#^tyz->^tyz",t1));;
let RRsndsnd [th1] =
  let t1a,t1b = dest_eq(concl th1) in
  let [tyx;ty] = snd(dest_type(type_of t1b)) in
  let [tyy;tyz] = snd(dest_type ty) in
  TRANS (AP_TERM "(SND o SND):^tyx#^tyy#^tyz->^tyz"  th1) (Rsndsnd [t1b])
  ? AP_TERM "(SND o SND):^tyx#^tyy#^tyz->^tyz" th1;;


% --- basic rules for lists --- %

let list_conl = ["[]:(*)list";"CONS:*->(*)list->(*)list"];;

% equality %
letrec Rlist_eq [t1;t2] =
 (if t1 = t2 then EQT_INTRO (REFL t1)
  else
   if is_cons t1 then
    if is_cons t2 then
     let [ty] = snd(dest_type(type_of t1)) in
     let t1x,t1y = dest_cons t1 in
     let t2x,t2y = dest_cons t2 in
     TRANS (ISPECL[t1x;t1y;t2x;t2y] CONS_11)
           (RRand [(rcorr_tyinst ty Reqs ? (\[t1;t2].REFL "^t1 = ^t2"))[t1x;t2x]
                 ;Rlist_eq [t1y;t2y]
                 ] )
    else % t2 is NIL %
     let t1x,t1y = dest_cons t1 in
     EQF_INTRO (ISPECL[t1x;t1y] NOT_CONS_NIL)
   else % t1 is NIL %
    if is_cons t2 then
     let t2x,t2y = dest_cons t2 in
     EQF_INTRO (ISPECL[t2x;t2y] NOT_NIL_CONS)
    else % t2 is NIL %
     fail )
 ? REFL(mk_eq(t1,t2));;
let RRlist_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [ty] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM (mk_comb("$=:(^ty)list->(^ty)list->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:(^ty)list->(^ty)list->bool" th1) t2b)
              (Rlist_eq[t1b;t2b]) )
  ? AP_TERM_LIST  "$=:(^ty)list->(^ty)list->bool" [th2;th1] ;;
Reqs := (":(*)list",Rlist_eq).Reqs;;
RReqs := (":(*)list",RRlist_eq).RReqs;;

% HD %
letrec Rhd [t1] =
 let [ty] = snd(dest_type(type_of t1)) in
 (let h,t = dest_cons t1 in ISPECL[h;t] HD)
 ? REFL(mk_comb("HD:(^ty)list->^ty",t1));;
let RRhd [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 let [ty] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM "HD:(^ty)list->^ty" th1)
       (Rhd [t1b])
 ? AP_TERM "HD:(^ty)list->^ty" th1;;

% TL %
letrec Rtl [t1] =
 let [ty] = snd(dest_type(type_of t1)) in
 (let h,t = dest_cons t1 in ISPECL[h;t] TL)
 ? REFL(mk_comb("TL:(^ty)list->(^ty)list",t1));;
let RRtl [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 let [ty] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM "TL:(^ty)list->(^ty)list" th1)
       (Rtl [t1b])
 ? AP_TERM "TL:(^ty)list->(^ty)list" th1;;

% LENGTH %
let LENGTH_CONJS = CONJUNCTS LENGTH;;
letrec Rlength [t1] =
 let [ty] = snd(dest_type(type_of t1)) in
 (if t1 = "[]:(^ty)list" then INST_TYPE[ty,":*"] (hd LENGTH_CONJS)
  else
   let h,t = dest_cons t1 in
   (TRANS (ISPECL[h;t] (hd(tl LENGTH_CONJS)))
          (AP_TERM "SUC" (Rlength [t]) ) ) )
 ? REFL(mk_comb("LENGTH:(^ty)list->num",t1));;
let RRlength [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 let [ty] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM "LENGTH:(^ty)list->num" th1)
       (Rlength [t1b])
 ? AP_TERM "LENGTH:(^ty)list->num" th1;;

% APPEND %
let APPEND_CONJS = CONJUNCTS APPEND;;
letrec Rappend[t1;t2] =
 let [ty] = snd(dest_type(type_of t1)) in
 (if is_cons t1 then 
   let h,l1 = dest_cons t1 in
   (TRANS (ISPECL[l1;t2;h] (hd(tl APPEND_CONJS)))
       (AP_TERM_LIST2 "CONS:^ty->(^ty)list->(^ty)list"
         [REFL h;Rappend[l1;t2]] ) )
  else ISPEC t2 (hd APPEND_CONJS) )
 ? REFL(list_mk_comb("APPEND:(^ty)list->(^ty)list->(^ty)list",[t1;t2]));;
let RRappend [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [ty] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM_LIST "APPEND:(^ty)list->(^ty)list->(^ty)list" [th2;th1])
       (Rappend [t1b;t2b])
 ? AP_TERM_LIST "APPEND:(^ty)list->(^ty)list->(^ty)list" [th2;th1];;

% LAPPEND %
let LAPPEND_CONJS = CONJUNCTS LAPPEND_DEF;;
letrec Rlappend[t1] =
 let [ty] = snd(dest_type(hd(snd(dest_type(type_of t1))))) in
 (if is_cons t1 then 
   let h,t = dest_cons t1 in
   (TRANS (ISPECL[h;t] (hd(tl LAPPEND_CONJS)))
       (RRappend[REFL h;Rlappend[t]]) )
  else INST_TYPE[ty,":*"](hd LAPPEND_CONJS) )
 ? REFL(list_mk_comb("LAPPEND:((^ty)list)list->(^ty)list",[t1]));;
let RRlappend [th1] =
 let t1a,t1b = dest_eq(concl th1) in
  let [ty] = snd(dest_type(hd(snd(dest_type(type_of t1b))))) in
 TRANS (AP_TERM "LAPPEND:((^ty)list)list->(^ty)list" th1)
       (Rlappend [t1b])
 ? AP_TERM "LAPPEND:((^ty)list)list->(^ty)list" th1;;

% MAP %
let MAP_CONJS = CONJUNCTS MAP;;
letrec Rmap Rule [f;t2] =
 let [tyx;tyy] = snd(dest_type(type_of f)) in
 (if t2 = "[]:(^tyx)list" then ISPEC f (hd MAP_CONJS)
  else
   let h,t = dest_cons t2 in
   (TRANS (ISPECL[f;h;t] (hd(tl MAP_CONJS)))
       (AP_TERM_LIST "CONS:^tyy->(^tyy)list->(^tyy)list"
         [Rmap Rule [f;t]
         ;Rule [h] ? AP_TERM f (REFL h)
         ] ) ) )
 ? REFL(list_mk_comb("MAP:(^tyx->^tyy)->(^tyx)list->(^tyy)list",[f;t2]));;
let RRmap Rule [th1;th2] =
 let t1a,f = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [tyx;tyy] = snd(dest_type(type_of f)) in
 TRANS (AP_TERM_LIST "MAP:(^tyx->^tyy)->(^tyx)list->(^tyy)list" [th2;th1])
       (Rmap Rule [f;t2b])
 ? AP_TERM_LIST "MAP:(^tyx->^tyy)->(^tyx)list->(^tyy)list" [th2;th1];;

% XMAP2 %
let XMAP2_CONJS = CONJUNCTS XMAP2;;
letrec Rxmap2 Rule [f;t1;t2] =
 let [tyx;ty] = snd(dest_type(type_of f)) in
 let [tyy;tyz] = snd(dest_type ty) in
 (if is_cons t1 then
   let h1,t1 = dest_cons t1 in
   let h2,t2 = dest_cons t2 in
   (TRANS (ISPECL[f;h1;t1;h2;t2] (hd(tl XMAP2_CONJS)))
       (AP_TERM_LIST2 "CONS:^tyz->(^tyz)list->(^tyz)list"
              [Rule[h1;h2]
              ;Rxmap2 Rule [f;t1;t2]
              ] ) )
  else  ISPEC f (hd XMAP2_CONJS) )
 ? REFL(list_mk_comb
  ("XMAP2:(^tyx->^tyy->^tyz)->(^tyx)list->(^tyy)list->(^tyz)list",[f;t1;t2]));;
let RRxmap2 Rule [th1;th2;th3] =
 let t1a,f = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let t3a,t3b = dest_eq(concl th3) in
 let [tyx;ty] = snd(dest_type(type_of f)) in
 let [tyy;tyz] = snd(dest_type ty) in
 TRANS (AP_TERM_LIST 
   "XMAP2:(^tyx->^tyy->^tyz)->(^tyx)list->(^tyy)list->(^tyz)list"[th3;th2;th1])
       (Rxmap2 Rule [f;t2b;t3b])
 ? AP_TERM_LIST 
   "XMAP2:(^tyx->^tyy->^tyz)->(^tyx)list->(^tyy)list->(^tyz)list"[th3;th2;th1];;

% EVERY %
let EVERY_CONJS = CONJUNCTS EVERY_DEF;;
letrec Revery Rule [f;t2] =
 let [ty;_] = snd(dest_type(type_of f)) in
 (if t2 = "[]:(^ty)list" then ISPEC f (hd EVERY_CONJS)
  else
   let h,t = dest_cons t2 in
   (TRANS (ISPECL[f;h;t] (hd(tl EVERY_CONJS)))
       (RRand [Rule [h] ? AP_TERM f (REFL h)
              ;Revery Rule [f;t]
              ] ) ) )
 ? REFL(list_mk_comb("EVERY:(^ty->bool)->(^ty)list->bool",[f;t2]));;
let RRevery Rule [th1;th2] =
 let t1a,f = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [ty;_] = snd(dest_type(type_of f)) in
 TRANS (AP_TERM_LIST "EVERY:(^ty->bool)->(^ty)list->bool" [th2;th1])
       (Revery Rule [f;t2b])
 ? AP_TERM_LIST "EVERY:(^ty->bool)->(^ty)list->bool" [th2;th1];;

% EVERY2 %
let EVERY2_CONJS = CONJUNCTS EVERY2;;
letrec Revery2 Rule [f;t1;t2] =
 let [tyx;ty] = snd(dest_type(type_of f)) in
 let [tyy;_] = snd(dest_type ty) in
 (if is_cons t1 then
   let h1,t1 = dest_cons t1 in
   let h2,t2 = dest_cons t2 in
   (TRANS (ISPECL[f;h1;t1;h2;t2] (hd(tl EVERY2_CONJS))))
       (RRand [Rule [h1;h2] ? AP_TERM_LIST2 f [REFL h1;REFL h2]
              ;Revery2 Rule [f;t1;t2]
              ] )
  else ISPEC f (hd EVERY2_CONJS) )
 ? REFL(list_mk_comb
     ("EVERY2:(^tyx->^tyy->bool)->(^tyx)list->(^tyy)list->bool",[f;t1;t2]));;
let RRevery2 Rule [th1;th2;th3] =
 let t1a,f = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let t3a,t3b = dest_eq(concl th3) in
 let [tyx;ty] = snd(dest_type(type_of f)) in
 let [tyy;_] = snd(dest_type ty) in
 TRANS (AP_TERM_LIST 
    "EVERY2:(^tyx->^tyy->bool)->(^tyx)list->(^tyy)list->bool" [th3;th2;th1])
       (Revery2 Rule [f;t2b;t3b])
 ? AP_TERM_LIST 
     "EVERY2:(^tyx->^tyy->bool)->(^tyx)list->(^tyy)list->bool" [th3;th2;th1];;


% --- conversions for auxiliary list handling functions --- %

% mem %
let mem_CONJS = CONJUNCTS mem_DEF;;
letrec Rmem [x;t2] =
 let ty = type_of x in
 (if t2 = "[]:(^ty)list" then
   ISPEC x (hd mem_CONJS)
  else
   let h,t = dest_cons t2 in
   TRANS (ISPECL[x;h;t] (hd(tl mem_CONJS)))
         (RRor [(rcorr_tyinst ty Reqs ? \[t1;t2]. REFL(mk_eq(t1,t2))) [x;h]
               ;Rmem [x;t]
               ] ) )
 ? REFL(list_mk_comb("mem:^ty->(^ty)list->bool",[x;t2]));;
let RRmem [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = type_of t1b in
 TRANS (AP_TERM_LIST "mem:^ty->(^ty)list->bool" [th2;th1])
       (Rmem[t1b;t2b])
 ? AP_TERM_LIST "mem:^ty->(^ty)list->bool" [th2;th1];;

% mem1 %
let mem1_CONJS = CONJUNCTS mem1_DEF;;
letrec Rmem1 [x;t2] =
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2))))) in
 (if t2 = "[]:(^tyx#^tyy)list" then
   SPEC x (INST_TYPE[tyx,":*";tyy,":**"] (hd mem1_CONJS))
  else
   let h,t = dest_cons t2 in
   TRANS (ISPECL[x;h;t] (hd(tl mem1_CONJS)))
         (RRor [(rcorr_tyinst tyx RReqs ? AP_TERM_LIST2 "$=:^tyx->^tyx->bool")
                 [REFL x;Rfst[h]]
               ;Rmem1 [x;t]
               ] ) )
 ? REFL(list_mk_comb("mem1:^tyx->(^tyx#^tyy)list->bool",[x;t2]));;
let RRmem1 [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2b))))) in
 TRANS (AP_TERM_LIST "mem1:^tyx->(^tyx#^tyy)list->bool" [th2;th1])
       (Rmem1 [t1b;t2b])
 ? AP_TERM_LIST "mem1:^tyx->(^tyx#^tyy)list->bool" [th2;th1];;

% mem2 %
let mem2_CONJS = CONJUNCTS mem2_DEF;;
letrec Rmem2 [x;t2] =
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2))))) in
 (if t2 = "[]:(^tyx#^tyy)list" then
   SPEC x (INST_TYPE[tyx,":*";tyy,":**"] (hd mem2_CONJS))
  else
   let h,t = dest_cons t2 in
   TRANS (ISPECL[x;h;t] (hd(tl mem2_CONJS)))
         (RRor [(rcorr_tyinst tyy RReqs ? AP_TERM_LIST2 "$=:^tyy->^tyy->bool")
                 [REFL x;Rsnd[h]]
               ;Rmem2 [x;t]
               ] ) )
 ? REFL(list_mk_comb("mem2:^tyy->(^tyx#^tyy)list->bool",[x;t2]));;
let RRmem2 [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2b))))) in
 TRANS (AP_TERM_LIST "mem2:^tyy->(^tyx#^tyy)list->bool" [th2;th1])
       (Rmem2 [t1b;t2b])
 ? AP_TERM_LIST "mem2:^tyy->(^tyx#^tyy)list->bool" [th2;th1];;

% corr1 %
let corr1_CONJS = CONJUNCTS corr1_DEF;;
letrec Rcorr1 [x;t2] =
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2))))) in
 (if t2 = "[]:(^tyx#^tyy)list" then
   SPEC x (INST_TYPE[tyx,":*";tyy,":**"] (hd corr1_CONJS))
  else
   let h,t = dest_cons t2 in
   (TRANS (ISPECL[x;h;t] (hd(tl corr1_CONJS)))
          (RRcond [(rcorr_tyinst tyx RReqs ? AP_TERM_LIST2 "=:^tyx->^tyx->bool")
                       [REFL x;Rfst[h]]
                       ;Rsnd [h]
                       ;Rcorr1 [x;t]
                       ] ) ) )
 ? REFL(list_mk_comb("corr1:^tyx->(^tyx#^tyy)list->^tyy",[x;t2]));;
let RRcorr1 [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2b))))) in
 TRANS (AP_TERM_LIST "corr1:^tyx->(^tyx#^tyy)list->^tyy" [th2;th1])
       (Rcorr1[t1b;t2b])
 ? AP_TERM_LIST "corr1:^tyx->(^tyx#^tyy)list->^tyy" [th2;th1];;

% corr2 %
let corr2_CONJS = CONJUNCTS corr2_DEF;;
letrec Rcorr2 [x;t2] =
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2))))) in
 (if t2 = "[]:(^tyx#^tyy)list" then
   SPEC x (INST_TYPE[tyx,":*";tyy,":**"] (hd corr2_CONJS))
  else
   let h,t = dest_cons t2 in
   (TRANS (ISPECL[x;h;t] (hd(tl corr2_CONJS)))
          (RRcond [(rcorr_tyinst tyy RReqs ? AP_TERM_LIST2 "=:^tyy->^tyy->bool")
                       [REFL x;Rsnd[h]]
                       ;Rfst [h]
                       ;Rcorr2 [x;t]
                       ] ) ) )
 ? REFL(list_mk_comb("corr2:^tyy->(^tyx#^tyy)list->^tyx",[x;t2]));;
let RRcorr2 [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t2b))))) in
 TRANS (AP_TERM_LIST "corr2:^tyy->(^tyx#^tyy)list->^tyx" [th2;th1])
       (Rcorr2[t1b;t2b])
 ? AP_TERM_LIST "corr2:^tyy->(^tyx#^tyy)list->^tyx" [th2;th1];;

% lmem %
let lmem_CONJS = CONJUNCTS lmem_DEF;;
letrec Rlmem [t1;l] =
 let [ty] = snd(dest_type(type_of t1)) in
 (if is_cons t1 then 
   let x,xl = dest_cons t1 in
   (TRANS (ISPECL[x;xl;l] (hd(tl lmem_CONJS)))
          (RRand [Rmem [x;l];Rlmem [xl;l]]) )
  else ISPEC l (hd lmem_CONJS) )
 ? REFL(list_mk_comb("lmem:(^ty)list->(^ty)list->bool",[t1;l]));;
let RRlmem [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [ty] = snd(dest_type(type_of t1b)) in
 TRANS (AP_TERM_LIST "lmem:(^ty)list->(^ty)list->bool" [th2;th1])
       (Rlmem [t1b;t2b])
 ? AP_TERM_LIST "lmem:(^ty)list->(^ty)listbool" [th2;th1];;

% lor %
let lor_CONJS = CONJUNCTS lor_DEF;;
letrec Rlor [t1] =
 (if t1 = "[]:(bool)list" then 
   hd lor_CONJS
  else
   let h,t = dest_cons t1 in
   TRANS (SPECL[h;t] (el 2 lor_CONJS))
         (RRor [REFL h;Rlor [t]]) )
 ? REFL(list_mk_comb("lor",[t1]));;
let RRlor [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 TRANS (AP_TERM "lor" th1) (Rlor [t1b])
 ? AP_TERM "lor" th1;;

% land %
let land_CONJS = CONJUNCTS land_DEF;;
letrec Rland [t1] =
 (if t1 = "[]:(bool)list" then 
   hd land_CONJS
  else
   let h,t = dest_cons t1 in
   TRANS (SPECL[h;t] (el 2 land_CONJS))
         (RRand [REFL h;Rland [t]]) )
 ? REFL(list_mk_comb("land",[t1]));;
let RRland [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 TRANS (AP_TERM "land" th1) (Rland [t1b])
 ? AP_TERM "land" th1;;

% nocontr %
let nocontr_CONJS = CONJUNCTS nocontr_DEF;;
letrec Rnocontr [t1] =
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t1))))) in
 (if is_cons t1 then 
   let xy,xyl = dest_cons t1 in
   TRANS (ISPECL[xy;xyl] (el 2 nocontr_CONJS))
     (RRand[RRor[RRnot[RRmem2[Rsnd[xy];REFL xyl]]
                ;(snd(assoc tyx RReqs))[RRcorr2[Rsnd[xy];REFL xyl];Rfst[xy]] ]
           ;Rnocontr[xyl] ] )
  else
   INST_TYPE[tyx,":*";tyy,":**"] (hd nocontr_CONJS) )
 ? REFL(list_mk_comb("nocontr:(^tyx#^tyy)list->bool",[t1]));;
let RRnocontr [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 let [tyx;tyy] = snd(dest_type(hd(snd(dest_type(type_of t1b))))) in
 TRANS (AP_TERM "nocontr:(^tyx#^tyy)list->bool" th1) (Rnocontr [t1b])
 ? AP_TERM "nocontr:(^tyx#^tyy)list->bool" th1;;


% --- rules for sets --- %

% SUBSET %
letrec Rsubset [t1;t2] =
 (let ty = hd(snd(dest_type(type_of t1))) in
  let conv = \t.(rcorr_tyinst ty Reqs)(snd(strip_comb t)) in
  let op1,argl1 = strip_comb t1 in
  if argl1 = [] then
   EQT_INTRO (ISPEC t2 EMPTY_SUBSET)
  else
   let [x;s] = argl1 in
   TRANS (ISPECL [x;s;t2] INSERT_SUBSET)
         (RRand [IN_CONV conv (list_mk_comb("IN:^ty->(^ty)set->bool",[x;t2]))
                ;Rsubset[s;t2]])
 ? REFL (list_mk_comb("SUBSET:(^ty)set->(^ty)set->bool",[t1;t2])) )
 ? failwith `Rsubset`;;
let RRsubset [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = hd(snd(dest_type(type_of t1a))) in
 TRANS (AP_TERM (mk_comb("SUBSET:(^ty)set->(^ty)set->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "SUBSET:(^ty)set->(^ty)set->bool" th1) t2b)
              (Rsubset[t1b;t2b]) )
  ? AP_TERM_LIST  "SUBSET:(^ty)set->(^ty)set->bool" [th2;th1] ;;

% equality %
let SUBSET_ANTISYM_EQ = prove
 ("!s:(*)set.!t. s SUBSET t /\ t SUBSET s = (s = t)",
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  IMP_RES_TAC SUBSET_ANTISYM THEN ART[SUBSET_REFL]);;
let Rset_eq [t1;t2] =
 (TRANS (SYM(ISPECL[t1;t2] SUBSET_ANTISYM_EQ))
       (RRand[Rsubset[t1;t2];Rsubset[t2;t1]]) )
 ? REFL(mk_eq(t1,t2))
 ? failwith `Rset_eq`;;
let RRset_eq [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = hd(snd(dest_type(type_of t1a))) in
 TRANS (AP_TERM (mk_comb("$=:(^ty)set->(^ty)set->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "$=:(^ty)set->(^ty)set->bool" th1) t2b)
              (Rset_eq[t1b;t2b]) )
  ? AP_TERM_LIST  "$=:(^ty)set->(^ty)set->bool" [th2;th1] ;;
Reqs := (":(*)set",Rset_eq).Reqs;;
RReqs := (":(*)set",RRset_eq).RReqs;;

% IN %
let Rin [t1;t2] =
 (let ty = type_of t1 in
  let conv = \t.(rcorr_tyinst ty Reqs)(snd(strip_comb t)) in
  IN_CONV conv (list_mk_comb("IN:^ty->(^ty)set->bool",[t1;t2]))
 ? REFL (list_mk_comb("IN:^ty->(^ty)set->bool",[t1;t2])) )
 ? failwith `Rin`;;
let RRin [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = type_of t1a in
 TRANS (AP_TERM (mk_comb("IN:^ty->(^ty)set->bool",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "IN:^ty->(^ty)set->bool" th1) t2b)
              (Rin[t1b;t2b]) )
  ? AP_TERM_LIST  "IN:^ty->(^ty)set->bool" [th2;th1] ;;

% DELETE %
let Rdelete [t1;t2] =
 (let ty = type_of t2 in
  let conv = \t.(rcorr_tyinst ty Reqs)(snd(strip_comb t)) in
  DELETE_CONV conv (list_mk_comb("DELETE:(^ty)set->^ty->(^ty)set",[t1;t2]))
 ? REFL (list_mk_comb("DELETE:(^ty)set->^ty->(^ty)set",[t1;t2])) )
 ? failwith `Rdelete`;;
let RRdelete [th1;th2] =
 let t1a,t1b = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let ty = type_of t2a in
 TRANS (AP_TERM (mk_comb("DELETE:(^ty)set->^ty->(^ty)set",t1a)) th2)
       (TRANS (AP_THM (AP_TERM "DELETE:(^ty)set->^ty->(^ty)set" th1) t2b)
              (Rdelete[t1b;t2b]) )
  ? AP_TERM_LIST  "DELETE:(^ty)set->^ty->(^ty)set" [th2;th1] ;;

% UNION %
let Runion [t1;t2] =
 (let ty = hd(snd(dest_type(type_of t1))) in
  let conv = \t.(rcorr_tyinst ty Reqs)(snd(strip_comb t)) in
  UNION_CONV conv (list_mk_comb("UNION:(^ty)set->(^ty)set->(^ty)set",[t1;t2]))
 ? REFL (list_mk_comb("UNION:(^ty)set->(^ty)set->(^ty)set",[t1;t2])) )
 ? failwith `Runion`;;
let RRunion [th1;th2] =
 (let t1a,t1b = dest_eq(concl th1) in
  let t2a,t2b = dest_eq(concl th2) in
  let ty = type_of t1a in
  TRANS (AP_TERM (mk_comb("UNION:^ty->^ty->^ty",t1a)) th2)
        (TRANS (AP_THM (AP_TERM "UNION:^ty->^ty->^ty" th1) t2b)
               (Runion[t1b;t2b]) )
   ? AP_TERM_LIST  "UNION:^ty->^ty->^ty" [th2;th1] )
  ? failwith `RRunion`;;

% SEVERY %
let SEVERY_CONJS = CONJUNCTS SEVERY_DEF;;
letrec Rsevery Rule [f;t2] =
 let [ty;_] = snd(dest_type(type_of f)) in
 (if t2 = "{}:(^ty)set" then ISPEC f (hd SEVERY_CONJS)
  else
   let _,[tm;tms] = strip_comb t2 in
   TRANS (ISPECL[f;tm;tms] (hd(tl SEVERY_CONJS)))
         (RRand [Rule [tm]
                ;Rsevery Rule [f;tms]
                ] ) )
 ? REFL(list_mk_comb("SEVERY:(^ty->bool)->(^ty)set->bool",[f;t2]));;
let RRsevery Rule [th1;th2] =
 let t1a,f = dest_eq(concl th1) in
 let t2a,t2b = dest_eq(concl th2) in
 let [ty;_] = snd(dest_type(type_of f)) in
 TRANS (AP_TERM_LIST "SEVERY:(^ty->bool)->(^ty)set->bool" [th2;th1])
       (Rsevery Rule [f;t2b])
 ? AP_TERM_LIST "SEVERY:(^ty->bool)->(^ty)set->bool" [th2;th1];;

% LUNION %
let LUNION_CONJS = CONJUNCTS LUNION_DEF;;
letrec Rlunion [t1] =
 let ty1 = type_of t1 in
 let [ty2] = snd(dest_type ty1) in
 let [ty3] = snd(dest_type ty2) in
 (if is_cons t1 then 
   let h,t = dest_cons t1 in
   TRANS (ISPECL[h;t] (el 2 LUNION_CONJS))
         (RRunion [REFL h;Rlunion [t]])
  else INST_TYPE[ty3,":*"] (hd LUNION_CONJS) )
 ? REFL(list_mk_comb("LUNION:^ty1->^ty2",[t1]));;
let RRlunion [th1] =
 let t1a,t1b = dest_eq(concl th1) in
 let ty1 = type_of t1b in
 let [ty2] = snd(dest_type ty1) in
 let [ty3] = snd(dest_type ty2) in
 TRANS (AP_TERM "LUNION:^ty1->^ty2" th1) (Rlunion [t1b])
 ? AP_TERM "LUNION:^ty1->^ty2" th1;;


