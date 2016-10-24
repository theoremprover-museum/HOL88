% File: RCprocedure_convs.ml

  conversions for procedure handling
%

% --- extended regular_conv --- %

% File: RCrecursion_convs.ml

  conversions for recursion handling
%

letrec regular_CONV1 x c =
 let [ty1;ty2] = snd(dest_type(type_of x)) in
 let ty1,ty2 = hd(snd(dest_type ty1)),hd(snd(dest_type ty2)) in
 if not (mem x (frees c)) then 
   let th1 = mono_CONV c in
   MP (ISPEC c (INST_TYPE[ty1,":*s3";ty2,":*s4"] regular_const)) th1
 else if c = x ? false then 
   INST_TYPE[ty1,":*s1";ty2,":*s2"] regular_id
 else
  let op,argl = strip_comb c in
  let ty = type_of op in
  if op = "seq:^ty" ? false then 
   let [c1;c2] = argl in
   let th1 = regular_CONV1 x c1 in
   let th2 = regular_CONV1 x c2 in
   BETA_RULE (MP(ISPECL[mk_abs(x,c1);mk_abs(x,c2)]regular_seq)(CONJ th1 th2))
 else if op = "cond:^ty" ? false then 
   let [g;c1;c2] = argl in
   let th1 = regular_CONV1 x c1 in
   let th2 = regular_CONV1 x c2 in
   BETA_RULE(MP(ISPECL[g;mk_abs(x,c1);mk_abs(x,c2)]regular_cond)(CONJ th1 th2))
 else if op = "pcall:^ty" ? false then 
   let [X;G;R] = argl in
   ISPECL[G;R]regular_pcall
 else fail;;
letrec regular_CONV f =
 let x,c = dest_abs f in
 regular_CONV1 x c;;
let regular_TAC:tactic (asl,w) = 
  [],\[].regular_CONV (snd(dest_comb w)) ? failwith `regular_TAC`;;



% --- procedure handling --- %

% produce the Rest function, given gluing function G 
  Example: gluR "\(x,y,z).y" --> "\(x,y,z.(x,z)"
%
let gluR G = % the rest function %
  letrec del y xl =
    if xl = [] then failwith `parameter not in state`
    else
      let h.t = xl in
      if y=h then t
      else h.(del y t) in
  letrec ldel yl xl =
    if yl = [] then xl
    else
      let y.yt = yl in
      ldel yt (del y xl) in
  if is_pabs G then
    let u,v = dest_pabs G in
    let ul,vl = strip_pair u,strip_pair v in
    let wl = ldel vl ul in
    if wl = [] then
       mk_pabs(u,"one")
    else
      let w = list_mk_pair wl in
      mk_pabs(u,w)
  else 
    let u,v = dest_abs G in
    if v=u then mk_abs(u,"one")
    else mk_abs(u,u);;

% produce type instantiation for procedure specification
  proc is specification (assert seq) nondass
  G is gluing function 
  result is type instantiated proc
%
let gluinst proc G =
  let op = fst(strip_comb proc) in
  let ty = type_of op in
  let P =
    if op = mk_const(`seq`,ty)? false then rand(rand proc)
    else rand proc in
  let u = fst(dest_pabs P) ? fst(dest_abs P) in
  let v = snd(dest_pabs G) ? fst(dest_abs G) in
  let tyinst = snd(match u v) in
  inst [] tyinst proc;;


% produce gluing instantiation tuple corresponding to gluing function G 
  G is gluing function
  result is "FST p,...,SND(SND(..(SND p)..))"
%
let gluaux G =
  letrec tuplify p =
    let (tyc,tyl) = dest_type(type_of p) in
    if tyc = `prod` then
      let thm = SYM(ISPEC p PAIR) in
      let a,b = dest_pair(rhs(concl thm)) in
      a.tuplify b
   else [p] in
  letrec glusplice u v p =
    if v = [] then p
    else
      if hd u = hd v then (hd v).(glusplice(tl u)(tl v)(tl p))
      else (hd p).(glusplice(tl u) v (tl p)) in
  let u,v = dest_pabs G ? dest_abs G in
  let ul,vl = strip_pair u,strip_pair v ? [u],[v] in
  let sty = type_of u in
  let pl = tuplify(mk_var(`p`,sty)) in
  list_mk_pair(glusplice ul vl pl);;

% --- prove that pcall to specification yields same result in-line ---
  proc in specification (nondass-command)
  G is gluing function
  result is theorem  |- nondass ... = pcall proc G R
%
let POP_NONEQ_TAC = 
  letrec POP_NONEQ_TAC1 n (asl,w) = 
    if is_eq(el n asl) then POP_NONEQ_TAC1 (n+1) (asl,w)
    else UNDISCH_TAC (el n asl) (asl,w) in
  POP_NONEQ_TAC1 1;;
let prove_pcall proc G =
  let u,v = dest_pabs G ? dest_abs G in
  let sty = type_of u in
  let R = gluR G in
  let proc' = gluinst proc G in
  let P' = rand proc' in
  let c1 = "nondass \u u'. ^P'(^G u)(^G u') /\ (^R u = ^R u')" in
  let thm1 = prove
   ("^c1 = pcall ^proc' ^G ^R",
    FUN_TAC THEN FUN_TAC THEN LPORT[pcall_DEF;nondass_DEF] THEN PBETA_TAC THEN
    PRT[PAIR_EQ] THEN EQ_TAC THENL
    [STRIP_TAC THEN EXISTS_TAC
       (mk_pabs(v,mk_comb(mk_var(`f`,mk_type(`fun`,[sty;mk_type(`bool`,[])])),
                          gluaux G))) THEN
     CONJ_TAC THENL
     [PBETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN POP_NONEQ_TAC THEN
      REPEAT (POP_ASSUM(SUBST1_TAC o SYM)) THEN RT[PAIR]
     ;GEN_TAC THEN PBETA_TAC THEN STRIP_TAC THEN ART[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN ART[]
    ]) in
  RR[PAIR_EQ;GSYM CONJ_ASSOC]
             (CONV_RULE (REDEPTH_CONV(CHANGED_CONV(PALPHA_CONV u)))
                        (PBETA_RULE thm1));;

% same for procedure with precondition (assert-command) %
let prove_pcall_pre proc G =
  let u,v = dest_pabs G ? dest_abs G in
  let sty = type_of u in
  let R = gluR G in
  let proc' = gluinst proc G in
  let B,P' = rand(rand(rator proc')),rand(rand proc') in
  let c1 = "(assert \u. ^B(^G u)) seq
            (nondass \u u'. ^P'(^G u)(^G u') /\ (^R u = ^R u'))" in
  let thm1 = prove
   ("^c1 = pcall ^proc' ^G ^R",
    FUN_TAC THEN FUN_TAC THEN LPORT[pcall_DEF;seq_DEF;nondass_DEF;assert_DEF;
       and_DEF] THEN PBETA_TAC THEN RT[PAIR_EQ] THEN EQ_TAC THENL
    [STRIP_TAC THEN ART[] THEN EXISTS_TAC
       (mk_pabs(v,mk_comb(mk_var(`f`,mk_type(`fun`,[sty;mk_type(`bool`,[])])),
                          gluaux G))) THEN
     CONJ_TAC THENL
     [PBETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN POP_NONEQ_TAC THEN
      REPEAT (POP_ASSUM(SUBST1_TAC o SYM)) THEN RT[PAIR]
     ;GEN_TAC THEN PBETA_TAC THEN STRIP_TAC THEN ART[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;REPEAT STRIP_TAC THEN ART[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[] THEN
     FIRST_ASSUM MATCH_MP_TAC THEN ART[]
    ]) in
  RR[PAIR_EQ;GSYM CONJ_ASSOC]
             (CONV_RULE (REDEPTH_CONV(CHANGED_CONV(PALPHA_CONV u)))
                        (PBETA_RULE thm1));;


% --- automatic proof of pcall correctness theorem ---
  procthm is theorem which says procedure implements specification
          |- ((assert B) seq (nondass P)) ref proc
  G is gluing function
  result is theorem  |- ((assert..)seq(nondass..)) ref (pcall proc G R)
%
let prove_pcall_ref procthm G =
  let spec = rand(rator(concl procthm)) in
  let op = fst(strip_comb spec) in
  let ty = type_of op in
  let thm1 = 
    if op = mk_const(`seq`,ty) ? false then prove_pcall_pre spec G 
    else prove_pcall spec G in
  let thm2 = ISPECL[G;gluR G] (MATCH_MP pcall_mono procthm) in
  PORR[SYM thm1] thm2;;



% --- procedure call with value parameters --- %

let list_mk_pair0 l =
  if l = [] then "a:one"
  else list_mk_pair l;;
let prove_xpcall proc G =
  let u,v = dest_pabs G ? dest_abs G in
  let sty = type_of u in
  let R = gluR G in
  let proc' = gluinst proc G in
  let P' = rand proc' in
  let a = list_mk_pair0(frees proc') in 
  let V = mk_var(`V`,mk_type(`fun`,[sty;type_of a])) in
  let c1 = "nondass \u. \u':^sty.
              (^(mk_pabs(a,"^P'(^G u)(^G u') /\ (^R u = ^R u')")))(^V u)" in
  let c2 = "xpcall ^(mk_pabs(a,proc')) ^G ^R ^V" in
  let thm1 = prove
   (mk_forall(V,mk_eq(c1,c2)),
    GEN_TAC THEN FUN_TAC THEN FUN_TAC THEN LPORT[xpcall_DEF;nondass_DEF] THEN
    PBETA_TAC THEN PORT[nondass_DEF] THEN PRT[PAIR_EQ] THEN EQ_TAC THENL
    [STRIP_TAC THEN EXISTS_TAC
       (mk_pabs(v,mk_comb(mk_var(`f`,mk_type(`fun`,[sty;mk_type(`bool`,[])])),
                          gluaux G))) THEN
     CONJ_TAC THENL
     [PBETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN POP_NONEQ_TAC THEN
      REPEAT (POP_ASSUM(SUBST1_TAC o SYM)) THEN RT[PAIR]
     ;PBETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN ART[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ART[]
     ]
    ;REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[] THEN
     FIRST_ASSUM (MATCH_MP_TAC o CONV_RULE PBETA_CONV) THEN 
     PBETA_TAC THEN ART[]
    ]) in
  RR[PAIR_EQ;GSYM CONJ_ASSOC]
             (CONV_RULE (REDEPTH_CONV(CHANGED_CONV(PALPHA_CONV u)))
                        (PBETA_RULE thm1));;

let prove_xpcall_ref procthm G V =
  let spec = rand(rator(concl procthm)) in
  let impl = rand(concl procthm) in
  let op = fst(strip_comb spec) in
  let ty = type_of op in
  let th1 = 
    if op = mk_const(`seq`,ty) ? false then prove_pcall_pre spec G 
    else prove_xpcall spec G in
  let a = list_mk_pair0(frees spec) in
  let th2 = SYM(PBETA_CONV(mk_comb(mk_pabs(a,spec),a))) in
  let th3 = SYM(PBETA_CONV(mk_comb(mk_pabs(a,impl),a))) in
  let th4 = GEN_ALL(SUBS_OCCS[[1],th2;[1],th3] procthm) in
  let th5 = ISPECL[G;gluR G] (MATCH_MP xpcall_mono th4) in
  PBETA_RULE(ISPEC V(PORR[GSYM th1] th5));;


