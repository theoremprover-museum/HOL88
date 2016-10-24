%******************************************************************************
** LIBRARY:     reduce (part II)                                             **
**                                                                           **
** DESCRIPTION: Conversions to reduce arithmetic constant expressions        **
**                                                                           **
** AUTHOR:      John Harrison                                                **
**              University of Cambridge Computer Laboratory                  **
**              New Museums Site                                             **
**              Pembroke Street                                              **
**              Cambridge CB2 3QG                                            **
**              England.                                                     **
**                                                                           **
**              jrh@cl.cam.ac.uk                                             **
**                                                                           **
** DATE:        18th May 1991                                                **
******************************************************************************%

%-----------------------------------------------------------------------%
% dest_op - Split application down spine, checking head operator        %
%-----------------------------------------------------------------------%

let dest_op op tm = snd ((assert (curry $= op) # I) (strip_comb tm));;

%-----------------------------------------------------------------------%
% term_of_int - Convert ML integer to object level numeric constant     %
%-----------------------------------------------------------------------%

let term_of_int =
  let ty = ":num" in
  \n. mk_const(string_of_int n, ty);;

%-----------------------------------------------------------------------%
% int_of_term - Convert object level numeric constant to ML integer     %
%-----------------------------------------------------------------------%

let int_of_term =
  int_of_string o fst o dest_const;;

%-----------------------------------------------------------------------%
% provelt x y = |- [x] < [y], if true, else undefined.                  %
%-----------------------------------------------------------------------%

let provelt =
  let ltstep = PROVE("!x. (z = SUC y) ==> (x < y) ==> (x < z)",
                     GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
                     MATCH_ACCEPT_TAC (theorem `prim_rec` `LESS_SUC`))
  and ltbase  = PROVE("(y = SUC x) ==> (x < y)",
                     DISCH_THEN SUBST1_TAC THEN
                     MATCH_ACCEPT_TAC (theorem `prim_rec` `LESS_SUC_REFL`))
  and bistep = PROVE("(SUC x < SUC y) = (x < y)",
                     MATCH_ACCEPT_TAC (theorem `arithmetic` `LESS_MONO_EQ`))
  and bibase = PROVE("!x. 0 < (SUC x)",
                     MATCH_ACCEPT_TAC (theorem `prim_rec` `LESS_0`))
  and ltop = "$<" and eqop = "$=:bool->bool->bool" and rhs = "x < y"
  and xv = "x:num" and yv = "y:num" and zv = "z:num" and Lo = "$< 0" in
  \x y. let xn = term_of_int x and yn = term_of_int y in
        if 4*(y - x) < 5*x then
          let x' = x + 1 in let xn' = term_of_int x' in
          let step = SPEC xn ltstep in
          letref z,zn,zn',th = x',xn',xn', MP (INST [(xn,xv);(xn',yv)] ltbase)
                                                  (num_CONV xn') in
          while z < y do
            (zn':=term_of_int(z:=z+1);
             th := MP (MP (INST [(zn,yv); (zn',zv)] step) (num_CONV zn')) th;
             zn:=zn');
          th
        else
         let lhs = mk_comb(mk_comb(ltop,xn),yn) in
         let pat = mk_comb(mk_comb(eqop,lhs),rhs) in
         letref w, z, wn, zn, th = x, y, xn, yn, REFL lhs in
         while w > 0 do
          (th :=
           let tran = TRANS (SUBST [(num_CONV wn,xv); (num_CONV zn,yv)] pat th)
           in tran (INST[((wn:=term_of_int(w:=w-1)),xv);
                         ((zn:=term_of_int(z:=z-1)),yv)] bistep));
         EQ_MP (SYM (TRANS th (AP_TERM Lo (num_CONV zn))))
               (SPEC (term_of_int(z-1)) bibase);;

%-----------------------------------------------------------------------%
% NEQ_CONV "[x] = [y]" = |- ([x] = [y]) = [x=y -> T | F]                %
%-----------------------------------------------------------------------%

let NEQ_CONV =
  let eq1 = PROVE
    ("(x < y) ==> ((x = y) = F)",
     ONCE_REWRITE_TAC[] THEN
     MATCH_ACCEPT_TAC (theorem `prim_rec` `LESS_NOT_EQ`))
  and eq2 = PROVE
    ("(y < x) ==> ((x = y) = F)",
     ONCE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
     MATCH_ACCEPT_TAC (theorem `prim_rec` `LESS_NOT_EQ`))
  and neqop = "=:num->num->bool" and xv = "x:num" and yv = "y:num" in
  \tm. (let [xn;yn] = dest_op neqop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x = y then EQT_INTRO (REFL xn) else
        if x < y then MP (INST [(xn,xv);(yn,yv)] eq1)
                         (provelt x y)
        else MP (INST [(xn,xv);(yn,yv)] eq2)
                (provelt y x))
       ? failwith `NEQ_CONV`;;

%-----------------------------------------------------------------------%
% LT_CONV "[x] < [y]" = |- ([x] < [y]) = [x<y -> T | F]                 %
%-----------------------------------------------------------------------%

let LT_CONV =
  let lt1 = PROVE("!x. (x < x) = F",
                  REWRITE_TAC[theorem `prim_rec` `LESS_REFL`])
  and lt2 = PROVE("(y < x) ==> ((x < y) = F)",
                  PURE_ONCE_REWRITE_TAC[EQ_CLAUSES] THEN REPEAT DISCH_TAC THEN
                  IMP_RES_TAC (theorem `arithmetic` `LESS_ANTISYM`))
  and ltop = "$<" and xv = "x:num" and yv = "y:num" in
  \tm. (let [xn;yn] = dest_op ltop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x < y then EQT_INTRO (provelt x y) else
        if x = y then SPEC xn lt1
        else MP (INST [(xn,xv);(yn,yv)] lt2)
                (provelt y x))
       ? failwith `LT_CONV`;;

%-----------------------------------------------------------------------%
% GT_CONV "[x] > [y]" = |- ([x] > [y]) = [x>y -> T | F]                 %
%-----------------------------------------------------------------------%

let GT_CONV =
  let gt1 = PROVE("!x. (x > x) = F",
                  REWRITE_TAC[theorem `prim_rec` `LESS_REFL`;
                              definition `arithmetic` `GREATER`])
  and gt2 = PROVE("(x < y) ==> ((x > y) = F)",
                  PURE_REWRITE_TAC
                   [EQ_CLAUSES; definition `arithmetic` `GREATER`]
                  THEN REPEAT DISCH_TAC THEN
                  IMP_RES_TAC (theorem `arithmetic` `LESS_ANTISYM`))
  and gt3 = PROVE("(y < x) ==> ((x > y) = T)",
                  DISCH_THEN (SUBST1_TAC o SYM o EQT_INTRO) THEN
                  MATCH_ACCEPT_TAC (definition `arithmetic` `GREATER`))
  and gtop = "$>" and xv = "x:num" and yv = "y:num" in
  \tm. (let [xn;yn] = dest_op gtop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x = y then SPEC xn gt1 else
        if x < y then MP (INST [(xn,xv);(yn,yv)] gt2)
                         (provelt x y)
        else MP (INST [(xn,xv); (yn,yv)] gt3)
                (provelt y x))
       ? failwith `GT_CONV`;;

%-----------------------------------------------------------------------%
% LE_CONV "[x] <= [y]" = |- ([x]<=> [y]) = [x<=y -> T | F]              %
%-----------------------------------------------------------------------%

let LE_CONV =
  let le1 = PROVE("!x. (x <= x) = T",
                  REWRITE_TAC[theorem `arithmetic` `LESS_EQ_REFL`])
  and le2 = PROVE("(x < y) ==> ((x <= y) = T)",
                  DISCH_THEN (ACCEPT_TAC o EQT_INTRO o MATCH_MP
                   (theorem `arithmetic` `LESS_IMP_LESS_OR_EQ`)))
  and le3 = PROVE("(y < x) ==> ((x <= y) = F)",
                  PURE_ONCE_REWRITE_TAC[EQ_CLAUSES] THEN
                  REPEAT DISCH_TAC THEN
                  IMP_RES_TAC (theorem `arithmetic` `LESS_EQ_ANTISYM`))
  and leop = "$<=" and xv = "x:num" and yv = "y:num" in
  \tm. (let [xn;yn] = dest_op leop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x = y then SPEC xn le1 else
        if x < y then MP (INST [(xn,xv);(yn,yv)] le2)
                         (provelt x y)
        else MP (INST [(xn,xv);(yn,yv)] le3)
                (provelt y x))
       ? failwith `LE_CONV`;;

%-----------------------------------------------------------------------%
% GE_CONV "[x] >= [y]" = |- ([x] >= [y]) = [x>=y -> T | F]              %
%-----------------------------------------------------------------------%

let GE_CONV =
  let ge1 = PROVE("!x. (x >= x) = T",
                  REWRITE_TAC[definition `arithmetic` `GREATER_OR_EQ`])
  and ge2 = PROVE("(y < x) ==> ((x >= y) = T)",
                  DISCH_TAC THEN
                  ASM_REWRITE_TAC[definition `arithmetic` `GREATER_OR_EQ`;
                                  definition `arithmetic` `GREATER`])
  and ge3 = PROVE("(x < y) ==> ((x >= y) = F)",
                  PURE_REWRITE_TAC (EQ_CLAUSES. (map (definition `arithmetic`)
                   [`GREATER_OR_EQ`; `GREATER`])) THEN
                  PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
                  REPEAT STRIP_TAC THEN IMP_RES_TAC (PURE_REWRITE_RULE
                   [definition `arithmetic` `LESS_OR_EQ`]
                   (theorem `arithmetic` `LESS_EQ_ANTISYM`)))
  and geop = "$>=" and xv = "x:num" and yv = "y:num" in
  \tm. (let [xn;yn] = dest_op geop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x = y then SPEC xn ge1 else
        if x < y then MP (INST [(xn,xv);(yn,yv)] ge3)
                         (provelt x y)
        else MP (INST [(xn,xv);(yn,yv)] ge2)
                (provelt y x))
       ? failwith `GE_CONV`;;

%-----------------------------------------------------------------------%
% SUC_CONV "SUC [x]" = |- SUC [x] = [x+1]                               %
%-----------------------------------------------------------------------%

let SUC_CONV =
  let sucop = "SUC" in
  \tm. (let [xn] = dest_op sucop tm in
        SYM (num_CONV (term_of_int (1 + (int_of_term xn)))))
       ? failwith `SUC_CONV`;;

%-----------------------------------------------------------------------%
% PRE_CONV "PRE [n]" = |- PRE [n] = [n-1]                               %
%-----------------------------------------------------------------------%

let PRE_CONV =
  let preop = "PRE" and zero = "0" and xv = "x:num" and yv = "y:num"
  and spree = PROVE("(x = SUC y) ==> (PRE x = y)",
               DISCH_TAC THEN ASM_REWRITE_TAC[theorem `prim_rec` `PRE`])
  and szero = PROVE("PRE 0 = 0",REWRITE_TAC[theorem `prim_rec` `PRE`]) in
  \tm. (let [xn] = dest_op preop tm in
        if xn = zero then szero
        else MP (INST[(xn,xv);(term_of_int((int_of_term xn) - 1),yv)] spree)
                (num_CONV xn))
       ? failwith `PRE_CONV`;;

%-----------------------------------------------------------------------%
% SBC_CONV "[x] - [y]" = |- ([x] - [y]) = [x - y]                       %
%-----------------------------------------------------------------------%

let SBC_CONV =
  let subm = PROVE("(x < y) ==> (x - y = 0)",
                   PURE_ONCE_REWRITE_TAC[theorem `arithmetic` `SUB_EQ_0`]
                   THEN MATCH_ACCEPT_TAC
                   (theorem `arithmetic` `LESS_IMP_LESS_OR_EQ`))
  and step = PROVE("(SUC x) - (SUC y) = x - y",
                   MATCH_ACCEPT_TAC (theorem `arithmetic` `SUB_MONO_EQ`))
  and base1 = PROVE("!x. x - 0 = x",
                    REWRITE_TAC[theorem `arithmetic` `SUB_0`])
  and base2 = PROVE("!x. x - x = 0",
                    MATCH_ACCEPT_TAC(theorem `arithmetic` `SUB_EQUAL_0`))
  and less0 = PROVE("!x. 0 < SUC x",
                    REWRITE_TAC[theorem `prim_rec` `LESS_0`])
  and swap = PROVE("(x - z = y) ==> (0 < y) ==> (x - y = z)",
    let [sub_less_0; sub_sub; less_imp_less_or_eq; add_sym; add_sub] =
      map (theorem `arithmetic`)
      [`SUB_LESS_0`; `SUB_SUB`; `LESS_IMP_LESS_OR_EQ`; `ADD_SYM`; `ADD_SUB`] in
    DISCH_THEN (SUBST1_TAC o SYM) THEN PURE_ONCE_REWRITE_TAC
     [SYM (SPEC_ALL sub_less_0)] THEN DISCH_THEN (SUBST1_TAC o SPEC "x:num" o
    MATCH_MP sub_sub o MATCH_MP less_imp_less_or_eq) THEN PURE_ONCE_REWRITE_TAC
     [add_sym] THEN PURE_ONCE_REWRITE_TAC[add_sub] THEN REFL_TAC)
  and lop = "$< 0" and minusop = "$-" and eqop = "$=:num->num->bool"
  and rhs = "x - y" and xv = "x:num" and yv = "y:num" and zv = "z:num" in
  let sprove x y =
    let xn = term_of_int x and yn = term_of_int y in
    let lhs = mk_comb(mk_comb(minusop,xn),yn) in
    let pat = mk_comb(mk_comb(eqop,lhs),rhs) in
    letref w, z, wn, zn, th = x, y, xn, yn, REFL lhs in
    while (z > 0) do
     (th :=
       let tran = TRANS (SUBST [(num_CONV wn,xv); (num_CONV zn,yv)] pat th) in
       tran (INST [((wn := term_of_int(w:=w-1)),xv);
                   ((zn := term_of_int(z:=z-1)),yv)] step));
    TRANS th (SPEC wn base1) in
  \tm. (let [xn;yn] = dest_op minusop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x < y then MP (INST[(xn,xv);(yn,yv)] subm)
                         (provelt x y) else
        if y = 0 then SPEC xn base1 else
        if x = y then SPEC xn base2 else
        if y < (x - y) then sprove x y
        else
          let z = x - y in let zn = term_of_int z in
          MP (MP
               (INST[(xn,xv);(yn,yv);(zn,zv)] swap)
               (sprove x z))
             (EQ_MP (AP_TERM lop (SYM (num_CONV yn)))
                    (SPEC (term_of_int (y-1)) less0)))
       ? failwith `SBC_CONV`;;

%-----------------------------------------------------------------------%
% ADD_CONV "[x] + [y]" = |- [x] + [y] = [x+y]                           %
%-----------------------------------------------------------------------%

let ADD_CONV =
  let subadd = PROVE
    ("(z - y = x) ==> 0 < x ==> (x + y = z)",
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL (theorem `arithmetic` `SUB_LESS_0`))]
     THEN DISCH_THEN (SUBST1_TAC o MATCH_MP (theorem `arithmetic` `SUB_ADD`) o
     MATCH_MP (theorem `arithmetic` `LESS_IMP_LESS_OR_EQ`)) THEN REFL_TAC)
  and [raz; laz] = CONJUNCTS(PROVE("(!x. x + 0 = x) /\ (!y. 0 + y = y)",
    REWRITE_TAC[definition `arithmetic` `ADD`; theorem `arithmetic` `ADD_0`]))
  and lo = PROVE("!n. 0 < SUC n",MATCH_ACCEPT_TAC(theorem `prim_rec` `LESS_0`))
  and plusop = "$+" and minusop = "$-" and lop = "$< 0"
  and xv = "x:num" and yv = "y:num" and zv = "z:num" in
  \tm. (let [xn;yn] = dest_op plusop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x = 0 then SPEC yn laz else
        if y = 0 then SPEC xn raz else
        let zn = term_of_int(x + y) in
        let p1 = SBC_CONV (mk_comb(mk_comb(minusop,zn),yn))
        and p2 = EQ_MP (AP_TERM lop (SYM (num_CONV xn)))
                       (SPEC (term_of_int (int_of_term xn - 1)) lo)
        and chain = INST[(xn,xv); (yn,yv); (zn,zv)] subadd in
        MP (MP chain p1) p2)
       ? failwith `ADD_CONV`;;

%-----------------------------------------------------------------------%
% MUL_CONV "[x] * [y]" = |- [x] * [y] = [x*y]                           %
%-----------------------------------------------------------------------%

let MUL_CONV =
  let [mbase; mstep; mzero] = CONJUNCTS (PROVE
   ("(!y. 0 * y = 0) /\ (!y x. (SUC x) * y = (x * y) + y) /\ (!n. n * 0 = 0)",
    REWRITE_TAC[definition `arithmetic` `MULT`;
                theorem `arithmetic` `MULT_0`]))
  and msym = PROVE("!m n. m * n = n * m",
    MATCH_ACCEPT_TAC (theorem `arithmetic` `MULT_SYM`))
  and multop = "$*" and xv = "x:num" and pv = "p:num" and zero = "0"
  and plusop = "$+" and eqop = "=:num->num->bool" in
  let mulpr x y =
    let xn = term_of_int x and yn = term_of_int y in
    let step = SPEC yn mstep in
      let pat = mk_comb(mk_comb(eqop,(mk_comb(mk_comb(multop,xv),yn))),
                        mk_comb(mk_comb(plusop,pv),yn)) in
      letref w, wn, p, th = 0, zero, 0, SPEC yn mbase in
      while w < x do
        (th := TRANS
                 (let st = SPEC wn step in
                  SUBST [(SYM (num_CONV(wn:=term_of_int(w:=w+1))),xv);
                         (th,pv)] pat st)
                 (ADD_CONV (mk_comb(mk_comb(plusop,(term_of_int p)),yn)));
         p := p + y);
      th in
  \tm. (let [xn;yn] = dest_op multop tm in
        let x = int_of_term xn and y = int_of_term yn in
        if x = 0 then SPEC yn mbase else
        if y = 0 then SPEC xn mzero else
        if x < y then mulpr x y
        else TRANS (SPECL [xn;yn] msym) (mulpr y x))
       ? failwith `MUL_CONV`;;

%-----------------------------------------------------------------------%
% EXP_CONV "[x] EXP [y]" = |- [x] EXP [y] = [x**y]                      %
%-----------------------------------------------------------------------%

let EXP_CONV =
  let [ebase; estep] = CONJUNCTS (PROVE
    ("(!m. m EXP 0 = 1) /\ (!m n. m EXP (SUC n) = m * (m EXP n))",
     REWRITE_TAC[definition `arithmetic` `EXP`]))
  and expop = "EXP" and multop = "$*" and zero = "0" and ev = "e:num"
  and eqop = "$=:num->num->bool" and yv = "y:num" in
  \tm. (let [xn;yn] = dest_op expop tm in
        let x = int_of_term xn and y = int_of_term yn
        and step = SPEC xn estep in
        let pat = mk_comb(mk_comb(eqop,mk_comb(mk_comb(expop,xn),yv)),
                          mk_comb(mk_comb(multop,xn),ev)) in
        letref z, zn, e, th = 0, zero, 1, SPEC xn ebase in
        while z < y do
         (th := TRANS
                  (let st = SPEC zn step in
                   SUBST [(SYM (num_CONV(zn:=term_of_int(z:=z+1))),yv);
                          (th,ev)] pat st)
                  (MUL_CONV (mk_comb(mk_comb(multop,xn),term_of_int e)));
          e := x * e);
        th)
       ? failwith `EXP_CONV`;;

%-----------------------------------------------------------------------%
% DIV_CONV "[x] DIV [y]" = |- [x] DIV [y] = [x div y]                   %
%-----------------------------------------------------------------------%

let DIV_CONV =
 let divt = PROVE("(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x DIV y = q)",
   REPEAT DISCH_TAC THEN MATCH_MP_TAC (theorem `arithmetic` `DIV_UNIQUE`) THEN
   EXISTS_TAC "r:num" THEN ASM_REWRITE_TAC[])
 and divop = "$DIV" and multop = "$*" and plusop = "$+"
 and xv,yv,pv,qv,rv = "x:num","y:num","p:num","q:num","r:num" in
  \tm. (let [xn;yn] = dest_op divop tm in
        let x = int_of_term xn and y = int_of_term yn in
        let q = x / y in
        let p = q * y in
        let r = x - p in
        let pn = term_of_int p and qn = term_of_int q and rn = term_of_int r in
        let p1 = MUL_CONV (mk_comb(mk_comb(multop,qn),yn))
        and p2 = ADD_CONV (mk_comb(mk_comb(plusop,pn),rn))
        and p3 = provelt r y
        and chain = INST[(xn,xv); (yn,yv); (pn,pv); (qn,qv); (rn,rv)] divt
        in MP (MP (MP chain p1) p2) p3)
       ? failwith `DIV_CONV`;;

%-----------------------------------------------------------------------%
% MOD_CONV "[x] MOD [y]" = |- [x] MOD [y] = [x mod y]                   %
%-----------------------------------------------------------------------%

let MOD_CONV =
 let modt = PROVE("(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x MOD y = r)",
   REPEAT DISCH_TAC THEN MATCH_MP_TAC (theorem `arithmetic` `MOD_UNIQUE`) THEN
   EXISTS_TAC "q:num" THEN ASM_REWRITE_TAC[])
 and modop = "$MOD" and multop = "$*" and plusop = "$+"
 and xv,yv,pv,qv,rv = "x:num","y:num","p:num","q:num","r:num" in
  \tm. (let [xn;yn] = dest_op modop tm in
        let x = int_of_term xn and y = int_of_term yn in
        let q = x / y in
        let p = q * y in
        let r = x - p in
        let pn = term_of_int p and qn = term_of_int q and rn = term_of_int r in
        let p1 = MUL_CONV (mk_comb(mk_comb(multop,qn),yn))
        and p2 = ADD_CONV (mk_comb(mk_comb(plusop,pn),rn))
        and p3 = provelt r y
        and chain = INST[(xn,xv); (yn,yv); (pn,pv); (qn,qv); (rn,rv)] modt
        in MP (MP (MP chain p1) p2) p3)
       ? failwith `MOD_CONV`;;
