% This file contains a number of conversions which are fairly general.
They are required by various rules.
They should be put in the system or a library. %

%-----------------------------------------------------------------------%
% EL_CONV : conv    	    	    					%
% The argument to this conversion should be in the form of		%
%   "EL k [x0; x1; ...; xk; ...; xn]" 					%
% It returns a theorem 	    	    					%
%  |- EL k [x0; x1; ...; xk; ...; xn] = xk				%
% iff 0 <= k <= n, otherwise failure occurs.				%
%-----------------------------------------------------------------------%
let EL_CONV =
    let bthm,ithm = CONJ_PAIR EL in
    let dec n = let nn = int_of_string(fst(dest_const n)) in
        mk_const(string_of_int(nn - 1), ":num") in
    let tail lst = hd(tl(snd(strip_comb lst))) in
    let check = assert (\x. fst(dest_const x) = `EL`) in
    let iter ct N bits =
      letref n',m',lst' = ct-1, (dec N), (tail bits) in
      letref sthm = PURE_ONCE_REWRITE_RULE[TL](ISPECL [bits; m'] ithm) in
      if (n' = 0) then
        (TRANS sthm (SUBS[ISPECL(snd(strip_comb lst'))HD](ISPEC lst' bthm)))
      loop
        (n' :=  n' -1;
         sthm := TRANS (RIGHT_CONV_RULE(RATOR_CONV(RAND_CONV num_CONV)) sthm)
           (SUBS[ISPECL(snd(strip_comb lst'))TL](ISPECL[lst';(dec m')] ithm));
         lst' := tail lst';
         m' := dec m')    in
  \tm.
     let _,[N;bits] = (check # I) (strip_comb tm) in
     let n = int_of_string(fst (dest_const N)) in
     let lst = bits and m = N in
     if (n = 0) then
       (PURE_ONCE_REWRITE_RULE[HD](ISPEC bits bthm))
     else if (n < length(fst(dest_list bits))) then
       (SUBS [SYM (num_CONV N)](iter n N bits))
     else failwith `EL_CONV: index too large` ;;

%-----------------------------------------------------------------------%
% APPEND_CONV : conv 	    	    					%
% It takes a term of the form "APPEND [a0; ...; an] [b0; ...; bn]"	%
% and returns the following theorem:					%
% |- APPEND [a0; ...; an] [b0; ...; bn] = [a0; ...; an;b0; ...; bn]	%
%-----------------------------------------------------------------------%
let APPEND_CONV =  
    let th1,th2 = CONJ_PAIR (definition `list` `APPEND`) in
    let th3 = SPECL ["l1:(*)list";"l2:(*)list"] th2 in
    let th4 = GENL  ["l2:(*)list";"l1:(*)list"] th3 in
    let check tm = assert (\t. fst(dest_const t) = `APPEND`) tm in
    let itfn (cns,ath) v th =
        let th1 = AP_TERM (mk_comb(cns,v)) th in
        let l = rand(rator(rand(rator(concl th)))) in
            TRANS (SPEC v (SPEC l ath)) th1 in
    \tm. (let _,[l1;l2] = (check # I) (strip_comb tm) in
          let els,ty = dest_list l1 in
          if (null els) then ISPEC l2 th1 else
          let cns = rator(rator l1) in
          let step = ISPEC l2 th4 and base = ISPEC l2 th1 in
              itlist (itfn (cns,step)) els base) ?
         failwith `APPEND_CONV`;;

% --------------------------------------------------------------------- %
% MAP_CONV.		This already in the system version 2.1		%
% --------------------------------------------------------------------- %

let MAP_CONV =
    let mn,mc = CONJ_PAIR(definition `list` `MAP`) in
    let check = assert (\c. fst(dest_const c) = `MAP`) in
    \conv tm.
     (let _,[fn;l] = (check # I) (strip_comb tm) in
      let els,ty = dest_list l in
      let nth = ISPEC fn mn and cth = ISPEC fn mc in
      let cns = rator(rator(rand(snd(strip_forall(concl cth))))) in
      let APcons t1 t2 = MK_COMB(AP_TERM cns t2,t1) in
      let itfn e th =
          let t = rand(rand(rator(concl th))) in
          let th1 = SPEC t(SPEC e cth) in
              th1 TRANS (APcons th (conv (mk_comb(fn,e)))) in
      itlist itfn els nth) ? failwith `MAP_CONV`;;

%-----------------------------------------------------------------------%
% SPLIT_CONV : conv 	    	    					%
% It tahes a term of the form "SPLIT k [a0; ...; ak; ...; an]"		%
% and returns the following theorem:					%
% |- SPLIT k [a0; ...; ak; ...; an] = [a0;...;a(k-1);],[ak;...;an]	%
%-----------------------------------------------------------------------%
let SPLIT_CONV =  
    let th1,th2 = CONJ_PAIR (definition `ltree` `SPLIT`) in
    let th2' = GEN_ALL (PURE_REWRITE_RULE[HD;TL]
    	    (SPECL["n:num"; "(CONS (h:*) l)"] th2)) in
    let check = assert (\tm. fst(dest_const tm) = `SPLIT`) in
    let iter n cns (l1,l2) th = 
    	letref  count,n,bs,lst,thm = n, ("0"), l1, l2, th in
    	if (count = 0) then thm 
    	loop (count := count - 1 ;
    	      thm := PURE_ONCE_REWRITE_RULE[FST;SND]
    	    	 (SUBS[thm](ISPECL[n;(hd bs);lst] th2')) ;
    	      n := mk_comb("SUC", n) ;
    	      lst := mk_comb(mk_comb(cns,(hd bs)), lst) ;
    	      bs := tl bs ) in
    \tm. (let _,[n;l] = (check # I) (strip_comb tm) in
          let els,ty = dest_list l in
    	  if (n = "0") then (ISPEC l th1) else
          let cns = rator(rator l) in
    	  let nn = int_of_string (fst (dest_const n)) in
    	  let l1,l2 = (I # (\t.mk_list(t,ty))) (chop_list nn els) in
    	  let base = ISPEC l2 th1 in
    	  let th = (iter nn cns ((rev l1),l2) base) in
    	  (SUBS[SYM((REDEPTH_CONV num_CONV) n)] th)) ?
    	  failwith `SPLIT_CONV`;;

%-----------------------------------------------------------------------%
% There is a different version with the same name in reduce library.	%
% PRE_CONV : conv   	    	    					%
% It takes a term of the following form: "PRE n" where n is a number and%
% returns a theorem |- PRE n = m where m = n -1.			%
%-----------------------------------------------------------------------%
let PRE_CONV =
    let p0thm,psthm = CONJ_PAIR PRE in
  \tm.
    (let PRE,N = dest_comb tm in
     if (not(PRE = "PRE")) then failwith `PRE_CONV: not PRE term`
     else if (N = "0") then (p0thm)
     else
     (let thm0 = num_CONV N in
      let N' = snd(dest_comb(rhs(concl thm0))) in
      let thm1 = AP_TERM "PRE" thm0 in
      TRANS thm1 (SPEC N' psthm)));;
     
%--------***------%
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
%------*****-------%

%-----------------------------------------------------------------------%
% NBUTLAST_CONV : conv	    	    					%
% It takes a term of the form "NBUTLAST k [x0; x1; ...; x(n-k);...;xn]" %
% and returns the following theorem:					%
% |- NBUTLASST k  [x0; x1; ...; x(n-k);...;xn] = [x0; ...; x(n-k-1)]	%
%-----------------------------------------------------------------------%
let NBUTLAST_CONV =
    let bthm = CONJUNCT1 (definition `last_subseq` `NBUTLAST`) in
    let lthm = let th =  (SPEC "l:* list" 
          (theorem `last_subseq` `NBUTLAST_LENGTH_NULL`)) in
          let l = snd(dest_comb (concl th)) in
        GEN_ALL(EQ_MP (SPEC l(theorem `general_lists` `NULL_EQ_EMPTY`))th) in
    let athm = GEN_ALL (TRANS (SPECL ["l2:* list"; "l1:* list"]
    	(theorem `last_subseq` `NBUTLAST_LENGTH_APPEND`))
        (SPEC "l1:* list" (CONJUNCT1 (theorem `append` `APPEND_NIL`)))) in
    let check = assert (\x. fst(dest_const x) = `NBUTLAST`) in
    let len_conv ty lst =
        LENGTH_CONV(mk_comb("LENGTH:(^ty)list -> num",lst)) in
  \tm.
    (let _,[N;lst] = (check # I) (strip_comb tm) in
     if (N = "0") then (ISPEC lst bthm)
     else 
      (let n = int_of_string(fst (dest_const N)) in
       let bits,lty = (dest_list lst) in
       let len = (length bits) in
       if (n = len) then
         let thm1 = len_conv lty lst in (SUBS[thm1](ISPEC lst lthm))
       else
        (let l1,l2 = (chop_list (len - n) bits) in
         let l1' = mk_list(l1, lty) and l2' = mk_list(l2, lty) in
         let APP = "APPEND:(^lty)list -> (^lty)list -> (^lty)list" in
         let thm2 = len_conv lty l2' in
         let thm3 = APPEND_CONV (mk_comb(mk_comb(APP, l1'),l2')) in
         (SUBS[thm2;thm3](ISPECL [l2';l1'] athm)) )))
    ? failwith `NBUTLAST_CONV`;;

%-----------------------------------------------------------------------%
% LASTN_CONV : conv 	    	    					%
% It takes a term of the form "LASTN k [x0; ...; x(n-k); ...; xn]"	%
% and returns the following theorem:					%
% |- LASTN k [x0; ...; x(n-k); ...; xn] = [x(n-k); ...; xn]		%
%-----------------------------------------------------------------------%
%This theorem should be in the library. Remember to change the following line%
let LASTN_LENGTH_APPEND = % prove_thm(`LASTN_LENGTH_APPEND`, %
    PROVE(
    "!l1 (l2:* list). LASTN (LENGTH l2) (APPEND l1 l2) = l2",
    let lem = let llsts = ["LENGTH (l2:* list)";"LENGTH (l1:* list)"] in
        (SUBS[SYM (SPECL["(l1:* list)";"(l2:* list)"] LENGTH_APPEND)]
        (PURE_ONCE_REWRITE_RULE[ADD_SYM](SPECL llsts  LESS_EQ_ADD))) in
    LIST_INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[APPEND] THENL[
      ACCEPT_TAC LASTN_LENGTH_ID;
      REPEAT GEN_TAC THEN ASSUME_TAC lem
      THEN IMP_RES_TAC LASTN_CONS THEN ASM_REWRITE_TAC[]]);;

let LASTN_CONV =
    let bthm = CONJUNCT1 (definition `last_subseq` `LASTN`) in
    let ithm = (theorem `last_subseq` `LASTN_LENGTH_ID`) in
    let check = assert (\x. fst(dest_const x) = `LASTN`) in
    let len_conv ty lst =
        LENGTH_CONV(mk_comb("LENGTH:(^ty)list -> num",lst)) in
  \tm.
    (let _,[N;lst] = (check # I) (strip_comb tm) in
     if (N = "0") then (ISPEC lst bthm)
     else 
      (let n = int_of_string(fst (dest_const N)) in
       let bits,lty = (dest_list lst) in
       let len = (length bits) in
       if (n = len) then 
         let thm1 = len_conv lty lst in (SUBS[thm1](ISPEC lst ithm))
       else
        (let l1,l2 = (chop_list (len - n) bits) in
         let l1' = mk_list(l1, lty) and l2' = mk_list(l2, lty) in
         let APP = "APPEND:(^lty)list -> (^lty)list -> (^lty)list" in
         let thm2 = len_conv lty l2' in
         let thm3 = APPEND_CONV (mk_comb(mk_comb(APP, l1'),l2')) in
         (SUBS[thm2;thm3](ISPECL [l1';l2'] LASTN_LENGTH_APPEND)) )))
    ? failwith `LASTN_CONV`;;


let SNOC_CONV =
    let bthm,sthm = CONJ_PAIR SNOC_DEF in
    let check = assert (\t. fst(dest_const t) = `SNOC`) in
  \tm. 
    (let _,[d;lst] = (check # I)(strip_comb tm) in
     let ty = type_of lst in
     let lst',ety = (dest_list lst) in
     let EMP = "[]:^ty"  and CONS = "CONS:^ety -> ^ty ->^ty" in
     let itfn x (lst,ithm) =
       mk_comb(mk_comb(CONS,x),lst), (SUBS[ithm](ISPECL[d;x;lst]sthm)) in
     snd(itlist itfn lst' (EMP,(ISPEC d bthm))))
    ?\s failwith(`SNOC_CONV: `^s);;

let LAST_CONV = 
    let check tm = assert (\t. fst(dest_const t) = `LAST`) tm in
  \tm. 
    (let _,lst = (check # I)(dest_comb tm) in
     let ty = type_of lst in
     let lst',ety = (dest_list lst) in
     let x = (last lst') and l = mk_list(butlast lst',ety) in
     let sthm = ISPECL [l;x] (theorem `append` `LAST1`) in
     CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) APPEND_CONV) sthm)
    ?\s failwith(`LAST_CONV: `^s);;

let BUTLAST_CONV = 
    let check tm = assert (\t. fst(dest_const t) = `BUTLAST`) tm in
  \tm. 
    (let _,lst = (check # I)(dest_comb tm) in
     let ty = type_of lst in
     let lst',ety = (dest_list lst) in
     let x = (last lst') and l = mk_list(butlast lst',ety) in
     let sthm = ISPECL [l;x] (theorem `append` `BUTLAST1`) in
     CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) APPEND_CONV) sthm)
    ?\s failwith(`BUTLAST_CONV: `^s);;
