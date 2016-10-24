% ===================================================================== %
% FILE		: wordn_num.ml						%
% DESCRIPTION   : Functions for defining  conversions between		%
%      	    	  n-bit words and unsigned natural numbers.             %
% REQUIRED      : library reduce					%
%									%
% AUTHOR	: (c) Wai Wong						%
% DATE		: 2 April 1992					        %
% ===================================================================== %

%-----------------------------------------------------------------------%
% define_word_val : (thm -> (string # string) -> (string # string)	%
%    -> thm list)   	    	 					%
% The arguments:    	    	    					%
%   thm --- the type definition returned by define_wordn_type		%
%   (string # string) --- the name of the constant and the name under	%
%   	    which the definition is stored.				%
%   	    The first pair is for the conversion from :wordn to :num	%
%   	    The second pair is for the conversion from :num to :wordn 	%
%   	    	    	    	    					%
% eg.define_word_val word3 (`NVAL3`,`NVAL3_DEF`) (`NWORD3`,`NWORD3_DEF`)%
% defines the constants NVAL3 and NWORD3 and return the definitions:	%
%    NVAL3_DEF = |- !w. NVAL3 w = VAL(BITS3 w)				%
%    NWORD3_DEF = |- !n. NWORD3 n = WORD3(WORDN 3 n)			%
%   	    	    	    	    					%
% They are defined in terms of the generic conversion functions between %
% (bool)list and num: WORDN and VAL.					%
%-----------------------------------------------------------------------%

let define_word_val dthm (val_const,val_name) (word_const,word_name) =
    let WD,(BS,w) =  (I # dest_comb) (dest_comb (fst (dest_eq 
    	(snd (dest_forall (concl (CONJUNCT1 dthm))))))) in
    let _,[wdty;blst] = dest_type (snd (dest_const BS)) in
    let nstr = (implode(fst 
    	(partition is_digit (explode(fst(dest_type wdty)))))) in
    let N = mk_const(nstr, ":num") in
    let NV = mk_var(val_const, ":^wdty -> num") in
    let NW = mk_var(word_const, ":num -> ^wdty") in
    (map new_definition [
     ((val_name), "(^NV) (^w) = VAL((^BS) (^w))");
     ((word_name), "(^NW) n = (^WD)(WORDN (^N) n)")]);;

%
let define_word_val n = 
    let nstr = string_of_int n in
    let wdty = mk_type((`word`^nstr), []) in
    let nv = `NVAL` ^ nstr and nw = `NWORD` ^ nstr in
    let N = mk_const(nstr, ":num") in
    let NV = mk_var(nv, ":^wdty -> num") in
    let NW = mk_var(nw, ":num -> ^wdty") in
    let WN = mk_const((`WORD`^nstr), ":(bool)list -> ^wdty") in
    let NB = mk_const((`BITS`^nstr), ":^wdty -> (bool)list") in
    (map new_definition [
     ((nv), "(^NV) w = VAL((^NB) w)");
     ((nw), "(^NW) n = (^WN)(WORDN (^N) n)")]);;
%

%-----------------------------------------------------------------------%
% prove_word_val : thm -> thm -> thm -> thm	    		%
% prove_word_val  proves a basic theorem about the conversion function  %
% between wordn and natural number. The theorem is in the form below:	%
%   	    	    	    	    					%
% eg. prove_word_val word3 NVAL3_DEF NWORD3_DEF)	%
% returns the theorem below;	    					%
%|- (!w. NWORD3(NVAL3 w) = w) /\ (!m. NVAL3(NWORD3 m) = m MOD (2 EXP 3))%
%-----------------------------------------------------------------------%

let prove_word_val =
    let word_val = theorem `wordn_num` `WORDN_VAL` in
    let wdthm = definition `wordn_num` `WORDN` in
  \dthm vdef wdef.
    let lthm = prove_LENGTH_BITS_thm dthm in
    let d1,d2 = CONJ_PAIR dthm in
    let WD,(BS,w) =  (I # dest_comb) (dest_comb (fst (dest_eq 
    	(snd (dest_forall (concl d1)))))) in
    let _,[wdty;blst] = dest_type (snd (dest_const BS)) in
    let bs = mk_comb(BS, w) in
    let th1 = AP_TERM WD (SPEC bs word_val) in
    let vth.ths = map (SPEC w) [vdef;lthm; (CONJUNCT1 dthm)] in
    let th2 = SUBS ((SYM vth).ths) th1 in
    let wth = (SPEC (fst(dest_eq (concl vth))) wdef) in
    let thm1 = GEN_ALL (TRANS wth th2) in
    let nstr = (implode(fst 
    	(partition is_digit (explode(fst(dest_type wdty)))))) in
    let N = mk_const(nstr, ":num") in
    let WN = "WORDN ^N (m:num)" in
    let th10 = SYM(SPEC "m:num" wdef) in
    let th11 = AP_TERM WD (REFL WN) in
    let th12 = AP_TERM BS (SUBS_OCCS [[1],th10] th11) in
    let th13,th13' = CONJ_PAIR (SPECL [N; "m:num"] wdthm) in
    let th14 = AP_TERM "VAL" (TRANS th12 (EQ_MP (SPEC WN d2) th13)) in
    let thm2 = GEN_ALL(TRANS (TRANS (SPEC(rhs(concl th10))vdef) th14) th13') in
    (CONJ thm1 thm2) ? failwith `prove_word_val`;;

let EXP2_CONV =
    let exp0,exp1 = ((SPEC "2") # (\t.PURE_ONCE_REWRITE_RULE[TIMES2]
    	(SPEC "2" t))) (CONJ_PAIR EXP) in
    let itfn ct bthm =
    	letref n,th,count = 0, bthm , ct in
    	if (count = 0) then th
    	loop
    	    (count := count - 1;
    	  th := RIGHT_CONV_RULE ADD_CONV (SUBS[th]
    	        (SPEC (mk_const((string_of_int n),":num")) exp1));
    	  n := n + 1;
    	  th := SUBS[(SYM(num_CONV(mk_const((string_of_int n),":num"))))]th) in
  \tm. let ex,[two;N] = strip_comb tm in
    if (not (ex = "EXP")) or (not (two = "2")) then fail
    else
      let n = int_of_string(fst (dest_const N)) in
      (itfn n exp0) ? failwith `EXP2_CONV`;;

%-----------------------------------------------------------------------%
% prove_NWORD_MOD : thm -> thm	    					%
% prove_NWORD_MOD wvthm returns the following theorem:			%
%  |- NWORDn  m = NWORDn (m MOD e)  					%
% where e = 2 EXP n 	    	    					%
%-----------------------------------------------------------------------%
let prove_NWORD_MOD wvthm =
    let t1,t2 = CONJ_PAIR wvthm in
    let NW = fst(dest_comb(lhs(snd(dest_forall(concl t1))))) in
    GEN_ALL (RIGHT_CONV_RULE (ONCE_DEPTH_CONV EXP2_CONV) 
    	(PURE_ONCE_REWRITE_RULE[t1] (AP_TERM NW (SPEC_ALL t2)))) ?
    failwith `prove_NWORD_MOD` ;;

%-----------------------------------------------------------------------%
% VAL_CONV :  conv  	 						%
% VAL_CONV "VAL [T;...;F]"  returns the following theorem:		%
%  |- VAL [T;...;F] = m    	    					%
% where m is the value represented by the bool list which is interpreted%
% in bigendian format, eg. |- VAL {F;T;T] = 3				%
%-----------------------------------------------------------------------%

let VAL_CONV =
  let bth,ith = (I # (PURE_ONCE_REWRITE_RULE[(definition `wordn_num` `BV`)]))
    (CONJ_PAIR (definition `wordn_num` `VAL`)) in
  let mult0,multsuc = (I # (SPEC "0")) (CONJ_PAIR MULT) in
  let mult1 = PURE_REWRITE_RULE[mult0;ADD] multsuc in
  let Cons = "CONS:bool->(bool)list->(bool)list" in
  let itfn b (thm,bs) =
    let th1 = SPECL[b;bs] ith in
    let th2 = CONV_RULE (ONCE_DEPTH_CONV COND_CONV) th1 in
    let th = if (b = "F")
    	then (SUBS [thm] (PURE_ONCE_REWRITE_RULE[mult0] th2))
    	else
    	  (let th3 = PURE_ONCE_REWRITE_RULE[mult1] th2 in
    	   SUBS[thm] (RIGHT_CONV_RULE (EVERY_CONV
   	     [(ONCE_DEPTH_CONV LENGTH_CONV);(ONCE_DEPTH_CONV EXP2_CONV)])th3))
    	     in
    ((RIGHT_CONV_RULE ADD_CONV th), mk_comb(mk_comb(Cons,b),bs)) in
  \tm. (let val,bits = (I # (fst o dest_list)) (dest_comb tm) in
    	(fst(itlist itfn bits (bth,"[]:(bool)list")))) ?
    failwith `VAL_CONV`;;

%-----------------------------------------------------------------------%
% wordn_NVAL_CONV : thm -> thm -> conv 					%
% wordn_NVAL_CONV wordn NVALn_DEF "NVALn (WORDn[T;...;F])"		%
% returns the following	theorem:  |- NVALn (WORDn[T;...;F]) = m		%
% where wordn is the definition of the type :wordn			%
%   NVALn_DEF is the definition of th constant NVALn			%
%   m is the value of the word (WORDn[T;...;F]) which is interpreted	%
% in bigendian format, eg. |- NVAL3 word3 NVAL3_DEF (WORD3[F;T;T]) = 3	%
%-----------------------------------------------------------------------%

let wordn_NVAL_CONV =
    let check s = let nv = implode(fst(chop_list 4 (explode s))) in
    	not(nv = `NVAL`) in
  \dthm nthm tm.
    let nval,w = dest_comb tm in
    let WD,bs = dest_comb w in 
    let nv = fst (dest_const nval) in
    if (check nv) then fail else
     (let thm1 = EQ_MP (SPEC bs (CONJUNCT2 dthm))(LENGTH_CONV "LENGTH ^bs") in
      let thm2 = SUBS[thm1] (SPEC w nthm) in
      (RIGHT_CONV_RULE VAL_CONV thm2)) ? failwith `wordn_NVAL_CONV`;;

%-----------------------------------------------------------------------%
% wordn_NVAL_CONV : thm -> thm -> conv 					%
% wordn_NVAL_CONV wordn NVALn_DEF "NVALn #1...0"			%
% returns the following	theorem:  |- NVALn #1...0 = m			%
% where wordn is the definition of the type :wordn			%
%   NVALn_DEF is the definition of th constant NVALn			%
%   m is the value of the word (WORDn[T;...;F]) which is interpreted	%
% in bigendian format, eg. |- NVAL3 word3 NVAL3_DEF #011 = 3		%
%-----------------------------------------------------------------------%

let NVAL_CONV = 
  \tdef ndef.((ONCE_DEPTH_CONV wordn_CONV) THENC (wordn_NVAL_CONV tdef ndef));;

%
let EXP_LEN0 = TAC_PROOF(([],
    "2 EXP (LENGTH ([]:(bool)list)) = 1"),
    PURE_REWRITE_TAC[LENGTH;EXP] THEN REFL_TAC);;

let EXP_LEN = TAC_PROOF(([],
"!x l. 2 EXP (LENGTH (CONS x l)) = (2 EXP (LENGTH l)) + (2 EXP (LENGTH l))"),
    REPEAT GEN_TAC THEN PURE_REWRITE_TAC[LENGTH;EXP;TIMES2] THEN REFL_TAC);;

let wordn_NVAL_CONV =
  let bth,ith = (I # (PURE_ONCE_REWRITE_RULE[(definition `wordn_num` `BV`)]))
    (CONJ_PAIR (definition `wordn_num` `VAL`)) in
  let eth = EXP_LEN and eth0 = EXP_LEN0 in
  let mult0,multsuc = (I # (SPEC "0")) (CONJ_PAIR MULT) in
  let mult1 = PURE_REWRITE_RULE[mult0;ADD] multsuc in
  let Cons = "CONS:bool->(bool)list->(bool)list" in
  let itfn b (thm,thm2,bs) =
    let th1 = SPECL[b;bs] ith in
    let th2 = CONV_RULE (ONCE_DEPTH_CONV COND_CONV) th1 in
    let eth1 = RIGHT_CONV_RULE ADD_CONV (SUBS[thm2] (ISPECL [b;bs] eth)) in
    let th = if (b = "F")
    	then (SUBS [thm] (PURE_ONCE_REWRITE_RULE[mult0] th2))
    	else
    	    (let th3 = PURE_ONCE_REWRITE_RULE[mult1] th2 in
    	     (SUBS [thm;thm2] th3)) in
    ((RIGHT_CONV_RULE ADD_CONV th), eth1, mk_comb(mk_comb(Cons,b),bs)) in
  let mkbs w = 
    if is_const w 
    	then (let (hash.ds) = explode (fst (dest_const w)) in
    	    if (hash = `#`) then (map (\s. (s=`1`)=> "T"|"F") ds)
    	    else fail)
    	else (let W,bs = (I # (fst o dest_list))(dest_comb w) in bs) in
  \dthm nthm tm. (let nval,w = dest_comb tm in
    let bwthm = prove_BITS_WORD dthm in
    let bits = mkbs w in
    let thm1 = RIGHT_CONV_RULE (ONCE_DEPTH_CONV wordn_CONV) (SPEC w nthm) in
    let thm2 = SUBS[(SPECL bits bwthm)] thm1 in
    (TRANS thm2 (fst(itlist itfn bits (bth, eth0,"[]:(bool)list"))))) ?
    failwith `wordn_NVAL_CONV`;; %

%-----------------------------------------------------------------------%
% wordn_NWORD_CONV : thm -> conv    					%
% wordn_NWORD_CONV NWORDn_DEF "NWORDn m" returns the following theorem:	%
%   |- NWORDn m = #10...01  	    					%
% where m must be less than (2 EXP n) otherwise the conversion will fail%
%-----------------------------------------------------------------------%

let wordn_NWORD_CONV =
    let mod = (\m n. m - ((m /n) * n)) in
    let odd n = ((mod n 2) = 1) in
    letrec exp2 n = if(not(n > 0)) then 1 else (2 * exp2 (n-1))  in
    let BV = definition `wordn_num` `BV` and
    	VAL = definition `wordn_num` `VAL` and
    	WORDN_VAL = theorem `wordn_num` `WORDN_VAL` in
    let ntobs n = 
    	letrec ntbs n = if (n = 0) then [] 
    	    else ((odd n) => 1 | 0) . (ntbs(n / 2)) in
        if (not (n < 0)) then rev (ntbs n) else failwith `n < 0`  in
    let padto n l =
    	letrec padl n l =
            if (n = 0) then l else 0.(padl (n-1) l) in
    	let m = (n - (length l)) in
    	if (not(m > 0)) then l else (padl m l) in
  \wthm tm. (let (w,ty),M = (dest_const # I) (dest_comb tm) in
    let (mstr,nty) = dest_const M in
    let (_,[nty';wdty]) = dest_type ty in
    let nstr = implode (fst(partition is_digit
    	 (explode (fst(dest_type wdty))))) in
    let n = int_of_string nstr and m = int_of_string mstr in
    if  (not(m < (exp2 n)))  then fail
    else 
    	let nlst = (ntobs (int_of_string mstr)) in
    	let len = (length nlst) in
    	let nlst' = if (len > n)
    	   	    then (snd(chop_list (len - n) nlst))
    	    	    else (padto n nlst) in
    	let bits = map (\n. ((n = 1) => "T" | "F")) nlst' in
    	let blst = mk_list(bits, ":bool") in
    	let W = mk_const((`#`^(implode (map string_of_int nlst'))),wdty) in
    	let vth = VAL_CONV "VAL ^blst" in
    	let th1 = CONV_RULE (ONCE_DEPTH_CONV LENGTH_CONV)
    	    	(SPEC blst WORDN_VAL) in
    	let th2 = SUBS[(SUBS[vth]th1)](SPEC M wthm) in
        (TRANS th2 (SYM (wordn_CONV W)))) ? failwith `wordn_NWORD_CONV`;;

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

%-----------------------------------------------------------------------%
% NWORD_CONV : thm -> thm -> conv    					%
% NWORD_CONV NWORDn_DEF word3_NWORD_MOD "NWORDn m" returns the theorem: %
%   |- NWORDn m = #10...01  	    					%
% where m may be greater than (2 EXP n) and the resulting word is eqaul %
%   to m MOD (2 EXP n)	    	    					%
%-----------------------------------------------------------------------%

let NWORD_CONV =
    let mod = (\m n. m - ((m /n) * n)) in
    letrec exp2 n = if(not(n > 0)) then 1 else (2 * exp2 (n-1))  in
  \wthm modthm tm. (let NW,M = (dest_comb tm) in
    let (mstr,nty) = dest_const M in
    let (_,[nty';wdty]) = dest_type (snd(dest_const NW)) in
    let nstr = implode (fst(partition is_digit
    	 (explode (fst(dest_type wdty))))) in
    let n = int_of_string nstr and m = int_of_string mstr in
    if (m < (exp2 n)) then (wordn_NWORD_CONV wthm tm)
    else
    	(let MM = mk_const(string_of_int(mod m (exp2 n)), nty) in
    	 let th1 = RIGHT_CONV_RULE (ONCE_DEPTH_CONV MOD_CONV)(SPEC M modthm) in
    	 (TRANS th1 (wordn_NWORD_CONV wthm (mk_comb(NW,MM)))))) ?
    failwith `NWORD_CONV`;;

