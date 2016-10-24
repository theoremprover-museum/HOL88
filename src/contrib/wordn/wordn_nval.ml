%<
let MULT_CONV =
    let mth0,mth = CONJ_PAIR ( definition `arithmetic` `MULT`) in
    let int_of_tm tm = int_of_string(fst(dest_const tm)) and
        tm_of_int i  = mk_const(string_of_int i,":num") in
    let conv (n,m) tm = 
    	let th = RATOR_CONV(RAND_CONV num_CONV) tm in
    	SUBS[(SPECL [n;m] mth)] th in
    let iter tm (nint,m) th =
    	letref thm,count,tm' = th,nint,tm in
    	if (count = 0)
    	then (SUBS [(SPEC m mth0)] thm)
    	loop (tm' := "^(tm_of_int count) * ^m" ;
    	      count := count - 1;
    	      thm := SUBS [(conv ((tm_of_int count),m) tm')] thm ) in
    \tm. (let c,[n;m] = (assert (\c.c="*") # I) (strip_comb tm) in
    	let nint = int_of_tm n and mint = int_of_tm m in
    	if (nint = 0) then (SPEC m mth0)
    	if (mint = 0) then (PURE_ONCE_REWRITE_RULE[MULT_SYM](SPEC n mth0))
    	else 
    	  let thm =
    	    if (not(nint > mint))
            then (iter tm ((nint-1),m) (conv ((tm_of_int(nint-1)),m) tm))
    	    else (let tm' = "^m * ^n" in
    	    	  let th = (iter tm' ((mint-1),n) (conv ((tm_of_int(mint-1)),n) tm')) in
    	          (PURE_ONCE_REWRITE_RULE[MULT_SYM]th)) in
    	(CONV_RULE (DEPTH_CONV ADD_CONV) thm)) ?
    	failwith `MULT_CONV`;;

let EXP_CONV =
    let eth0,eth = CONJ_PAIR ( definition `arithmetic` `EXP`) in
    let int_of_tm tm = int_of_string(fst(dest_const tm)) and
        tm_of_int i  = mk_const(string_of_int i,":num") in
    let conv (n,m) tm = 
    	let th = (RAND_CONV num_CONV) tm in
    	SUBS[(SPECL [n;m] eth)] th in
    let iter tm (n,mint) th =
    	letref thm,count,tm' = th,mint,tm in
    	if (count = 0)
    	then (SUBS [(SPEC n eth0)] thm)
    	loop (tm' := "^n EXP ^(tm_of_int count)" ;
    	      count := count - 1;
    	      thm := SUBS [(conv (n,(tm_of_int count)) tm')] thm ) in
    \tm. (let c,[n;m] = (assert (\c.c="EXP") # I) (strip_comb tm) in
    	let nint = int_of_tm n and mint = int_of_tm m in
    	if (mint = 0) then (SPEC n eth0)
    	if (nint = 0) then ( SUBS[(SYM(num_CONV m))]
    	    (SPEC (tm_of_int(mint-1))(PURE_REWRITE_RULE[MULT](SPEC n eth))))
    	else 
    	  let thm = (iter tm (n,(mint-1)) (conv (n,(tm_of_int(mint-1))) tm))
    	    in
    	(CONV_RULE (DEPTH_CONV MULT_CONV) thm)) ?
    	failwith `EXP_CONV`;;

load_library`reduce`;;

>%

%-----------------------------------------------------------------------%
% wordn_NVAL_CONV : conv    	    					%
% wordn_NVAL_CONV "NVALn #10...01"  returns the following theorem:	%
%  |- NVALn #10...01 = m    	    					%
% where m is the value of the word #10...01 which is interpreted as	%
% natural number in bigendian format, eg. |- NVAL3 #011 = 3.		%
%-----------------------------------------------------------------------%

let wordn_NVAL_CONV =
    let BV = definition `wordn_num` `BV` and
    	VAL = definition `wordn_num` `VAL` in
    let bool s = ((s = `1`) => "T" | ((s = `0`) => "F" | fail)) in
    let f = (\b n. (b =`1` => 1 | (b = `0` => 0 | fail)) + (n + n)) in
    let bston bits = rev_itlist f bits 0 in
    \tm. (let v,w = dest_comb tm in
      let (hash.bits),ty = (explode # I) (dest_const w) in
      let v' = (implode o butlast o explode) (fst(dest_const v)) in
      if (not(hash = `#`) or not(v' = `NVAL`)) then fail else
    	let N = mk_const ((string_of_int (bston bits)), ":num") in
    	let tmlst = map bool bits in
    	let nstr = (string_of_int(length bits)) in
    	let defthm = definition `-` (`NVAL`^nstr%^`_DEF`%) in
    	let bwthm = theorem `-` (`word`^nstr^`_BITS_WORD`) ?
            prove_BITS_WORD (definition `-` (`word`^nstr)) in
    	let gl = "^tm = ^N" in
    	TAC_PROOF(([],gl),
    	    PURE_ONCE_REWRITE_TAC[defthm]
    	    THEN CONV_TAC (ONCE_DEPTH_CONV wordn_CONV)
    	    THEN SUBST1_TAC (SPECL tmlst bwthm)
    	    THEN PURE_REWRITE_TAC[VAL;BV;LENGTH]THEN REDUCE_TAC))
    	? failwith `wordn_NVAL_CONV`;;


%-----------------------------------------------------------------------%
% wordn_NWORD_CONV : conv   	    					%
% wordn_NWORD_CONV "NWORDn m" returns the following theorem:		%
%   |- NWORDn m = #10...01  	    					%
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
    let VAL_CONV =
    	\g. TAC_PROOF(([],g),
    	    PURE_REWRITE_TAC[VAL;BV;LENGTH]THEN REDUCE_TAC) in
  \tm. (let (w,ty),M = (dest_const # I) (dest_comb tm) in
        let dthm = definition `-` w in
    	let (mstr,nty) = dest_const M in
    	let (_,[nty';wdty]) = dest_type ty in
    	let nstr = last (explode w) and str = implode (butlast (explode w)) in
    	let n = int_of_string nstr and m = int_of_string mstr in
    	let MM = mk_const(string_of_int(mod m (exp2 n)), nty) in
    	if (not (str = `NWORD`)) then fail
    	else 
    	    let nlst = (ntobs (int_of_string mstr)) in
    	    let len = (length nlst) in
    	    let nlst' = if (len > n)
    	    	    then (snd(chop_list (len - n) nlst))
    	    	    else (padto n nlst) in
    	    let bits = map (\n. ((n = 1) => "T" | "F")) nlst' in
    	    let blst = mk_list(bits, ":bool") in
    	    let W = mk_const((`#`^(implode (map string_of_int nlst'))),wdty) in
    	    let vth = VAL_CONV "VAL ^blst = ^MM" in
    	    let th1 = CONV_RULE (ONCE_DEPTH_CONV LENGTH_CONV)
    	    	(SPEC blst WORDN_VAL) in
    	    let th2 = SUBS[(SUBS[vth]th1)](SPEC MM dthm) in
    	    let th3 = SUBS [(SYM (wordn_CONV W))] th2 in
    	    if (MM = M) then th3
    	    else let modthm = theorem `-` (`NWORD`^nstr^`_MOD`) ?
    	    	    prove_NWORD_MOD n in
    	    	(TRANS (RIGHT_CONV_RULE REDUCE_CONV (SPEC M modthm)) th3))
    ? failwith `wordn_NWORD_CONV`;;
