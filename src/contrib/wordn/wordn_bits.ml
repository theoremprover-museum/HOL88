%-----------------------------------------------------------------------%
% FILE: wordn_bits.ml 	DATE: 16 June 1992 BY Wai Wong			%
%-----------------------------------------------------------------------%

let SPLIT = definition `ltree` `SPLIT`;;

%< let SPLIT_LENGTH = % prove_thm(`SPLIT_LENGTH`, % PROVE(
    "!l:* list. SPLIT (LENGTH l) l = l,[]",
    LIST_INDUCT_TAC THEN REWRITE_TAC[SPLIT;LENGTH]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[HD;TL]);; >%

%-----------------------------------------------------------------------%
% Bit vector index. the index of the bits in a bit vector is always	%
% starting with 0 from the least significant bit(LSB), so the most 	%
% significant bit is indexed as (n-1)th bit for a n-bit word.		%
% The following definitions assume that the bit vector is interpreted	%
% using the little endian format, ie., the HD of the list is the MSB.	%
%-----------------------------------------------------------------------%

%-----------------------------------------------------------------------%
% define_wordn_msb : thm -> string -> thm 				%
% This defines a logical function whose name is MSBn and whose type is	%
%  :wordn -> bool. This function returns the most significant bit of 	%
% its argument word as a boolean.   					%
% The theorem argument is the wordn type definition theorem.		%
% The string argument is the name under which the definition of MSBn	%
%  is stored in the current theory. 					%
% It returns this definition as the function value.			%
% The definition is in the format below:				%
%   |- !w:wordn. MSBn w = HD(BITSn w)					%
%-----------------------------------------------------------------------%
let define_wordn_msb wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let BITS = snd(dest_comb(lhs eqn)) in
    let MSB = mk_var((`MSB`^nstr), ":^wdty -> bool") in
    new_definition(name, "^MSB ^w = HD (^BITS)") 
    ?\s  failwith (`define_wordn_msb: `^s);;

%-----------------------------------------------------------------------%
% prove_msb_thm = - : (thm -> thm -> thm)				%
% This proves a theorem asserting the expansion of the MSBn definition. %
% It takes two theorems as its argument, the first is the wordn type 	%
% definition and, the second is the definition of the MSBn function.	%
% It return a theorem in the following form:				%
% |- !b(n-1) ... b0. MSBn(WORDn[b(n-1); ...; b0]) = b(n-1)     		%
%-----------------------------------------------------------------------%
let prove_msb_thm wdthm defthm =
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD = fst(dest_comb(lhs eqn)) in
    let blst = rev(mk_bit_list `b` (int_of_string nstr) ``) in
    let bits = mk_list(blst, ":bool") in
    let W = mk_comb(WORD, bits) in
    let thm1 = LENGTH_CONV "LENGTH ^bits" in
    let thm2 = EQ_MP (SPEC bits bw) thm1 in
    GEN_ALL (PURE_ONCE_REWRITE_RULE[HD] (SUBS[thm2] (SPEC W defthm)))
    ?\s  failwith (`prove_msb_thm: `^s);;

%-----------------------------------------------------------------------%
% MSB_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_msb_thm, and the term is in the following form:	%
%   "MSBn (WORDn [b(n-1); ...; b0])" 					%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let MSB_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `MSB`) in
  \gthm tm.
    (let _,(W,bits) = (check # dest_comb) (dest_comb tm) in
     let lst = fst(dest_list bits) in
     (SPECL lst gthm)) ?\s failwith (`MSB_CONV: `^s);;

%-----------------------------------------------------------------------%
% define_wordn_lsb : thm -> string -> thm 				%
% This defines a logical function whose name is LSBn and whose type is	%
%  :wordn -> bool. This function returns the least significant bit of 	%
% its argument word as a boolean.   					%
% The theorem argument is the wordn type definition theorem.		%
% The string argument is the name under which the definition of LSBn	%
%  is stored in the current theory. 					%
% It returns this definition as the function value.			%
% The definition is in the format below:				%
% |- !w:wordn. LSBn w = EL(PRE(LENGTH(BITSn w)))(BITSn w)		%
%-----------------------------------------------------------------------%
let define_wordn_lsb wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let BITS = snd(dest_comb(lhs eqn)) in
    let LSB = mk_var((`LSB`^nstr), ":^wdty -> bool") in
    new_definition(name, "^LSB ^w = EL (PRE(LENGTH ^BITS)) (^BITS)") 
    ?\s  failwith (`define_wordn_lsb: `^s);;

%-----------------------------------------------------------------------%
% prove_lsb_thm = - : (thm -> thm -> thm)				%
% This proves a theorem asserting the expansion of the LSBn definition. %
% It takes two theorems as its argument, the first is the wordn type 	%
% definition and, the second is the definition of the LSBn function.	%
% It return a theorem in the following form:				%
% |- !b(n-1) ... b0. LSBn(WORDn[b(n-1); ...; b0]) = b0     		%
%-----------------------------------------------------------------------%
let LENGTH = definition `list` `LENGTH`;;
let prove_lsb_thm =
    let EL_LENGTH = PROVE("!l (x:bool). EL (LENGTH l) (APPEND l [x]) = x",
      LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND;LENGTH;EL;HD;TL]
      THEN POP_ASSUM ACCEPT_TAC) in
    let PRE_LENGTH = PROVE(
      "!l (x:bool). PRE (LENGTH (APPEND l [x])) = LENGTH l",
      LIST_INDUCT_TAC THEN
      REWRITE_TAC[LENGTH_APPEND;LENGTH;PRE;ADD_CLAUSES]) in
  \wdthm defthm.
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD = fst(dest_comb(lhs eqn)) in
    let blst = (mk_bit_list `b` (int_of_string nstr) ``) in
    let bits = mk_list((rev blst), ":bool") and
        bits' = mk_list((rev(tl blst)), ":bool") and b = hd blst in
    let W = mk_comb(WORD, bits) in
    let thm1 = LENGTH_CONV "LENGTH ^bits" in
    let thm2 = EQ_MP (SPEC bits bw) thm1 in
    let thm3 = SYM(APPEND_CONV "APPEND ^bits' [^b]") in
    let thm4 = ISPECL [bits'; b] PRE_LENGTH and
        thm5 = ISPECL [bits'; b] EL_LENGTH in
    GEN_ALL (TRANS (SUBS[thm4](SUBS_OCCS[[2;3],thm3]
    (SUBS [thm2] (SPEC W defthm)))) thm5)
    ?\s  failwith (`prove_lsb_thm: `^s);;

%-----------------------------------------------------------------------%
% LSB_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_lsb_thm, and the term is in the following form:	%
%   "LSBn (WORDn [b(n-1); ...; b0])" 					%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let LSB_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
    (fst(dest_const t))))) = `LSB`) in
  \gthm tm.
    (let _,(W,bits) = (check # dest_comb) (dest_comb tm) in
     let lst = fst(dest_list bits) in
     (SPECL lst gthm)) ?\s failwith (`LSB_CONV: `^s);;

%-----------------------------------------------------------------------%
% define_wordn_bit : thm -> string -> thm 				%
% This defines a logical function whose name is BITn and whose type is	%
%  :wordn -> num -> bool. This function returns the kth bit of		%
% its argument word as a boolean.   					%
% The theorem argument is the wordn type definition theorem.		%
% The string argument is the name under which the definition of BITn	%
%  is stored in the current theory. 					%
% It returns this definition as the function value.			%
% The definition is in the format below:				%
%  |- !k w. BITn k w = EL(PRE((LENGTH(BITSn w)) - k))(BITSn w)		%
%-----------------------------------------------------------------------%
let define_wordn_bit wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let BITS = snd(dest_comb(lhs eqn)) in
    let BIT = mk_var((`BIT`^nstr), ":num -> ^wdty -> bool") in
    new_definition(name, "^BIT k ^w = EL (PRE((LENGTH ^BITS)- k)) (^BITS)") 
    ?\s  failwith (`define_wordn_bit: `^s);;

%-----------------------------------------------------------------------%
% prove_bit_thm = - : (thm -> thm -> int -> thm)			%
% This proves a theorem asserting the expansion of the BITn definition. %
% It takes three arguments, the first is the wordn type definition,	%
% the second is the definition of the BITn function and the last is the %
% required index. It return a theorem in the following form:		%
% |- !b(n-1) ... b0. BITn k (WORDn[b(n-1); ...; bk; ...; b0]) = bk     	%
%-----------------------------------------------------------------------%
let prove_bit_thm =
  \wdthm defthm ix.
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let n =  (int_of_string nstr) in
    if (ix < n)  then
      let WORD = fst(dest_comb(lhs eqn)) in
      let blst = (mk_bit_list `b` (int_of_string nstr) ``) in
      let bits = mk_list((rev blst), ":bool") and b = el (ix + 1) blst in
      let W = mk_comb(WORD, bits) and N = mk_const((string_of_int ix),":num")in
      let L = mk_const(string_of_int(n -1), ":num") in
      let thm1 = LENGTH_CONV "LENGTH ^bits" in
      let thm2 = EQ_MP (SPEC bits bw) thm1 in
      let thm3 = RIGHT_CONV_RULE ((ONCE_DEPTH_CONV SBC_CONV) THENC
    	 ((RATOR_CONV o RAND_CONV) PRE_CONV))
         (SUBS[thm1](SUBS[thm2](SPECL[N; W] defthm))) in
      (GEN_ALL (RIGHT_CONV_RULE EL_CONV thm3))
    else failwith `prove_bit_thm: index too large`;;

%-----------------------------------------------------------------------%
% BIT_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_bit_thm, and the term is in the following form:	%
%   "BITn k (WORDn [b(n-1); ...; b0])" 					%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let BIT_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `BIT`) in
  \gthm tm.
    (let _,[k;W] = (check # I) (strip_comb tm) in
     let lst = fst (dest_list (snd(dest_comb W))) in
     (SPECL lst gthm)) ?\s failwith (`BIT_CONV: `^s);;

%-----------------------------------------------------------------------%
% define_wordn_seg : thm -> string -> int -> thm			%
% This defines a logical function whose name is SEGn_m and whose type is%
%  :wordn -> num -> wordm. This function returns a seg of m-bits long of%
% its argument word as a m-bit word.   					%
% The theorem argument is the wordn type definition theorem.		%
% The string argument is the name under which the definition of SEGn_m	%
%  is stored in the current theory. 					%
% The int argument specifies the length of the segment.			%
% It returns this definition as the function value.			%
% The definition is in the format below:				%
%  |- !k w. SEGn_m k w = WORDm(LASTN m(NBUTLAST k(BITSn w)))		%
%-----------------------------------------------------------------------%
let define_wordn_seg wdthm name m =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    if (int_of_string(nstr) < m) then failwith `segment too long`
    else
     (let BITS = snd(dest_comb(lhs eqn)) in
      let mstr = string_of_int m in
      let M = mk_const(mstr, ":num") in
      let wdty' = mk_type((`word`^mstr), []) in
      let WM = mk_const((`WORD`^mstr), ":(bool)list -> ^wdty'") in
      let SEG = mk_var((`SEG`^nstr^`_`^mstr), ":num -> ^wdty -> ^wdty'") in
      new_definition(name, "^SEG k ^w = ^WM (LASTN ^M (NBUTLAST k ^BITS))"))
    ?\s  failwith (`define_wordn_seg: `^s);;

%-----------------------------------------------------------------------%
% prove_seg_thm = - : (thm -> thm -> int -> thm)			%
% This proves a theorem asserting the expansion of the SEGn_m definition%
% It takes three arguments, the first is the wordn type definition,	%
% the second is the definition of the SEGn_m function and the last is	%
% the required index. It return a theorem in the following form:	%
% |- !b(n-1) ... b0. SEGn_m k (WORDn[b(n-1); ...; bk; ...; b0]) = 	%
%     WORDm [ b(k+m-1); ... bk]	    				     	%
%-----------------------------------------------------------------------%
let prove_seg_thm =
    let get_len ty = implode(snd(chop_list 4 (explode(fst(dest_type ty))))) in
  \wdthm defthm ix.
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let S = fst(strip_comb(lhs(snd(strip_forall (concl defthm))))) in
    let wdty' =  hd (tl(snd(dest_type(hd (tl(snd(dest_type(type_of S)))))))) in
    let nstr = get_len wdty and lstr = get_len wdty' in
    let n =  (int_of_string nstr) and l = int_of_string lstr in
    if ((ix + l) > n) then failwith `index too large`
    else if (ix < n)  then
     (let WORD = fst(dest_comb(lhs eqn)) in
      let blst = (mk_bit_list `b` (int_of_string nstr) ``) in
      let bits = mk_list((rev blst), ":bool") in
      let W = mk_comb(WORD, bits) and N = mk_const((string_of_int ix),":num")in
      let L = mk_const(string_of_int(n -1), ":num") in
      let thm1 = LENGTH_CONV "LENGTH ^bits" in
      let thm2 = EQ_MP (SPEC bits bw) thm1 in
      (GEN_ALL (RIGHT_CONV_RULE ((ONCE_DEPTH_CONV NBUTLAST_CONV)
       THENC (RAND_CONV LASTN_CONV))
       (SUBS[thm2](SPECL [N;W] defthm)))))
   else fail
    ?\s failwith (`prove_seg_thm: `^s);;

%-----------------------------------------------------------------------%
% SEG_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_seg_thm, and the term is in the following form:	%
%   "SEGn_m k (WORDn [b(n-1); ...; b0])" 				%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let SEG_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `SEG`) in
  \gthm tm.
    (let _,[k;W] = (check # I) (strip_comb tm) in
     let lst = fst(dest_list (snd(dest_comb W))) in
     (SPECL lst gthm)) ?\s failwith (`SEG_CONV: `^s);;

%-----------------------------------------------------------------------%
% define_wordn_pad : thm -> string -> int -> thm			%
% This defines a logical function whose name is PADn_m and whose type is%
%  :wordn -> num -> wordm -> wordn. This function returns a n-bit word  %
% which is the result of replaceing the m-bit segment starting from the %
% kth bit of the input wordn.	    					%
% The theorem argument is the wordn type definition theorem.		%
% The string argument is the name under which the definition of PADn_m	%
%  is stored in the current theory. 					%
% The int argument specifies the length of the segment.			%
% It returns this definition as the function value.			%
% The definition is in the format below:				%
%  |- !w k wm.	    	    	    					%
%    PADn_m w k wm =  WORDn (APPEND (NBUTLAST(k + m)(BITSn w)) 		%
%    (APPEND(BITSm wm)(LASTN k(BITSn w))))				%
%-----------------------------------------------------------------------%
let define_wordn_pad =
  \wdthm name m.
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    if (int_of_string(nstr) < m) then failwith `segment too long`
    else
     (let WORD,BITS = (dest_comb(lhs eqn)) in
      let mstr = string_of_int m in
      let M = mk_const(mstr, ":num") in
      let wdty' = mk_type((`word`^mstr), []) in
      let wm = mk_var(`wm`, wdty') in
      let BITSM = mk_const((`BITS`^mstr), ":^wdty' -> (bool)list") in
      let BM = mk_comb(BITSM, wm) in
      let PAD = mk_var((`PAD`^nstr^`_`^mstr), ":^wdty->num->^wdty'->^wdty") in
      new_definition(name, "^PAD ^w k ^wm = ^WORD
      (APPEND (NBUTLAST (k + ^M) ^BITS) (APPEND (^BM) (LASTN k ^BITS)))"))
    ?\s  failwith (`define_wordn_pad: `^s);;

%-----------------------------------------------------------------------%
% prove_pad_thm = - : (thm -> thm -> thm -> int -> thm)			%
% This proves a theorem asserting the expansion of the PADn_m definition%
% It takes three arguments, the first is the wordn type definition,	%
% the second is the definition of the SEGn_m function and the last is	%
% the required index. It return a theorem in the following form:	%
% |- !b(n-1) ... b0 a(m-1) ... a0.	    				% 
%  PADn_m (WORDn[b(n-1); ...; bk; ...; b0]) k (WORDm[a(m-1);...;a0]) = 	%
%     WORDn [b(n-1);...; a(m-1); ...; a0; b(k-1); ...; b0]	     	%
%-----------------------------------------------------------------------%
let prove_pad_thm =
    let get_len ty = implode(snd(chop_list 4 (explode(fst(dest_type ty))))) in
  \wdthm wdmthm defthm ix.
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdnty = type_of w in
    let wbm,bwm = CONJ_PAIR wdmthm in
    let wm,eqnm = dest_forall (concl wbm) in
    let wdmty = type_of wm in
    let PAD = fst(strip_comb(lhs(snd(strip_forall (concl defthm))))) in
    let nstr = get_len wdnty and mstr = get_len wdmty in
    let n =  (int_of_string nstr) and m = int_of_string mstr in
    if ((ix + m) > n) then failwith `index too large`
    else 
     (let WN = fst(dest_comb(lhs eqn)) in
      let blst = (mk_bit_list `b` (int_of_string nstr) ``) in
      let bits = mk_list((rev blst), ":bool") in
      let blst' = (mk_bit_list `a` (int_of_string mstr) ``) in
      let bits' = mk_list((rev blst'), ":bool") in
      let WM = mk_const((`WORD`^mstr), ":(bool)list -> ^wdmty") in
      let WDN = mk_comb(WN, bits) and WDM = mk_comb(WM, bits') in
      let IX = term_of_int ix and M = term_of_int m in
      let L = term_of_int (ix + m) in
      let thm1 = LENGTH_CONV "LENGTH ^bits" and
          thm1' = LENGTH_CONV "LENGTH ^bits'" in
      let thm2 = EQ_MP (SPEC bits bw) thm1 and
          thm2' = EQ_MP (SPEC bits' bwm) thm1' in
      let thm3 = ADD_CONV "^IX + ^M" in
      let thm4 = NBUTLAST_CONV "NBUTLAST ^L ^bits" in
      let thm5 = LASTN_CONV "LASTN ^IX ^bits" in
      (GEN_ALL (RIGHT_CONV_RULE (DEPTH_CONV APPEND_CONV)
       (SUBS[thm4;thm5](SUBS[thm2;thm2';thm3](SPECL [WDN;IX;WDM] defthm))))))
    ?\s failwith (`prove_pad_thm: `^s);;

%-----------------------------------------------------------------------%
% PAD_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_pad_thm, and the term is in the following form:	%
%   "PADn_m (WORDn [b(n-1); ...; b0]) k (WORDm[a(m-1);...;a0]"		%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let PAD_CONV =
    let check = assert(\t. implode(fst(chop_list 3(explode
    	(fst(dest_const t))))) = `PAD`) in
    let get_list w = fst(dest_list (snd(dest_comb w))) in
  \gthm tm.
    (let _,[Wn;k;Wm] = (check # I) (strip_comb tm) in
     let nlst = get_list Wn and mlst = get_list Wm in
     (SPECL (append nlst mlst) gthm)) ?\s failwith (`PAD_CONV: `^s);;

% --------------------------------------------------------------------- %
% define_wordn_partition : ((string # string) -> thm list -> (thm # thm))%
% the strings specify the names of the join and split functions		%
% bxthms' are theorems return by prove_BITS_WORD 			%
% define_word_partition (`ffj`,`ffs`) [wordm_bw;wordn_bw;wordl_bw]	%
%  defines two functions    	    					%
%   JOIN_m_n : (wordm # wordn) -> wordl  				%
%   SPLIT_m_n : wordl -> (wordm # wordn)  				%
% by the following definitions and stored under the names ffj and ffs:	%
% |- !wm wn. JOIN_m_n(wm,wn) = WORDl(APPEND(BITSm wm)(BITSn wn))	%
% |- !wl. SPLIT_m_n wl =    	    					%
%     (let (lm,ln) = SPLIT m(BITSl wl) in WORDn lm,WORDn ln)		%
% and then proves two theorems which are returned as the function value %
% |- !b0 ... b(l-1).	    	    					%
%    ffj(WORDm[b0;...;b(m-1)],WORDn[bn;...;b(l-1)]) =			%
%    WORDl[b0;...;b(l-1)]   	    					%
% |- !b0 ... b(l-1).	    	    					%
%    ffs(WORDl[b0;...;b(l-1)]) =    					%
%    WORDm[b0;...;b(m-1)],WORDn[bm;...;b(l-1)]				%
% --------------------------------------------------------------------- %
let define_wordn_partition =
    let strip_bthm bthm =
      let (BITS,w),l = (dest_comb # I)(dest_eq (concl bthm)) in
      (BITS,(fst(dest_comb w)),w,l) in
    let get_ty = \b. hd(snd (dest_type (snd (dest_const b)))) in
  \(join,split) [bmthm;bnthm;blthm].
    let [m;n;l] = map (\l. length (fst (strip_forall (concl l))))
    	 [bmthm;bnthm;blthm] in
    let mstr = string_of_int m and nstr = string_of_int n in
    let BITSl,WORDl,wl,ll = strip_bthm (SPEC_ALL blthm) in
    let lstl = fst(dest_list ll) in
    let lstm,lstn = chop_list m lstl in
    let blthm' = SPECL  lstl blthm and 
    	bmthm' = SPECL lstm bmthm and bnthm' = SPECL lstn bnthm in 
    let BITSm,WORDm,wm,lm = strip_bthm bmthm' and
        BITSn,WORDn,wn,ln = strip_bthm bnthm' in
    let [wmty;wnty;wlty] = map get_ty [BITSm;BITSn;BITSl] in
    let M = mk_const((string_of_int m),":num") in
    let JOIN = mk_var((`JOIN_`^mstr^`_`^nstr), ":(^wmty # ^wnty) -> ^wlty") and
        SPLIT = mk_var((`SPLIT_`^mstr^`_`^nstr),":^wlty -> (^wmty # ^wnty)") in
    let jdef = new_definition(join,
    	"^JOIN ((wm:^wmty),(wn:^wnty)) =
    	    ^WORDl  (APPEND (^BITSm wm) (^BITSn wn))") in
    let sdef = new_definition(split,
    	"^SPLIT (wl:^wlty) = let (lm,ln) = SPLIT ^M (^BITSl wl) in
    	    ((^WORDm lm), (^WORDn ln))") in
    let jthm = GEN_ALL (RIGHT_CONV_RULE (ONCE_DEPTH_CONV APPEND_CONV)
    	(SUBS[bmthm';bnthm'] (SPECL [wm;wn] jdef))) in
    let sthm = GEN_ALL (RIGHT_CONV_RULE ((ONCE_DEPTH_CONV SPLIT_CONV)
    	THENC (ONCE_DEPTH_CONV let_CONV)) (SUBS[blthm'] (SPEC wl sdef))) in
    (jthm, sthm) ? failwith `define_word_partition`;;

%-----------------------------------------------------------------------%
% wordn_JOIN_CONV : thm -> conv    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by define_word_partition, and the term is in the following	%
%  form: JOIN_m_n (WORDm[b(l-1);...;bn]),(WORDn[b(n-1);...;b0])		%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let wordn_JOIN_CONV =
    let check = assert (\t. implode(fst(chop_list 4(explode
       (fst(dest_const t))))) = `JOIN`) in
  \gthm tm.
    (let _,(wm,wn) = (check # dest_pair) (dest_comb tm) in
     let Wm,bitsm = dest_comb wm and Wn,bitsn = dest_comb wn in
     let lstm = fst(dest_list bitsm) and lstn = fst(dest_list bitsn) in
     (SPECL (lstm @ lstn) gthm)) ?\s failwith (`wordn_JOIN_CONV: `^s);;

%-----------------------------------------------------------------------%
% wordn_SPLIT_CONV : thm -> conv    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by define_word_partition, and the term is in the following	%
%  form: SPLIT_m_n (WORDl[b(l-1);...;b0])				%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let wordn_SPLIT_CONV =
    let check = assert (\t. implode(fst(chop_list 5(explode
       (fst(dest_const t))))) = `SPLIT`) in
  \gthm tm.
    (let _,w = (check # I) (dest_comb tm) in
     let W,bits = dest_comb w  in
     let lst = fst(dest_list bits) in
     (SPECL lst gthm)) ?\s failwith (`wordn_SPLIT_CONV: `^s);;

% --------------------------------------------------------------------- %
% prove_partition_thm : ((thm # thm) -> thm list -> thm) 		%
% jthm, sthm are the theorem returned by define_word_partition 		%
% cxthms' are teh theorems returned by prove_wordn_cases_thm 		%
% This function returns a theorem:  					%
% |- (!wl. ffj(ffs wl) = wl) /\ (!wm wn. ffs(ffj(wm,wn)) = wm,wn) 	%
% where ffj and ffs are the join and split functions defined by  	%
%    define_word_partition (`ffj`,ffs`) ... 				%
% --------------------------------------------------------------------- %
let prove_partition_thm =
  \(jthm, sthm) [cmthm; cnthm; clthm].
    let lstl,e = strip_forall(concl jthm) in
    let (ffj,ww),wl = (dest_comb # I) (dest_eq e) in
    let wm,wn = dest_pair ww in
    let _,e' = strip_forall(concl sthm) in
    let ffs = fst(dest_comb (fst(dest_eq e'))) in
    let [wmty;wnty;wlty] = map type_of [wm;wn;wl] in
    let m = length(fst(dest_list(snd(dest_comb wm)))) in
    let lstn = snd(chop_list m lstl) in
    let j_s = PROVE("!wl:^wlty. ^ffj(^ffs wl) = wl",
    	GEN_TAC THEN wordn_CASES_TAC "wl:^wlty" clthm
    	THEN ACCEPT_TAC (SUBS[SPEC_ALL jthm](AP_TERM ffj (SPEC_ALL sthm)))) and
        s_j = PROVE("!(wm:^wmty) (wn:^wnty). ^ffs(^ffj(wm,wn)) = (wm,wn)",
        REPEAT GEN_TAC THEN wordn_CASES_TAC "wm:^wmty" cmthm
    	THEN wordn_X_CASES_TAC "wn:^wnty" cnthm lstn
        THEN ACCEPT_TAC (SUBS[SPEC_ALL sthm](AP_TERM ffs (SPEC_ALL jthm)))) in
    (CONJ j_s s_j) ? failwith `prove_patition_thm`;;


%-----------------------------------------------------------------------%
% SHIFT and ROTATION.	    	    					%
%   	    	    	    	    					%
% Shift  --- There are two types of shift operations depending on	%
% what is put in the bit position vocated by the shift. The first type  %
% copies what was in that position; and the second type puts the value	%
% given by the user. So the generic shift operators take a boolean, a 	%
% bit and a word, and returns a word and the bit shifted out.		%
%-----------------------------------------------------------------------%

%-----------------------------------------------------------------------%
% Shift right ---    	    	    					%
% SHRn :bool -> bool -> wordn -> (wordn # bool)				%
% SHRn f b w = let l = BITSn w in   					%
%   (WORDn(CONS (f => HD l | b) (BUTLAST l)), LAST l)			%
%   	    	    	    	    					%
% define_wordn_shift_right :thm -> string -> thm			%
%-----------------------------------------------------------------------%
let define_wordn_shift_right wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let SHR = mk_var((`SHR`^nstr), ":bool -> ^bty -> ^wdty->(^wdty # ^bty)")in
    new_definition(name, "^SHR (f:bool) (b:^bty) (^w) =
      let l = ^BITS in (^WORD(CONS (f => HD l | b) (BUTLAST l)),LAST l)")
    ?\s  failwith (`define_wordn_shift_right: `^s);;

%-----------------------------------------------------------------------%
% prove_shift_right_thm : thm -> thm -> thm				%
% prove_shift_right_thm wordn SHRn_DEF returns the following theorem	%
% |-!f b b(n-1) b0. SHRn f b(WORDn[b(n-1);...;b0]) =			%
%    WORDn[(f => b(n-1)| b);b(n-1);...;b1], b0				%
%-----------------------------------------------------------------------%
let prove_shift_right_thm wdthm defthm =
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let blst = rev(mk_bit_list `b` (int_of_string nstr) ``) in
    let bits = mk_list(blst, bty) in
    let W = mk_comb(WORD, bits) in
    let thm1 = LENGTH_CONV "LENGTH ^bits" in
    let thm2 = EQ_MP (SPEC bits bw) thm1 in
    (GEN_ALL(PURE_ONCE_REWRITE_RULE[HD](CONV_RULE((ONCE_DEPTH_CONV LAST_CONV)
     THENC (ONCE_DEPTH_CONV BUTLAST_CONV))(RIGHT_CONV_RULE let_CONV
     (SUBS[thm2](SPECL["f:bool";"b:^bty";W] defthm))))))
    ?\s  failwith (`prove_shift_right_thm: `^s);;

%-----------------------------------------------------------------------%
% SHR_CONV : thm -> conv -> conv    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_shift_right_thm, and the term is in the following	%
%  form: SHRn f (WORDn[b(n-1);...;b0]) b				%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let SHR_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `SHR`) in
  \gthm fconv tm.
    (let _,[f;b;w] = (check # I) (strip_comb tm) in
     let W,bits = dest_comb w in
     let lst = fst(dest_list bits) in
     let thm1 = SYM(fconv f) in
     let f' = lhs (concl thm1) in
     (SUBS_OCCS[[1],thm1] (RIGHT_CONV_RULE (ONCE_DEPTH_CONV COND_CONV)
     (SPECL (f'.(b . lst)) gthm)))) ?\s failwith (`SHR_CONV: `^s);;

%-----------------------------------------------------------------------%
% Shift left ---    	    	    					%
% SHLn :bool -> wordn -> bool -> (bool # wordn)				%
% SHLn f w b = let l = BITSn w in   					%
%   (HD l), WORDn(APPEND (TL l) [(f => (LAST l) | b)])			%
%   	    	    	    	    					%
% define_wordn_shift_left :thm -> string -> thm				%
%-----------------------------------------------------------------------%
let define_wordn_shift_left wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let SHL = mk_var((`SHL`^nstr), ":bool -> ^wdty -> ^bty->(^bty # ^wdty)")in
    new_definition(name, "^SHL (f:bool) (^w) (b:^bty) =
      let l = ^BITS in (HD l),(^WORD(APPEND(TL l) [(f => LAST l | b)]))")
    ?\s  failwith (`define_wordn_shift_left: `^s);;

%-----------------------------------------------------------------------%
% prove_shift_left_thm : thm -> thm -> thm				%
% prove_shift_left_thm wordn SHLn_DEF returns the following theorem	%
% |-!f b(n-1) b0 b. SHRn f (WORDn[b(n-1);...;b0]) b =			%
%    b(n-1), WORDn[b(n-2);...;b0;(f => b0| b)]				%
%-----------------------------------------------------------------------%
let prove_shift_left_thm wdthm defthm =
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let blst = rev(mk_bit_list `b` (int_of_string nstr) ``) in
    let bits = mk_list(blst, bty) in
    let W = mk_comb(WORD, bits) in
    let thm1 = LENGTH_CONV "LENGTH ^bits" in
    let thm2 = EQ_MP (SPEC bits bw) thm1 in
    (GEN_ALL(CONV_RULE(ONCE_DEPTH_CONV APPEND_CONV)
     (PURE_ONCE_REWRITE_RULE[HD;TL](CONV_RULE(ONCE_DEPTH_CONV LAST_CONV)
     (RIGHT_CONV_RULE let_CONV (SUBS[thm2]
     (SPECL["f:bool";W;"b:^bty"] defthm)))))))
    ?\s  failwith (`prove_shift_left_thm: `^s);;

%-----------------------------------------------------------------------%
% SHL_CONV : thm -> conv -> conv    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_shift_left_thm, and the term is in the following	%
%  form: SHLn f (WORDn[b(n-1);...;b0]) b				%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let SHL_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `SHL`) in
  \gthm fconv tm.
    (let _,[f;w;b] = (check # I) (strip_comb tm) in
     let W,bits = dest_comb w in
     let lst = fst(dest_list bits) in
     let thm1 = SYM(fconv f) in
     let f' = lhs (concl thm1) in
     (SUBS_OCCS[[1],thm1] (RIGHT_CONV_RULE (ONCE_DEPTH_CONV COND_CONV)
     (SPECL (f'.(lst @ [b])) gthm)))) ?\s failwith (`SHL_CONV: `^s);;

%-----------------------------------------------------------------------%
% Rotate right ---  	    	    					%
% RORn :wordn -> wordn	    	    					%
% RORn w = let l = BITSn w in (WORDn(CONS (LAST l) (BUTLAST l)))	%
% define_wordn_rotate_right : thm -> string				%
%-----------------------------------------------------------------------%
let define_wordn_rotate_right wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let ROR = mk_var((`ROR`^nstr), ":^wdty-> ^wdty")in
    new_definition(name, "^ROR (^w) =
      let l = ^BITS in (^WORD(CONS (LAST l) (BUTLAST l)))")
    ?\s  failwith (`define_wordn_rotate_right: `^s);;

%-----------------------------------------------------------------------%
% prove_rotate_right_thm : thm -> thm -> thm				%
% prove_rotate_right_thm wordn ROLn_DEF  returns the following theorem	%
% |- ! b(n-1) ... b0.	    	    					%
%    ROLn(WORDn[b(n-1);...;b0]) =  WORDn[b0;b(n-1);...b1]		%
%-----------------------------------------------------------------------%
let prove_rotate_right_thm wdthm defthm =
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let blst = rev(mk_bit_list `b` (int_of_string nstr) ``) in
    let bits = mk_list(blst, bty) in
    let W = mk_comb(WORD, bits) in
    let thm1 = LENGTH_CONV "LENGTH ^bits" in
    let thm2 = EQ_MP (SPEC bits bw) thm1 in
    GEN_ALL (RIGHT_CONV_RULE (let_CONV THENC (ONCE_DEPTH_CONV LAST_CONV)
     THENC (ONCE_DEPTH_CONV BUTLAST_CONV)) (SUBS[thm2] (SPEC W defthm)))
    ?\s  failwith (`prove_rotate_right_thm: `^s);;

%-----------------------------------------------------------------------%
% ROR_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_rotate_right_thm, and the term is in the following	%
%  form: RORn (WORDn[b(n-1);...;b0])					%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let ROR_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `ROR`) in
  \gthm tm.
    (let _,(W,bits) = (check # dest_comb) (dest_comb tm) in
     let lst = fst(dest_list bits) in
     (SPECL lst gthm)) ?\s failwith (`ROR_CONV: `^s);;

%-----------------------------------------------------------------------%
% Rotate left ---  	    	    					%
% ROLn :wordn -> wordn	    	    					%
% ROLn w = let l = BITSn w in (WORDn(APPEND (TL l) [HD l]))		%
% define_wordn_rotate_right : thm -> string				%
%-----------------------------------------------------------------------%
let define_wordn_rotate_left wdthm name =
    let w,eqn = dest_forall (concl (CONJUNCT1 wdthm)) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let ROL = mk_var((`ROL`^nstr), ":^wdty-> ^wdty")in
    new_definition(name, "^ROL (^w) =
      let l = ^BITS in (^WORD(APPEND (TL l) [HD l]))")
    ?\s  failwith (`define_wordn_rotate_left: `^s);;

%-----------------------------------------------------------------------%
% prove_rotate_left_thm : thm -> thm -> thm				%
% prove_rotate_left_thm wordn ROLn_DEF  returns the following theorem	%
% |- ! b(n-1) ... b0.	    	    					%
%    ROLn(WORDn[b(n-1);...;b0]) =  WORDn[b(n-2);...b0;b(n-1)]		%
%-----------------------------------------------------------------------%
let prove_rotate_left_thm wdthm defthm =
    let wb,bw = CONJ_PAIR wdthm in
    let w,eqn = dest_forall (concl wb) in
    let wdty = type_of w in
    let nstr = implode(snd(chop_list 4 (explode(fst(dest_type wdty))))) in
    let WORD,BITS = dest_comb(lhs eqn) in
    let bty = hd(snd(dest_type (type_of BITS))) in
    let blst = rev(mk_bit_list `b` (int_of_string nstr) ``) in
    let bits = mk_list(blst, bty) in
    let W = mk_comb(WORD, bits) in
    let thm1 = LENGTH_CONV "LENGTH ^bits" in
    let thm2 = EQ_MP (SPEC bits bw) thm1 in
    GEN_ALL (RIGHT_CONV_RULE (ONCE_DEPTH_CONV APPEND_CONV)
    (PURE_ONCE_REWRITE_RULE[TL;HD]
    (RIGHT_CONV_RULE let_CONV (SUBS[thm2] (SPEC W defthm)))))
    ?\s  failwith (`prove_rotate_left_thm: `^s);;

%-----------------------------------------------------------------------%
% ROL_CONV : thm -> conv    	    					%
% It takes a theorem and a term. The theorem is in the format of those	%
% returned by prove_rotate_left_thm, and the term is in the following	%
%  form: ROLn (WORDn[b(n-1);...;b0])					%
% It returns a theorem which is an instance of the input theorem.	%
%-----------------------------------------------------------------------%
let ROL_CONV =
    let check = assert (\t. implode(fst(chop_list 3(explode
       (fst(dest_const t))))) = `ROL`) in
  \gthm tm.
    (let _,(W,bits) = (check # dest_comb) (dest_comb tm) in
     let lst = fst(dest_list bits) in
     (SPECL lst gthm)) ?\s failwith (`ROL_CONV: `^s);;

