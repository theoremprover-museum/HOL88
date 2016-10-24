% ===================================================== %
% FILE: word_convs.ml	    DATE: 15 Dec 1992		%
% AUTHOR: Wai WONG  	    	    			%
% Uses: Libraries: arith res_quan			%
% Description: tactics and conversions for words	%
% ===================================================== %
% Revised for version 2.02 on 9 Feb. 1994 by WW		%

let word_CASES_TAC =
    let cthm = (theorem `word_base` `word_cases`) in
  \w. CHOOSE_THEN SUBST1_TAC (ISPEC w cthm) ;;

let word_INDUCT_TAC = 
    let ithm = theorem `word_base` `word_induct` in
    (INDUCT_THEN ithm (\t.ALL_TAC));;

let RESQ_WORDLEN_TAC = 
    (CONV_TAC RESQ_FORALL_CONV THEN word_INDUCT_TAC
     THEN PURE_ONCE_REWRITE_TAC[definition `word_base` `PWORDLEN_DEF`]
     THEN GEN_TAC THEN DISCH_TAC);;


% --------------------------------------------------------------------- %
% BIT_CONV : conv   	    	    					%
% BIT_CONV "BIT k (WORD [bn-1;...;bk;...b0])" returns a theorem		%
% |- BIT k (WORD [bn-1;...;bk;...b0]) = bk				%
% --------------------------------------------------------------------- %

let BIT_CONV =
    let defthm = definition `word_base` `BIT_DEF` in
    let check tm = assert (\t. fst(dest_const t) = `BIT`) tm in
  \tm.
    let _,[N;W] = (check # I) (strip_comb tm) in
    let LST =  snd (dest_comb W) in let lst = (fst o dest_list) LST in
    let n = int_of_term N in
    if not(n < (length lst)) then failwith `index too large`
    else (RIGHT_CONV_RULE ELL_CONV (ISPECL[N; LST] defthm))
  ?\s failwith (`BIT_CONV: `^s);;


% --------------------------------------------------------------------- %
% WSEG_CONV : conv   	    	    					%
% WSEG_CONV "WSEG m k (WORD [bn-1;...;bk;...b0])" returns a theorem	%
% |- WSEG m k (WORD [bn-1;...;bk;...b0]) = WORD [b(m+k-1); ...; bk]	%
% --------------------------------------------------------------------- %
let WSEG_CONV =
    let defthm = definition `word_base` `WSEG_DEF` in
    let check tm = assert (\t. fst(dest_const t) = `WSEG`) tm in
  \tm.
    let _,[N;INX;W] = (check # I) (strip_comb tm) in
    let LST =  snd (dest_comb W) in let lst = (fst o dest_list) LST in
    let n = int_of_term N and inx = int_of_term INX in
    if ((n+inx) > (length lst)) then failwith `index too large`
    else (RIGHT_CONV_RULE (((RAND_CONV o RAND_CONV) BUTLASTN_CONV)
       THENC (RAND_CONV LASTN_CONV)) (ISPECL[N; INX; LST] defthm))
  ?\s failwith (`WSEG_CONV: `^s);;

% --------------------------------------------------------------------- %
% PWORDLEN_CONV : term list -> conv					%
% PWORDLEN_CONV tms "PWORDLEN n tm" returns a theorem A |- PWORDLEN n tm%
% The input term tm should be in the following form:			%
%  WORD [ bs ]	    	    	    					%
%  WSEG m k tm' and tms should be [ N ] which indicates the size of tm'	%
%   	(m + k) <= N	    	    					%
%  WNOT tm' 	    PWORDLEN n tm' |- PWORDLEN n (WNOT tm')		%
%  WAND tm' tm''    PWORDLEN n tm', PWORDLEN n tm'' 			%
%   	    	    |- PWORDLEN n (WAND tm' tm'')			%
%  WOR tm' tm''     PWORDLEN n tm', PWORDLEN n tm'' 			%
%   	    	    |- PWORDLEN n (WOR tm' tm'')			%
%  WXOR tm' tm''    PWORDLEN n tm', PWORDLEN n tm'' 			%
%   	    	    |- PWORDLEN n (WXOR tm' tm'')			%
%  WCAT (tm',tm'')  tms should be [ n1; n2 ] and n1 + n2 = n		%
%   	    	    PWORDLEN n1 tm', PWORDLEN n2 tm''			%
%   	    	    |- PWORDLEN n (WCAT tm', tm'')			%
% --------------------------------------------------------------------- %


begin_section `PWORDLEN_CONV`;;

% --------------------------------------------------------------------- %

let LESS_CONV =
    let check s = assert (\x. fst(dest_const x) = s) in
    let less_conv t = EQT_INTRO 
    	(REWRITE_RULE (map (theorem `arithmetic`)[`LESS_MONO_EQ`;`LESS_0`])
    	(REDEPTH_CONV num_CONV t)) in
  \tm.
    let _,[M;N] = ((check `<`) # I) (strip_comb tm) in
    let m = int_of_term M and n = int_of_term N in
    (if (m < n) 
     then (let t = mk_comb(mk_comb("<", M), N) in
    	   (less_conv t))    	
     else if (m = n)
     then (EQF_INTRO (MATCH_MP (theorem `prim_rec` `NOT_LESS_EQ`)
    	 (EQT_ELIM (num_EQ_CONV "^M = ^N"))))
     else (let t = mk_comb(mk_comb("<", N), M) in
    	   (EQF_INTRO (PURE_REWRITE_RULE[AND_CLAUSES;(less_conv t)]
    	    (SPECL[M;N](theorem `arithmetic` `LESS_ANTISYM`))))));;

% --------------------------------------------------------------------- %
% LESS_EQ_CONV : conv  	    	    					%
% LESS_EQ_CONV "m <= n"  ---> |- (m <= n) = T iff m < n			%
%   	    	    	      |- (m <= n) = F otherwise			%
% --------------------------------------------------------------------- %

let LESS_EQ_CONV =
    let MATCH_EQ_MP = \eq lh. EQ_MP (PART_MATCH lhs eq (concl lh)) lh in
    let check s = assert (\x. fst(dest_const x) = s) in
    let nthm = GEN_ALL (PURE_REWRITE_RULE[NOT_CLAUSES;
    	GEN_ALL (SYM (el 4 (CONJ_LIST 4 (SPEC_ALL EQ_CLAUSES))))]
    	(AP_TERM "$~" (SPEC_ALL (theorem `arithmetic` `NOT_LESS`)))) in
  \tm.
    let _,[M;N] = ((check `<=`) # I) (strip_comb tm) in
    let m = int_of_term M and n = int_of_term N in
    (if (m > n)
     then (let t = mk_comb(mk_comb("<", N), M) in
    	   MATCH_EQ_MP nthm (EQT_ELIM (LESS_CONV t)))
     else if (m = 0) then (EQT_INTRO (SPEC N 
    	(theorem `arithmetic` `ZERO_LESS_EQ`)))
     else (EQT_INTRO (REWRITE_RULE
    	    (map(theorem `arithmetic`) [`LESS_EQ_MONO`;`ZERO_LESS_EQ`])
    	     (REDEPTH_CONV num_CONV tm))));;

let word_inst_thm = \(n,w) th. (RESQ_SPEC w (SPEC n th));;

let WNOT_PWORDLEN = RESQ_MATCH_MP (theorem `word_bitop` `PBITOP_PWORDLEN`)
    (theorem `bword_bitop` `PBITOP_WNOT`);;

let [WAND_PWORDLEN; WOR_PWORDLEN; WXOR_PWORDLEN] =
    let pthm =  (theorem `word_bitop` `PBITBOP_PWORDLEN`) in
    map (\s. RESQ_MATCH_MP pthm (theorem `bword_bitop` s))
    	[`PBITBOP_WAND`; `PBITBOP_WOR`; `PBITBOP_WXOR`];;

letref pwordlen_bitop_funs =
    [(`WNOT`, WNOT_PWORDLEN);
     (`WAND`, WAND_PWORDLEN);
     (`WOR`,  WOR_PWORDLEN);
     (`WXOR`, WXOR_PWORDLEN)];;

let pwordlen_funs =
    let PWORDLEN_DEF = (definition `word_base` `PWORDLEN_DEF`) in
    	[(`WORD`,  (\tms n w. 
    	    if (int_of_term n) = 0 then
              REWRITE_RULE[definition `list` `LENGTH`]
    	    	 (ISPECL[n;hd w] PWORDLEN_DEF)
    	    else
              REWRITE_RULE[]
    	      (CONV_RULE ((RAND_CONV o RAND_CONV) LENGTH_CONV)
                (ISPECL[n;(hd w)]PWORDLEN_DEF))));
    	 (`WSEG`,   (\tms n w.
    	    let prove_less_eq m n = 
    	    let th = LESS_EQ_CONV
    	     (mk_comb(mk_comb("$<=", (term_of_int m)), (term_of_int n))) in
    	    if (m > n) then EQF_ELIM th else EQT_ELIM th in
    	    let [m;k;wd] =  w in
    	    MP (CONV_RULE
    	        ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)ADD_CONV)
    	        (SPECL [m;k] (word_inst_thm ((hd tms), wd) 
    	    	 (theorem `word_base` `WSEG_PWORDLEN`))))
       	       (prove_less_eq ((int_of_term m) + (int_of_term k))
    	    	    (int_of_term (hd  tms)))) );
    	 (`WNOT`,  (\tms n w.
    	    word_inst_thm (n, (hd w)) WNOT_PWORDLEN) );
    	 (`WAND`, (\tms n w.
    	    (RESQ_SPECL w (SPEC n WAND_PWORDLEN)))  );
    	 (`WOR`,  (\tms n w.
    	    (RESQ_SPECL w (SPEC n WOR_PWORDLEN)))  );
    	 (`WXOR`, (\tms n w.
    	    (RESQ_SPECL w (SPEC n WXOR_PWORDLEN)))  );
         (`WCAT`, (\tms n w.
    	    let w1, w2 = dest_pair (hd w) in
    	    let n1 = hd tms and n2 = hd(tl tms) in
    	    let N1 = int_of_term n1 and N2 = int_of_term n2 in
     	    (if not((int_of_term n) = (N1 + N2))
     	     then failwith `theorems and term do not match`
     	     else 
    	     (CONV_RULE ((RATOR_CONV o RAND_CONV)ADD_CONV)
    	      (itlist word_inst_thm [(n2,w2); (n1,w1)]
    	    	(theorem `word_base` `WCAT_PWORDLEN`))))) )
    	 ];;

let check s = assert (\x. fst(dest_const x) = s) ;;

let pick_fn s l op = 
    	let ops = fst (dest_const op) in
         snd (find (\(s,t). (s = ops)) l) 
    	 ? failwith s ;;

let PWORDLEN_CONV =
  \tms tm.
    (let _,[n;w'] = ((check `PWORDLEN`) # I) (strip_comb tm) in
    let wc,w = strip_comb w' in
    let fn = pick_fn `unknown constant` pwordlen_funs wc in
    EQT_INTRO(fn tms n w))  ?\s failwith (`PWORDLEN_CONV: `^s);;

% --------------------------------------------------------------------- %
% PWORDLEN_bitop_CONV : conv						%
% PWORDLEN_bitop_CONV tms "PWORDLEN n tm" returns a theorem		%
% A |- PWORDLEN n tm	    	    					%
% The input term tm should be in the following form:			%
%  WNOT tm' 	    PWORDLEN n vi,... |- PWORDLEN n (WNOT tm')		%
%  WAND tm' tm''    PWORDLEN n vi,... |- PWORDLEN n (WAND tm' tm'')	%
%  WOR tm' tm''     PWORDLEN n vi,... |- PWORDLEN n (WOR tm' tm'')	%
%  WXOR tm' tm''    PWORDLEN n vi,... |- PWORDLEN n (WXOR tm' tm'')	%
% where the vi's are variables in tm'.					%
% --------------------------------------------------------------------- %

letrec PWORDLEN_bitop_CONV tm =
    (let pw,w' = dest_comb tm in
     let _,n = ((check `PWORDLEN`) # I) (dest_comb pw) in
     if (is_var w') then (ASSUME tm)
     else
        (let wc,w = strip_comb w' in
    	 let thm1 = GQSPECL (n . w)
    	    (pick_fn `unknown bitop` pwordlen_bitop_funs wc) in
         EQT_INTRO
    	  (itlist PROVE_HYP (map PWORDLEN_bitop_CONV (hyp thm1)) thm1)))
    ?\s failwith (`PWORDLEN_bitop_CONV: `^s);;
    
% --------------------------------------------------------------------- %
% WSEG_WSEG_CONV "N" "WSEG m2 k2 (WSEG m1 k1 w)" --->			%
% PWORDLEN N w |- WSEG m2 k2 (WSEG m1 k1 w) = WSEG m2 k w			%
%   where k = k1 + k2 and k1+m1 <= N /\ k2+m2 <= m1			%
%   and N, k1, k2, m1,m2 are all constants				%
% --------------------------------------------------------------------- %

let WSEG_WSEG_CONV = 
    let check s = assert (\x. fst(dest_const x) = s) in
    let thm' = theorem `word_base` `WSEG_WSEG` in
    let add_less_eq_conv k m n =
    	(((RATOR_CONV o RAND_CONV) ADD_CONV) THENC LESS_EQ_CONV)
    	(mk_comb(mk_comb("<=", (mk_comb(mk_comb("$+", k), m))), n)) in
  \N tm.
    let _,[m2;k2;s] = ((check `WSEG`) # I) (strip_comb tm) in
    let _,[m1;k1;w] = ((check `WSEG`) # I) (strip_comb s) in
    let thm = GQSPECL [N; w; m1; k1; m2; k2] thm' in
    (RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) ADD_CONV) 
    (MP thm (CONJ (EQT_ELIM (add_less_eq_conv k1 m1 N))
    	    	 (EQT_ELIM (add_less_eq_conv k2 m2 m1)))));;

(PWORDLEN_CONV, PWORDLEN_bitop_CONV, WSEG_WSEG_CONV);;
end_section `PWORDLEN_CONV`;;

let (PWORDLEN_CONV, PWORDLEN_bitop_CONV, WSEG_WSEG_CONV) = it;;


% --------------------------------------------------------------------- %
% PWORDLEN_TAC = -: term list -> tactic					%
%      A ?- PWORDLEN n tm   	    					%
%    ========================== PWORDLEN_TAC l				%
%      A, A' ?- PWORDLEN n tm'	    					%
% The input list is the same as PWORDLEN_CONV.				%
% let th = PWORDLEN_CONV l "PWORDLEN n tm"				%
%        = A' |- PWORDLEN n tm	    					%
% It solves the goal if all the hypotheses of th (ie. A') are already 	%
% in A, otherwise, returns the above subgoal.				%
% --------------------------------------------------------------------- %

let PWORDLEN_TAC l =
  \(asm,gl). let th = EQT_ELIM(PWORDLEN_CONV l gl) in
    let hyps = hyp th in
    if (null hyps)
    then ((ACCEPT_TAC th) (asm,gl))
    else (
      let mlist = 
    	mapfilter (\h. if not(mem h asm) then h else fail) hyps in
      if null mlist then ((ACCEPT_TAC th) (asm,gl))
      else (
        let sgl = list_mk_conj mlist in
    	(SUBGOAL_THEN sgl STRIP_ASSUME_TAC THENL[
    	 REPEAT CONJ_TAC; ACCEPT_TAC th]) (asm,gl)));;
