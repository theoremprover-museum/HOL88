%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        num.ml                                                %
%                                                                             %
%     DESCRIPTION:      Derived rules/tactics for :num.  Assumes that theorems%
%                       from arithmetic.th are already loaded.                %
%                                                                             %
%                       Provied for compatibility with old HOL:               %
%                          - INDUCT_TAC                                       %
%                          - new_prim_rec_definition                          %
%                          - new_infix_prim_rec_definition                    %
%                                                                             %
%     AUTHOR:           MJCG and TFM                                          %
%                                                                             %
%     USES FILES:       ind.ml, prim_rec.ml, numconv.ml                       %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

if compiling then (loadf `ml/ind`;loadf `ml/prim_rec`;loadf `ml/numconv`);;


% --------------------------------------------------------------------- %
% INDUCT: (thm # thm) -> thm                                            %
%                                                                       %
%   A1 |- t[0]      A2 |- !n. t[n] ==> t[SUC n]                         %
% -----------------------------------------------                       %
%             A1 u A2 |- !n. t[n]                                       %
% --------------------------------------------------------------------- %

let INDUCT =
    let INDUCTION = theorem `num` `INDUCTION` in
    \(base,step).
     (let n,body = dest_forall(concl step) in
      let assm,conc = dest_imp body in
      let P  = "\^n.^assm" and
          v1 = genvar bool_ty and
          v2 = genvar bool_ty in
     let base'  = EQ_MP (SYM(BETA_CONV "^P 0")) base and
         step'  = SPEC n step and
         hypth  = SYM(RIGHT_BETA(REFL "^P ^n")) and
         concth = SYM(RIGHT_BETA(REFL "^P(SUC ^n)")) and
         IND    = SPEC P INDUCTION in
     let th1 = SUBST [hypth,v1;concth,v2]
                     "^(concl step') = (^v1 ==> ^v2)"
                     (REFL (concl step')) in
     let th2 = GEN n (EQ_MP th1 step') in
     let th3 = SPEC n (MP IND (CONJ base' th2)) in
         GEN n (EQ_MP (BETA_CONV(concl th3)) th3)) ? failwith`INDUCT`;;

% --------------------------------------------------------------------- %
%             [A] !n.t[n]                                               %
%  ================================                                     %
%   [A] t[0]  ,  [A,t[n]] t[SUC x]                                      %
% --------------------------------------------------------------------- %

let INDUCT_TAC =
    let INDUCTION = theorem `num` `INDUCTION` in
    let tac = INDUCT_THEN INDUCTION ASSUME_TAC in
        \g. tac g ? failwith `INDUCT_TAC`;;

% --------------------------------------------------------------------- %
% For compatibility of new/old HOL.                                     %
% --------------------------------------------------------------------- %

let new_prim_rec_definition =
    let num_Axiom = theorem `prim_rec` `num_Axiom` in
        \(name,tm). new_recursive_definition false num_Axiom name tm;;

let new_infix_prim_rec_definition =
    let num_Axiom = theorem `prim_rec` `num_Axiom` in
        \(name,tm). new_recursive_definition true num_Axiom name tm;;

% --------------------------------------------------------------------- %
% ADD_CONV: addition of natural number constants (numerals).            %
%                                                                       %
% If n and m are numerals (i.e 0,1,2,3,...) then:                       %
%                                                                       %
%      ADD_CONV "n + m"                                                 %
%                                                                       %
% returns                                                               %
%                                                                       %
%      |- n + m = s                                                     %
%                                                                       %
% where s is the numeral denoting the sum of n and m.                   %
%                                                                       %
% NOTE: iterative version.                                              %
% --------------------------------------------------------------------- %

let ADD_CONV =
    let nv = "n:num" and mv = "m:num" and numty = ":num" in
    let asym = SPECL [nv;mv] (theorem `arithmetic` `ADD_SYM`) in
    let Sth = let addc = theorem `arithmetic` `ADD_CLAUSES` in
              let t1,t2 = CONJ_PAIR (CONJUNCT2(CONJUNCT2 addc)) in
                  (TRANS t1 (SYM t2)) in
    let ladd0 = let addc = theorem `arithmetic` `ADD_CLAUSES` in
                    GEN "n:num" (CONJUNCT1 addc) in
    let v1 = genvar ":num" and v2 = genvar ":num" in
    let int_of_tm tm = int_of_string(fst(dest_const tm)) and
        tm_of_int i  = mk_const(string_of_int i,numty) in
    let mk_pat =
        let pl = "$+" in
        let lra = mk_comb(pl,v1) in
        \(n,m). mk_eq(mk_comb(lra,m),mk_comb(mk_comb(pl,n),v2)) in
    let trans (c,mi) th =
        let n,m = (rand # I) (dest_comb(rand (concl th))) in
        let nint = tm_of_int c and mint = tm_of_int mi in
        let nth = SYM(num_CONV n) and mth = SYM(num_CONV mint) in
        let thm1 = INST [nint,mv;m,nv] Sth in
            (SUBST [nth,v1;mth,v2] (mk_pat(nint,m)) thm1) in
    let zconv = RAND_CONV(REWR_CONV ladd0) in
    let conv th (n,m) =
        letref thm,count,mint = th,n,m in
        if (count=0)
           then CONV_RULE zconv thm
           loop (count := count - 1 ;
                 mint := mint + 1;
                 thm := TRANS thm (trans (count,mint) thm)) in
    \tm. (let c,[n;m] = (assert (\c.c="+") # I) (strip_comb tm) in
          let nint = int_of_tm n and mint = int_of_tm m in
          if not(mint < nint) then conv (REFL tm) (nint,mint) else
             let th1 = conv (REFL(mk_comb(mk_comb(c,m),n))) (mint,nint) in
                 TRANS (INST [n,nv;m,mv] asym) th1) ?
         failwith `ADD_CONV`;;

% --------------------------------------------------------------------- %
% num_EQ_CONV: equality of natural number constants.                    %
%                                                                       %
% If n and m are numerals (i.e 0,1,2,3,...) or sucessors of numerals    %
% (e.g. SUC 0, SUC(SUC 2), etc), then:                                  %
%                                                                       %
%      num_EQ_CONV "n = m"                                              %
%                                                                       %
% returns                                                               %
%                                                                       %
%      |- (n = m) = T           if n=m                                  %
%      |- (n = m) = F           if ~(n=m)                               %
%                                                                       %
% and if n and m are syntactically identical terms of type :num, then   %
%                                                                       %
%      num_EQ_CONV "n = m"  returns |- (n = m) = T                      %
%                                                                       %
% NOTE: runs out of stack for large numbers.                            %
%									%
% Fixed Bug: 5 May 1993, TFM.						%
% --------------------------------------------------------------------- %

let num_EQ_CONV =
    let nv = genvar ":num" and mv = genvar ":num" in
    let rth = SPEC nv (theorem `prim_rec` `LESS_SUC_REFL`) and
        lnth = SPECL [nv;mv] (theorem `prim_rec` `LESS_NOT_EQ`) and
        lmth = SPECL [nv;mv] (theorem `prim_rec` `LESS_MONO`) and
        lz = SPEC  nv (theorem `prim_rec` `LESS_0`) in
    let checkty = assert (\t. type_of t = ":num") in
    let check = let tm = "SUC" in assert (\t. t = tm) in
    let Suc = AP_TERM "SUC" in
    let int_of_tm tm = int_of_string(fst(dest_const tm)) in
    letrec val n = (int_of_tm n) ? val (snd((check # I) (dest_comb n)))+1 in
    let mk_pat = let less = "$<" in \n. mk_comb(mk_comb(less,n),mv) in
    let mk_pat2 = let less = "$<" in \m. mk_comb(mk_comb(less,nv),m) in
    letrec eqconv n m =
       if (n=m) then REFL n else
       if (is_const n) then
           let th = num_CONV n in
               TRANS th (eqconv (rand(concl th)) m) else
       if (is_const m) then
           let th = num_CONV m in
               TRANS (eqconv n (rand(concl th))) (SYM th) else
       Suc (eqconv (rand n) (rand m)) in
    letrec neqconv n m =
       if (is_const m) then
            let th = num_CONV m in
            let thm = (neqconv n (rand(concl th))) in
                SUBST [SYM th,mv] (mk_pat n) thm else
       let m' = rand m in
       if (n=m') then INST [n,nv] rth else
       if (is_const n) then
           if (n="0") then INST [m',nv] lz else
           let th = num_CONV n in
           let n' = rand(rand(concl th)) in
           let th2 = MP (INST [n',nv;m',mv] lmth) (neqconv n' m') in
               SUBST [SYM th,nv] (mk_pat2 m) th2 else
       let n' = rand n in
           MP (INST [n',nv;m',mv] lmth) (neqconv n' m') in
    \tm. (let n,m = (checkty # I) (dest_eq tm) in
          if (n=m) then EQT_INTRO (REFL n) else
          let nint = val n and mint = val m in
          if (mint=nint) then EQT_INTRO(eqconv n m) else
          if (nint<mint) then
             let thm = INST [n,nv;m,mv] lnth in
                 EQF_INTRO (MP thm (neqconv n m)) else
             let thm = INST [m,nv;n,mv] lnth in
             let thm2 = MP thm (neqconv m n) in
                 EQF_INTRO(NOT_EQ_SYM thm2)) ?
         failwith `num_EQ_CONV`;;


% --------------------------------------------------------------------- %
% EXISTS_LEAST_CONV: applies the well-ordering property to non-empty    %
% sets of numbers specified by predicates.                              %
%                                                                       %
% A call to EXISTS_LEAST_CONV "?n:num. P[n]" returns:                   %
%                                                                       %
%   |- (?n. P[n]) = ?n. P[n] /\ !n'. (n' < n) ==> ~P[n']                %
%                                                                       %
% --------------------------------------------------------------------- %

let EXISTS_LEAST_CONV =
    let wop = theorem `arithmetic` `WOP` in
    let wth = CONV_RULE (ONCE_DEPTH_CONV ETA_CONV) wop in
    let check = let ty = ":num" in assert (\tm. type_of tm = ty) in
    let acnv = RAND_CONV o ABS_CONV in
    \tm. (let n,P = (check # I) (dest_exists tm) in
          let thm1 = UNDISCH (SPEC (rand tm) wth) in
          let thm2 = CONV_RULE (GEN_ALPHA_CONV n) thm1 in
          let c1,c2 = dest_comb (snd(dest_exists(concl thm2))) in
          let bth1 = RAND_CONV BETA_CONV c1 in
          let bth2 = acnv (RAND_CONV (RAND_CONV BETA_CONV)) c2 in
          let n' = variant (n. frees tm) n in
          let abth2 = CONV_RULE (RAND_CONV (GEN_ALPHA_CONV n')) bth2 in
          let thm3 = EXISTS_EQ n (MK_COMB(bth1,abth2)) in
          let imp1 = DISCH tm (EQ_MP thm3 thm2) in
          let eltm = rand(concl thm3) in
          let thm4 = CONJUNCT1 (ASSUME (snd(dest_exists eltm))) in
          let thm5 = CHOOSE (n,ASSUME eltm) (EXISTS (tm,n) thm4) in
              IMP_ANTISYM_RULE imp1 (DISCH eltm thm5)) ?
         failwith `EXISTS_LEAST_CONV`;;

%---------------------------------------------------------------------------%
% EXISTS_GREATEST_CONV - Proves existence of greatest element satisfying P. %
%                                                                           %
% EXISTS_GREATEST_CONV "(?x. P[x]) /\ (?y. !z. z > y ==> ~(P[z]))" =        %
%    |- (?x. P[x]) /\ (?y. !z. z > y ==> ~(P[z])) =                         %
%        ?x. P[x] /\ !z. z > x ==> ~(P[z])                                  %
%                                                                           %
% If the variables x and z are the same, the "z" instance will be primed.   %
% [JRH 91.07.17]                                                            %
%---------------------------------------------------------------------------%

let EXISTS_GREATEST_CONV =
  let LESS_EQ' = theorem `arithmetic` `LESS_EQ`
  and LESS_EQUAL_ANTISYM' = theorem `arithmetic` `LESS_EQUAL_ANTISYM`
  and NOT_LESS' = theorem `arithmetic` `NOT_LESS`
  and LESS_SUC_REFL' = theorem `prim_rec` `LESS_SUC_REFL`
  and LESS_0_CASES' = theorem `arithmetic` `LESS_0_CASES`
  and NOT_LESS_0' = theorem `prim_rec` `NOT_LESS_0`
  and num_CASES' = theorem `arithmetic` `num_CASES`
  and GREATER' = definition `arithmetic` `GREATER` in
  let EXISTS_GREATEST = PROVE
   ("!P.(?x. P x) /\ (?x. !y. y > x ==> ~P y) = ?x. P x /\ !y. y > x ==> ~P y",
    GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC[GREATER'] THEN DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN "g:num" MP_TAC o CONV_RULE EXISTS_LEAST_CONV)) THEN
      DISCH_THEN (\th. EXISTS_TAC "g:num" THEN REWRITE_TAC[th] THEN MP_TAC th)
      THEN STRUCT_CASES_TAC (SPEC "g:num" num_CASES') THENL
       [REWRITE_TAC[NOT_LESS_0'] THEN DISCH_THEN (MP_TAC o SPEC "x:num") THEN
        DISJ_CASES_TAC (SPEC "x:num" LESS_0_CASES');
        POP_ASSUM (K ALL_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2
        (MP_TAC o REWRITE_RULE[] o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV))
        (X_CHOOSE_TAC "y:num" o REWRITE_RULE[NOT_IMP] o CONV_RULE
        NOT_FORALL_CONV o REWRITE_RULE[LESS_SUC_REFL'] o SPEC "n:num")) THEN
        DISCH_THEN (MP_TAC o SPEC "y:num") THEN ASM_REWRITE_TAC[NOT_LESS'] THEN
        POP_ASSUM (CONJUNCTS_THEN2 (\th. DISCH_THEN (SUBST1_TAC o MATCH_MP
        LESS_EQUAL_ANTISYM' o CONJ (REWRITE_RULE[LESS_EQ'] th))) ASSUME_TAC)];
      DISCH_THEN CHOOSE_TAC THEN CONJ_TAC THEN EXISTS_TAC "x:num"]
    THEN ASM_REWRITE_TAC[]) in
 let t = RATOR_CONV and n = RAND_CONV and b = ABS_CONV in
 let red1 = t o n o t o n o n o b and red2 = t o n o n o n o b o n o b o n o n
 and red3 = n o n o b o t o n and red4 = n o n o b o n o n o b o n o n in
 \tm. (let (lc,rc) = dest_conj tm in let pred = rand lc in
       let (xv,xb) = dest_exists lc in let (yv,yb) = dest_exists rc in
       let zv = fst (dest_forall yb) in
       let prealpha = CONV_RULE (red1 BETA_CONV THENC red2 BETA_CONV THENC
          red3 BETA_CONV THENC red4 BETA_CONV) (SPEC pred EXISTS_GREATEST) in
       let rqd = mk_eq(tm,mk_exists(xv,mk_conj(xb,subst[(xv,yv)] yb))) in
       S (C EQ_MP) (C ALPHA rqd o concl) prealpha)
      ? failwith `EXISTS_GREATEST_CONV`;;

%---------------------------------------------------------------------------%
% A couple of useful function for converting between  ML integers and 	    %
% numeric terms, e.g., "2" <---> 2  					    %
%---------------------------------------------------------------------------%

let term_of_int =  
      \n. mk_const(string_of_int n, mk_type(`num`,[])) ;;

let int_of_term = int_of_string o fst o dest_const ;;

