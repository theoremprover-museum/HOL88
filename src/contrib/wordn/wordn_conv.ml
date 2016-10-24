% ===================================================================== %
% FILE		: wordn_CONV.ml						%
% DESCRIPTION   : Definition-scheme for wordn constants.                %
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 90.08.20						%
% ===================================================================== %

% ===================================================================== %
% wordn_CONV : definition scheme for wordn constants.                   %
%                                                                       %
% wordn_CONV "#b1...bn" returns |- #b1...bn = WORDn [b1;...;bn]         %
% ===================================================================== %

let wordn_CONV = 
    let Nil = "NIL:(bool)list" in
    let Cons = let C = "CONS:bool->(bool)list->(bool)list" in 
               let T = "T" and F = "F" in
               let bool s = (s=`1` => T | (s=`0` => F | fail)) in
                   \h t. mk_comb(mk_comb(C,bool h),t) in
    let Wordn = let lty = ":bool list" in
                \n ty. mk_const(`WORD` ^ n,mk_type(`fun`,[lty;ty])) in
    \tm. (let (hash.bits),ty = (explode # I) (dest_const tm) in
          if (not (hash = `#`)) then fail else
          let list = itlist Cons bits Nil in
          let size = string_of_int(length bits) in
              mk_thm([],mk_eq(tm,mk_comb(Wordn size ty,list)))) ? 
         failwith `wordn_CONV`;;

% ===================================================================== %
% Exhaustive cases theorem for wordn constants		        	%
%                                                                       %
% prove_wordn_const_cases: derives an exhaustive cases theorem for      %
% constants of type :wordn.  Use only for small n.                      %
%                                                                       %
% The input is a theorem of the form returned by prove_word_cases_thm:  %
%                                                                       %
%    |- !w. ?b0...bn-1. w = WORDn [b0;...;bn-1] 			%
%                                                                       %
% The corresponding output has the form: 			        %
%                                                                       %
%    |- !w. ((w = #0...0) \/ ...)  \/ (... \/ w = #1...1)               %
%                                                                       %
% For example, the output for :word2 is:                                %
%                                                                       %
%    |- !w. ((w = #00) \/ (w = #01)) \/ ((w = #10) \/ (w = #11))        %
% ===================================================================== %

let prove_wordn_const_cases = 
    let b = genvar ":bool" and T = "T" and F = "F" in
    let cth = ONCE_REWRITE_RULE [DISJ_SYM] (SPEC b BOOL_CASES_AX) in
    let mkcase v th =
        let th1 = SUBST [ASSUME (mk_eq(v,F)),v] (concl th) th and
            th2 = SUBST [ASSUME (mk_eq(v,T)),v] (concl th) th in
        let dth1 = DISJ1 th1 (concl th2) and dth2 = DISJ2 (concl th1) th2 in
            DISJ_CASES (INST [v,b] cth) dth1 dth2 in
    let num ty st = SYM(wordn_CONV(mk_const(`#` ^ st,ty))) in
    letrec mkcases ty st vs th =
       if (null vs) then (TRANS th (num ty st)) else
       let cth = mkcase (hd vs) th in
       let d1,d2 = (ASSUME # ASSUME) (dest_disj(concl cth)) in
       let th1 = mkcases ty (st ^ `0`) (tl vs) d1 and
           th2 = mkcases ty (st ^ `1`) (tl vs) d2 in
           DISJ_CASES_UNION cth th1 th2 in
    let efn v th = 
        let [hy] = hyp th in CHOOSE (v,ASSUME (mk_exists(v,hy))) th in
    \th. (let w,vs,eq = (I # strip_exists) (dest_forall (concl th)) in
          let cases = mkcases (type_of w) `` vs (ASSUME eq) in
              GEN w (PROVE_HYP (SPEC w th) (itlist efn vs cases)))
          ? failwith `prove_wordn_const_cases`;;

% ===================================================================== %
% Equality of wordn constants.                                          %
% ===================================================================== %

let wordn_EQ_CONV = 
    let Nil = "NIL:(bool)list" in
    let Cons = let C = "CONS:bool->(bool)list->(bool)list" in 
               \h t. mk_comb(mk_comb(C,h),t) in
    let genvs =
        let boolty = ":bool" in
        let mkvar i = mk_primed_var(`b` ^ string_of_int i,boolty) in
        letrec gvs n i = ((i=n) => [] | mkvar i . (gvs n (i+1))) in
        \n. gvs n 0 in
    \th. let ooth = prove_WORD_one_one th ? 
                    failwith `wordn_EQ_CONV: invalid input theorem` in
         let len = rand(lhs(snd(dest_forall(rand (concl th))))) in
         let vs = genvs (int_of_string (fst(dest_const len))) in
         let vs' = map (variant vs) vs in
         let l1 = itlist Cons vs Nil and l2 = itlist Cons vs' Nil in
         let spec = SPEC l2 (SPEC l1 ooth) in
         let eq1,eq2 = (lhs # lhs) (dest_conj (rand(rator (concl spec)))) in
         let oth = MP spec (CONJ (LENGTH_CONV eq1) (LENGTH_CONV eq2)) in
         \tm. (let l,r = (wordn_CONV # wordn_CONV) (dest_eq tm) in
               if (lhs tm = rhs tm) then EQT_INTRO (REFL (lhs tm)) else
               let l1,l2 = ((rand o rand)#(rand o rand)) (concl l,concl r) in
               let leq = list_EQ_CONV bool_EQ_CONV (mk_eq(l1,l2)) in
               let ilst = fst(match (rand(concl oth)) (mk_eq(l1,l2))) in
               let fth = EQ_MP leq (UNDISCH (INST ilst oth)) in
               let neq = let [hy] = hyp fth in NOT_INTRO(DISCH hy fth) in
               let eqth = MK_COMB(AP_TERM(rator(rator tm))l,r) in
                  TRANS eqth (EQF_INTRO neq))
              ? failwith `wordn_EQ_CONV`;;



