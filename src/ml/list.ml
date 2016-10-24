%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        list.ml                                               %
%                                                                             %
%     DESCRIPTION:      Defined procedures for list induction and definition  %
%                       by primitive recursion on lists.  Derived inference   %
%                       rules for reasoning about lists.                      %
%                                                                             %
%                       The induction/primitive recursion are really only for %
%                       compatibility with old HOL.                           %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.05.30)                               %
%                       W. Wong (31 Jan 94)                                   %
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
%     COPYRIGHT:        T. F. Melham 1987 1990                                %
%                                                                             %
%     REVISION HISTORY: 90.09.08                                              %
%=============================================================================%

if compiling then
    (loadf `../ml/ind`;
     loadf `../ml/prim_rec`;
     loadf `../ml/numconv`;
     loadf `../ml/num`);;

% --------------------------------------------------------------------- %
%   LIST_INDUCT: (thm # thm) -> thm                                     %
%                                                                       %
%     A1 |- t[[]]      A2 |- !tl. t[tl] ==> !h. t[CONS h t]             %
% ----------------------------------------------------------            %
%                   A1 u A2 |- !l. t[l]                                 %
%                                                                       %
% --------------------------------------------------------------------- %

let LIST_INDUCT =
    let list_INDUCT = theorem `list` `list_INDUCT` in
    \(base,step).
     (let (tl,body) = dest_forall(concl step) in
      let (asm,h,con) = (I # dest_forall) (dest_imp body) in
      let P  = "\^tl.^asm" and
          b1 = genvar bool_ty and
          b2 = genvar bool_ty in
      let base'  = EQ_MP (SYM(BETA_CONV "^P []")) base and
          step'  = DISCH asm (SPEC h (UNDISCH(SPEC tl step))) and
          hypth  = SYM(RIGHT_BETA(REFL "^P ^tl")) and
          concth = SYM(RIGHT_BETA(REFL "^P(CONS ^h ^tl)")) and
          IND    = SPEC P (INST_TYPE [type_of h,":*"] list_INDUCT) in
      let th1 = SUBST [hypth,b1;concth,b2]
                      "^(concl step') = (^b1 ==> ^b2)"
                      (REFL (concl step')) in
      let th2 = GEN tl (DISCH "^P ^tl" (GEN h(UNDISCH (EQ_MP th1 step')))) in
      let th3 = SPEC tl (MP IND (CONJ base' th2)) in
          GEN tl (EQ_MP (BETA_CONV(concl th3)) th3))?failwith `LIST_INDUCT`;;

% --------------------------------------------------------------------- %
%                                                                       %
% LIST_INDUCT_TAC                                                       %
%                                                                       %
%             [A] !l.t[l]                                               %
%  ================================                                     %
%   [A] t[[]],  [A,t[l]] !h. t[CONS h t]                                %
%                                                                       %
% --------------------------------------------------------------------- %

let LIST_INDUCT_TAC  =
    let list_INDUCT = theorem `list` `list_INDUCT` in
        INDUCT_THEN list_INDUCT ASSUME_TAC;;

% --------------------------------------------------------------------- %
%                                                                       %
% SNOC_INDUCT_TAC                                                       %
%                                                                       %
%             [A] !l.t[l]                                               %
%  ================================                                     %
%   [A] t[[]],  [A,t[l]] !h. t[SNOC x t]                                %
%                                                                       %
% --------------------------------------------------------------------- %
let SNOC_INDUCT_TAC  =
    let SNOC_INDUCT = theorem `list` `SNOC_INDUCT` in
        INDUCT_THEN SNOC_INDUCT ASSUME_TAC;;

% ------------------------------------------------------------------------- %
% EQ_LENGTH_INDUCT_TAC : tactic                                             %
%  A ?- !l1 l2. (LENGTH l1 = LENGTH l2) ==> t[l1, l2]                       %
% ==================================================== EQ_LENGTH_INDUCT_TAC %
%  A                       ?- t[ []/l1, []/l2 ]                             %
%  A,LENGTH l1 = LENGTH l2 ?- t[(CONS h l1)/l1,(CONS h' l2)/l2]             %
% ------------------------------------------------------------------------- %

let EQ_LENGTH_INDUCT_TAC =
    let SUC_NOT = theorem `arithmetic` `SUC_NOT` and
        NOT_SUC = theorem `num` `NOT_SUC` and
        INV_SUC_EQ = theorem `prim_rec` `INV_SUC_EQ` and
        LENGTH = definition `list` `LENGTH` in
    LIST_INDUCT_TAC THENL[
     LIST_INDUCT_TAC THENL[
      REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (\t.ALL_TAC);
      REWRITE_TAC[LENGTH;SUC_NOT]];
     GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH;NOT_SUC;INV_SUC_EQ]
     THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];;

% ------------------------------------------------------------------------- %
% EQ_LENGTH_SNOC_INDUCT_TAC : tactic                                        %
% A ?- !l1 l2.(LENGTH l1 = LENGTH l2) ==> t[l1,l2]                          %
% =============================================== EQ_LENGTH_SNOC_INDUCT_TAC %
%  A                       ?- t[ []/l1, []/l2 ]                             %
%  A,LENGHT l1 = LENGTH l2 ?- t[(SNOC h l1)/l1,(SNOC h' l2)/l2]             %
% ------------------------------------------------------------------------- %

let EQ_LENGTH_SNOC_INDUCT_TAC =
    let SUC_NOT = theorem `arithmetic` `SUC_NOT` and
        NOT_SUC = theorem `num` `NOT_SUC` and
        INV_SUC_EQ = theorem `prim_rec` `INV_SUC_EQ` and
        LENGTH = definition `list` `LENGTH` and
        LENGTH_SNOC = theorem `list` `LENGTH_SNOC` in
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (\t.ALL_TAC);
      REWRITE_TAC[LENGTH;LENGTH_SNOC;SUC_NOT]];
     GEN_TAC THEN SNOC_INDUCT_TAC
     THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;NOT_SUC;INV_SUC_EQ]
     THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];;

% --------------------------------------------------------------------- %
% Definition by primitive recursion for lists                           %
% (For compatibility of new/old HOL.)                                   %
% --------------------------------------------------------------------- %

let new_list_rec_definition =
    let list_Axiom = theorem `list` `list_Axiom` in
        \(name,tm). new_recursive_definition false list_Axiom name tm;;

let new_infix_list_rec_definition =
    let list_Axiom = theorem `list` `list_Axiom` in
        \(name,tm). new_recursive_definition true list_Axiom name tm;;

% --------------------------------------------------------------------- %
% LENGTH_CONV: compute the length of a list                             %
%                                                                       %
% A call to LENGTH_CONV "LENGTH[x1;...;xn]" returns:                    %
%                                                                       %
%    |- LENGTH [x1;...;xn] = n   where n is a numeral constant          %
% --------------------------------------------------------------------- %

let LENGTH_CONV =
    let LEN = definition `list` `LENGTH` in
    let dcons tm = snd(((\c.fst(dest_const c)=`CONS`) # I)(strip_comb tm)) in
    let cend tm = (fst(dest_const tm) = `NIL` => [] | fail) in
    letrec stripl tm = (let [h;t] = dcons tm in (h . stripl t)) ? cend tm in
    let SUC = let suctm  = "SUC" and numty = ":num" in
              \(i,th). let n = mk_const(string_of_int i,numty) in
                       TRANS (AP_TERM suctm th) (SYM(num_CONV n)) in
    let itfn cth h (i,th) =
        i+1,TRANS (SPEC (rand(lhs(concl th))) (SPEC h cth)) (SUC (i,th)) in
    let check = assert(curry $= `LENGTH` o fst o dest_const) in
    \tm. (let _,[ty] = dest_type(type_of (snd((check # I)(dest_comb tm)))) in
          let nil,cons = CONJ_PAIR (INST_TYPE [ty,":*"] LEN) in
              snd(itlist (itfn cons) (stripl (rand tm)) (1,nil)))
          ? failwith `LENGTH_CONV`;;

% --------------------------------------------------------------------- %
% list_EQ_CONV: equality of lists.                                      %
%                                                                       %
% This conversion proves or disproves the equality of two lists, given  %
% a conversion for deciding the equality of elements.                   %
%                                                                       %
% A call to:                                                            %
%                                                                       %
%    list_EQ_CONV conv "[x1;...;xn] = [y1;...;ym]"                      %
%                                                                       %
% returns:                                                              %
%                                                                       %
%    |- ([x1;...;xn] = [y1;...;ym]) = F                                 %
%                                                                       %
% if:                                                                   %
%                                                                       %
%    1: ~(n=m)  or 2: conv proves |- (xi = yi) = F for any 1<=i<=n,m    %
%                                                                       %
% and:                                                                  %
%                                                                       %
%   |- ([x1;...;xn] = [y1;...;ym]) = T                                  %
%                                                                       %
% if:                                                                   %
%                                                                       %
%    1: (n=m) and xi is syntactically identical to yi for 1<=i<=n,m, or %
%    2: (n=m) and conv proves  |- (xi=yi)=T for 1<=i<=n,m               %
% --------------------------------------------------------------------- %

let list_EQ_CONV =
    let T = "T" and F = "F" in
    let cnil = theorem `list` `NOT_CONS_NIL` in
    let lne = theorem `list` `LIST_NOT_EQ` in
    let nel = theorem `list` `NOT_EQ_LIST`in
    let leq = theorem `list` `EQ_LIST` in
    let dcons tm = snd(((\c.fst(dest_const c)=`CONS`) # I)(strip_comb tm)) in
    let cend tm = (fst(dest_const tm) = `NIL` => [] | fail) in
    letrec stripl tm = (let [h;t] = dcons tm in (h . stripl t)) ? cend tm in
    let Cons ty = let lty = mk_type(`list`,[ty]) in
                  let cty = mk_type(`fun`,[ty;mk_type(`fun`,[lty;lty])]) in
                  \h t. mk_comb(mk_comb(mk_const(`CONS`,cty),h),t) in
    let Nil ty = let lty = mk_type(`list`,[ty]) in mk_const(`NIL`,lty) in
    letrec split n l =
        if (n=0) then [],l else ((curry $. (hd l)) # I)(split (n-1) (tl l)) in
    let itfn cnv [leq;lne;nel] (h1,h2) th =
        if (is_neg (concl th)) then
           let l1,l2 = dest_eq(dest_neg (concl th)) in
               SPEC h2 (SPEC h1 (MP (SPEC l2 (SPEC l1 lne)) th)) else
           let l1,l2 = dest_eq(concl th) in
           let heq = cnv (mk_eq(h1,h2)) in
           if (rand(concl heq) = T) then
               let th1 = MP (SPEC h2 (SPEC h1 leq)) (EQT_ELIM heq) in
                    MP (SPEC l2 (SPEC l1 th1)) th else
               let th1 = MP (SPEC h2 (SPEC h1 nel)) (EQF_ELIM heq) in
                    SPEC l2 (SPEC l1 th1) in
    \cnv tm. (let l1,l2 = (stripl # stripl) (dest_eq tm) in
              if (l1=l2) then EQT_INTRO(REFL (rand tm)) else
              let _,[ty] = dest_type(type_of(rand tm)) in
              let n = length l1 and m = length l2 in
              let thms = map (INST_TYPE [ty,":*"]) [leq;lne;nel] in
              let ifn = itfn cnv thms in
              if (n<m) then
                 let exd,(x.xs) = split n l2 in
                 let rest = itlist (Cons ty) xs (Nil ty) in
                 let thm1 = SPEC rest (SPEC x (INST_TYPE [ty,":*"] cnil)) in
                 EQF_INTRO(itlist ifn (combine(l1,exd))(NOT_EQ_SYM thm1)) else
              if (m<n) then
                 let exd,(x.xs) = split m l1 in
                 let rest = itlist (Cons ty) xs (Nil ty) in
                 let thm1 = SPEC rest (SPEC x (INST_TYPE [ty,":*"] cnil)) in
                 EQF_INTRO(itlist ifn (combine(exd,l2)) thm1) else
             let thm = itlist ifn (combine(l1,l2)) (REFL (Nil ty)) in
                 (EQF_INTRO thm ? EQT_INTRO thm))
             ? failwith `list_EQ_CONV`;;

%--------------------------------------------------------------%
% Following local functions added by WW 31 Jan 94              %

begin_section `list_convs`;;

let check_const name const =
    if (name = (fst (dest_const const))) then true
    else failwith (`not `^name) ;;

let int_of_term = int_of_string o fst o dest_const;;

let term_of_int =  let ty = ":num" in
      \n. mk_const(string_of_int n, ty) ;;


%---------------------------------------------------------------------- %
% APPEND_CONV: this conversion maps terms of the form                   %
%                                                                       %
%   "APPEND [x1;...;xm] [y1;...;yn]"                                    %
%                                                                       %
% to the equation:                                                      %
%                                                                       %
% |- APPEND [x1;...;xm] [y1;...;yn] = [x1;...;xm;y1;...;yn]             %
%                                                                       %
% ADDED: TFM 91.10.26                                                   %
%---------------------------------------------------------------------- %


let APPEND_CONV =
    let th1,th2 = CONJ_PAIR (definition `list` `APPEND`) in
    let th3 = SPECL ["l1:(*)list";"l2:(*)list"] th2 in
    let th4 = GENL  ["l2:(*)list";"l1:(*)list"] th3 in
    let itfn (cns,ath) v th =
        let th1 = AP_TERM (mk_comb(cns,v)) th in
        let l = rand(rator(rand(rator(concl th)))) in
            TRANS (SPEC v (SPEC l ath)) th1 in
    \tm. (let _,[l1;l2] = ((check_const`APPEND`) # I) (strip_comb tm) in
          let els,ty = dest_list l1 in
          if (null els) then ISPEC l2 th1 else
          let cns = rator(rator l1) in
          let step = ISPEC l2 th4 and base = ISPEC l2 th1 in
              itlist (itfn (cns,step)) els base) ?
         failwith `APPEND_CONV`;;

% --------------------------------------------------------------------- %
% MAP_CONV conv "MAP f [e1;...;en]".                     [TFM 92.04.16] %
%                                                                       %
% Returns |- MAP f [e1;...;en] = [r1;...;rn]                            %
% where conv "f ei" returns |- f ei = ri for 1 <= i <= n                %
% --------------------------------------------------------------------- %

let MAP_CONV =
    let mn,mc = CONJ_PAIR(definition `list` `MAP`) in
    \conv tm.
     (let _,[fn;l] = ((check_const`MAP`) # I) (strip_comb tm) in
      let els,ty = dest_list l in
      let nth = ISPEC fn mn and cth = ISPEC fn mc in
      let cns = rator(rator(rand(snd(strip_forall(concl cth))))) in
      let APcons t1 t2 = MK_COMB(AP_TERM cns t2,t1) in
      let itfn e th =
          let t = rand(rand(rator(concl th))) in
          let th1 = SPEC t(SPEC e cth) in
              th1 TRANS (APcons th (conv (mk_comb(fn,e)))) in
      itlist itfn els nth) ? failwith `MAP_CONV`;;

%-==============================================================-%
%- CONVERSIONS added by WW 31 Jan 94                            -%
%-==============================================================-%

%----------------------------------------------------------------%
%- Reductions                                                   -%
%- FOLDR_CONV conv "FOLDR f e [a0;...an]" --->
    |- FOLDR f e [a0;...an] = tm
   FOLDR_CONV evaluates the input expression by iteratively apply
    the function f the successive element of the list starting from
    the end of the list. tm is the result of the calculation.
    FOLDR_CONV returns a theorem stating this fact. During each
    iteration, an expression "f e' ai" is evaluated. The user
    supplied conversion conv is used to derive a theorem
     |- f e' ai = e'' which is then used to reduce the expression
    to e''. For example,

   #FOLDR_CONV conv "FOLDR ^f 0 ([x0;x1;x2;x3;x4;x5]:* list)";;
   |- FOLDR(\x l'. SUC l')0[x0;x1;x2;x3;x4;x5] = 6

   where f = (\x l'. SUC l') and
      conv = ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC SUC_CONV))

   In general, if the function f is an explicit lambda abstraction
   (\x x'. t[x,x']), the conversion should be in the form
    ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))
   where conv' applied to t[x,x'] returns the theorem |-t[x,x'] = e''.

-%

let FOLDR_CONV  =
    let (bthm,ithm) = CONJ_PAIR (definition `list` `FOLDR`) in
  \conv tm.
    let (_,[f;e;l]) = ((check_const`FOLDR`)#I)(strip_comb tm) in
    let ithm' = ISPECL[f;e] ithm in
    let (els,lty) =  (dest_list l) in
    let itfn a th =
        let [f';e';l'] = snd(strip_comb(lhs(concl th))) in
        let lem = SUBS [th](SPECL[a;l'] ithm') in
        TRANS lem (conv (rhs (concl lem)))
    in
    (itlist itfn els (ISPECL [f;e] bthm)) ?\s failwith (`FOLDR_CONV: `^s);;


%----------------------------------------------------------------%
%- FOLDL_CONV conv "FOLDL f e [a0;...an]" --->
    |- FOLDL f e [a0;...an] = tm
   FOLDL_CONV evaluates the input expression by iteratively apply
    the function f the successive element of the list starting from
    the head of the list. tm is the result of the calculation.
    FOLDL_CONV returns a theorem stating this fact. During each
    iteration, an expression "f e' ai" is evaluated. The user
    supplied conversion conv is used to derive a theorem
     |- f e' ai = e'' which is then used to reduce the expression
    to e''. For example,

   #FOLDL_CONV conv "FOLDL ^f 0 ([x0;x1;x2;x3;x4;x5]:* list)";;
   |- FOLDL(\l' x. SUC l')0[x0;x1;x2;x3;x4;x5] = 6

   where f = (\l' x. SUC l') and
      conv = ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC SUC_CONV))

   In general, if the function f is an explicit lambda abstraction
   (\x x'. t[x,x']), the conversion should be in the form
    ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))
   where conv' applied to t[x,x'] returns the theorem |-t[x,x'] = e''.

-%
let FOLDL_CONV  =
    let (bthm,ithm) = CONJ_PAIR (definition `list` `FOLDL`) in
  \conv tm.
    let (_,[f;e;l]) = ((check_const `FOLDL`)#I)(strip_comb tm) in
    let ithm' = ISPEC f ithm in
    letrec itfn (term) =
        let (_,[f;e;l]) = strip_comb term in
           if (is_const l)
           then let (nil,_) = dest_const l in
                if not(nil = `NIL`)
                then failwith `expecting null list`
                else (ISPECL[f;e]bthm)
            else
                let [h;t] = snd(strip_comb l) in
                let th = ISPECL[e;h;t] ithm' in
                let lem = CONV_RULE
                     ((RAND_CONV o RATOR_CONV o RAND_CONV) conv) th in
                (TRANS lem (itfn (rhs(concl lem)))) in
    (itfn tm) ?\s failwith (`FOLDL_CONV: `^s);;

% --------------------------------------------------------------------- %
% list_FOLD_CONV : thm -> conv -> conv                                  %
% list_FOLD_CONV foldthm conv tm                                        %
% where canme is the name of constant and foldthm is a theorem of the   %
% the following form:                                                   %
% |- !x0 ... xn. CONST x0 ... xn = FOLD[LR] f e l                       %
% and conv is a conversion which will be passed to FOLDR_CONV or        %
% FOLDL_CONV to reduce the right-hand side of the above theorem         %
% --------------------------------------------------------------------- %
let list_FOLD_CONV =
  \foldthm conv tm.
   (let (cname,args) = (strip_comb tm) in
    let fthm = ISPECL args foldthm in
    let left,right = (dest_eq(concl fthm)) in
    let const = fst(strip_comb left) in
    let f = fst(dest_const(fst(strip_comb right))) in
    if not(cname = const) then failwith `theorem and term are different`
    else if (f = `FOLDL`) then
        TRANS fthm (FOLDL_CONV conv right)
    else if (f = `FOLDR`) then
        TRANS fthm (FOLDR_CONV conv right)
    else failwith `not FOLD theorem`)
    ?\s failwith (`list_FOLD_CONV: `^s);;

let SUM_CONV =
    list_FOLD_CONV (theorem `list` `SUM_FOLDR`) ADD_CONV;;

%----------------------------------------------------------------%
%- Filter                                                       -%
%- FILTER_CONV conv "FILTER P [a0;...an]" --->
    |- FILTER P [a0,...;an] = [...;ai;...]
    where conv "P ai" returns a theorem |- P ai = T for all ai
    in the resulting list.
-%
let FILTER_CONV =
    let (bth,ith) = CONJ_PAIR (definition `list` `FILTER`) in
  \conv tm.
    (let (_,[P;l]) =
         ((check_const `FILTER`) # I) (strip_comb tm) in
     let bth' = ISPEC P bth and ith' = ISPEC P ith in
     let lis = fst(dest_list l) in
     let ffn x th =
        let (left,right) = dest_eq(concl th) in
        let (_,[p;ls]) = strip_comb left in
        let fthm = SPECL [x;ls] ith' and cthm = conv "^P ^x" in
        (CONV_RULE (RAND_CONV COND_CONV) (SUBS[cthm;th]fthm))
     in
     (itlist ffn lis bth')) ?\s failwith (`FILTER_CONV: `^s);;

%----------------------------------------------------------------%
%- SNOC_CONV : conv
   SNOC_CONV "SNOC x [x0;...xn]" --->
    |- SNOC x [x0;...xn] = [x0;...;xn;x]                        -%
%----------------------------------------------------------------%
let SNOC_CONV =
    let bthm,sthm = CONJ_PAIR (definition `list` `SNOC`) in
  \tm.
    (let _,[d;lst] =
        ((check_const `SNOC`) # I) (strip_comb tm) in
     let ty = type_of lst in
     let lst',ety = (dest_list lst) in
     let EMP = "[]:^ty"  and CONS = "CONS:^ety -> ^ty ->^ty" in
     let itfn x (lst,ithm) =
       mk_comb(mk_comb(CONS,x),lst), (SUBS[ithm](ISPECL[d;x;lst]sthm)) in
     snd(itlist itfn lst' (EMP,(ISPEC d bthm))))
    ?\s failwith(`SNOC_CONV: `^s);;

%----------------------------------------------------------------%
%- REVERSE_CONV : conv
   REVERSE_CONV "REVERSE [x0;...;xn]" --->
    |- REVERSE [x0;...;xn] = [xn;...;x0]                        -%
%----------------------------------------------------------------%
let REVERSE_CONV =
    let fthm = theorem `list` `REVERSE_FOLDL` in
    let conv = ((RATOR_CONV BETA_CONV) THENC BETA_CONV) in
  \tm.
    (let _,lst =
        ((check_const `REVERSE`) # I) (dest_comb tm) in
     let fthm' = ISPEC lst fthm in
     TRANS fthm' (FOLDL_CONV conv (rhs(concl fthm'))))
    ?\s failwith (`REVERSE_CONV: `^s);;

%----------------------------------------------------------------%
%- FLAT_CONV : conv
   FLAT_CONV "FLAT [[x00;...;x0n];...;[xm0;...xmn]]" --->
   |- "FLAT [[x00;...;x0n];...;[xm0;...xmn]]" =
        [x00;...;x0n;...;xm0;...xmn]                            -%
%----------------------------------------------------------------%
let FLAT_CONV =
    let lem = PROVE("APPEND = (\x1 x2:* list. APPEND x1 x2)",
        CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
        THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
        THEN BETA_TAC THEN REFL_TAC) in
    let ffthm = theorem `list` `FLAT_FOLDR` in
    let afthm = theorem `list` `APPEND_FOLDR` in
    let fthm = REWRITE_RULE[afthm](SUBS[lem] ffthm) in
    let conv = (RAND_CONV (FOLDR_CONV ((RATOR_CONV BETA_CONV)
                 THENC BETA_CONV THENC (FOLDR_CONV ALL_CONV)))) in
  \tm.
    (let _,lst = ((check_const `FLAT`) # I) (dest_comb tm) in
     let fthm' = ISPEC lst fthm in
     CONV_RULE conv fthm') ?\s failwith (`FLAT_CONV: `^s);;

%-----------------------------------------------------------------------%
% EL_CONV : conv                                                        %
% The argument to this conversion should be in the form of              %
%   "EL k [x0; x1; ...; xk; ...; xn]"                                   %
% It returns a theorem                                                  %
%  |- EL k [x0; x1; ...; xk; ...; xn] = xk                              %
% iff 0 <= k <= n, otherwise failure occurs.                            %
%-----------------------------------------------------------------------%
let EL_CONV =
    let bthm,ithm = CONJ_PAIR (definition `list` `EL`) in
    let HD = definition `list` `HD` and TL = definition `list``TL` in
    let dec n = let nn = int_of_term n in
        mk_const(string_of_int(nn - 1), ":num") in
    let tail lst = hd(tl(snd(strip_comb lst))) in
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
    (let _,[N;bits] = ((check_const `EL`) # I) (strip_comb tm) in
     let n = int_of_term N in
     let lst = bits and m = N in
     if (n = 0) then
       (PURE_ONCE_REWRITE_RULE[HD](ISPEC bits bthm))
     else if (n < length(fst(dest_list bits))) then
       (SUBS [SYM (num_CONV N)](iter n N bits))
     else failwith `index too large` )?\s failwith(`EL_CONV: `^s);;

%-----------------------------------------------------------------------%
% ELL_CONV : conv                                                       %
% It takes a term of the form "ELL k [x(n-1); ... x0]" and returns      %
% |- ELL k [x(n-1); ...; x0] = x(k)                                     %
%-----------------------------------------------------------------------%
let ELL_CONV =
    let bthm = theorem `list` `ELL_0_SNOC` and
        ithm = theorem `list` `ELL_SUC_SNOC` in
    let iter count (d,lst) elty =
     letref n = count and x = d and l = lst in
     letref th = (ISPECL[(term_of_int n); x; mk_list(l,elty)]ithm) in
     if (n = 0) then
       (x := last l; l := butlast l;
       (th := TRANS th (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
             SNOC_CONV) (ISPECL [mk_list(l,elty);x] bthm))))
     loop
       (n := n - 1;
        x := (last l);
        l := butlast l;
        th := TRANS (RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) num_CONV) th)
             (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV)
              (ISPECL[(term_of_int n); x; mk_list(l,elty)]ithm))) in
  \tm.
    (let _,[N;lst] = ((check_const`ELL`) # I)(strip_comb tm) in
     let ty = type_of lst in
     let lst',ety = (dest_list lst) in
     let n =  int_of_term N in
     if not(n < (length lst')) then failwith `index too large`
     else if (n = 0) then
       (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV)
        (ISPECL[mk_list(butlast lst', ety);(last lst')]bthm))
     else
      SUBS_OCCS[[1],(SYM (num_CONV N))]
      (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV)
        (iter (n - 1) ((last lst'), (butlast lst')) ety)))
    ?\s failwith(`ELL_CONV: `^s);;

% --------------------------------------------------------------------- %
% MAP2_CONV conv "MAP2 f [x1;...;xn] [y1;...;yn]"                       %
%                                                                       %
% Returns |- MAP2 f [x1;...;xn] [y1;...;yn] = [r1;...;rn]               %
% where conv "f xi yi" returns |- f xi yi = ri for 1 <= i <= n          %
% --------------------------------------------------------------------- %

let MAP2_CONV =
    let mn,mc = CONJ_PAIR(definition `list` `MAP2`) in
    \conv tm.
     (let _,[fn;l1;l2] = ((check_const`MAP2`) # I) (strip_comb tm) in
      let el1s,ty1 = dest_list l1 and el2s,ty2 = dest_list l2 in
      let els = combine (el1s,el2s) in
      let nth = ISPEC fn mn and cth = ISPEC fn mc in
      let cns = rator(rator(rand(snd(strip_forall(concl cth))))) in
      let itfn (e1,e2) th =
          let _,[f;t1;t2] = strip_comb(lhs(concl th)) in
          let th1 = SPECL [e1; t1; e2; t2] cth in
          let r = conv (mk_comb(mk_comb(fn,e1),e2)) in
          (SUBS[r;th]th1) in
      itlist itfn els nth) ?\s failwith (`MAP2_CONV: `^s);;

% --------------------------------------------------------------------- %
% ALL_EL_CONV : conv -> conv                                            %
% ALL_EL_CONV conv "ALL_EL P [x0;...;xn]" --->                          %
% |- ALL_EL P [x0;...;xn] = T iff conv "P xi"---> |- P xi = T for all i %
% |- ALL_EL P [x0;...;xn] = F otherwise                                 %
% --------------------------------------------------------------------- %
let ALL_EL_CONV =
    let bth,ith = CONJ_PAIR (definition `list` `ALL_EL`) in
    let AND_THM = setify(flat(map (CONJ_LIST 5)
        [(SPEC "T" AND_CLAUSES);(SPEC "F" AND_CLAUSES)])) in
  \conv tm.
    (let (_,[P;l]) = ((check_const`ALL_EL`) # I)(strip_comb tm) in
     let bth' = ISPEC P bth and ith' = ISPEC P ith in
     let lis = fst(dest_list l) in
     let ffn x th =
        let (left,right) = dest_eq(concl th) in
        let (_,[p;ls]) = strip_comb left in
        let fthm = SPECL [x;ls] ith' and cthm = conv "^P ^x" in
        SUBS AND_THM (SUBS[cthm;th]fthm)
     in
     (itlist ffn lis bth')) ?\s failwith (`ALL_EL_CONV: `^s);;

% --------------------------------------------------------------------- %
% SOME_EL_CONV : conv -> conv                                           %
% SOME_EL_CONV conv "SOME_EL P [x0;...;xn]" --->                        %
% |- SOME_EL P [x0;...;xn] = F iff conv "P xi"---> |- P xi = F for all i%
% |- SOME_EL P [x0;...;xn] = F otherwise                                %
% --------------------------------------------------------------------- %
let SOME_EL_CONV =
    let bth,ith = CONJ_PAIR (definition `list` `SOME_EL`) in
    let OR_THM = setify(flat(map (CONJ_LIST 5)
        [(SPEC "T" OR_CLAUSES);(SPEC "F" OR_CLAUSES)])) in
  \conv tm.
    (let (_,[P;l]) = ((check_const`SOME_EL`) # I)(strip_comb tm) in
     let bth' = ISPEC P bth and ith' = ISPEC P ith in
     let lis = fst(dest_list l) in
     let ffn x th =
        let (left,right) = dest_eq(concl th) in
        let (_,[p;ls]) = strip_comb left in
        let fthm = SPECL [x;ls] ith' and cthm = conv "^P ^x" in
        SUBS OR_THM (SUBS[cthm;th]fthm)
     in
     (itlist ffn lis bth')) ?\s failwith (`SOME_EL_CONV: `^s);;

% --------------------------------------------------------------------- %
% IS_EL_CONV : conv -> conv                                             %
% IS_EL_CONV conv "IS_EL P [x0;...;xn]" --->                            %
% |- IS_EL x [x0;...;xn] = T iff conv "x = xi" --->                     %
%                                    |- (x = xi) = F for an i           %
% |- IS_EL x [x0;...;xn] = F otherwise                                  %
% --------------------------------------------------------------------- %
let IS_EL_CONV =
    let bth = (definition `list` `IS_EL_DEF`) in
  \conv tm.
    (let (_,[x;l]) = ((check_const`IS_EL`) # I)(strip_comb tm) in
     let bth' = ISPECL[x;l] bth in
     let right = rhs (concl bth') in
     TRANS bth' (SOME_EL_CONV conv right))
     ?\s failwith (`IS_EL_CONV: `^s);;

% --------------------------------------------------------------------- %
% LAST_CONV : conv                                                      %
% LAST_CONV "LAST [x0;...;xn]" ---> |- LAST [x0;...;xn] = xn            %
% --------------------------------------------------------------------- %
let LAST_CONV =
    let bth = theorem `list` `LAST` in
  \tm.
    (let _,l = ((check_const`LAST`) # I) (dest_comb tm) in
     let l',lty = dest_list l in
     if ((length l') = 0) then failwith `empty list`
     else
       (let x = last l' and lis = mk_list((butlast l'),lty) in
        let bth' = ISPECL[x;lis] bth in
        CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV) bth'))
    ?\s failwith (`LAST_CONV: `^s);;

% --------------------------------------------------------------------- %
% BUTLAST_CONV : conv                                                   %
% BUTLAST_CONV "BUTLAST [x0;...;xn-1;xn]" --->                          %
% |- BUTLAST [x0;...;xn-1;xn] = [x0;...;xn-1]                           %
% --------------------------------------------------------------------- %
let BUTLAST_CONV =
    let bth = theorem `list` `BUTLAST` in
  \tm.
    (let _,l = ((check_const`BUTLAST`) # I) (dest_comb tm) in
     let l',lty = dest_list l in
     if ((length l') = 0) then failwith `empty list`
     else
       (let x = last l' and lis = mk_list((butlast l'),lty) in
        let bth' = ISPECL[x;lis] bth in
        CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV) bth'))
    ?\s failwith (`BUTLAST_CONV: `^s);;

%----------------------------------------------------------------%
let SUC_CONV =
    let numty = mk_type(`num`,[]) in
  \tm.
    let (SUC,(n,_)) = (I # dest_const)(dest_comb tm) in
    let n' = string_of_int(1 + (int_of_string n)) in
    SYM (num_CONV (mk_const(n', numty)));;

%---------------------------------------------------------------%
% SEG_CONV : conv                                               %
% SEG_CONV "SEG m k [x0;...;xk;...;xm+k;...xn]" --->            %
% |- SEG m k [x0;...;xk;...;xm+k;...xn] = [xk;...xm+k-1]        %
%---------------------------------------------------------------%
let SEG_CONV =
    let [bthm;mthm;kthm] = CONJ_LIST 3 (definition `list` `SEG`) in
    let SUC = "SUC" in
    let mifn mthm' x th =
        let [M';_;L] = snd(strip_comb(lhs(concl th))) in
        SUBS[(SUC_CONV(mk_comb(SUC,M')));th](SPECL[M';x;L]mthm') in
    let kifn kthm' x th =
        let [_;K';L] = snd(strip_comb(lhs(concl th))) in
        SUBS[(SUC_CONV(mk_comb(SUC,K')));th](SPECL[K';x;L]kthm') in
  \tm.
   (let _,[M;K;L] = ((check_const`SEG`)# I)(strip_comb tm) in
    let lis,lty = dest_list L in
    let m = int_of_term M and k = int_of_term K in
    if ((m + k) > (length lis)) then failwith `indexes too large`
    else if (m = 0) then (ISPECL[K;L]bthm)
    else let mthm' = INST_TYPE [(lty,":*")] mthm in
        if (k = 0) then
            let (ls,lt) = chop_list m lis in
            let bthm' = ISPECL["0";(mk_list(lt,lty))] bthm in
            (itlist (mifn mthm') ls bthm')
        else
            let lk,(ls,lt) = (I #(chop_list m))(chop_list k lis) in
            let bthm' = ISPECL["0";(mk_list(lt,lty))] bthm in
            let kthm' = SUBS[SYM(num_CONV M)]
                (INST_TYPE[(lty,":*")](SPEC (term_of_int(m-1)) kthm)) in
            let bbthm = itlist (mifn mthm') ls bthm' in
            (itlist (kifn kthm') lk bbthm))
    ?\s failwith (`SEG_CONV: `^s);;

%-----------------------------------------------------------------------%
% LASTN_CONV : conv                                                     %
% It takes a term of the form "LASTN k [x0; ...; x(n-k); ...; x(n-1)]"  %
% and returns the following theorem:                                    %
% |- LASTN k [x0; ...; x(n-k); ...; x(n-1)] = [x(n-k); ...; x(n-1)]     %
%-----------------------------------------------------------------------%
let LASTN_CONV =
    let LASTN_LENGTH_APPEND = theorem `list` `LASTN_LENGTH_APPEND` and
         bthm = CONJUNCT1 (definition `list` `LASTN`) and
         ithm = (theorem `list` `LASTN_LENGTH_ID`) in
    let len_conv ty lst =
        LENGTH_CONV(mk_comb("LENGTH:(^ty)list -> num",lst)) in
  \tm.
    (let _,[N;lst] = ((check_const`LASTN`) # I) (strip_comb tm) in
     let n = int_of_term N in
     if (n = 0) then (ISPEC lst bthm)
     else
      (let bits,lty = (dest_list lst) in
       let len = (length bits) in
       if (n > len) then failwith `index too large`
       else if (n = len) then
            (SUBS[(len_conv lty lst)](ISPEC lst ithm))
       else
        (let l1,l2 = (chop_list (len - n) bits) in
         let l1' = mk_list(l1, lty) and l2' = mk_list(l2, lty) in
         let APP = "APPEND:(^lty)list -> (^lty)list -> (^lty)list" in
         let thm2 = len_conv lty l2' in
         let thm3 = APPEND_CONV (mk_comb(mk_comb(APP, l1'),l2')) in
         (SUBS[thm2;thm3](ISPECL [l1';l2'] LASTN_LENGTH_APPEND)) )))
    ?\s failwith (`LASTN_CONV: `^s);;

%-----------------------------------------------------------------------%
% BUTLASTN_CONV : conv                                                  %
% It takes a term of the form "BUTLASTN k [x0;x1;...;x(n-k);...;x(n-1)]"%
% and returns the following theorem:                                    %
% |- BUTLASTN k  [x0; x1; ...; x(n-k);...;x(n-1)] = [x0; ...; x(n-k-1)] %
%-----------------------------------------------------------------------%
let BUTLASTN_CONV =
    let bthm = CONJUNCT1 (definition `list` `BUTLASTN`) in
    let lthm = (theorem `list` `BUTLASTN_LENGTH_NIL`) in
    let athm = (theorem `list` `BUTLASTN_LENGTH_APPEND`) in
    let len_conv ty lst =
        LENGTH_CONV(mk_comb("LENGTH:(^ty)list -> num",lst)) in
  \tm.
    (let _,[N;lst] = ((check_const`BUTLASTN`) # I) (strip_comb tm) in
     let n = int_of_term N in
     if (n = 0) then (ISPEC lst bthm)
     else
      (let bits,lty = (dest_list lst) in
       let len = (length bits) in
       if (n > len) then failwith `index too large`
       else if (n = len) then
         let thm1 = len_conv lty lst in (SUBS[thm1](ISPEC lst lthm))
       else
        (let l1,l2 = (chop_list (len - n) bits) in
         let l1' = mk_list(l1, lty) and l2' = mk_list(l2, lty) in
         let APP = "APPEND:(^lty)list -> (^lty)list -> (^lty)list" in
         let thm2 = len_conv lty l2' in
         let thm3 = APPEND_CONV (mk_comb(mk_comb(APP, l1'),l2')) in
         (SUBS[thm2;thm3](ISPECL [l2';l1'] athm)) )))
    ?\s failwith (`BUTLASTN_CONV: `^s);;

%-----------------------------------------------------------------------%
% BUTFIRSTN_CONV : conv                                                 %
% BUTFIRSTN_CONV "BUTFIRSTN k [x0;...;xk;...;xn]" --->                  %
% |- BUTFIRSTN k [x0;...;xk;...;xn] = [xk;...;xn]                       %
%-----------------------------------------------------------------------%
let BUTFIRSTN_CONV =
    let bthm,ithm = CONJ_PAIR (definition `list` `BUTFIRSTN`) in
    let SUC = "SUC" in
    let itfn ithm' x th =
        let _,[N';L'] = strip_comb(lhs(concl th)) in
        SUBS[(SUC_CONV(mk_comb(SUC,N')));th](SPECL[N';x;L']ithm') in
  \tm.
   (let _,[K;L] = ((check_const`BUTFIRSTN`)# I)(strip_comb tm) in
    let k = int_of_term K and  lis,lty = dest_list L  in
    if (k > (length lis)) then failwith `index too large`
    else if (k = 0) then (ISPEC L bthm)
    else
        let ll,lr = chop_list k lis in
        let bthm' = ISPEC (mk_list(lr,lty)) bthm in
        let ithm' = INST_TYPE[(lty,":*")]ithm in
        itlist (itfn ithm') ll bthm')
    ?\s failwith (`BUTFIRSTN_CONV: `^s);;


%-----------------------------------------------------------------------%
% FIRSTN_CONV : conv                                                    %
% FIRSTN_CONV "FIRSTN k [x0;...;xk;...;xn]" --->                        %
% |- FIRSTN k [x0;...;xk;...;xn] = [x0;...;xk]                          %
%-----------------------------------------------------------------------%
let FIRSTN_CONV =
    let bthm,ithm = CONJ_PAIR (definition `list` `FIRSTN`) in
    let SUC = "SUC" in
    let itfn ithm' x th =
        let _,[N';L'] = strip_comb(lhs(concl th)) in
        SUBS[(SUC_CONV(mk_comb(SUC,N')));th](SPECL[N';x;L']ithm') in
  \tm.
   (let _,[K;L] = ((check_const`FIRSTN`)# I)(strip_comb tm) in
    let k = int_of_term K and  lis,lty = dest_list L  in
    if (k > (length lis)) then failwith `index too large`
    else if (k = 0) then (ISPEC L bthm)
    else
        let ll,lr = chop_list k lis in
        let bthm' = ISPEC (mk_list(lr,lty)) bthm in
        let ithm' = INST_TYPE[(lty,":*")]ithm in
        itlist (itfn ithm') ll bthm')
    ?\s failwith (`FIRSTN_CONV: `^s);;

%-----------------------------------------------------------------------%
% SCANL_CONV : conv -> conv                                             %
% SCANL_CONV conv "SCANL f e [x0;...;xn]" --->                          %
% |- SCANL f e [x0;...;xn] = [e; t0; ...; tn]                           %
% where conv "f ei xi" ---> |- f ei xi = ti                             %
%-----------------------------------------------------------------------%
let SCANL_CONV =
    let bthm,ithm = CONJ_PAIR (definition `list` `SCANL`) in
  \conv tm.
   (let _,[f;e;l] = ((check_const`SCANL`)#I)(strip_comb tm) in
    let bthm' = ISPEC f bthm and ithm' = ISPEC f ithm in
    letrec scan_conv  tm' =
        let [_;E;L] = snd(strip_comb tm') in
        if (is_const L) then (SPEC E bthm')
        else
            let [x;l] = snd(strip_comb L) in
            let th1 = conv (mk_comb(mk_comb(f,E),x)) in
            let th2 = SUBS[th1](SPECL[E;x;l] ithm') in
            let th3 = scan_conv (last(snd(strip_comb(rhs(concl th2))))) in
            SUBS[th3]th2
    in
    (scan_conv tm)) ?\s failwith (`SCANL_CONV: `^s);;

%-----------------------------------------------------------------------%
% SCANR_CONV : conv -> conv                                             %
% SCANR_CONV conv "SCANR f e [x0;...;xn]" --->                          %
% |- SCANR f e [x0;...;xn] = [t0; ...; tn; e]                           %
% where conv "f xi ei" ---> |- f xi ei = ti                             %
%-----------------------------------------------------------------------%
let SCANR_CONV =
    let bthm,ithm = CONJ_PAIR (definition `list` `SCANR`) in
    let HD = definition `list` `HD` in
  \conv tm.
   (let _,[f;e;l] = ((check_const`SCANR`)#I)(strip_comb tm) in
    let bthm' = ISPEC f bthm and ithm' = ISPEC f ithm in
    letrec scan_conv  tm' =
        let [_;E;L] = snd(strip_comb tm') in
        if (is_const L) then (SPEC E bthm')
        else
            let [x;l] = snd(strip_comb L) in
            let th2 = (SPECL[E;x;l] ithm') in
            let th3 = scan_conv (last(snd(strip_comb(rhs(concl th2))))) in
            let th4 = PURE_ONCE_REWRITE_RULE[HD](SUBS[th3]th2) in
            let th5 = conv (hd(snd(strip_comb(rhs(concl th4))))) in
            SUBS[th5]th4
    in
    (scan_conv tm)) ?\s failwith (`SCANR_CONV: `^s);;

%-----------------------------------------------------------------------%
% REPLICATE_CONV : conv                                                 %
% REPLICATE conv "REPLICATE f n" --->                                   %
%  |- REPLICATE n x = [x; ...; x]                                       %
%-----------------------------------------------------------------------%
let REPLICATE_CONV  =
    let (bthm,ithm) = CONJ_PAIR (definition `list` `REPLICATE`) in
    let dec n = term_of_int((int_of_term n) - 1) in
    letrec repconv (bthm, ithm) tm =
        let [n;x] = snd(strip_comb tm) in
        if ((int_of_term n) = 0) then bthm
        else (let th1 = SUBS[SYM (num_CONV n)](SPEC (dec n) ithm) in
            CONV_RULE ((RAND_CONV o RAND_CONV) (repconv(bthm,ithm))) th1) in
  \tm.
   (let _,[n;x] = ((check_const`REPLICATE`)#I)(strip_comb tm) in
    let xty = type_of x in
    let bthm' = ISPEC x bthm and
        ithm' = GEN_ALL(ISPECL[mk_var(`n`,xty);x] ithm) in
    (repconv (bthm',ithm') tm)) ?\s failwith (`REPLICATE_CONV: `^s);;

%-----------------------------------------------------------------------%
% GENLIST_CONV : conv -> conv                                           %
% GENLIST conv "GENLIST f n" ---> |- GENLIST f n = [f 0;f 1; ...;f(n-1)]%
%-----------------------------------------------------------------------%
let GENLIST_CONV =
    let (bthm,ithm) = CONJ_PAIR (definition `list` `GENLIST`) in
    let dec n = term_of_int((int_of_term n) - 1) in
    letrec genconv (bthm,ithm) conv tm =
        let n = last(snd(strip_comb tm)) in
        if ((int_of_term n) = 0) then CONV_RULE(ONCE_DEPTH_CONV conv) bthm
        else (let th1 = SUBS[SYM (num_CONV n)](SPEC (dec n) ithm) in
              let th2 = RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th1 in
              RIGHT_CONV_RULE (RAND_CONV (genconv (bthm,ithm) conv)) th2) in
  \conv tm.
   (let _,[f;n] = ((check_const`GENLIST`)# I)(strip_comb tm) in
    let bthm' = ISPEC f bthm and ithm' = ISPEC f ithm in
    RIGHT_CONV_RULE (TOP_DEPTH_CONV SNOC_CONV)(genconv (bthm',ithm') conv tm))
    ?\s failwith (`GENLIST_CONV: `^s);;


(APPEND_CONV, MAP_CONV, FOLDR_CONV, FOLDL_CONV, list_FOLD_CONV,
 SUM_CONV, FILTER_CONV, SNOC_CONV, REVERSE_CONV, FLAT_CONV,
 EL_CONV, ELL_CONV,  MAP2_CONV, ALL_EL_CONV,  SOME_EL_CONV,
 IS_EL_CONV,  LAST_CONV, BUTLAST_CONV, SEG_CONV, LASTN_CONV,
 BUTLASTN_CONV, BUTFIRSTN_CONV, FIRSTN_CONV, SCANL_CONV, SCANR_CONV,
 REPLICATE_CONV,GENLIST_CONV);;

end_section `list_convs`;;

let (APPEND_CONV, MAP_CONV, FOLDR_CONV, FOLDL_CONV, list_FOLD_CONV,
 SUM_CONV, FILTER_CONV, SNOC_CONV, REVERSE_CONV, FLAT_CONV,
 EL_CONV, ELL_CONV,  MAP2_CONV, ALL_EL_CONV,  SOME_EL_CONV,
 IS_EL_CONV,  LAST_CONV, BUTLAST_CONV, SEG_CONV, LASTN_CONV,
 BUTLASTN_CONV, BUTFIRSTN_CONV, FIRSTN_CONV, SCANL_CONV, SCANR_CONV,
 REPLICATE_CONV,GENLIST_CONV)
    = it;;
