% FILE		: num_tac.ml						%
% DESCRIPTION   : contains the rule and tactic for general induction.	%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.3.23						%
%									%
%-----------------------------------------------------------------------%

% add_lib_path `group`;; Not needed for HOL88.1.05 (MJCG 14 April, 1989)%

loadf (library_pathname() ^ `/group/start_groups`);;

%GEN_INDUCTION =
 |- !P. P 0 /\ (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n)%


% GEN_INDUCT_RULE : thm -> thm -> thm

  A1 |- P(0)     A2 |- (!n. (!m. m < n ==> P(m)) ==> P(n))
--------------------------------------------------------
                  A1 u A2 |- !n. P(n)
%

let GEN_INDUCT_RULE (thm1:thm) (thm2:thm)=(
 let var1,(test1,prop1)=((fst(dest_forall(concl thm2))),
                         (dest_imp(snd(dest_forall(concl thm2)))))
 in
 let var2=fst(dest_forall test1)  in
 let P = "\^var1.^prop1" in
 
 let IND_thm = 
    (EQ_MP 
     (ALPHA "!P.P 0/\(!n.(!m.m<n ==> P m) ==> P n) ==> (!n.P n)"
            "!P.P 0/\(!^var1.(!^var2.^var2<^var1 ==> P ^var2) ==> P ^var1)
                ==> (!^var1.P ^var1)")
     (theorem `more_arith` `GEN_INDUCTION`)) and_then
    (SPEC P) and_then
    (\thm.EQ_MP (((DEPTH_CONV BETA_CONV)o concl)thm) thm)
 in

 (MP IND_thm (CONJ thm1 thm2)) )?failwith `GEN_INDUCT_RULE`;;


% GEN_INDUCT_TAC : tactic

                  [A] !n. P n
======================================================
 [A] P(0)        [A;(!m. m < n ==> P m)] P(n)
%

let GEN_INDUCT_TAC ((hypoth,aim):goal) =(
 let V,prop=dest_forall(aim) in
 let var1=variant ((frees aim) @ (freesl hypoth)) V in
 let prop1=subst [(var1,V)] prop in
 let var2=variant (frees prop) "m:num" in
 let assum="!^var2.(^var2 < ^var1)==>^(subst [(var2,V)] prop)" in
 ([(hypoth,(subst [("0",V)] prop));(assum.hypoth,prop1)],
 (\[thm1;thm2].(GEN_INDUCT_RULE thm1 (GEN var1 (DISCH assum thm2)))and_then
   (\thm.(EQ_MP (ALPHA (concl thm) aim) thm))  ))
)?failwith `GEN_INDUCT_TAC`;;

