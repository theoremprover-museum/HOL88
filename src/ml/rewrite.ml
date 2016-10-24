%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        rewrite.ml                                            %
%                                                                             %
%     DESCRIPTION:      Simple rewriting rules and tactics for HOL            %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml,     %
%                       conv.ml, hol-net.ml                                   %
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

% --------------------------------------------------------------------- %
% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.              		%
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml, etc   	%
% --------------------------------------------------------------------- %

if compiling then  (loadf `ml/hol-in-out`;
            loadf `ml/hol-rule`;
            loadf `ml/hol-drule`;
            loadf `ml/drul`;
            loadf `ml/tacticals`;
            loadf `ml/conv`;
            loadf `ml/hol-net`);;

% ===================================================================== %
% Section for defining mk_conv_net           [TFM 91.03.17] 		%
% ===================================================================== %
begin_section mk_conv_net;;

% --------------------------------------------------------------------- %
% Redundant GEN_ALL/SPEC_ALL combinations resulting from applying       %
% mk_conv_net to mk_rewrite eliminated as was done by Konrad Slind in   %
% HOL90 [JG 92.04.24]                                                   %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% mk_rewrites: split a theorem into a list of theorems suitable for	%
% rewriting by doing:                           			%
%                                   					%
%   1. Specialize all variables (SPEC_ALL).             		%
%                                   					%
%   2. Then do the following:                       			%
%                                   					%
%        |- t1 /\ t2     -->    [|- t1 ; |- t2]             		%
%        |- t1 <=> t2    -->    [|- t1=t2]              		%
%                                   					%
%   3. Then |- t --> |- t = T and |- ~t --> |- t = F            	%
%                                   					%
% iff case deleted [TFM 91.01.20]      		                 	%
% optimized [TFM 91.03.17]                          			%
% --------------------------------------------------------------------- %

letrec mk_rewrites th =
   (let thm = SPEC_ALL th in
    let t = concl thm in
    if is_eq t
       then [thm] else
    if is_conj t then
       let (c1,c2) = CONJ_PAIR thm in (mk_rewrites c1 @ mk_rewrites c2) else
    if is_neg t then [EQF_INTRO thm]
       else [EQT_INTRO thm]) ? failwith `mk_rewrites`;;

% --------------------------------------------------------------------- %
% [th1; ... ; thn]  --> (mk_rewrites th1) @ ... @ (mk_rewrites thn)     %
% --------------------------------------------------------------------- %

let mk_rewritesl thl = itlist (append o mk_rewrites ) thl [];;

% --------------------------------------------------------------------- %
% Inefficient ML implementation of nets as lists of pairs:      	%
%                                   					%
% let enter_term(t,x)n = (t,x).n                    			%
% and lookup_term n t  =                        			%
%      mapfilter(\(t',x).if can(match t)t' then x else fail)        	%
% and nil_term_net     = []:(term#*)list;;              		%
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% Build a conv net from a list of theorems              		%
% --------------------------------------------------------------------- %

let mk_conv_net thl =
 itlist
  enter_term
  (map (\th. (lhs(concl th),REWR_CONV th)) (mk_rewritesl thl))
  nil_term_net;;

% --------------------------------------------------------------------- %
% Export mk_conv_net outside of section.                		%
% --------------------------------------------------------------------- %
mk_conv_net;;
end_section mk_conv_net;;
let mk_conv_net = it;;

% ===================================================================== %
% List of basic rewrites (temporarily made assignable to enable     	%
% experimental changes to be quickly made)              		%
% ===================================================================== %

%  |- !t. (!x.t)  =  t  %

let FORALL_SIMP =
 let t = "t:bool"
 and x = "x:*"
 in
 GEN t (IMP_ANTISYM_RULE
        (DISCH "!^x.^t" (SPEC x (ASSUME "!^x.^t")))
        (DISCH t (GEN x (ASSUME t))));;

%  |- !t. (?x.t)  =  t  %

let EXISTS_SIMP =
 let t = "t:bool"
 and x = "x:*"
 in
 GEN t (IMP_ANTISYM_RULE
        (DISCH "?^x.^t" (CHOOSE("p:*", ASSUME"?^x.^t")(ASSUME t)))
        (DISCH t (EXISTS("?^x.^t", "r:*")(ASSUME t))));;

%   |- !t1 t2. (\x. t1)t2  =  t1 %

let ABS_SIMP = GEN_ALL(BETA_CONV "(\x:*.(t1:**))t2");;

let basic_rewrites = 
 [REFL_CLAUSE;
  EQ_CLAUSES;
  NOT_CLAUSES;
  AND_CLAUSES;
  OR_CLAUSES;
  IMP_CLAUSES;                             
  COND_CLAUSES;
% IFF_EQ;        |- !t1 t2. (t1<=>t2) = (t1=t2)  DELETED [TFM 91.01.20] %
  FORALL_SIMP;
  EXISTS_SIMP;
  ABS_SIMP;
  PAIR;
  FST;
  SND
 ];;

% ===================================================================== %
% Main rewriting conversion                         			%
% ===================================================================== %

let GEN_REWRITE_CONV =
    let RW_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm in
    \(rewrite_fun:conv->conv) built_in_rewrites.
      let basic_net = mk_conv_net built_in_rewrites in
      \thl. rewrite_fun
                (RW_CONV (merge_term_nets (mk_conv_net thl) basic_net));;

% --------------------------------------------------------------------- %
% Rewriting conversions.                        			%
%                                                                       %
% Modified to use special versions of the depth conversions.            %
%                                                        [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let PURE_REWRITE_CONV = GEN_REWRITE_CONV REW_DEPTH_CONV []
and REWRITE_CONV = GEN_REWRITE_CONV REW_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV ONCE_REW_DEPTH_CONV []
and ONCE_REWRITE_CONV = GEN_REWRITE_CONV ONCE_REW_DEPTH_CONV basic_rewrites;;

%====================================================================== %
% Main rewriting rule                           			%
% OLD version:                                                          %
%                                                                       %
% let GEN_REWRITE_RULE =                                                %
%     let REWRITE_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm in %
%     \rewrite_fun built_in_rewrites.                                   %
%       let basic_net = mk_conv_net built_in_rewrites in                %
%       \thl. let conv = rewrite_fun                                    %
%                 (REWRITE_CONV(merge_term_nets (mk_conv_net thl)       %
%                                                basic_net)) in         %
%            \th. EQ_MP (conv (concl th)) th;;                          %
%                                                                       %
% New version rewritten using the new GEN_REWRITE_CONV  [JG 92.04.07]   %
% The code is most simply expressed as follows:                         %
%                                                                       %
% let GEN_REWRITE_RULE rewrite_fun built_in_rewrites thl =              %
%     CONV_RULE (GEN_REWRITE_CONV rewrite_fun built_in_rewrites thl) ;; %
%                                                                       %
% However, it is optimised below so that the built_in_rewrites gets     %
% made into a conv net at compile time.                                 %
%                                                                       %
% Futher optimized 13.5.93 by JVT to remove the function composition    %
% to enhance speed.                                                     %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
% let GEN_REWRITE_RULE rewrite_fun built_in_rewrites =                  %
%     let REWL_CONV = GEN_REWRITE_CONV rewrite_fun built_in_rewrites in %
%     	CONV_RULE o REWL_CONV ;;                                        %
%====================================================================== %

let GEN_REWRITE_RULE rewrite_fun built_in_rewrites =
    let REWL_CONV = GEN_REWRITE_CONV rewrite_fun built_in_rewrites in
    	\tm. (CONV_RULE (REWL_CONV tm));;

% --------------------------------------------------------------------- %
% Rewriting rules.                          				%
%                                                                       %
% Modified to use special versions of the depth conversions.            %
%                                                        [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let PURE_REWRITE_RULE      = GEN_REWRITE_RULE REW_DEPTH_CONV [] 
and REWRITE_RULE           = GEN_REWRITE_RULE REW_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_RULE = GEN_REWRITE_RULE ONCE_REW_DEPTH_CONV []
and ONCE_REWRITE_RULE      = GEN_REWRITE_RULE ONCE_REW_DEPTH_CONV
                                                             basic_rewrites;;

% --------------------------------------------------------------------- %
% Rewrite a theorem with the help of its assumptions            	%
% --------------------------------------------------------------------- %

let PURE_ASM_REWRITE_RULE thl th =
    PURE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and ASM_REWRITE_RULE thl th = 
    REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and PURE_ONCE_ASM_REWRITE_RULE thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
and ONCE_ASM_REWRITE_RULE thl th = 
    ONCE_REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th;;

% --------------------------------------------------------------------- %
% Rules that rewrite using those assumptions that satisfy a predicate %
% --------------------------------------------------------------------- %

let FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_ASM_REWRITE_RULE f thl th = 
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
and FILTER_ONCE_ASM_REWRITE_RULE f thl th = 
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;

%====================================================================== %
% Main rewriting tactic                         			%
% OLD version:                                                          %
%                                                                       %
% let GEN_REWRITE_TAC =                                                 %
%     let REWRITE_CONV net = \tm. FIRST_CONV (lookup_term net tm) tm in %
%     \rewrite_fun built_in_rewrites.                                   %
%       let basic_net = mk_conv_net built_in_rewrites in                %
%       \thl.let conv = rewrite_fun                                     %
%                (REWRITE_CONV(merge_term_nets (mk_conv_net thl)        %
%                                               basic_net)) in          %
%       \(A,t):goal. let th = conv t in                                 %
%                    let (),right = dest_eq(concl th) in                %
%                    if right="T"                                       %
%                      then ([], \[]. EQ_MP (SYM th) TRUTH)             %
%                      else ([A,right], \[th']. EQ_MP (SYM th) th');;   %
%                                                                       %
% New version rewritten using the new GEN_REWRITE_CONV  [JG 92.04.07]   %
% The code is most simply expressed as follows:                         %
%                                                                       %
% let GEN_REWRITE_TAC rewrite_fun built_in_rewrites thl =               %
%     CONV_TAC (GEN_REWRITE_CONV rewrite_fun built_in_rewrites thl) ;;  %
%                                                                       %
% However, it is optimised below so that the built_in_rewrites gets     %
% made into a conv net at compile time.                                 %
%                                                                       %
% Futher optimized 13.5.93 by JVT to remove the function composition    %
% to enhance speed.                                                     %
%                                                                       %
% OLD VERSION:                                                          %
%                                                                       %
% let GEN_REWRITE_TAC rewrite_fun built_in_rewrites =                   %
%     let REWL_CONV = GEN_REWRITE_CONV rewrite_fun built_in_rewrites in %
%    	CONV_TAC o REWL_CONV ;;                                         %
%====================================================================== %

let GEN_REWRITE_TAC rewrite_fun built_in_rewrites =
    let REWL_CONV = GEN_REWRITE_CONV rewrite_fun built_in_rewrites in
    	\tm. (CONV_TAC (REWL_CONV tm));;

% --------------------------------------------------------------------- %
% Rewriting tactics.                            			%
%                                                                       %
% Modified to use special versions of the depth conversions.            %
%                                                        [RJB 94.02.15] %
% --------------------------------------------------------------------- %

let PURE_REWRITE_TAC      = GEN_REWRITE_TAC REW_DEPTH_CONV []
and REWRITE_TAC           = GEN_REWRITE_TAC REW_DEPTH_CONV basic_rewrites
and PURE_ONCE_REWRITE_TAC = GEN_REWRITE_TAC ONCE_REW_DEPTH_CONV []
and ONCE_REWRITE_TAC      = GEN_REWRITE_TAC ONCE_REW_DEPTH_CONV
                                                           basic_rewrites;;

% --------------------------------------------------------------------- %
% Rewrite a goal with the help of its assumptions           		%
% --------------------------------------------------------------------- %

let PURE_ASM_REWRITE_TAC thl = 
    ASSUM_LIST (\asl. PURE_REWRITE_TAC (asl @ thl))
and ASM_REWRITE_TAC thl      = 
    ASSUM_LIST (\asl. REWRITE_TAC (asl @ thl))
and PURE_ONCE_ASM_REWRITE_TAC thl = 
    ASSUM_LIST (\asl. PURE_ONCE_REWRITE_TAC (asl @ thl))
and ONCE_ASM_REWRITE_TAC thl      = 
    ASSUM_LIST (\asl. ONCE_REWRITE_TAC (asl @ thl));;

% --------------------------------------------------------------------- %
% Tactics that rewrite using those assumptions that satisfy a predicate %
% --------------------------------------------------------------------- %

let FILTER_PURE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. PURE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. PURE_ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl))
and FILTER_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (\asl. ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl));;

% --------------------------------------------------------------------- %
% Search a sub-term of t matching u                     		%
% --------------------------------------------------------------------- %

let find_match u =
 letrec find_mt t =
  (match u t
   ? find_mt(rator t)
   ? find_mt(rand  t)
   ? find_mt(snd(dest_abs t))
   ? failwith `find_match`)
 in
 find_mt;;

%
 SUBST_MATCH (|-u=v) th   searches for an instance of u in
 (the conclusion of) th and then substitutes the corresponding
 instance of v. Much faster than rewriting.
%

let SUBST_MATCH eqth th =
 let tm_inst,ty_inst = find_match (lhs(concl eqth)) (concl th)
 in
 SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th;;


% Possible further simplifications:

  |- !t. ((\x.t1) t2)  =  t1

  |- !t P. (!x. t /\ P x) = (t /\ (!x. P x))

  |  !x:*. (@x'.x'=x) = x

  |- !t1 t2 t3. (t1\/t2) ==> t3   =   (t1==>t3) /\ (t2==>t3)  

  |- !t1 t2 t3.  (t1\/t2) /\ t3   =   (t1/\t3) \/ (t2/\t3)   

  |- !t1 t2 t3.  t3 /\ (t1\/t2)   =   (t3/\t1) \/ (t3/\t2)   

  |- !t P.  (?x.P x) ==> t   =   !x'.(P x' ==> t)

  |- !t P.  (?x.P x) /\ t   =   ?x'.(P x' /\ t)

  |- !t P.  t /\ (?x.P x)   =   ?x'.(t /\ P x')

  |- !t1 t2.  (t1<=>t2)  =  (t1==>t2  /\  t2==>t1)

%

