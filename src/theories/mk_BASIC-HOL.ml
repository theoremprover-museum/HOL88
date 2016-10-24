%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_BASIC-HOL.ml                                       %
%                                                                             %
%     DESCRIPTION:      Proves a simple theorem that is useful for defining   %
%                       new logical types.  Stores this theorem in BASIC-HOL. %
%                                                                             %
%     AUTHOR:           T. F. Melham 87.02.26                                 %
%                                                                             %
%     USES FILES:       basic-hol lisp files, ind.th, genfns.ml, hol-syn.ml   %
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

load_theory `ind`;;

% Load the hol parser/pretty printer.					%
loadf (concat ml_dir_pathname `hol-in-out`);;   

% Load the required theorem-proving support.				%
loadf (concat ml_dir_pathname `hol-rule`);;
loadf (concat ml_dir_pathname `hol-drule`);;
loadf (concat ml_dir_pathname `hol-thyfn`);;

new_theory `BASIC-HOL`;;

% new_parent `ind`;;  Redundant (MJCG 22 Sept 1989)                     %

% close the theory							%
close_theory();;

% The following theorem is used to prove generally useful lemmas for 	%
% newly defined logical types.  Given a type axiom of the form asserted	%
% by "new_type_definition":						%
%									%
%    |- ?rep. TYPE_DEFINITION P rep					%
%									%
% we wish to show that there exist abstraction and representation 	%
% functions ABS and REP, such  that:					%
%									%
% 1: (!a. ABS(REP a) = a)  --- I.e. ABS is the left inverse of REP.	%
%									%
% 2: (!r. P r = (REP(ABS r) = r)) --- I.e. REP is the left inverse of	%
%    ABS for the set of things in P.					%


% Load the definition of TYPE_DEFINITION.				%
let TYPE_DEFINITION = definition `bool` `TYPE_DEFINITION`;;

% Now prove the theorem							%
let ABS_REP_THM = 
    let th1 = ASSUME "?rep:**->*. TYPE_DEFINITION P rep" and
        th2 = MK_EXISTS (SPEC "P:*->bool" TYPE_DEFINITION) in
    let def = EQ_MP th2 th1 in
    let asm = ASSUME (snd(dest_exists(concl def))) in
    let (asm1,asm2)  = (CONJUNCT1 asm, CONJUNCT2 asm) in
    let rep_eq = 
        let th1 = DISCH "a:**=a'"(AP_TERM "rep:**->*" (ASSUME "a:**=a'")) in
        IMP_ANTISYM_RULE (SPECL ["a:**";"a':**"] asm1) th1 in
    let ABS = "\r:*. @a:**. r = rep a" in
    let absd =  RIGHT_BETA (AP_THM (REFL ABS) "rep (a:**):*") in
    let lem = SYM(SELECT_RULE(EXISTS ("?a':**.a=a'","a:**") (REFL "a:**"))) in
    let TH1 = GEN "a:**" (TRANS(TRANS absd (SELECT_EQ "a':**" rep_eq)) lem) in
    let t1 = SELECT_RULE(EQ_MP (SPEC "r:*" asm2)(ASSUME "(P:*->bool) r")) in
    let absd2 =  RIGHT_BETA (AP_THM (REFL ABS) "r:*") in
    let imp1 = DISCH "(P:*->bool) r" (SYM (SUBS [SYM absd2] t1)) in
    let t2 = EXISTS ("?a:**. r:* = rep a", "^ABS r") 
	            (SYM(ASSUME "rep(^ABS (r:*):**) = r")) in
    let imp2 = DISCH "rep(^ABS (r:*):**) = r" 
     		     (EQ_MP (SYM (SPEC "r:*" asm2)) t2) in
    let TH2 = GEN "r:*" (IMP_ANTISYM_RULE imp1 imp2) in
    let CTH = CONJ TH1 TH2 in
    let ath = subst ["abs:*->**",ABS] (concl CTH) in
    let eth1 = EXISTS ("?abs:*->**. ^ath", ABS) CTH in
    let eth2 = EXISTS ("?rep:**->*. ^(concl eth1)", "rep:**->*") eth1 in
    let result = DISCH (concl th1) (CHOOSE ("rep:**->*",def) eth2) in
        GEN "P:*->bool" result;;

% And save it.								%
save_thm(`ABS_REP_THM`, ABS_REP_THM);;

quit();;
