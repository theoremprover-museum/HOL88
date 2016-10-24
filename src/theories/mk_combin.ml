%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_combin.ml                                          %
%                                                                             %
%     DESCRIPTION:      Creates the theory "combin.th" containing some basic  %
%                       combinator definitions and theorems about them.       %
%                                                                             %
%     AUTHOR:           T. F. Melham (87.02.26)                               %
%                                                                             %
%     PARENTS:          BASIC-HOL.th                                          %
%     WRITES FILES:     combin.th                                             %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% Create the new theory.						%
new_theory `combin`;;

% Definition of function composition.					%
let o_DEF =
    new_infix_definition
     (`o_DEF`, "$o (f:** -> ***) g = \x:*.f(g(x))");;

% Definition of K.							%
let K_DEF = new_definition(`K_DEF`, "K = \x:*.\y:**.x");;

% Definition of S.							%
let S_DEF = 
    new_definition
	(`S_DEF`, 
	 "S = \f:*->**->***.\g:*->**.\x:*. (f x)(g x)");;

% Definition of the Identity function.					%


% MJCG for HOL88:
  Type of K changed to ":*->*->*" to prevent unbound free type variable %

let I_DEF = new_definition(`I_DEF`, "(I:*->*) = S K (K:*->*->*)");;

% Close the theory.							%
close_theory ();;


% Theorem about application of composed functions.			%
let o_THM = 
    prove_thm(`o_THM`,
	      "!f:**->***. !g:*->**. !x:*.(f o g) x = f(g(x))", 
	      PURE_REWRITE_TAC [o_DEF] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT GEN_TAC THEN REFL_TAC);;

% This theorem states that function composition is associative.		%
let o_ASSOC =
    prove_thm(`o_ASSOC`,
	      "!f:***->****. !g:**->***. !h:*->**.f o (g o h) = (f o g) o h",
	      REPEAT GEN_TAC THEN REWRITE_TAC [o_DEF] THEN
	      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
	      REFL_TAC);;

% Theorem about application of K.					%
let K_THM = 
    prove_thm(`K_THM`,
	      "!x:*.!y:**. K x y = x",
	      PURE_REWRITE_TAC [K_DEF] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT GEN_TAC THEN REFL_TAC);;

% Theorem about application of S.					%
let S_THM = 
    prove_thm(`S_THM`,
	      "!f:*->**->***.!g:*->**.!x:*. S f g x = (f x)(g x)",
	      PURE_REWRITE_TAC [S_DEF] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      REPEAT GEN_TAC THEN REFL_TAC);;

% Theorem about application of I.					%
let I_THM = 
    prove_thm(`I_THM`,
	      "!x:*. I x = x",
	      REWRITE_TAC [I_DEF;S_THM;K_THM] THEN
	      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	      GEN_TAC THEN REFL_TAC);;

% I is the identity for function composition.				%
let I_o_ID =
    prove_thm(`I_o_ID`,
	      "!f:*->**. (I o f = f) /\ (f o I = f)",
	      REPEAT STRIP_TAC THEN
	      CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
	      REWRITE_TAC [o_DEF] THEN
	      CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
	      REWRITE_TAC [I_THM]);;

quit();;
