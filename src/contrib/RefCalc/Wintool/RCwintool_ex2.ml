% File: RCex_window2.ml

  testing the window inference: trivial data refinement
%

let aty = ":num";;
let cty = ":num";;
let sty = ":bool";;
let ainit = "\(a,z:bool).a=0";;
let abody = "(nondass \(a,z:bool)(a':num,z'). (a'=a)/\(z' =(a=0)))";;
let absrel = "\(a,k,z:bool).k=a+1";;
let cstep = " \(k,z:bool)(k':num,z'). (k'=k)/\(z'=(k=1))";;

BEGIN_STACK 
  `dataref1` 
  "(refines)
   (block ^ainit ^abody)"
  []
  [];;
BLOCK_DR_WIN absrel;;

OPEN_WIN [RATOR;RAND];;
REWRITE_WIN[abst_DEF];;
CONVERT_WIN (DEPTH_CONV PBETA_CONV);;
ONCE_REWRITE_WIN[CONJ_SYM];;
CONVERT_WIN (DEPTH_CONV EX_1PT_CONV);;
REWRITE_WIN[ADD];;
CLOSE_WIN();;

OPEN_WIN [RAND];;
NONDASS_DR_WIN cstep;;
CLOSE_WIN();;

ESTABLISH (hd(hyp(WIN_THM())));;
goal (focus (TOP_WIN()));;
e(REPEAT STRIP_TAC THEN EXISTS_TAC "a:num" THEN ART[] THEN
  PORT[num_CONV"1"] THEN LRT[ADD_CLAUSES;INV_SUC_EQ]);;
REWRITE_WIN[top_thm()];;
CLOSE_WIN();;

WIN_THM();;
END_STACK `dataref1` ;;

