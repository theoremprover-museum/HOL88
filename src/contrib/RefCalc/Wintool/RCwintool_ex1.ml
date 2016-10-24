% File: RCex_window1.ml

  testing the window inference
%

% simple example: demonic assignment made deterministic %

let RBEGIN_STACK s t = BEGIN_STACK s t [] [];;

RBEGIN_STACK `EX1` "(refines)(nondass \x x'. x'>x)";;
C_MATCH_TRANSFORM_WIN (ISPEC "\x.x+1" nondass_to_assign);;
WIN_THM();;
ESTABLISH (hd(hyp(WIN_THM())));;
REWRITE_WIN[GSYM ADD1;GREATER;LESS_SUC_REFL];;
CLOSE_WIN();;
WIN_THM();;
END_STACK `EX1`;;


% trivial example with various constructs %

BEGIN_STACK 
  `EX2` 
  "(refines)
   (block (\(x:num,y:bool).0<x)
          (skip seq (do (\(x,y).y/\(0<x)) (assert \(x,y).0<x))))"
  []
  [];;
OPEN_WIN [RAND];;          % using IBLOCK_CLOSE %
OPEN_WIN [RAND];;          % using SEQ_RIGHT_CLOSE %
OPEN_WIN [RAND];;          % using DO_CLOSE %
let th = prove ("skip refines (assert(p:^pred))",
      LPORT[refines_DEF;ref_DEF;assert_DEF;skip_DEF] THEN PRED_TAUT_TAC);;
MATCH_TRANSFORM_WIN th;;
CLOSE_WIN();;
CLOSE_WIN();;
CLOSE_WIN();;
WIN_THM();;
END_STACK `EX2`;;
