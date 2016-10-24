%******************************************************************************
** LIBRARY:     reduce (part III)                                            **
**                                                                           **
** DESCRIPTION: Reduction tools using all the conversions in the library     **
**                                                                           **
** AUTHOR:      John Harrison                                                **
**              University of Cambridge Computer Laboratory                  **
**              New Museums Site                                             **
**              Pembroke Street                                              **
**              Cambridge CB2 3QG                                            **
**              England.                                                     **
**                                                                           **
**              jrh@cl.cam.ac.uk                                             **
**                                                                           **
** DATE:        18th May 1991                                                **
** REVISED:      8th July 1991                                               **
******************************************************************************%

%-----------------------------%
% Extend the help search path %
%-----------------------------%

tty_write `Extending help search path`;
let path = library_pathname()^`/reduce/help/entries/` in
    set_help_search_path (union [path] (help_search_path()));;

%------------------------------%
% Load the boolean conversions %
%------------------------------%

tty_write `\
Loading boolean conversions`;
load (library_pathname()^`/reduce/boolconv`,get_flag_value `print_lib`);;

%---------------------------------%
% Load the arithmetic conversions %
%---------------------------------%

tty_write `\
Loading arithmetic conversions`;
load (library_pathname()^`/reduce/arithconv`,get_flag_value `print_lib`);;

tty_write `\
Loading general conversions, rule and tactic`;;

%-----------------------------------------------------------------------%
% RED_CONV - Try all the conversions in the library                     %
%-----------------------------------------------------------------------%

let RED_CONV =
  let FAIL_CONV (s:string) (tm:term) = (failwith s) :thm in
  itlist $ORELSEC
         [ADD_CONV;  AND_CONV;  BEQ_CONV;  COND_CONV;
          DIV_CONV;  EXP_CONV;   GE_CONV;    GT_CONV;
          IMP_CONV;   LE_CONV;   LT_CONV;   MOD_CONV;
          MUL_CONV;  NEQ_CONV;  NOT_CONV;    OR_CONV;
          PRE_CONV;  SBC_CONV;  SUC_CONV] (FAIL_CONV `RED_CONV`);;

%-----------------------------------------------------------------------%
% REDUCE_CONV - Perform above reductions at any depth.                  %
%-----------------------------------------------------------------------%

let REDUCE_CONV = DEPTH_CONV RED_CONV;;

%-----------------------------------------------------------------------%
% REDUCE_RULE and REDUCE_TAC - Inference rule and tactic versions.      %
%-----------------------------------------------------------------------%

let REDUCE_RULE = CONV_RULE REDUCE_CONV;;

let REDUCE_TAC = CONV_TAC REDUCE_CONV;;
