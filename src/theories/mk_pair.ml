%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_pair.ml                                            %
%                                                                             %
%     DESCRIPTION:      Define a theory of pairs                              %
%                                                                             %
%     WRITES FILES:     pair.th                                               %
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

% In this theory we define pairs and verify the basic properties. The
  built-in theory of pairs (i.e. the theory `prod`) is put in with mk_thm
  for kludgy reasons hinted at in the file theories/mk_bool.ml %

new_theory `pair`;;

let MAKE_PAIR_DEF =
 new_definition
  (`MAKE_PAIR_DEF`, "MAKE_PAIR(x:*)(y:**) = \a b.(a=x)/\(b=y)");;

let ISA_PAIR_DEF =
 new_definition
  (`ISA_PAIR_DEF`, "ISA_PAIR p = ?x:*.?y:**. p = MAKE_PAIR x y");;

let PAIR_EXISTS_THM =
 prove_thm
  (`PAIR_EXISTS_THM`,
   "?p:*->**->bool. ISA_PAIR p",
   EXISTS_TAC "MAKE_PAIR (x:*) (y:**)"
    THEN REWRITE_TAC[MAKE_PAIR_DEF;ISA_PAIR_DEF]
    THEN EXISTS_TAC "x:*"
    THEN EXISTS_TAC "y:**"
    THEN REWRITE_TAC[]);;

new_type_definition
 (`pair`, "ISA_PAIR:(*->**->bool)->bool", PAIR_EXISTS_THM);;

let ABS_pair =
 new_definition
  (`ABS_pair_DEF`, "ABS_pair p = @p':(*,**)pair. REP_pair p' = p");;

let COMMA_DEF =
 new_infix_definition
  (`COMMA`, "$COMMA (x:*) (y:**) = ABS_pair(MAKE_PAIR x y)");;

let FIRST_DEF =
 new_definition
  (`FIRST_DEF`, "FIRST(p:(*,**)pair) = @x.?y. MAKE_PAIR x y = REP_pair p");;

let SECOND_DEF =
 new_definition
  (`SECOND_DEF`, "SECOND(p:(*,**)pair) = @y.?x. MAKE_PAIR x y = REP_pair p");;

% Not yet finished ... %

let ABS_REP =
 prove_thm
  (`ABS_REP`,
   "ABS_pair(REP_pair(p:(*,**)pair)) = p",
   ???);;

let PAIR_THM =
 prove_thm
  (`PAIR_THM`,
    "!x:(*,**)pair. (FIRST x) COMMA (SECOND x) = x",
    GEN_TAC
     THEN REWRITE_TAC[FIRST_DEF;SECOND_DEF;COMMA_DEF;MAKE_PAIR_DEF]);;

let FIRST_THM =
 prove_thm
  (`FIRST_THM`,
    "!x:*.!y:**. FIRST(x COMMA y) = x",
    GEN_TAC
     THEN REWRITE_TAC[FIRST_DEF;SECOND_DEF;COMMA_DEF;MAKE_PAIR_DEF]);;

let SECOND_THM =
 prove_thm
  (`SECOND_THM`,
    "!x:*.!y:**. SECOND(x COMMA y) = y",
    GEN_TAC
     THEN REWRITE_TAC[FIRST_DEF;SECOND_DEF;COMMA_DEF;MAKE_PAIR_DEF]);;

close_theory();;
