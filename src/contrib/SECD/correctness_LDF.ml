% SECD verification                                                 %
%                                                                   %
% FILE:         correctness_LDF.ml                                  %
%                                                                   %
% DESCRIPTION:  This sets up the top level goal, and starts         %
%               on simplifying it.  Useful for examining the        %
%               structure of the goal.                              %
%                                                                   %
% USES FILES:   constraints.th, mem_abs.th, when.th                 %
%               prove_SYS_lemmas*                                   %
%                                                                   %
% Brian Graham 90.05.10                                             %
%                                                                   %
% Modifications:                                                    %
% 06.12.90 BtG Revised to the standardized proof format.            %
% 08.08.91 - BtG - updated to HOL2                                  %
% ================================================================= %
new_theory `correctness_LDF`;;

map new_parent
[ `correctness_misc`
; `liveness`
];;

loadf `wordn`;;
load_library `integer`;;

map (load_theorem `correctness_misc`)
 [ `LET_THM`
 ; `Store14_root_2_lemma`
 ; `Store14_car_cdr_2_lemma`
 ; `LDF_opcode_lemma`
 ];;

map (load_definition `when`)
 [ `when`
 ];;
map (load_theorem `when`)
 [ `TimeOf_Next_lemma`
 ];;

map (load_definition `constraints`)
 [ `reserved_words_constraint`
 ];;
map (load_theorem `constraints`)
 [ `state_abs_thm`
 ; `well_formed_free_list_lemma`
 ; `well_formed_free_list_nonintersection_lemma`
 ];;
map (load_definition `top_SECD`)
 [ `LDF_trans`
 ; `cell_of`
 ; `mem_free_of`
 ; `mem_of`
 ; `free_of`
 ];;
map (load_theorem `mu-prog_LDF`)
 [ `LDF_state`
 ; `LDF_Next`
 ];;
map (load_definition `abstract_mem_type`)
 [ `M_CAR`
 ; `M_CDR`
 ; `M_Cons_tr`
 ];;
map (load_theorem `mem_abs`)
 [ `car_cdr_mem_abs_lemma`
 ; `M_Cons_unfold_1_thm`
 ; `M_Cons_unfold_2_thm`
 ];;
% ================================================================= %
let mtime = ":num"
and ctime = ":num";;
let w14_mvec = ":^mtime->word14";;

let mem14_32 = ":word14->word32";;
let m14_32_mvec = ":^mtime->^mem14_32";;
let M = ":(word14,atom)mfsexp_mem";;
let M_mvec = ":^mtime->^M";;

let state = ":bool # bool";;
let state_msig = ":^mtime->^state"
and state_csig = ":^ctime->^state";;

%=================================================================%
% This defines a relation on the inputs and outputs.              %
%=================================================================%
let SYS_imp = (hd o tl o hyp)(theorem `phase_lemmas1` `phase_lemma_0`);;

% ================================================================= %
loadt `ABBREV_TAC`;;

% ================================================================= %
timer true;;

% ================================================================= %
% Discharge every assumption with "t" in it, and generalize it.     %
% ================================================================= %
let LDF_state' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000011"
         LDF_state));;
let LDF_Next' =
 GEN "t:^mtime" 
 (DISCH "mpc (t:^mtime) = #000101011"
  (DISCH "opcode_bits((memory:^m14_32_mvec) t(car_bits(memory t(c t))))
          = #000000011"
         LDF_Next));;

% ================================================================= %
% Correctness goal for the LDF instruction.                         %
% ================================================================= %
let correctness_LDF = TAC_PROOF
(([
   % ----------------------------- (cdr c) is a cons cell %
    "is_cons(memory(TimeOf(is_major_state mpc)t)
             (cdr_bits(memory(TimeOf(is_major_state mpc)t)
                       ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- the opcode is LDF %
    "atom_bits(memory(TimeOf(is_major_state mpc)t)
             (car_bits(memory(TimeOf(is_major_state mpc)t)
                       ((c:^w14_mvec)(TimeOf(is_major_state mpc)t))))) =
     #0000000000000000000000000011" 
 ; % ----------------------------- opcode is a number record %
    "is_number(memory(TimeOf(is_major_state mpc)t)
               (car_bits(memory(TimeOf(is_major_state mpc)t)
                         ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))))"
 ; % ----------------------------- c is itself a cons cell %
    "is_cons(memory(TimeOf(is_major_state mpc)t)
             ((c:^w14_mvec)(TimeOf(is_major_state mpc)t)))"
 ; "mpc(TimeOf(is_major_state mpc)t) = #000101011" 
 ; "Inf(is_major_state mpc)"
 ; "well_formed_free_list memory mpc free s e c d"
 ; "reserved_words_constraint mpc memory" 
 ; SYS_imp
 ; "clock_constraint SYS_Clocked" 
 ],
 "((s                  when (is_major_state mpc))(SUC t),    
   (e                  when (is_major_state mpc))(SUC t),
   (c                  when (is_major_state mpc))(SUC t),
   (d                  when (is_major_state mpc))(SUC t),
   (free               when (is_major_state mpc))(SUC t), 
   ((mem_abs o memory) when (is_major_state mpc))(SUC t), 
   ((state_abs o mpc)  when (is_major_state mpc))(SUC t)) =
   LDF_trans ((s                  when (is_major_state mpc))t,
              (e                  when (is_major_state mpc))t,
              (c                  when (is_major_state mpc))t,
              (d                  when (is_major_state mpc))t,
              (free               when (is_major_state mpc))t,
              ((mem_abs o memory) when (is_major_state mpc))t)
 "),
 FIRST_ASSUM				% state_abs is top_of_cycle %
      (\th. (ASSUME_TAC o (porr[state_abs_thm])
			o (AP_TERM "state_abs")) th ? NO_TAC)
 THEN IMP_RES_TAC LDF_opcode_lemma 		% opcode_bits assumption %
 THEN port[when]
 THEN in_conv_tac BETA_CONV
					% Next assumption %
 THEN IMP_RES_THEN (ASSUME_TAC o UNDISCH) LDF_Next'
 					% rewrite Timeof ... (SUC t) %
 THEN IMP_RES_n_THEN 2 port1 TimeOf_Next_lemma
 THEN port[o_THM]

					% abbreviate times for readability ... %
 THEN ABBREV_TAC "(TimeOf(is_major_state mpc)t)" "t':num"

					% generate req'd assumptions ... %
 THEN IMP_RES_n_THEN 3 ASSUME_TAC
                       well_formed_free_list_lemma
	    % only 3 of the 6 free cell inequalities are likely needed %
 THEN IMP_RES_n_THEN 2			% mem0 NIL_addr = ... %
      (\th. (free_in "NIL_addr" (concl th)) => ASSUME_TAC th | ALL_TAC)
      reserved_words_constraint
 THEN IMP_RES_n_THEN 2			% nonintersecting mem0 free [s;e;c] %
      (\th. (free_in "c:^w14_mvec" (concl th))
             => ASSUME_TAC th
              | ALL_TAC)
      well_formed_free_list_nonintersection_lemma

 THEN port[LDF_trans]                    % unfold spec %
% ================================================================= %
			                % expand the M_* ops %

 THEN port[M_CDR]                       % rewrite M_CDR c  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
 THEN port[M_CAR]                       % rewrite M_CAR (cdr c)  %
 THEN IMP_RES_THEN port1 car_cdr_mem_abs_lemma
					% rewrite the 1st M_Cons %
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_1_thm))
 THEN port[M_Cons_tr]
 THEN IMP_RES_n_THEN 3 port1 (hd(IMP_CANON M_Cons_unfold_2_thm))
					% unwind the cell1_mem_free let binding %
 THEN port[LET_THM]
 THEN in1_conv_tac BETA_CONV
 THEN prt[cell_of; mem_free_of; free_of; mem_of]

 THEN port[M_CDR]			% unwind M_CDR (c,mem2, ) %
 THEN IMP_RES_n_THEN 4
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_root_2_lemma))
 THEN IMP_RES_n_THEN 5			% unwind M_Cdr (cdr(mem2 s),mem2, ) %
      ((IMP_RES_THEN (port1 o (MATCH_MP car_cdr_mem_abs_lemma) o SPEC_ALL))
       o snd
       o EQ_IMP_RULE
       o (AP_TERM "is_cons")
       o SPEC_ALL)
      (hd(IMP_CANON Store14_car_cdr_2_lemma))
					% simplify _imp view %
 THEN IMP_RES_THEN (SUBST1_TAC o UNDISCH) LDF_state'
 THEN port[state_abs_thm]
 THEN REFL_TAC
 );;

% ================================================================= %
save_thm(`correctness_LDF`,correctness_LDF);;

timer false;;
close_theory ();;
print_theory `-`;;
