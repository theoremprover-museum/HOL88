%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        stack.ml                                              %
%                                                                             %
%     DESCRIPTION:      A system of routines to maintain goals and partial    %
%                       results. You create and traverse the proof tree       %
%                       top-down, left to right. You expand the current goal  %
%                       into a list of subgoals, which are pushed onto the    %
%                       goalstack, on top of the proof.                       %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-thyfn.ml, hol-rule.ml, hol-drule.ml, drul.ml,     %
%                       tacticals.ml, goals.ml                                %
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

% Operations:                                                           %
%   set_goal g          state the top-level goal                        %
%   expand tac          apply a tactic to the topmost goal              %
%   expandf tac         fast expand -- don't check validity of tactic   %
%   print_state n       print topmost n goals                           %
%   top_thm ()          return the top of the theorem stack             %
%   save_top_thm name   call save_thm (name, top of thmstack)           %
%   rotate n            rotate goals to move the nth goal to the front  %
%   backup ()           undo last proof step (may be repeated)          %
%                                                                       %

% Must be compiled in the presence of the hol parser/pretty printer     %
% This loads genfns.ml and hol-syn.ml too.                              %
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml, etc       %

if compiling then  (loadf `ml/hol-in-out`;
                    loadf `ml/hol-thyfn`;
                    loadf `ml/hol-rule`;
                    loadf `ml/hol-drule`;
                    loadf `ml/drul`;
                    loadf `ml/tacticals`;
                    loadf `ml/goals`);;

abstype goalstack = subgoals list
    with abs_goals = abs_goalstack
    and  rep_goals = rep_goalstack;;


letref goals = abs_goals []
and    (backup_list: goalstack list) = [];;


%Parameters for the user to adjust%

%Minimum number of previous states to retain%
letref backup_limit = 12;;


let print_state depth =
    print_stack (rep_goals goals) depth;;


let change_state newgoals =
   do (let newbackup =
              fst (chop_list backup_limit backup_list)
              ? backup_list
       in
       %no failures in these assignments%
       backup_list := goals . newbackup;
       goals := newgoals);;


% Set the top-level goal, initialize                                    %
% Added test for boolean goal, including assumptions [JRH 92.02.12]     %

let set_goal =
  let bty = ":bool" in
  let isbty tm = (type_of tm = bty) in
  \(asl,w). if forall isbty (w.asl) then
              change_state (abs_goals (new_stack (asl,w)))
            else failwith `Term in goal not of type ":bool"`;;


%Expand the top subgoal using the tactic%
let expandf tac =
   change_state (abs_goals (push_fsubgoals (rep_goals goals) tac));;


%Expand after validating tactic %

let expand = expandf o VALID;;


%Rotate goals of current proof%
let rotate n = change_state (abs_goals (rotate_top n (rep_goals goals)));;


%Restore the previous proof state;  discard current state. %
let (backup : void->void) () =
   (let newgoals.newbackup = backup_list in
    if null (rep_goals newgoals) then fail
    else do
     (goals := newgoals;
      backup_list := newbackup;
      print_state 1))
    ? failwith `backup:  backup list is empty`;;

%Get top theorem (added by MJCG 17/10/89)%

let top_thm =
 set_fail_prefix `top_thm`
  (\():void. top_proof(rep_goals goals));;

%Record topmost theorem on a Fact file.%
let save_top_thm =
 set_fail_prefix `save_top_thm`
    (\name. save_thm(name, top_thm()));;


let top_goal : void->goal =
  set_fail_prefix `top_goal` (\().
    let (g.gl),prf = hd (rep_goals goals) in
    g);;


let get_state: void -> goalstack = \().goals;;
let set_state goals = change_state goals; print_state 1;;


% Added TFM 88.03.31 and MJCG 89.01.17                                  %

let g = \t. set_goal([],t)
and e = expand
and p = print_state
and b = backup
and r = rotate;;
