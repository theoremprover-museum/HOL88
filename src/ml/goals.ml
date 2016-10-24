%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        goals.ml                                              %
%                                                                             %
%     DESCRIPTION:      Utilities for maintaining subproofs, underlies goal   %
%                       stack package                                         %
%                                                                             %
%     USES FILES:       basic-hol lisp files, bool.th, genfns.ml, hol-syn.ml, %
%                       hol-thyfn.ml, hol-rule.ml, hol-drule.ml, drul.ml,     %
%                       tacticals.ml                                          %
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
%     REVISION HISTORY: Subgoals numbered (MJCG 31.01.94)                     %
%=============================================================================%

% Must be compiled in the presence of the hol parser/pretty printer	%
% This loads genfns.ml and hol-syn.ml too.				%
% Also load hol-rule.ml, hol-drule.ml, drul.ml, tacticals.ml, etc	%

if compiling then  (loadf `ml/hol-in-out`;
		    loadf `ml/hol-thyfn`;
		    loadf `ml/hol-rule`;
		    loadf `ml/hol-drule`;
		    loadf `ml/drul`;
		    loadf `ml/tacticals`);;


% mapcount f [x1;x2; ... ;xn] = [f 1 x1; f 2 x2; ... ;f n xn] %
% Added 31.01.94 by MJCG to support new print_hyps            %




% Assignable print function. Added by RJB 6/6/90. %
letref assignable_print_term = print_term;;

% Added by MJCG 31.01.94                                                %
new_flag(`number_subgoals`, true) ? ();; 

% Print assumptions -- in reverse order so new assumptions appear last. %
% Term-printing function made assignable by RJB 6/6/90.                 %
% Assumption numbering added by MJCG 31.01.94                           %
let print_hyps asl =
 let len = length asl + 1
 in
 letrec map_fn f n l = if null l then [] else f n (hd l).map_fn f (n+1) (tl l)
 in
 let print n as =
  let asm_head = 
   (if get_flag_value `number_subgoals`
     then `  ` ^ string_of_int(len-n) ^ (if (len-n) < 10  then `  [`
                                         if (len-n) < 100 then ` [`  else `[`)
     else `    [`)
  in
  (print_string asm_head;
   assignable_print_term (as); 
   print_string ` ]`;
   print_newline())
   in
   do (map_fn print 1 (rev asl));;

let print_goal (asl,w) =
    assignable_print_term w; print_newline(); print_hyps asl; print_newline();;

% Version of ML function prove that prints out the unsolvable goals.
  Added by MJCG 12/11/89 (based on code from Phil Windley).
%

let PROVE : (term # tactic) -> thm =
    set_fail_prefix `PROVE`
       (\(t,tac). 
           let gl,p = tac([],t) in
           if null gl then p[]
           else (message (`Unsolved goals:`);
                 map print_goal gl;
                 print_newline();
                 failwith `unsolved goals`));;



%Prove and store a theorem%
let prove_thm(tok, w, tac:tactic) =
    let gl,prf = tac ([],w) in
    if null gl then save_thm (tok, prf[])
    else
       (message (`Unsolved goals:`);
	map print_goal gl;
	print_newline();
	failwith (`prove_thm -- could not prove ` ^ tok));;

 

lettype subgoals = goal list # proof;;


%
The key to handling subgoals is to incorporate proved ones into the proof
immediately.  Suppose a tactic returns three subgoals:

	[g1;g2;g3], prf3

after proving a theorem th1 that achieves g1, we get the subgoals

	[g2;g3], prf2		where prf2 [th2;th3] = prf3 [th1;th2;th3]

rotating the subgoals gives us

	[g3;g2], prf2'		where prf2' [th3;th2] = prf2 [th2;th3]
%


let root_goal g : subgoals =  ([g], \[th].th);;


let attempt_first ((gl,pr):subgoals) tac : subgoals = 
    if null gl then failwith `no goals to expand`
    else tac (hd gl);;


% rotate_goals modified to use hd, tl, @, last and butlast	%
% instead of rotate_left and rotate_right [RJB 90.10.20].	%

let rotate_goals (gl,pr) :subgoals =
    (tl gl)@[hd gl], pr o (\l. (last l).(butlast l))
    ? failwith `rotate_goals`;;


let achieve_first (((asl,w).gl),pr) th :subgoals =
    (gl, \thl. pr (th . thl));;


let apply_proof =
   set_fail_prefix `apply_proof`
     (\(([],pr):subgoals). pr[]);;

%<Old version:
let print_subgoals ((gl,pr):subgoals) = 
do (let ngs = length gl in
    if ngs>1 then
       (print_int ngs;  print_string ` subgoals`; print_newline())
    else if ngs=0 then (print_string `goal proved`; print_newline());
    map print_goal (rev gl));;
>%

%< New version from Phil Windley:
   modified 10/6/89 to support print_all_subgoals flag -- PJW 
>%

new_flag(`print_all_subgoals`, true) ? ();; % Trap added by MJCG 31.01.94 %

let print_subgoals ((gl,pr):subgoals) = 
do (let ngs = length gl in (
    if ngs>1 then
       (print_int ngs;  print_string ` subgoals`; print_newline())
    else if ngs=0 then (print_string `goal proved`; print_newline());
    if get_flag_value(`print_all_subgoals`) then
       map print_goal (rev gl)
    else
       (if ngs > 1 then (print_string `Current subgoal: `;print_newline()); 
        [if (ngs>0) then print_goal (hd gl)])));;



let print_stack sg_stack n =
    let stack1 = fst (chop_list n sg_stack) ? sg_stack in
    do (map print_subgoals (rev stack1));;



%Use completed proofs to satisfy goals%
letrec pop_proofs sg_stack =
   (let (sgs1 . sgs2 . sg_tail) = sg_stack in
    let th = apply_proof sgs1 in
    print_thm th;  print_newline ();
    pop_proofs (achieve_first sgs2 th .  sg_tail))
   ? sg_stack;;



%pop proofs and print new stack if different%
let pop_proofs_print sg_stack =
    let sg2 = pop_proofs sg_stack in
    if length sg2 < length sg_stack   &  not (null sg2)  then
	(print_newline(); print_string `Previous subproof:`;
	 print_newline(); print_stack sg2 1);
    sg2;;



%Print a new layer of subgoals, and push it onto the stack%
let push_print sgs sg_stack =
    print_subgoals sgs;
    sgs . sg_stack;;




%Expand the top subgoal using the tactic;  push and print new subgoals %
%the f is for "fast" -- does not validate the tactic%
let push_fsubgoals sg_stack tac =
    message `OK..`;
    if null sg_stack then failwith `Goal stack is empty`
    else
    pop_proofs_print 
       (push_print (attempt_first (hd sg_stack) tac) sg_stack);;



%push subgoals after validating the tactic%
let push_subgoals sg_stack = 
    (push_fsubgoals sg_stack) o VALID;;



%Rotate subgoals on stack top%
let rotate_top n (sgs . sg_stack) =
    push_print (funpow n rotate_goals sgs) sg_stack;;



%Create a new goalstack, containing the initial goal%
let new_stack g =
    push_print (root_goal g) [];;



%Extract proof on top of stack%
let top_proof (sgs . sg_stack) =
    apply_proof sgs;;


