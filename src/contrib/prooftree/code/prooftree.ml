
% ---------------------------------------------------------------------

An enhanced subgoal package: prooftree.ml

depends on the `prettyp` library; also loads several other files:
 `prettyprinting`, `basic_tactics`, and `lisp_pt`
plus pretty-printing files generated from pp files:
 `print_the_goal`, `print_the_tree`, and `ml_subset`.


		                        Sara Kalvala, jan91

----------------------------------------------------------------------- %


load_library `prettyp` ;;



% ------ the data structures used ------- %

rectype prooftree = unexpanded of goal |
               expanded of (goal # proof # tactic # print_tree #
			    (prooftree list)) |
	       proved of (thm # goal # tactic # proof # tactic #
			   print_tree # (prooftree list)) ;;

letref prooflist = ([]: ((  string        %name of proof%
			  # prooftree     %structure of proof%
			  # ((int list) list) %goal stack%
			  # ((int list) list) %backup list%
			  ) list)) ;;

begin_section prooftree ;;

let goal_at = (fun
      unexpanded gl . gl |
      expanded (gl, prf, tac, printac, subl) . gl |
      proved (thrm, gl, solv_tac, prf, tac, printac, subl) . gl) and
    proof_at = (fun
      expanded (gl, prf, tac, printac, subl) . prf |
      proved (thrm, gl, solv_tac, prf, tac, printac, subl) . prf) and
    proved_thm_at = (fun
      proved (thrm, gl, solv_tac, prf, tac, printac, subl) . thrm) and
    tactic_at = (fun
      expanded (gl, prf, tac, printac, subl) . tac |
      proved (thrm, gl, solv_tac, prf, tac, printac, subl) . tac) and
    full_tac_at = (fun
      proved (thrm, gl, solv_tac, prf, tac, subl) . solv_tac) and
    subgoals_at = (fun
      expanded (gl, prf, tac, printac, subl) . subl |
      proved (thrm, gl, solv_tac, prf, tac, printac, subl) . subl) and
    print_tac_at = (fun
      expanded (gl, prf, tac, printac, subl) . printac |
      proved (thrm, gl, solv_tac, prf, tac, printac, subl) . printac) and
    unexpanded_node = (fun
      unexpanded (gl) . true |
      expanded (anode) . false |
      proved (anode) . false) and
    expanded_node = (fun
      unexpanded (gl) . false |
      expanded (anode) . true |
      proved (anode) . false) and
    proved_node = (fun
      unexpanded (gl) . false |
      expanded (anode) . false |
      proved (anode) . true) ;;

letref contextname = `defaultproof` ;;


% flag to indicate whether a node which has already been expanded can be
  expanded again (losing previous subproof) %

new_flag(`dont_cancel`,      true);;

let pack_path = (hol_pathname () ^ `/contrib/prooftree/code/`) ;;
loadf (pack_path ^ `prettyprinting`) ;;

% ------- general functions ----------- %

letrec removefromlist theelem thelist =
   null thelist => thelist |
       (fst (hd thelist)) = theelem =>
	    (removefromlist theelem (tl thelist)) |
	    ((hd thelist) . (removefromlist theelem (tl thelist))) ;;


letrec reconvert foclist =
(null foclist => ``|
     ((string_of_int (hd foclist)) ^ `.` ^ (reconvert (tl foclist)))) ;;

% given a list of type [1;2;1;..] return the node which
  is pointed by it %

letrec find_focus foc_addr a_prooftree =
(null foc_addr => a_prooftree
		|find_focus (tl foc_addr)
		 (el (hd foc_addr) (subgoals_at a_prooftree))
		  )? failwith `no node at given position` ;;

% insert a modified subtree into a prooftree, when the new subtree
  does not validate nodes above it %

let find_proof prooftreename =
	(snd (assoc prooftreename prooflist))? failwith
 `no such proof` ;;

% --------- user-level functions --------- %

loadf (pack_path ^ `basic_tactics`) ;;

% starting a new proof tree %

let new_goal (proofname: string) (g:goal) =
     let cleanlist = (removefromlist proofname prooflist) in (
     prooflist := ((proofname, unexpanded g, [[]], []) . cleanlist);
     contextname := proofname;
     (print_goal g) ) ;;

let do_tac prooftreename thefocus tac =
     do_tacf prooftreename thefocus (VALID tac) ;;

      
let store_thm prooftreename theoremname =
    let theproof = (fst (find_proof prooftreename)) in
	let (subl, prf) = ((full_tac_at theproof) (goal_at theproof)) in
	    (save_thm (theoremname, prf []);
% some people have asked for the proof not to be removed
	     prooflist := (removefromlist prooftreename prooflist) ; %
	     print_newline ();
	     print_string `saving theorem `; print_string theoremname;
%	     print_thm (prf []);%
	     print_newline(); print_newline();
	     print_string `solving tactic:`; print_newline ();
	     show_full_tac theproof;  print_newline (); prf []) ;;


let remove_proof prooftreename =
    let (theprooftree, focuslist, backuplist) =
	(find_proof prooftreename) in
	   (prooflist := (removefromlist prooftreename prooflist) ;
	    ():void ) ;;

let rm_proof (a:void) = remove_proof contextname ;;

let move_to_proof newone =
    (contextname := newone ;
    let (prooftree, focuslist, backuplist) =
	(find_proof contextname) in
     print_goal (goal_at (find_focus (hd focuslist) prooftree))) ;;

let proven prooftreename =
    let theproof = (fst (find_proof prooftreename)) in
	let (subl, prf) = ((full_tac_at theproof) (goal_at theproof)) in
	    prf [];;

let name_current_proof newname =
    let (prt,foc,bac) = (find_proof contextname) in
	let cleanlist = (removefromlist contextname prooflist) in (
     prooflist := ((newname,prt,foc,bac) . cleanlist);
     contextname := newname;
     print_goal (goal_at (find_focus (hd foc) prt))) ;;


% ------- extra display functions --------------------  %

let complete_proof prooftreename =
    let (prooftree, focuslist, backuplist) =
	(find_proof prooftreename) in
	 show_tree prooftree (null focuslist => [] | (hd focuslist));;

let current_proof (a:void) = complete_proof contextname ;;

let show_the_tactic prooftreename =
    let theproof = (fst (find_proof prooftreename)) in
	show_full_tac theproof %thefocus% ;;

let current_goal prooftreename =
    let (prooftree, focuslist, backuplist) =
	(find_proof prooftreename) in
	(print_newline ();
	 print_string `goal at `; print_string (reconvert (hd focuslist));
	 print_newline ();
	 print_goal (goal_at
		     (find_focus (hd focuslist) prooftree))
	  );;

let show_all_proofs (a: void) =
    print_newline ();
    (map (\prf.
	  ((proved_node (fst (snd prf)) =>
		print_string `PROVED     ` |
		print_string `UNPROVED   `);
	   print_string (fst prf); print_newline ();
	   (proved_node (fst (snd prf)) =>
		(print_thm (proved_thm_at (fst (snd prf))); print_newline ())
	       |print_goal (goal_at (fst (snd prf))))) ) prooflist);
     print_newline ();
     ():void ;;

let show_tac  (a:void) = show_the_tactic contextname ;;

let show_all_subgoals prooftreename =
    let (theprooftree, focuslist, backuplist) =
	(find_proof prooftreename) in
	 (map (\eachfocus.
	       (print_string (reconvert eachfocus) ; print_newline ();
		print_goal (goal_at
			    (find_focus eachfocus theprooftree))))
			     (rev focuslist); (): void) ;;

let all_subgoals (a: void) = show_all_subgoals contextname ;;


letrec convert focstring =
letrec isolate numpart rest =
    null rest => (numpart, rest) |
	((hd rest = `.`) => (numpart, (tl rest)) |
	      let (newnum, newrest) = (isolate [hd rest] (tl rest)) in
		  ((numpart @ newnum), newrest))
in
let foc = (explode focstring) in
    null foc => [] |
let (numpart, rest) = (isolate [] foc) in
(int_of_string (implode numpart)) . (convert (implode rest)) ;;


let subgoal_tac prooftreename atfocus = 
    let (theprooftree, focuslist, backuplist) =
	(find_proof prooftreename) and
    real_focus = (convert atfocus) in
	 show_full_tac (find_focus real_focus theprooftree) ;;


% ------- mapping previous subgoal package -----------  %


let set_goal g =  new_goal `defaultproof` g ;;

let expand sometac =
let foclist = (fst (snd (find_proof contextname))) in
    do_tac contextname (null foclist => ``| 
			(reconvert (hd foclist))) sometac ;;

let backup (a:void) =
    let backuplist = (snd (snd (find_proof contextname))) in
	cancel_tac contextname (null backuplist => ``|
				(reconvert (hd backuplist))) ;;

let backupn n =
    let backuplist = (snd (snd (find_proof contextname))) in
	(map ((cancel_tac contextname) o reconvert)
	 (fst (chop_list n backuplist)); ():void) ;;


let save_top_thm aname = store_thm contextname aname ;;


let top_thm (a:void) =
    let theproof = (fst (find_proof contextname)) in
	let (subl, prf) = ((full_tac_at theproof) (goal_at theproof)) in
	    prf [];;

let top_goal (a:void) = current_goal contextname ;;

% rotate has a different semantics %

let rotate (n:int) =
    let (theproof, thefocus, thebackup) = (find_proof contextname) in
    let (a,b) = (chop_list (n < (length thefocus) => (n+1)|n)
		 thefocus) in
    let newfocus = ((funpow n (\l. (tl l)@[hd l]) a) @ b) in
    let cleanlist = (removefromlist contextname prooflist) in (
     prooflist := ((contextname,theproof,newfocus,thebackup) .
		   cleanlist);
     print_goal (goal_at (find_focus (hd newfocus) theproof))) ;;

% print_state and rotate don't really make sense with this structure,
  so haven't implemented them... %

let g t = set_goal ([], t)
and e = expand
and p = print_state
and b = backup
and r = rotate ;;


(do_tacf, cancel_tac, compact, new_goal, do_tac, store_thm, remove_proof,
rm_proof, move_to_proof, proven, name_current_proof, complete_proof,
current_proof, show_the_tactic, current_goal, show_all_proofs, show_tac,
show_all_subgoals, all_subgoals, subgoal_tac, set_goal, expand, backup,
backupn, save_top_thm, top_thm, top_goal, rotate, g, e, p, b, r) ;;
end_section prooftree ;;

let
(do_tacf, cancel_tac, compact, new_goal, do_tac, store_thm, remove_proof,
rm_proof, move_to_proof, proven, name_current_proof, complete_proof,
current_proof, show_the_tactic, current_goal, show_all_proofs, show_tac,
show_all_subgoals, all_subgoals, subgoal_tac, set_goal, expand, backup,
backupn, save_top_thm, top_thm, top_goal, rotate, g, e, p, b, r) = it ;;
