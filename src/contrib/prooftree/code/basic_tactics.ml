
% applying a tactic to a given node %

begin_section tactics ;;

letrec makemylist n =
   (n = 0) => [] |
	(append (makemylist (n-1)) [[n]]) ;;

letrec remove_descendants pattern thelist =
letrec is_part l1 l2 =
    ((null l1) => true |
	  (null l2 => false |
	       (((hd l1) = (hd l2)) & (is_part (tl l1) (tl l2)))))
in
	(null thelist => [] | 
	     (is_part pattern (hd thelist) =>
		  remove_descendants pattern (tl thelist) |
		  (hd thelist) .
		   (remove_descendants pattern (tl thelist)))) ;;


let replace name value newfocuslist backuplist=
(prooflist := (map (\(aname, aproof, afocuslist, abackuplist) .
		     ((aname = name) =>
			   (aname, value, newfocuslist, backuplist) |
			   (aname, aproof, afocuslist, abackuplist)))
			   prooflist)) ;;


letrec make_change theprooftree change position =
null position => change |
    let (beforelist, (tochange . afterlist)) =
	(chop_list ((hd position) - 1)
	(subgoals_at theprooftree))? failwith `make_change`
    in
	let changedlist = append beforelist
	    ((make_change tochange change (tl position)) .
					    afterlist) in
	      expanded (goal_at theprooftree, proof_at theprooftree,
			tactic_at theprooftree,
			print_tac_at theprooftree, changedlist) ;;


% insert a modified subtree and also validate nodes above %

letrec propagate_proof theprooftree position =
(null position => theprooftree |      
    let parent_position = (butlast position) in
    let parent = (find_focus parent_position theprooftree) in
    let all_subgoals = (subgoals_at parent) in
    let each_proved = (map proved_node all_subgoals) in
    let all_proved = (itlist (\a b . a & b) each_proved true) in
	(all_proved => 
          (let new_tac = ((null (tl all_subgoals)) =>
	      ((tactic_at parent) THEN
		   (full_tac_at (hd all_subgoals))) |
	      ((tactic_at parent) THENL
		   (map full_tac_at all_subgoals))) in
%marking it as proved and checking parent%
	     (propagate_proof
	     (make_change theprooftree
	      (proved ((proof_at parent (map proved_thm_at all_subgoals)),
		       goal_at parent, new_tac, proof_at parent,
		       tactic_at parent, print_tac_at parent,
		       all_subgoals))
	      parent_position) parent_position )) | theprooftree)) ;;


% mark nodes as unproved when a tactic below is cancelled %

letrec unproveup position theprooftree =
(null position => theprooftree |
    let parent_position = (butlast position) in
    let parent = (find_focus parent_position theprooftree) in
	(expanded_node parent) => theprooftree |
    let new_parent = expanded (goal_at parent, proof_at parent,
			       tactic_at parent,
			       print_tac_at parent, subgoals_at parent) in
    let new_tree = (make_change theprooftree new_parent parent_position) in
 unproveup parent_position new_tree) ;;

     loadf (pack_path ^ `lisp_pt`) ;;

let prepare_input = (upper_case o transform_quot o transform_once o
		     transform_pt o first_arg o get_last_parse_tree) ;;

% convert a string of type `1.2.1` into a list [1;2;1] %

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

let do_tacf prooftreename thefocus tac =
    let (theprooftree, focuslist, backuplist) =
        	(find_proof prooftreename) in
    let focuspoint = (convert thefocus) in
    let pointinproof = find_focus focuspoint theprooftree in
% first check if node can be expanded %
	(get_flag_value `dont_cancel` &
	 ((expanded_node pointinproof) or
	   (proved_node pointinproof)))
	    => (print_string `node already explored, no action`;
		print_newline ()) |
% also make sure that lists are clean %
    let cleanfocus = (remove_descendants focuspoint focuslist) in
    let cleanbackup = (remove_descendants focuspoint backuplist) in
    let newsubl, newprf = tac (goal_at pointinproof) in
    let newbackup = (focuspoint . cleanbackup) in
    let modified_node = (null newsubl =>
	proved (newprf [], goal_at pointinproof, tac, newprf, tac,
		prepare_input(),  []) |
	expanded ((goal_at pointinproof), newprf, tac,
		  prepare_input(),
					   (map unexpanded newsubl))) in
    let new_tree = (null newsubl =>
	propagate_proof (make_change theprooftree modified_node
			      focuspoint) focuspoint |
	make_change theprooftree modified_node focuspoint) in
    let newfocus = ((null focuslist) => (makemylist (length newsubl)) |
		    (append (map (\each. (focuspoint @ each))
			     (makemylist (length newsubl))) cleanfocus))
    in
    (replace prooftreename new_tree newfocus newbackup;
     contextname := prooftreename;
%NOW COMPOSE OUTPUT%
(null newsubl =>
     (proved_node new_tree =>
	  (print_newline (); print_string `GOAL PROVED`;
	   print_newline (); print_newline ();
           print_thm (proved_thm_at new_tree);
	   print_newline (); print_newline ()) |
	  (print_newline (); print_string `SUBGOAL PROVED`;
	   print_newline (); print_string `next goal:`;
	   print_newline (); print_newline ();
	   print_goal (goal_at (find_focus (null newfocus => [] |
		      (hd newfocus)) new_tree))? failwith `no goal`)) |
(print_newline ();
 print_string (length newsubl = 1 => `new goal:` | `new goals:`);
 print_newline (); print_newline ();
(map (\eachfoc.
     (print_goal (goal_at (find_focus eachfoc new_tree))))
(rev (fst (chop_list (length newsubl) newfocus))))? failwith `dotac`;
 ():void ))) ;;

let cancel_tac prooftreename focuspoint =
    let (theprooftree, focuslist, backuplist) =
	(find_proof prooftreename) in
    let position = (convert focuspoint) in
    let node_val = (find_focus position theprooftree) in
    let new_val = unexpanded (goal_at node_val) in
    let new_proof = (proved_node node_val =>
		     unproveup position
		          (make_change theprooftree new_val position) |
		     make_change theprooftree new_val position) in
    let newfocuslist =  (position .
			(remove_descendants position focuslist)) in
    let newbackuplist = (remove_descendants position backuplist) in
	(replace prooftreename new_proof newfocuslist newbackuplist ;
	 print_newline (); print_string `BACKUP TO:`;
	 print_newline ();
	 print_goal (goal_at (find_focus (null newfocuslist => []
	   |(hd newfocuslist)) new_proof))) ;;

 
% cleaned up version and - hopefully - working version of comptac.ml.
  was having many problems in the compaction of a proof tree part, so
  will do it in a clean way.%

let print_then pt1 pt2 =
    Print_node (`MK-APPN`,
		[Print_node (`MK-APPN`,
			     [Print_node(`MK-VAR`,
					 [Print_node(`THEN`, [])])
					 ; pt1])
					 ; pt2]) ;;

let print_thenl pt1 ptl =
    Print_node (`MK-APPN`,
		[Print_node (`MK-APPN`,
			     [Print_node(`MK-VAR`,
					 [Print_node(`THENL`,[])])
					 ; pt1])
					 ; Print_node (`MK-LIST`
						       , ptl)]) ;;

let get_ptac ptree subl =
    if (null subl)
	then (print_tac_at ptree)
    else if (length subl = 1)
	     then print_then (print_tac_at ptree)
		 (print_tac_at (hd subl))
	 else print_thenl (print_tac_at ptree)
	     (map print_tac_at subl) ;;


letrec squeeze ptree =
   if (unexpanded_node ptree)
       then ptree %just return node, can't squeeze further %
   else
       if (proved_node ptree)
	   then
	       let sublist =  (map squeeze (subgoals_at ptree)) in
		   % the resulting node should have no children,
	             and should join other nodes %
	  proved
	  ((proof_at ptree) (map proved_thm_at sublist),
	    goal_at ptree,
	    (if (null sublist) then (tactic_at ptree) else
		 (if (length sublist = 1)
		      then (tactic_at ptree THEN
			    (full_tac_at (hd sublist)))
		  else (tactic_at ptree THENL
			(map full_tac_at sublist
			 )))),
           proof_at ptree,
	   tactic_at ptree,
	   (get_ptac ptree sublist),
	   [])
else 
    let sublist = (map squeeze (subgoals_at ptree)) in
% a bit trickier as some subgls may be expanded and others not %
    let  any_unexp = itlist (\a b. a or b)
	(map unexpanded_node sublist) false
    in if any_unexp then ptree else
	let newtac =  (if (null sublist) then (tactic_at ptree) else
	% (if (length sublist = 1)
	      then (tactic_at ptree THEN
		    (tactic_at (hd sublist)))
	 else% (tactic_at ptree THENL
	       (map (\each. (proved_node each => (full_tac_at each) |
                              (tactic_at each))) sublist))%)%) in
		let (newsubg, newprf) = (newtac (goal_at ptree)) in
	expanded
	(goal_at ptree,
	 newprf,
	newtac,
	 (get_ptac ptree sublist),
	      (flat (map subgoals_at sublist)))
;;


letrec find_leaves node foc = %gross; need the address of all children %
if (unexpanded_node node) then [foc]
else if (proved_node node) then []
else %concatenate addresses of all subgoals %
let subg_foc = map (\each. (foc @ each))
        (makemylist (length (subgoals_at node))) in
(flat (map (\(eachsubg, eachfoc). find_leaves eachsubg eachfoc)
       (combine (subgoals_at node, subg_foc)))) ;;

let compact proofname =
    let (proof, focl, back) = (find_proof proofname) in
    let newtree = (squeeze proof) in
    let leaves = (find_leaves newtree []) in
	(replace proofname newtree leaves back; show_tree newtree []) ;;



(do_tacf, cancel_tac, compact) ;;
end_section tactics ;;

let (do_tacf, cancel_tac, compact) = it ;;
