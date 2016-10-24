
% -------- pretty-printing interface --------- %

begin_section prettyprinting ;;

% load files obtained by "compiling" pretty-printing
  rules for goals, proof trees, and ml expressions    %

(map (\f_name. loadf (pack_path ^ f_name))
     [`print_the_tree_pp` ; `print_the_goal_pp` ; `ml_subset_pp`]  ) ;;


% transform the data structures used into appropriate
  print trees.                                        %

let goal_to_print_tree gl =
 (Print_node (`goal`, ((term_to_print_tree true No_types (snd gl)) .
	       (map (term_to_print_tree true No_types) (fst gl))))) ;;

letrec proof_to_print_tree thetree =
   case thetree of
       unexpanded gl .
          (Print_node (`unexp`,[goal_to_print_tree gl]))
      |proved (thrm, gl, solv_tac, prf, tac, printac, subl) .
          (Print_node (`proved`,
		       ((thm_to_print_tree true true No_types thrm) .
			 (printac .
			  (map proof_to_print_tree subl)))))
      |expanded (gl, prf, tac, printac, subl) .
       let ready_subl = map proof_to_print_tree (subgoals_at thetree)
       in
	   (Print_node (`exp`, ((goal_to_print_tree gl) .
				(printac . ready_subl)))) ;;


% interfaces to pretty-printing routines for the proof tree %

let show_tree the_tree thefocus =
    pretty_print 70 0
    (ml_subset_rules_fun then_try
     hol_rules_fun then_try
     printproof_rules_fun then_try
     printgoal_rules_fun) `proof` []
    (proof_to_print_tree the_tree %thefocus true%) ;;



% call the pretty printer to print tactics linked with THEN and THENL %

let show_full_tac the_tree =
    pretty_print 70 0
    (printproof_rules_fun then_try
     ml_subset_rules_fun then_try
     hol_term_rules_fun then_try
     hol_type_rules_fun) `firstfinaltac` [] 
     (proof_to_print_tree the_tree %[`1`] false%) ;;


% now export functions which are used outside %

(show_tree, show_full_tac) ;;
end_section prettyprinting ;;

let (show_tree, show_full_tac) = it ;;
