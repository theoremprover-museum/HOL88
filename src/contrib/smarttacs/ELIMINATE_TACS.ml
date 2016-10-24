% ELIMINATE_TACS.ml	 				%

% Exported Tactics: 				%
% 		 				%
% 		 				%

% 		 				%



%-----------------------------------------------------------------------%
% SMART VARIABLE ELIMINATION						%
%-----------------------------------------------------------------------%


%< deletes an element from a list >%
letrec delete = (fun 
      [] . (fun _ . [])
   |  (h'.t) . (fun h .  
      (let t' = delete t h in 
      if h=h' then t' else h'.t')));;



%< ---------------------------------------------------------------------
 < choose_subst_asms
 <    chooses from a set of theorems a subset appropriate to use as
 < a basis for elimination - i.e. a set of equality substitutions.
 < Two subsets are returned - the set to use, and the set to not to use
 < Assumptions of the form x = x are thrown away all together.
 < 
 < asms:        the assumptions as theorems 				
 < gl:          the goal as a term 					
 < no_terms:    completely disallows the elimination of terms other than 		
 <	      	variables 					
 < any_terms:   allows elimination of terms which have 		
 <		free variables being used in some other context 	
 <
 < The code for this is a bit ugly - I was trying to use a different
 < ML coding style but admit that it ends up not-so-good.  I'll rewrite
 < it sometime.
 <---------------------------------------------------------------------->%


letrec choose_subst_asms asms gl no_terms any_terms =

   let term_acceptance elim repl terms disallowed =  not no_terms & (
      let felim = frees elim in
                % prevent the elimination of constants %
      not null felim &	
                % ensure we dont eliminate something already in the rhs of a substitution %
      null (intersect disallowed felim) &	
                % ensure we only eliminate structure occuring elsewhere %
      exists (free_in elim) terms &	
      (not any_terms or		
       forall (\other.
          let after_subst = subst [repl,elim] other in
          null (intersect (frees after_subst) felim)
       ) terms
      )
   ) in

   letrec choose_rec sub_asms chosen disallowed =
      if (null sub_asms) then ([], [])
      else (
         let c = concl (hd sub_asms) in
         let terms = gl.(map concl (delete asms (hd sub_asms))) in
         let throw_away () = 
            choose_rec (tl sub_asms) chosen disallowed in
         let dont_accept () = 
            let (tlnosubs, tlsubs)=choose_rec (tl sub_asms) chosen disallowed in
            ((hd sub_asms).tlnosubs, tlsubs) in
         if (is_eq c) & null (intersect chosen (frees c)) then (
            let accept_lhs () = (
               let (tlnosubs, tlsubs)=
                  choose_rec 
                     (tl sub_asms) 
                     (union chosen (frees (lhs c))) 
                     (union disallowed (frees (rhs c))) in
               (tlnosubs, (hd sub_asms).tlsubs) 
            ) in
            let accept_rhs () =
               let (tlnosubs, tlsubs)=
                  choose_rec 
                     (tl sub_asms) 
                     (union chosen (frees (rhs c))) 
                     (union disallowed (frees (lhs c))) in
               (tlnosubs, (SYM (hd sub_asms)).tlsubs) in

%< The following lines determine whether we use a particular assumption as the basis for >%
%< an elimination or not >%
            if (lhs c = rhs c) then throw_away()
	    if (is_var (lhs c)) & not (mem (lhs c) disallowed) then accept_lhs()
            if (is_var (rhs c)) & not (mem (rhs c) disallowed) then accept_rhs()

%< Comment these out to disallow completely the elimination of terms other than variables >%
            if (term_acceptance (lhs c) (rhs c) terms disallowed) then accept_lhs()
            if (term_acceptance (rhs c) (lhs c) terms disallowed) then accept_rhs()
	    else dont_accept()
         )
         else dont_accept()
      ) in
   choose_rec asms [] [];;


let XELIMINATE_TAC no_terms any_terms (asms,gl) =
   POP_ASSUM_LIST (\thms.
      let (nosub, sub) = choose_subst_asms thms gl no_terms any_terms in
      if (null sub) then failwith `no terms found to eliminate`
      else (
         EVERY (rev (map (ASSUME_TAC o (SUBS sub)) nosub)) THEN
         SUBST_TAC sub 
      )
   ) (asms,gl)
   ?\s failwith `XELIMINATE_TAC -- ` ^ s;;


%< eliminate variables and seemingly safe terms >%
let SMART_ELIMINATE_TAC = XELIMINATE_TAC false true;;	      

%< eliminate variables only - safe >%
let SMART_VAR_ELIMINATE_TAC = XELIMINATE_TAC true true;;      

%< eliminate terms, including potentially unhelpful eliminations >% 
let SMART_TERM_ELIMINATE_TAC = XELIMINATE_TAC false false;;   



let DEEP_SYM_CONV = (ONCE_DEPTH_CONV SYM_CONV);;
let DEEP_SYM = (CONV_RULE DEEP_SYM_CONV);;


let CLEAN_ASMS_TAC =
   POP_ASSUM_LIST (\thms.
       letrec remove_silly_thms thml kept = (
          let throw_away () = remove_silly_thms (tl thml) kept in
          let keep () = remove_silly_thms (tl thml) (hd thml.kept) in
          if (null thml) then kept
          else (
             let thm = hd thml in
             if (is_eq (concl thm)) & (lhs (concl thm) = rhs (concl thm)) then throw_away()
             if (mem thm kept) or (mem (DEEP_SYM thm) kept) then throw_away()
             if (concl thm = "T") then throw_away()
             else keep ()
          )
      ) in
      let tokeep = remove_silly_thms thms [] in
      EVERY (map ASSUME_TAC tokeep)
   );;



