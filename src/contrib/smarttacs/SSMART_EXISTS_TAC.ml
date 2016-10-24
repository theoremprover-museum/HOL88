% SSMART_EXISTS_TAC.ml			 				%
						
% Exported Tactics: 							%
% 		 			       				%
%  SSMART_EXISTS_TAC 							%	
%  SMART_EXISTS_TAC			       				%
%  ASM_SMART_EXISTS_TAC							%
% 		 							%

   let choice_union a b =
      let (doma,rana) = split a 
      and (domb,ranb) = split b in
      if (intersect rana ranb) = [] then
         union a b
      else
         a;;


   letrec search_equals (chooseables,existentials,quant,left,right) =
      if (left = right) then
         (true, [])
      if (is_comb left) & (is_comb right) then (
         let (lok,lthms) = search_equals (chooseables,existentials,quant,
            (fst (dest_comb left)), (fst (dest_comb right)))
         and (rok,rthms) = search_equals (chooseables,existentials,quant,
              (snd (dest_comb left)), (snd (dest_comb right)))
         in (lok & rok, choice_union lthms rthms)
      )
      if (is_var left) & (mem left chooseables) & (intersect (frees right) quant = []) then
         (true,[right,left])
      if (is_var right) & (mem right chooseables) & (intersect (frees left) quant = []) then
         (true,[left,right])
      if (is_var left & mem left existentials) or (is_var right & mem right existentials) then
         (true,[])
      else (false, []);;

   let search_asm (chooseables,t,existentials,quant) asm = (
      if (type_of t = ":bool") then (
         let (ok,matches) = search_equals (chooseables,existentials,quant,t,asm) in
         if (ok) then matches else []
      )
      else []
   );;

   letrec bindings (chooseables,t,existentials,chex,quant) asms = (
      let asm_bindings = flat (map (search_asm (chooseables,t,existentials,quant)) asms) in
      let (sub_term_bindings,sub_asm_bindings) =  (
         if (chex & is_exists t) then
            (let (var,t1) = dest_exists t in
                (bindings (chooseables,t1,(var.existentials),chex,quant) asms)
            )
         if (is_eq t) then
            (let (t1,t2) = dest_eq t in
             let (ok,matches) = search_equals (chooseables,existentials,quant,t1,t2) in
                if (ok) then (matches,[]) else ([],[]))
         if (is_comb t) then (
            let (t1,t2) = dest_comb t in
            let (tb1, ab1) = bindings (chooseables,t1,existentials,false,quant) asms 
            and (tb2, ab2) = bindings (chooseables,t2,existentials,false,quant) asms  in
               (choice_union tb1 tb2, choice_union ab1 ab2)
         ) 
         if (is_abs t) then
            (let (v,t1) = dest_abs t in
               if (mem v chooseables) then ([],[])
               else (bindings (chooseables,t1,existentials,false, (v.quant)) asms))
         else ([],[])
      ) in
         (sub_term_bindings,choice_union sub_asm_bindings asm_bindings)
   );;




	     
let SSMART_EXISTS_RULE (asms,goal) =
   
   let (chooseables,rawgoal) = strip_exists goal in
   let (termb,asmb) = bindings(chooseables,rawgoal,[],true,[]) asms in
   let choice_list = choice_union termb asmb in
   if (choice_list = []) then 
      (failwith `SSMART_EXISTS_RULE - no choices found`)
   else (
      let (sub,var) = 
         tryfind (\var. rev_assoc var choice_list) chooseables in
      let chosen_term = subst [(sub,var)] rawgoal in

      let choices = map (\var'. if (var = var') then (var,sub) else (var',var')) chooseables in

      let assump = (
         itlist (\(var',choice) t.
            if (not var = var') then 
               mk_exists(var',t)
            else t
         ) choices chosen_term
      ) in

      PROVE("^assump ==> ^goal",
         (DISCH_THEN o (REPEAT_TCL CHOOSE_THEN)) ASSUME_TAC THEN
         EVERY (map (\(var,choice). EXISTS_TAC choice) choices) THEN
         POP_ASSUM ACCEPT_TAC
      )
   );;



let EXISTS_OUT_TAC =
CONV_TAC (
   (CHANGED_CONV (ONCE_DEPTH_CONV LEFT_AND_EXISTS_CONV))
   ORELSEC (CHANGED_CONV (ONCE_DEPTH_CONV RIGHT_AND_EXISTS_CONV))
   ORELSEC (CHANGED_CONV (ONCE_DEPTH_CONV LEFT_OR_EXISTS_CONV))
   ORELSEC (CHANGED_CONV (ONCE_DEPTH_CONV RIGHT_OR_EXISTS_CONV))
   ORELSEC (CHANGED_CONV (ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV))
);;




let SSMART_EXISTS_TAC goal =
   let rule = SSMART_EXISTS_RULE goal in
   MATCH_MP_TAC rule goal;;

let REPEATED_SMART_EXISTS_TAC L  =
   (REPEAT (CHANGED_TAC EXISTS_OUT_TAC)) 
   THEN REPEAT ((CHANGED_TAC ((REPEAT SSMART_EXISTS_TAC) THEN ONCE_ASM_REWRITE_TAC L)) ORELSE CONJ_TAC);;


