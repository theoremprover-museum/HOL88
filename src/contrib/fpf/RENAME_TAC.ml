% RENAME_TAC.ml 				%

% Exported Tactics: 				%
% 		 				%
%  ONCE_RENAME_TAC				%
%  RENAME_TAC					%
% 		 				%

% RENAME_TAC: tactic %
% --------------------------------------------------------------------- %
% Renames a variable in the goal so that it is not used             	%
% more than once in different bindings.  Fails if there is no variable 	%
% to rename. 								%


let asm_frees gam = itlist union (map frees gam) [];;
let all_frees (gam,t) = union (asm_frees gam) (frees t);;

let is_used v usedlist = 
   (let (s,ty) = dest_var v in
      mem s (fst (split (map dest_var usedlist))));;

letrec new_var v usedlist =
   if (not (is_used v usedlist)) then v
   else
      (let (s,ty) = dest_var v in
         new_var (mk_var (s^`'`,ty)) usedlist);;
         
letrec used_vars t = subtract (vars t) (frees t);;


letrec rename (t,usedlist,sofar) =
   if (is_var t) then ((snd(assoc t sofar) ? t), usedlist)
   else if (is_const t) then (t,usedlist)
   else if (is_comb t) then
      let (rrator,u') = rename (rator t, usedlist,sofar) in
      let (rrand,u'') = rename (rand t,u',sofar) in
         (mk_comb (rrator,rrand), u'')
   else if (is_abs t) then
      let (v,t1) = dest_abs t in
      let (v',u',s') = (
         if (is_used v usedlist) then
            let nv = new_var v usedlist in
            (nv, (nv.usedlist), ((v,nv).sofar))
         else if (mem v (fst(split sofar))) then
            (v,(v.usedlist),((v,v).sofar))
         else 
            (v,(v.usedlist),sofar)
      ) in
      let (t1',u'') = rename (t1,u',s') in
         (mk_abs (v',t1'), u'')
   else failwith `unrecognized term`;;



let ONCE_RENAME_TAC (gam,t) =
      let newgoal = fst(rename (t,all_frees (gam,t),[])) in
      if (newgoal = t) then failwith `no rename found`
      else [(gam,fst(rename (t,all_frees (gam,t),[])) )], (\[thm]. PROVE(t, ACCEPT_TAC thm));;

let RENAME_TAC = REPEAT ONCE_RENAME_TAC;;










