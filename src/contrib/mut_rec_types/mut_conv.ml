let EA_SWITCH = theorem `mut_rec_tools` `EA_SWITCH`;;

% ONE_EA_CONV flytter een forallkvantificeret var. ind som param. i en  %
% existkvantificeret funktion %


let ONE_EA_CONV t = 
  if (is_forall t) then
    let v,tm = dest_forall t in
    let a=list_mk_abs((\(x,(y,z)).([x;y],z)) (v,dest_exists tm)) in
    let t_def = "t:*->(*1->*2)->bool" in
    let Beta = (RATOR_CONV BETA_CONV) THENC BETA_CONV in
    let Conv = (RAND_CONV o BINDER_CONV o BINDER_CONV) in
    (CONV_RULE ((Conv Beta) THENC (RATOR_CONV (Conv Beta))) 
               ((\(x,y) . INST x (INST_TYPE y (SPEC t_def EA_SWITCH)))
                (match t_def a)))
  else failwith `ONE_EA_CONV: Forall expected`;;


% Anvender ONE_EA_CONV paa alle variable. %   
             
letrec EA_CONV t =
  if (is_forall t)
  then (( (BINDER_CONV EA_CONV) THENC ONE_EA_CONV) t)
  else (ALL_CONV t);;


let ONE_EA_RULE thm =
  CONV_RULE ONE_EA_CONV thm;;

letrec EA_RULE thm =
  if not (is_forall (concl thm))
  then thm
  else let (x,t) = dest_forall (concl thm) in
       let thm' = SPEC x thm in
       let thm'' = EA_RULE thm' in
       ONE_EA_RULE (GEN x thm'');;
