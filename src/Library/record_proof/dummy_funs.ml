% ===================================================================== %
% FILE: dummy_funs.ml 	DATE: 16 July 93    BY: Wai WONG		%
% Define some dummy functions to be used when not in recording		%
% ===================================================================== %

let new_proof_file (s:string) = ()
and close_proof_file (():void) = ()
and begin_proof (s:string) = ()
and end_proof (():void) = ()
and current_proof (():void) = ``
and current_proof_file (():void) = ``
and (write_proof_add_to:(string -> string -> thm list -> * list -> void))
     s s' thml lnl = ()
and (write_proof_to:(string -> string -> thm list -> * list -> void))
     s s' thml lnl = ()
and (write_last_proof : (string -> thm list -> void)) s thl = ();;

