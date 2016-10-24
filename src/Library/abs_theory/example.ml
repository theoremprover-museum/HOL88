%----------------------------------------------------------------

   File:         example.ml

   Description:  

   Examples of instantiating the example group theory with
   exclusive--or and equality on the booleans.

   Author:       (c) P. J. Windley 1992

   Modification History:

   02JUN92 [PJW] --- Original file released.

   15JUN92 [PJW] --- Added sticky type flag.

   
----------------------------------------------------------------%


set_flag(`sticky`,true);;

loadf `abs_theory`;;

system `/bin/rm example.th`;;

new_theory `example`;;

load_library `taut`;;

new_abstract_parent `group_def`;;

%----------------------------------------------------------------
 Try an instantiation for exclusive--or
----------------------------------------------------------------%
let GROUP_THOBS = TAC_PROOF
   (([],"IS_GROUP(group (\x y.~(x=y)) F I)"),
    EXPAND_THOBS_TAC `group_def`
    THEN BETA_TAC
    THEN REWRITE_TAC [I_THM]
    THEN TAUT_TAC
   );;

instantiate_abstract_theorem `group_def` `IDENTITY_UNIQUE` 
    ["g","group (\x y.~(x=y)) F I"]
    [GROUP_THOBS];;

instantiate_abstract_theorem `group_def` `LEFT_CANCELLATION` 
    ["g","group (\x y.~(x=y)) F I"]
    [GROUP_THOBS];;

instantiate_abstract_theorem `group_def` `INVERSE_INVERSE_LEMMA` 
    ["g","group (\x y.~(x=y)) F I"]
    [GROUP_THOBS];;

%----------------------------------------------------------------
 Instantiate with equality
----------------------------------------------------------------%
let concrete_rep = "(group (\x y.(x=y)) T I)";;

let GROUP_THOBS = TAC_PROOF
   (([],"IS_GROUP ^concrete_rep"),
    EXPAND_THOBS_TAC `group_def`
    THEN BETA_TAC
    THEN REWRITE_TAC [I_THM]
    THEN TAUT_TAC
   );;

let inst_func s =
    instantiate_abstract_theorem `group_def` s 
	["g",concrete_rep]
	[GROUP_THOBS];;

map inst_func 
    [`IDENTITY_UNIQUE`;
     `LEFT_CANCELLATION`;
     `INVERSE_INVERSE_LEMMA`];;


close_theory();;
