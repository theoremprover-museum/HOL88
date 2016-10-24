
% A1.8 UNITS %
unit:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit`,expected,WORD);
   
    if WORD = `CONC` then
        (let (unit1_0 , result_list , prev, lst) = unit1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push unit1_0 result_list in
         let (units_l_1 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push units_l_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`unit`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `unit` prev lst `nil`)
    else
         fail
  ?
    (let (unit_fn_0 , result_list , prev, lst) = unit_fn lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push unit_fn_0 result_list in
     let (units_l_1 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push units_l_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`unit`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `unit` prev lst `nil`)
  ?
    (let (unit_mac_0 , result_list , prev, lst) = unit_mac lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push unit_mac_0 result_list in
     let (units_l_1 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push units_l_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`unit`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `unit` prev lst `nil`)
  ?
    (let (unit1_0 , result_list , prev, lst) = unit1 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push unit1_0 result_list in
     let (units_l_1 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push units_l_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`unit`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `unit` prev lst `nil`);;

units_l:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`units_l`,expected,WORD);
   
    if WORD = `CONC` then
        (let (unit1_0 , result_list , prev, lst) = unit1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push unit1_0 result_list in
         let (units_l_1 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push units_l_1 result_list in
         do_return result_list whitespace `units_l` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (unit_fn_1 , result_list , prev, lst) =  unit_fn  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,unit_fn_1) in
     let result_list = push tmp_2 result_list in
     let (units_l_2 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push units_l_2 result_list in
     do_return result_list whitespace `units_l` prev lst `nil`)
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (unit_mac_1 , result_list , prev, lst) =  unit_mac  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,unit_mac_1) in
     let result_list = push tmp_2 result_list in
     let (units_l_2 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push units_l_2 result_list in
     do_return result_list whitespace `units_l` prev lst `nil`)
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (unit1_1 , result_list , prev, lst) =  unit1  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,unit1_1) in
     let result_list = push tmp_2 result_list in
     let (units_l_2 , result_list , prev, lst) = units_l lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push units_l_2 result_list in
     do_return result_list whitespace `units_l` prev lst `nil`)
  ?
    (do_return result_list whitespace `units_l` WORD lst expected);;

unit_fn:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit_fn`,expected,WORD);
   
    (let (fnname_0 , result_list , prev, lst) =  fnname  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let (unit_names_1 , result_list , prev, lst) =  unit_names  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
     let (unit1_2 , result_list , prev, lst) =  unit1  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_three(`unit_fn`,fnname_0,unit_names_1,unit1_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `unit_fn` prev lst `nil`);;

unit_mac:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit_mac`,expected,WORD);
   
    (let (macname_0 , result_list , prev, lst) = macname lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push macname_0 result_list in
     let (mac_poss_parms_names_1 , result_list , prev, lst) = mac_poss_parms_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push mac_poss_parms_names_1 result_list in
     do_return result_list whitespace `unit_mac` prev lst `nil`);;

mac_poss_parms_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`mac_poss_parms_names`,expected,WORD);
   
    if WORD = `{` then
        (let (macparams_0 , result_list , prev, lst) = macparams lst whitespace whitespace result_list FIRST_CHARS CHARS `\}` in
         let result_list = push macparams_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `mac_poss_parms_names` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (unit_names_3 , result_list , prev, lst) =  unit_names  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let (unit1_4 , result_list , prev, lst) =  unit1  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_5 = MK_four(`unit_mac`,POP_1,POP_2,unit_names_3,unit1_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `mac_poss_parms_names` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (unit_names_1 , result_list , prev, lst) =  unit_names  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let (unit1_2 , result_list , prev, lst) =  unit1  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_three(`unit_mac`,POP_0,unit_names_1,unit1_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `mac_poss_parms_names` prev lst `nil`);;

unit_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit_names`,expected,WORD);
   
    if WORD = `@` then
        (let (name_0 , result_list , prev, lst) = name lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push name_0 result_list in
         let (more_unit_names_1 , result_list , prev, lst) = more_unit_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_unit_names_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`unit_names`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `unit_names` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = MK_zero(`unit_names`) in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `unit_names` WORD lst expected);;

more_unit_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_unit_names`,expected,WORD);
   
    if WORD = `@` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (name_1 , result_list , prev, lst) =  name  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,name_1) in
         let result_list = push tmp_2 result_list in
         let (more_unit_names_2 , result_list , prev, lst) = more_unit_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_unit_names_2 result_list in
         do_return result_list whitespace `more_unit_names` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_unit_names` WORD lst expected);;

macparams:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macparams`,expected,WORD);
   
    (let (macparam_0 , result_list , prev, lst) =  macparam  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_1 = MK_one(`macparam`,macparam_0) in
     let result_list = push tmp_1 result_list in
     let (more_macparams_1 , result_list , prev, lst) = more_macparams lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_macparams_1 result_list in
     do_return result_list whitespace `macparams` prev lst `nil`);;

macparam:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macparam`,expected,WORD);
   
    (let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push int_0 result_list in
     do_return result_list whitespace `macparam` prev lst `nil`)
  ?
    (let (typ_0 , result_list , prev, lst) = typ lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push typ_0 result_list in
     do_return result_list whitespace `macparam` prev lst `nil`);;

more_macparams:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_macparams`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (macparam_1 , result_list , prev, lst) =  macparam  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,macparam_1) in
     let result_list = push tmp_2 result_list in
     let (more_macparams_2 , result_list , prev, lst) = more_macparams lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_macparams_2 result_list in
     do_return result_list whitespace `more_macparams` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_macparams` WORD lst expected);;

unit1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit1`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (unit1_2 , result_list , prev, lst) =  unit1  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`unit1_4`,POP_1,unit1_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`unit1`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `unit1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `[` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `INT` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
         let result_list = push name_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `=` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (int_1 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (int_2 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let (unit1_6 , result_list , prev, lst) =  unit1  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_7 = MK_four(`unit1_5`,POP_3,POP_4,POP_5,unit1_6) in
         let result_list = push tmp_7 result_list in
         do_return result_list whitespace `unit1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `STRING` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\[` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (unit1_2 , result_list , prev, lst) =  unit1  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`unit1_7`,POP_1,unit1_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`unit1`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `unit1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IO` then
        (let (name_0 , result_list , prev, lst) = name lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push name_0 result_list in
         let (poss_1st_int_1 , result_list , prev, lst) = poss_1st_int lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push poss_1st_int_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`unit1`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `unit1` prev lst `nil`)
    else
         fail
  ?
    (let (unit_fn_0 , result_list , prev, lst) =  unit_fn  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`unit1`,unit_fn_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `unit1` prev lst `nil`)
  ?
    (let (unit_mac_0 , result_list , prev, lst) =  unit_mac  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`unit1`,unit_mac_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `unit1` prev lst `nil`)
  ?
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `&` in
     let result_list = push name_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `&` WORD lst `unit1` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (unit1_2 , result_list , prev, lst) =  unit1  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`unit1_6`,POP_1,unit1_2) in
     let result_list = push tmp_3 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let tmp_4 = MK_one(`unit1`,POP_3) in
     let result_list = push tmp_4 result_list in
     do_return result_list whitespace `unit1` prev lst `nil`)
  ?
    (let (unit2_0 , result_list , prev, lst) = unit2 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push unit2_0 result_list in
     let (unit1_finish_1 , result_list , prev, lst) = unit1_finish lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push unit1_finish_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`unit1`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `unit1` prev lst `nil`);;

unit1_finish:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit1_finish`,expected,WORD);
   
    if WORD = `//` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (name_1 , result_list , prev, lst) =  name  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`unit1_8`,POP_0,name_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `unit1_finish` prev lst `nil`)
    else
         fail
  ?
    (let (poss_unit1_names_0 , result_list , prev, lst) = poss_unit1_names lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_unit1_names_0 result_list in
     do_return result_list whitespace `unit1_finish` prev lst `nil`);;

poss_unit1_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_unit1_names`,expected,WORD);
   
    if WORD = `@` then
        (let (name_0 , result_list , prev, lst) = name lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push name_0 result_list in
         let (unit_names_1 , result_list , prev, lst) = unit_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push unit_names_1 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_two(`unit1_1`,POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `poss_unit1_names` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (unit_names_1 , result_list , prev, lst) =  unit_names  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = MK_two(`unit1_1`,POP_0,unit_names_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `poss_unit1_names` prev lst `nil`);;

poss_1st_int:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_1st_int`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `poss_1st_int` in
         let TOKENS = explode WORD in
         let (poss_2nd_int_1 , result_list , prev, lst) = poss_2nd_int lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push poss_2nd_int_1 result_list in
         do_return result_list whitespace `poss_1st_int` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`unit1_9`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `poss_1st_int` WORD lst expected);;

poss_2nd_int:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_2nd_int`,expected,WORD);
   
    if WORD = `[` then
        (let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (int_2 , result_list , prev, lst) =  int  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `\]` in
         let tmp_3 = MK_three(`unit1_9`,POP_0,POP_1,int_2) in
         let result_list = push tmp_3 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `poss_2nd_int` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `poss_2nd_int` WORD lst expected)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`unit1_9`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `poss_2nd_int` WORD lst expected);;

unit2:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit2`,expected,WORD);
   
    if WORD = `?` then
        (let (typ_0 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`unit2_uninit`,typ_0) in
         let result_list = push tmp_1 result_list in
         let (unit2_stuff_1 , result_list , prev, lst) = unit2_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push unit2_stuff_1 result_list in
         do_return result_list whitespace `unit2` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IF` then
        (let (boolean_0 , result_list , prev, lst) = boolean lst whitespace whitespace result_list FIRST_CHARS CHARS `THEN` in
         let result_list = push boolean_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `THEN` WORD lst `unit2` in
         let TOKENS = explode WORD in
         let (unit_1 , result_list , prev, lst) = unit lst whitespace WORD result_list FIRST_CHARS CHARS `ELSE` in
         let result_list = push unit_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `ELSE` WORD lst `unit2` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (unit_4 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS `FI` in
         let tmp_5 = MK_three(`unit2_cond`,POP_2,POP_3,unit_4) in
         let result_list = push tmp_5 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `FI` WORD lst `unit2` in
         let TOKENS = explode WORD in
         let (unit2_stuff_5 , result_list , prev, lst) = unit2_stuff lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push unit2_stuff_5 result_list in
         do_return result_list whitespace `unit2` prev lst `nil`)
    else
         fail
  ?
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (name_stuff_1 , result_list , prev, lst) = name_stuff lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_stuff_1 result_list in
     let (unit2_stuff_2 , result_list , prev, lst) = unit2_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push unit2_stuff_2 result_list in
     do_return result_list whitespace `unit2` prev lst `nil`)
  ?
    (let (unit3_0 , result_list , prev, lst) = unit3 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push unit3_0 result_list in
     let (unit2_stuff_1 , result_list , prev, lst) = unit2_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push unit2_stuff_1 result_list in
     do_return result_list whitespace `unit2` prev lst `nil`);;

unit2_stuff:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit2_stuff`,expected,WORD);
   
    if WORD = `?` then
        (let (typ_0 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`unit2_uninit`,typ_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = add_to_list(POP_1,POP_2) in
         let result_list = push tmp_3 result_list in
         let (unit2_stuff_3 , result_list , prev, lst) = unit2_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push unit2_stuff_3 result_list in
         do_return result_list whitespace `unit2_stuff` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IF` then
        (let (boolean_0 , result_list , prev, lst) = boolean lst whitespace whitespace result_list FIRST_CHARS CHARS `THEN` in
         let result_list = push boolean_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `THEN` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         let (unit_1 , result_list , prev, lst) = unit lst whitespace WORD result_list FIRST_CHARS CHARS `ELSE` in
         let result_list = push unit_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `ELSE` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (unit_4 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS `FI` in
         let tmp_5 = MK_three(`unit2_cond`,POP_2,POP_3,unit_4) in
         let result_list = push tmp_5 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `FI` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let (POP_6 , pop_list ) = (pop pop_list) in
         let tmp_7 = add_to_list(POP_5,POP_6) in
         let result_list = push tmp_7 result_list in
         let (unit2_stuff_7 , result_list , prev, lst) = unit2_stuff lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push unit2_stuff_7 result_list in
         do_return result_list whitespace `unit2_stuff` prev lst `nil`)
    else
         fail
  ?
    if WORD = `[` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (int_1 , result_list , prev, lst) =  int  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `\]` in
         let tmp_2 = MK_two(`unit2_int`,POP_0,int_1) in
         let result_list = push tmp_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `unit2_stuff` WORD lst expected)
    else
         fail
  ?
    if WORD = `[` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\[` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (unit_1 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS `\]` in
         let tmp_2 = MK_two(`unit2_unit`,POP_0,unit_1) in
         let result_list = push tmp_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `unit2_stuff` WORD lst expected)
    else
         fail
  ?
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (int_3 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `\]` in
         let tmp_4 = MK_three(`unit2_int_range`,POP_1,POP_2,int_3) in
         let result_list = push tmp_4 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `unit2_stuff` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `unit2_stuff` WORD lst expected)
    else
         fail
  ?
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (name_stuff_1 , result_list , prev, lst) = name_stuff lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_stuff_1 result_list in
     let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let tmp_4 = add_to_list(POP_2,POP_3) in
     let result_list = push tmp_4 result_list in
     let (unit2_stuff_4 , result_list , prev, lst) = unit2_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push unit2_stuff_4 result_list in
     do_return result_list whitespace `unit2_stuff` prev lst `nil`)
  ?
    (let (unit3_0 , result_list , prev, lst) = unit3 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push unit3_0 result_list in
     let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = add_to_list(POP_1,POP_2) in
     let result_list = push tmp_3 result_list in
     let (unit2_stuff_3 , result_list , prev, lst) = unit2_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push unit2_stuff_3 result_list in
     do_return result_list whitespace `unit2_stuff` prev lst `nil`)
  ?
    (do_return result_list whitespace `unit2_stuff` WORD lst expected);;

name_stuff:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`name_stuff`,expected,WORD);
   
    if WORD = `/` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula2_1 , result_list , prev, lst) =  formula2  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`const2_formula2`,POP_0,formula2_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `name_stuff` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (char_1 , result_list , prev, lst) =  char  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = MK_two(`const2_char`,POP_0,char_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `name_stuff` prev lst `nil`)
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (string_1 , result_list , prev, lst) =  string  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = MK_two(`const2_string`,POP_0,string_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `name_stuff` prev lst `nil`)
  ?
    (do_return result_list whitespace `name_stuff` WORD lst expected);;

unit3:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`unit3`,expected,WORD);
   
    if WORD = `CASE` then
        (let (caseclause_0 , result_list , prev, lst) = caseclause lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
         let result_list = push caseclause_0 result_list in
         do_return result_list whitespace `unit3` prev lst `nil`)
    else
         fail
  ?
    (let (series_0 , result_list , prev, lst) = series lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push series_0 result_list in
     do_return result_list whitespace `unit3` prev lst `nil`)
  ?
    (let (sequence_0 , result_list , prev, lst) = sequence lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push sequence_0 result_list in
     do_return result_list whitespace `unit3` prev lst `nil`)
  ?
    if WORD = `(` then
        (let (unit_0 , result_list , prev, lst) = unit lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push unit_0 result_list in
         let (more_units_1 , result_list , prev, lst) = more_units lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_units_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `unit3` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`units`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `unit3` WORD lst expected)
    else
         fail
  ? fail;;

more_units:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_units`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (unit_1 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,unit_1) in
         let result_list = push tmp_2 result_list in
         let (more_units_2 , result_list , prev, lst) = more_units lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_units_2 result_list in
         do_return result_list whitespace `more_units` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_units` WORD lst expected);;

caseclause:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`caseclause`,expected,WORD);
   
    (let (unit_0 , result_list , prev, lst) = unit lst whitespace WORD result_list FIRST_CHARS CHARS `OF` in
     let result_list = push unit_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `OF` WORD lst `caseclause` in
     let TOKENS = explode WORD in
     let (choices_1 , result_list , prev, lst) = choices lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push choices_1 result_list in
     let (poss_case_else_2 , result_list , prev, lst) = poss_case_else lst whitespace prev result_list FIRST_CHARS CHARS `ESAC` in
     let result_list = push poss_case_else_2 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `ESAC` WORD lst `caseclause` in
     let TOKENS = explode WORD in
     do_return result_list whitespace `caseclause` WORD lst expected);;

choices:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`choices`,expected,WORD);
   
    (let (choosers_0 , result_list , prev, lst) = choosers lst whitespace WORD result_list FIRST_CHARS CHARS `:` in
     let result_list = push choosers_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `:` WORD lst `choices` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (unit_2 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_3 = MK_two(`choice`,POP_1,unit_2) in
     let result_list = push tmp_3 result_list in
     let (more_choices_3 , result_list , prev, lst) = more_choices lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_choices_3 result_list in
     do_return result_list whitespace `choices` prev lst `nil`);;

more_choices:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_choices`,expected,WORD);
   
    if WORD = `,` then
        (let (choosers_0 , result_list , prev, lst) = choosers lst whitespace whitespace result_list FIRST_CHARS CHARS `:` in
         let result_list = push choosers_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `:` WORD lst `more_choices` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (unit_2 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let tmp_3 = MK_two(`choice`,POP_1,unit_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = add_to_list(POP_3,POP_4) in
         let result_list = push tmp_5 result_list in
         let (more_choices_5 , result_list , prev, lst) = more_choices lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_choices_5 result_list in
         do_return result_list whitespace `more_choices` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`choices`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_choices` WORD lst expected);;

choosers:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`choosers`,expected,WORD);
   
    (let (const_0 , result_list , prev, lst) =  const  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`choosers`,const_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `choosers` prev lst `nil`);;

poss_case_else:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_case_else`,expected,WORD);
   
    if WORD = `ELSE` then
        (let tmp_0 = MK_zero(`caseclause_ELSEOF`) in
         let result_list = push tmp_0 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (unit_3 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = MK_four(`caseclause`,POP_0,POP_1,POP_2,unit_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `poss_case_else` prev lst `nil`)
    else
         fail
  ?
    if WORD = `ELSEOF` then
        (let (choices_0 , result_list , prev, lst) = choices lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push choices_0 result_list in
         let (more_elseofs_1 , result_list , prev, lst) = more_elseofs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_elseofs_1 result_list in
         do_return result_list whitespace `poss_case_else` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = MK_zero(`caseclause_ELSEOF`) in
     let result_list = push tmp_0 result_list in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_three(`caseclause`,POP_0,POP_1,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `poss_case_else` WORD lst expected);;

more_elseofs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_elseofs`,expected,WORD);
   
    if WORD = `ELSEOF` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (choices_1 , result_list , prev, lst) =  choices  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,choices_1) in
         let result_list = push tmp_2 result_list in
         let (more_elseofs_2 , result_list , prev, lst) = more_elseofs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_elseofs_2 result_list in
         do_return result_list whitespace `more_elseofs` prev lst `nil`)
    else
         fail
  ?
    (let (end_game_case_0 , result_list , prev, lst) = end_game_case lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push end_game_case_0 result_list in
     do_return result_list whitespace `more_elseofs` prev lst `nil`);;

end_game_case:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`end_game_case`,expected,WORD);
   
    if WORD = `ELSE` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let tmp_1 = MK_one(`caseclause_ELSEOF`,POP_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (unit_4 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_5 = MK_four(`caseclause`,POP_1,POP_2,POP_3,unit_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `end_game_case` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`caseclause_ELSEOF`,POP_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let tmp_4 = MK_three(`caseclause`,POP_1,POP_2,POP_3) in
     let result_list = push tmp_4 result_list in
     do_return result_list whitespace `end_game_case` WORD lst expected);;

