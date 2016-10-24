
% A1.9 SERIES %
series:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`series`,expected,WORD);
   
    if WORD = `BEGIN` then
        (let (BEGIN_steps_0 , result_list , prev, lst) = BEGIN_steps lst whitespace whitespace result_list FIRST_CHARS CHARS `END` in
         let result_list = push BEGIN_steps_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `END` WORD lst `series` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`series`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `series` WORD lst expected)
    else
         fail
  ?
    if WORD = `(` then
        (let (bracket_steps_0 , result_list , prev, lst) = bracket_steps lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push bracket_steps_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `series` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`series`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `series` WORD lst expected)
    else
         fail
  ? fail;;

BEGIN_steps:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`BEGIN_steps`,expected,WORD);
   
    if WORD = `OUTPUT` then
        (let (unit_0 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_one(`series_BEGINEND`,unit_0) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `BEGIN_steps` prev lst `nil`)
    else
         fail
  ?
    (let (step_0 , result_list , prev, lst) = step lst whitespace WORD result_list FIRST_CHARS CHARS `.` in
     let result_list = push step_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `.` WORD lst `BEGIN_steps` in
     let TOKENS = explode WORD in
     let (more_B_steps_1 , result_list , prev, lst) = more_B_steps lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_B_steps_1 result_list in
     do_return result_list whitespace `BEGIN_steps` prev lst `nil`);;

more_B_steps:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_B_steps`,expected,WORD);
   
    if WORD = `OUTPUT` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (unit_0 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`series_BEGINEND`,unit_0,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `more_B_steps` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (step_1 , result_list , prev, lst) =  step  lst whitespace  WORD  result_list FIRST_CHARS CHARS `.` in
     let tmp_2 = add_to_list(POP_0,step_1) in
     let result_list = push tmp_2 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `.` WORD lst `more_B_steps` in
     let TOKENS = explode WORD in
     let (more_B_steps_2 , result_list , prev, lst) = more_B_steps lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_B_steps_2 result_list in
     do_return result_list whitespace `more_B_steps` prev lst `nil`);;

bracket_steps:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`bracket_steps`,expected,WORD);
   
    if WORD = `OUTPUT` then
        (let (unit_0 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_one(`series_brackets`,unit_0) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `bracket_steps` prev lst `nil`)
    else
         fail
  ?
    (let (step_0 , result_list , prev, lst) = step lst whitespace WORD result_list FIRST_CHARS CHARS `.` in
     let result_list = push step_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `.` WORD lst `bracket_steps` in
     let TOKENS = explode WORD in
     let (more_br_steps_1 , result_list , prev, lst) = more_br_steps lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_br_steps_1 result_list in
     do_return result_list whitespace `bracket_steps` prev lst `nil`);;

more_br_steps:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_br_steps`,expected,WORD);
   
    if WORD = `OUTPUT` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (unit_0 , result_list , prev, lst) =  unit  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`series_brackets`,unit_0,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `more_br_steps` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (step_1 , result_list , prev, lst) =  step  lst whitespace  WORD  result_list FIRST_CHARS CHARS `.` in
     let tmp_2 = add_to_list(POP_0,step_1) in
     let result_list = push tmp_2 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `.` WORD lst `more_br_steps` in
     let TOKENS = explode WORD in
     let (more_br_steps_2 , result_list , prev, lst) = more_br_steps lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_br_steps_2 result_list in
     do_return result_list whitespace `more_br_steps` prev lst `nil`);;

step:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`step`,expected,WORD);
   
    if WORD = `MAKE` then
        (let (makeitem_0 , result_list , prev, lst) = makeitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push makeitem_0 result_list in
         let (more_makeitems_1 , result_list , prev, lst) = more_makeitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_makeitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_MAKE`,POP_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`step`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `step` prev lst `nil`)
    else
         fail
  ?
    if WORD = `LET` then
        (let (letitem_0 , result_list , prev, lst) = letitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push letitem_0 result_list in
         let (more_letitems_1 , result_list , prev, lst) = more_letitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_letitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_LET`,POP_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`step`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `step` prev lst `nil`)
    else
         fail
  ?
    if WORD = `FOR` then
        (let (multiplier_0 , result_list , prev, lst) =  multiplier  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`multiplier`,multiplier_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (joinstep_2 , result_list , prev, lst) =  joinstep  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`step`,POP_1,joinstep_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `step` prev lst `nil`)
    else
         fail
  ?
    (let (joinstep_0 , result_list , prev, lst) =  joinstep  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`step`,joinstep_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `step` prev lst `nil`)
  ?
    if WORD = `PRINT` then
        (let (printitem_0 , result_list , prev, lst) = printitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push printitem_0 result_list in
         let (more_printitems_1 , result_list , prev, lst) = more_printitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_printitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_PRINT`,POP_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`step`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `step` prev lst `nil`)
    else
         fail
  ?
    if WORD = `FAULT` then
        (let (faultitem_0 , result_list , prev, lst) = faultitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push faultitem_0 result_list in
         let (more_faultitems_1 , result_list , prev, lst) = more_faultitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_faultitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_FAULT`,POP_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`step`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `step` prev lst `nil`)
    else
         fail
  ?
    (let (declaration_0 , result_list , prev, lst) = declaration lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push declaration_0 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_one(`step`,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `step` prev lst `nil`);;

makeitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`makeitem`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `makeitem` in
         let TOKENS = explode WORD in
         let (makeitem_body_1 , result_list , prev, lst) = makeitem_body lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push makeitem_body_1 result_list in
         let (unit_names_2 , result_list , prev, lst) = unit_names lst whitespace prev result_list FIRST_CHARS CHARS `:` in
         let result_list = push unit_names_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `:` WORD lst `makeitem` in
         let TOKENS = explode WORD in
         let (name_3 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push name_3 result_list in
         let (more_item_names_4 , result_list , prev, lst) = more_item_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_item_names_4 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = MK_one(`names`,POP_5) in
         let result_list = push tmp_6 result_list in
         let (result_list,pop_list) = chop_off 4 [] result_list in
         let (POP_6 , pop_list ) = (pop pop_list) in
         let (POP_7 , pop_list ) = (pop pop_list) in
         let (POP_8 , pop_list ) = (pop pop_list) in
         let (POP_9 , pop_list ) = (pop pop_list) in
         let tmp_10 = MK_four(`makeitem`,POP_6,POP_7,POP_8,POP_9) in
         let result_list = push tmp_10 result_list in
         do_return result_list whitespace `makeitem` prev lst `nil`)
    else
         fail
  ?
    (let (makeitem_body_0 , result_list , prev, lst) = makeitem_body lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push makeitem_body_0 result_list in
     let (unit_names_1 , result_list , prev, lst) = unit_names lst whitespace prev result_list FIRST_CHARS CHARS `:` in
     let result_list = push unit_names_1 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `:` WORD lst `makeitem` in
     let TOKENS = explode WORD in
     let (name_2 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_2 result_list in
     let (more_item_names_3 , result_list , prev, lst) = more_item_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_item_names_3 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_4 , pop_list ) = (pop pop_list) in
     let tmp_5 = MK_one(`names`,POP_4) in
     let result_list = push tmp_5 result_list in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_5 , pop_list ) = (pop pop_list) in
     let (POP_6 , pop_list ) = (pop pop_list) in
     let (POP_7 , pop_list ) = (pop pop_list) in
     let tmp_8 = MK_three(`makeitem`,POP_5,POP_6,POP_7) in
     let result_list = push tmp_8 result_list in
     do_return result_list whitespace `makeitem` prev lst `nil`);;

makeitem_body:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`makeitem_body`,expected,WORD);
   
    (let (fnname_0 , result_list , prev, lst) =  fnname  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`makeitem_body`,fnname_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `makeitem_body` prev lst `nil`)
  ?
    (let (macname_0 , result_list , prev, lst) = macname lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push macname_0 result_list in
     let (make_mac_1 , result_list , prev, lst) = make_mac lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push make_mac_1 result_list in
     do_return result_list whitespace `makeitem_body` prev lst `nil`);;

make_mac:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`make_mac`,expected,WORD);
   
    if WORD = `{` then
        (let (macparams_0 , result_list , prev, lst) = macparams lst whitespace whitespace result_list FIRST_CHARS CHARS `\}` in
         let result_list = push macparams_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `make_mac` in
         let TOKENS = explode WORD in
         let (snd_macparams_1 , result_list , prev, lst) = snd_macparams lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push snd_macparams_1 result_list in
         do_return result_list whitespace `make_mac` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`makeitem_body`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `make_mac` WORD lst expected);;

snd_macparams:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`snd_macparams`,expected,WORD);
   
    if WORD = `{` then
        (let (macparams_0 , result_list , prev, lst) = macparams lst whitespace whitespace result_list FIRST_CHARS CHARS `\}` in
         let result_list = push macparams_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `snd_macparams` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_three(`makeitem_body`,POP_1,POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `snd_macparams` WORD lst expected)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`makeitem_body`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `snd_macparams` WORD lst expected);;

more_makeitems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_makeitems`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (makeitem_1 , result_list , prev, lst) =  makeitem  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,makeitem_1) in
         let result_list = push tmp_2 result_list in
         let (more_makeitems_2 , result_list , prev, lst) = more_makeitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_makeitems_2 result_list in
         do_return result_list whitespace `more_makeitems` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_makeitems` WORD lst expected);;

more_item_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_item_names`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (name_1 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,name_1) in
     let result_list = push tmp_2 result_list in
     let (more_item_names_2 , result_list , prev, lst) = more_item_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_item_names_2 result_list in
     do_return result_list whitespace `more_item_names` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_item_names` WORD lst expected);;

letitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`letitem`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
     let result_list = push name_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `=` WORD lst `letitem` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (unit_2 , result_list , prev, lst) =  unit  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`letitem`,POP_1,unit_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `letitem` prev lst `nil`);;

more_letitems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_letitems`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (letitem_1 , result_list , prev, lst) =  letitem  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,letitem_1) in
         let result_list = push tmp_2 result_list in
         let (more_letitems_2 , result_list , prev, lst) = more_letitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_letitems_2 result_list in
         do_return result_list whitespace `more_letitems` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_letitems` WORD lst expected);;

joinstep:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`joinstep`,expected,WORD);
   
    if WORD = `JOIN` then
        (let (joinitem_0 , result_list , prev, lst) = joinitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push joinitem_0 result_list in
         let (more_joinitems_1 , result_list , prev, lst) = more_joinitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_joinitems_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`step_JOIN`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `joinstep` prev lst `nil`)
    else
         fail
  ? fail;;

multiplier:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`multiplier`,expected,WORD);
   
    if WORD = `INT` then
        (let (name_0 , result_list , prev, lst) = name lst whitespace whitespace result_list FIRST_CHARS CHARS `=` in
         let result_list = push name_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `=` WORD lst `multiplier` in
         let TOKENS = explode WORD in
         let (int_1 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `multiplier` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (int_4 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let tmp_5 = MK_three(`multiplier_INT`,POP_2,POP_3,int_4) in
         let result_list = push tmp_5 result_list in
         let (more_multipliers_5 , result_list , prev, lst) = more_multipliers lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_multipliers_5 result_list in
         do_return result_list whitespace `multiplier` prev lst `nil`)
    else
         fail
  ? fail;;

more_multipliers:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_multipliers`,expected,WORD);
   
    if WORD = `INT` then
        (let (name_0 , result_list , prev, lst) = name lst whitespace whitespace result_list FIRST_CHARS CHARS `=` in
         let result_list = push name_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `=` WORD lst `more_multipliers` in
         let TOKENS = explode WORD in
         let (int_1 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `more_multipliers` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (int_4 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let tmp_5 = MK_three(`multiplier_INT`,POP_2,POP_3,int_4) in
         let result_list = push tmp_5 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let (POP_6 , pop_list ) = (pop pop_list) in
         let tmp_7 = add_to_list(POP_5,POP_6) in
         let result_list = push tmp_7 result_list in
         let (more_multipliers_7 , result_list , prev, lst) = more_multipliers lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_multipliers_7 result_list in
         do_return result_list whitespace `more_multipliers` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_multipliers` WORD lst expected);;

joinitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`joinitem`,expected,WORD);
   
    (let (unit_0 , result_list , prev, lst) = unit lst whitespace WORD result_list FIRST_CHARS CHARS `->` in
     let result_list = push unit_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `->` WORD lst `joinitem` in
     let TOKENS = explode WORD in
     let (name_1 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_1 result_list in
     let (rest_of_joinitem_2 , result_list , prev, lst) = rest_of_joinitem lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push rest_of_joinitem_2 result_list in
     do_return result_list whitespace `joinitem` prev lst `nil`);;

rest_of_joinitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_joinitem`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `rest_of_joinitem` in
         let TOKENS = explode WORD in
         let (second_join_int_1 , result_list , prev, lst) = second_join_int lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push second_join_int_1 result_list in
         do_return result_list whitespace `rest_of_joinitem` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`joinitem`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `rest_of_joinitem` WORD lst expected);;

second_join_int:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`second_join_int`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `second_join_int` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 4 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = MK_four(`joinitem`,POP_1,POP_2,POP_3,POP_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `second_join_int` WORD lst expected)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_three(`joinitem`,POP_0,POP_1,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `second_join_int` WORD lst expected);;

more_joinitems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_joinitems`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (joinitem_1 , result_list , prev, lst) =  joinitem  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,joinitem_1) in
         let result_list = push tmp_2 result_list in
         let (more_joinitems_2 , result_list , prev, lst) = more_joinitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_joinitems_2 result_list in
         do_return result_list whitespace `more_joinitems` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_joinitems` WORD lst expected);;

printitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`printitem`,expected,WORD);
   
    if WORD = `IF` then
        (let (boolean_0 , result_list , prev, lst) = boolean lst whitespace whitespace result_list FIRST_CHARS CHARS `THEN` in
         let result_list = push boolean_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `THEN` WORD lst `printitem` in
         let TOKENS = explode WORD in
         let (printable_1 , result_list , prev, lst) = printable lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push printable_1 result_list in
         let (more_printables_2 , result_list , prev, lst) = more_printables lst whitespace prev result_list FIRST_CHARS CHARS `FI` in
         let result_list = push more_printables_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `FI` WORD lst `printitem` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = MK_two(`printitem`,POP_3,POP_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `printitem` WORD lst expected)
    else
         fail
  ?
    (let (printable_0 , result_list , prev, lst) = printable lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push printable_0 result_list in
     let (more_printables_1 , result_list , prev, lst) = more_printables lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_printables_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`printitem`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `printitem` prev lst `nil`);;

more_printables:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_printables`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (printable_1 , result_list , prev, lst) =  printable  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,printable_1) in
     let result_list = push tmp_2 result_list in
     let (more_printables_2 , result_list , prev, lst) = more_printables lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_printables_2 result_list in
     do_return result_list whitespace `more_printables` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_printables` WORD lst expected);;

more_printitems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_printitems`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (printitem_1 , result_list , prev, lst) =  printitem  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,printitem_1) in
         let result_list = push tmp_2 result_list in
         let (more_printitems_2 , result_list , prev, lst) = more_printitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_printitems_2 result_list in
         do_return result_list whitespace `more_printitems` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_printitems` WORD lst expected);;

faultitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`faultitem`,expected,WORD);
   
    (let (printitem_0 , result_list , prev, lst) =  printitem  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`faultitem`,printitem_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `faultitem` prev lst `nil`);;

more_faultitems:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_faultitems`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (faultitem_1 , result_list , prev, lst) =  faultitem  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,faultitem_1) in
         let result_list = push tmp_2 result_list in
         let (more_faultitems_2 , result_list , prev, lst) = more_faultitems lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_faultitems_2 result_list in
         do_return result_list whitespace `more_faultitems` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_faultitems` WORD lst expected);;

