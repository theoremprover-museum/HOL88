
% A1.11 MACROS %
macdec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macdec`,expected,WORD);
   
    (let (macname_0 , result_list , prev, lst) = macname lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push macname_0 result_list in
     let (macdec_type_1 , result_list , prev, lst) = macdec_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push macdec_type_1 result_list in
     do_return result_list whitespace `macdec` prev lst `nil`);;

macdec_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macdec_type`,expected,WORD);
   
    if WORD = `=` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `FNSET` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (mac_FNSET_0 , result_list , prev, lst) = mac_FNSET lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push mac_FNSET_0 result_list in
         do_return result_list whitespace `macdec_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `{` then
        (let (macspec_0 , result_list , prev, lst) = macspec lst whitespace whitespace result_list FIRST_CHARS CHARS `\}` in
         let result_list = push macspec_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (WORD,lst) = eat_terminal `=` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (input_1 , result_list , prev, lst) = input lst whitespace WORD result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (typ_2 , result_list , prev, lst) = typ lst whitespace WORD result_list FIRST_CHARS CHARS `:` in
         let result_list = push typ_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `:` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 4 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let (POP_6 , pop_list ) = (pop pop_list) in
         let (fnbody_7 , result_list , prev, lst) =  fnbody  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_8 = MK_five(`macdec`,POP_3,POP_4,POP_5,POP_6,fnbody_7) in
         let result_list = push tmp_8 result_list in
         do_return result_list whitespace `macdec_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `=` then
        (let (input_0 , result_list , prev, lst) = input lst whitespace whitespace result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (typ_1 , result_list , prev, lst) = typ lst whitespace WORD result_list FIRST_CHARS CHARS `:` in
         let result_list = push typ_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `:` WORD lst `macdec_type` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (fnbody_5 , result_list , prev, lst) =  fnbody  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_6 = MK_four(`macdec`,POP_2,POP_3,POP_4,fnbody_5) in
         let result_list = push tmp_6 result_list in
         do_return result_list whitespace `macdec_type` prev lst `nil`)
    else
         fail
  ? fail;;

mac_FNSET:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`mac_FNSET`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (WORD,lst) = eat_terminal `(` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (input_1 , result_list , prev, lst) = input lst whitespace WORD result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (typ_3 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_4 = MK_two(`fnarrow`,POP_2,typ_3) in
         let result_list = push tmp_4 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = MK_two(`fnset`,POP_4,POP_5) in
         let result_list = push tmp_6 result_list in
         let (WORD,lst) = eat_terminal `:` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (fnbody_6 , result_list , prev, lst) =  fnbody  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_7 = MK_one(`fnbody`,fnbody_6) in
         let result_list = push tmp_7 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_7 , pop_list ) = (pop pop_list) in
         let (POP_8 , pop_list ) = (pop pop_list) in
         let (POP_9 , pop_list ) = (pop pop_list) in
         let tmp_10 = MK_three(`macdec`,POP_7,POP_8,POP_9) in
         let result_list = push tmp_10 result_list in
         do_return result_list whitespace `mac_FNSET` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (input_0 , result_list , prev, lst) = input lst whitespace whitespace result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (typ_2 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let tmp_3 = MK_two(`fnarrow`,POP_1,typ_2) in
         let result_list = push tmp_3 result_list in
         let (more_mac_inputs_3 , result_list , prev, lst) = more_mac_inputs lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_mac_inputs_3 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = MK_one(`fnarrows`,POP_4) in
         let result_list = push tmp_5 result_list in
         let (WORD,lst) = eat_terminal `:` WORD lst `mac_FNSET` in
         let TOKENS = explode WORD in
         let (fnbody_5 , result_list , prev, lst) =  fnbody  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_6 = MK_one(`fnbody`,fnbody_5) in
         let result_list = push tmp_6 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_6 , pop_list ) = (pop pop_list) in
         let (POP_7 , pop_list ) = (pop pop_list) in
         let (POP_8 , pop_list ) = (pop pop_list) in
         let tmp_9 = MK_three(`macdec`,POP_6,POP_7,POP_8) in
         let result_list = push tmp_9 result_list in
         do_return result_list whitespace `mac_FNSET` prev lst `nil`)
    else
         fail
  ? fail;;

more_mac_inputs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_mac_inputs`,expected,WORD);
   
    if WORD = `,` then
        (let (input_0 , result_list , prev, lst) = input lst whitespace whitespace result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `more_mac_inputs` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (typ_2 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let tmp_3 = MK_two(`fnarrow`,POP_1,typ_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = add_to_list(POP_3,POP_4) in
         let result_list = push tmp_5 result_list in
         let (more_mac_inputs_5 , result_list , prev, lst) = more_mac_inputs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_mac_inputs_5 result_list in
         do_return result_list whitespace `more_mac_inputs` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_mac_inputs` WORD lst expected);;

macspec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macspec`,expected,WORD);
   
    if WORD = `INT` then
        (let (macspec_body_0 , result_list , prev, lst) =  macspec_body  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`mactype_INT`,macspec_body_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`mactype`,POP_1) in
         let result_list = push tmp_2 result_list in
         let (more_macspecs_2 , result_list , prev, lst) = more_macspecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_macspecs_2 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`macpsec`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `macspec` prev lst `nil`)
    else
         fail
  ?
    if WORD = `TYPE` then
        (let (macspec_body_0 , result_list , prev, lst) =  macspec_body  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`mactype_TYPE`,macspec_body_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`mactype`,POP_1) in
         let result_list = push tmp_2 result_list in
         let (more_macspecs_2 , result_list , prev, lst) = more_macspecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_macspecs_2 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`macpsec`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `macspec` prev lst `nil`)
    else
         fail
  ? fail;;

macspec_body:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macspec_body`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (more_mac_names_1 , result_list , prev, lst) = more_mac_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_mac_names_1 result_list in
     do_return result_list whitespace `macspec_body` prev lst `nil`);;

more_mac_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_mac_names`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (name_1 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,name_1) in
     let result_list = push tmp_2 result_list in
     let (more_mac_names_2 , result_list , prev, lst) = more_mac_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_mac_names_2 result_list in
     do_return result_list whitespace `more_mac_names` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_mac_names` WORD lst expected);;

more_macspecs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_macspecs`,expected,WORD);
   
    if WORD = `INT` then
        (let (macspec_body_0 , result_list , prev, lst) =  macspec_body  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`mactype_INT`,macspec_body_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`mactype`,POP_1) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = add_to_list(POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         let (more_macspecs_4 , result_list , prev, lst) = more_macspecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_macspecs_4 result_list in
         do_return result_list whitespace `more_macspecs` prev lst `nil`)
    else
         fail
  ?
    if WORD = `TYPE` then
        (let (macspec_body_0 , result_list , prev, lst) =  macspec_body  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = MK_one(`mactype_TYPE`,macspec_body_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`mactype`,POP_1) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = add_to_list(POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         let (more_macspecs_4 , result_list , prev, lst) = more_macspecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_macspecs_4 result_list in
         do_return result_list whitespace `more_macspecs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`mactypes`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_macspecs` WORD lst expected);;

printable:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`printable`,expected,WORD);
   
    (let (string_0 , result_list , prev, lst) =  string  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`printable`,string_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `printable` prev lst `nil`)
  ?
    (let (name_0 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`printable`,name_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `printable` prev lst `nil`);;

