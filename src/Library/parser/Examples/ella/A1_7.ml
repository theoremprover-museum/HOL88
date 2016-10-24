
% A1.7 FUNCTIONS %
fndec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`fndec`,expected,WORD);
   
    (let (fnname_0 , result_list , prev, lst) = fnname lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
     let result_list = push fnname_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `=` WORD lst `fndec` in
     let TOKENS = explode WORD in
     let (input_or_FNSET_1 , result_list , prev, lst) = input_or_FNSET lst whitespace WORD result_list FIRST_CHARS CHARS `:` in
     let result_list = push input_or_FNSET_1 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `:` WORD lst `fndec` in
     let TOKENS = explode WORD in
     let (fnbody_2 , result_list , prev, lst) =  fnbody  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_one(`fnbody`,fnbody_2) in
     let result_list = push tmp_3 result_list in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let (POP_4 , pop_list ) = (pop pop_list) in
     let (POP_5 , pop_list ) = (pop pop_list) in
     let tmp_6 = MK_three(`fndec`,POP_3,POP_4,POP_5) in
     let result_list = push tmp_6 result_list in
     do_return result_list whitespace `fndec` prev lst `nil`);;

input_or_FNSET:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`input_or_FNSET`,expected,WORD);
   
    if WORD = `FNSET` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `(` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (input_0 , result_list , prev, lst) = input lst whitespace WORD result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (typ_2 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
         let tmp_3 = MK_two(`fnarrow`,POP_1,typ_2) in
         let result_list = push tmp_3 result_list in
         let (more_input_type_3 , result_list , prev, lst) = more_input_type lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_input_type_3 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = MK_one(`fnarrows`,POP_4) in
         let result_list = push tmp_5 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = MK_one(`fnset`,POP_5) in
         let result_list = push tmp_6 result_list in
         do_return result_list whitespace `input_or_FNSET` WORD lst expected)
    else
         fail
  ?
    if WORD = `FNSET` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\[` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (WORD,lst) = eat_terminal `(` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (input_1 , result_list , prev, lst) = input lst whitespace WORD result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (typ_3 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_4 = MK_two(`fnarrow`,POP_2,typ_3) in
         let result_list = push tmp_4 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `input_or_FNSET` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = MK_two(`fnset`,POP_4,POP_5) in
         let result_list = push tmp_6 result_list in
         do_return result_list whitespace `input_or_FNSET` WORD lst expected)
    else
         fail
  ?
    (let (input_0 , result_list , prev, lst) = input lst whitespace WORD result_list FIRST_CHARS CHARS `->` in
     let result_list = push input_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `->` WORD lst `input_or_FNSET` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (typ_2 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`fnarrow`,POP_1,typ_2) in
     let result_list = push tmp_3 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let tmp_4 = MK_one(`fnset`,POP_3) in
     let result_list = push tmp_4 result_list in
     do_return result_list whitespace `input_or_FNSET` prev lst `nil`);;

more_input_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_input_type`,expected,WORD);
   
    if WORD = `,` then
        (let (input_0 , result_list , prev, lst) = input lst whitespace whitespace result_list FIRST_CHARS CHARS `->` in
         let result_list = push input_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `->` WORD lst `more_input_type` in
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
         let (more_input_type_5 , result_list , prev, lst) = more_input_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_input_type_5 result_list in
         do_return result_list whitespace `more_input_type` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_input_type` WORD lst expected);;

input:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`input`,expected,WORD);
   
    if WORD = `(` then
        (let (inputitem_0 , result_list , prev, lst) = inputitem lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push inputitem_0 result_list in
         let (more_inputs_1 , result_list , prev, lst) = more_inputs lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_inputs_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `input` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`input`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `input` WORD lst expected)
    else
         fail
  ? fail;;

more_inputs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_inputs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (inputitem_1 , result_list , prev, lst) =  inputitem  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,inputitem_1) in
         let result_list = push tmp_2 result_list in
         let (more_inputs_2 , result_list , prev, lst) = more_inputs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_inputs_2 result_list in
         do_return result_list whitespace `more_inputs` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_inputs` WORD lst expected);;

inputitem:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`inputitem`,expected,WORD);
   
    (let (typ_0 , result_list , prev, lst) = typ lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push typ_0 result_list in
     let (poss_name_1 , result_list , prev, lst) = poss_name lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_name_1 result_list in
     do_return result_list whitespace `inputitem` prev lst `nil`);;

poss_name:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_name`,expected,WORD);
   
    if WORD = `:` then
        (let (name_0 , result_list , prev, lst) = name lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push name_0 result_list in
         let (more_in_names_1 , result_list , prev, lst) = more_in_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_in_names_1 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_two(`inputitem`,POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `poss_name` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`inputitem`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `poss_name` WORD lst expected);;

more_in_names:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_in_names`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (name_1 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_2 = add_to_list(POP_0,name_1) in
     let result_list = push tmp_2 result_list in
     let (more_in_names_2 , result_list , prev, lst) = more_in_names lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_in_names_2 result_list in
     do_return result_list whitespace `more_in_names` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_in_names` WORD lst expected);;

fnbody:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`fnbody`,expected,WORD);
   
    if WORD = `DELAY` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `(` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         let (const1_0 , result_list , prev, lst) = const1 lst whitespace WORD result_list FIRST_CHARS CHARS `,` in
         let result_list = push const1_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `,` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         let (int_1 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
         let result_list = push int_1 result_list in
         let (poss_other_int_consts_2 , result_list , prev, lst) = poss_other_int_consts lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push poss_other_int_consts_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `fnbody` WORD lst expected)
    else
         fail
  ?
    if WORD = `ARITH` then
        (let (int_0 , result_list , prev, lst) =  int  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_one(`fnbody_ARITH`,int_0) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `fnbody` prev lst `nil`)
    else
         fail
  ?
    if WORD = `BIOP` then
        (let (biopname_0 , result_list , prev, lst) = biopname lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push biopname_0 result_list in
         let (poss_biopparms_1 , result_list , prev, lst) = poss_biopparms lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push poss_biopparms_1 result_list in
         do_return result_list whitespace `fnbody` prev lst `nil`)
    else
         fail
  ?
    if WORD = `REFORM` then
        (let tmp_0 = MK_zero(`fnbody_REFORM`) in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `fnbody` whitespace lst expected)
    else
         fail
  ?
    if WORD = `IMPORT` then
        (let tmp_0 = MK_zero(`fnbody_IMPORT`) in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `fnbody` whitespace lst expected)
    else
         fail
  ?
    if WORD = `IDELAY` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `(` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         let (const1_0 , result_list , prev, lst) = const1 lst whitespace WORD result_list FIRST_CHARS CHARS `,` in
         let result_list = push const1_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `,` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (int_2 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_3 = MK_two(`fnbody_IDELAY`,POP_1,int_2) in
         let result_list = push tmp_3 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `fnbody` WORD lst expected)
    else
         fail
  ?
    if WORD = `RAM` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `(` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         let (const1_0 , result_list , prev, lst) =  const1  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_1 = MK_one(`fnbody_RAM`,const1_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `fnbody` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `fnbody` WORD lst expected)
    else
         fail
  ?
    (let (unit_0 , result_list , prev, lst) = unit lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push unit_0 result_list in
     do_return result_list whitespace `fnbody` prev lst `nil`);;

poss_other_int_consts:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_other_int_consts`,expected,WORD);
   
    if WORD = `,` then
        (let (const1_0 , result_list , prev, lst) = const1 lst whitespace whitespace result_list FIRST_CHARS CHARS `,` in
         let result_list = push const1_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `,` WORD lst `poss_other_int_consts` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (int_4 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_5 = MK_four(`fnbody_DELAY`,POP_1,POP_2,POP_3,int_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `poss_other_int_consts` prev lst `nil`)
    else
         fail
  ?
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (int_2 , result_list , prev, lst) =  int  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_three(`fnbody_DELAY`,POP_0,POP_1,int_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `poss_other_int_consts` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`fnbody_DELAY`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `poss_other_int_consts` WORD lst expected);;

poss_biopparms:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_biopparms`,expected,WORD);
   
    if WORD = `{` then
        (let (macparams_0 , result_list , prev, lst) = macparams lst whitespace whitespace result_list FIRST_CHARS CHARS `\}` in
         let result_list = push macparams_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `poss_biopparms` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_two(`fnbody_BIOP`,POP_1,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `poss_biopparms` WORD lst expected)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`fnbody_BIOP`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `poss_biopparms` WORD lst expected);;

