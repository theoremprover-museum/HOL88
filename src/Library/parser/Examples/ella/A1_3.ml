
% A1.3 DECLARATIONS %
declaration:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`declaration`,expected,WORD);
   
    if WORD = `TYPE` then
        (let (typedec_0 , result_list , prev, lst) = typedec lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push typedec_0 result_list in
         let (more_typedecs_1 , result_list , prev, lst) = more_typedecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_typedecs_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`declaration`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `declaration` prev lst `nil`)
    else
         fail
  ?
    if WORD = `FN` then
        (let (fndec_0 , result_list , prev, lst) = fndec lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push fndec_0 result_list in
         let (more_fndecs_1 , result_list , prev, lst) = more_fndecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_fndecs_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`declaration`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `declaration` prev lst `nil`)
    else
         fail
  ?
    if WORD = `INT` then
        (let (intdec_0 , result_list , prev, lst) = intdec lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push intdec_0 result_list in
         let (more_intdecs_1 , result_list , prev, lst) = more_intdecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_intdecs_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`declaration`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `declaration` prev lst `nil`)
    else
         fail
  ?
    if WORD = `CONST` then
        (let (constdec_0 , result_list , prev, lst) = constdec lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push constdec_0 result_list in
         let (more_constdecs_1 , result_list , prev, lst) = more_constdecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_constdecs_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`declaration`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `declaration` prev lst `nil`)
    else
         fail
  ?
    if WORD = `MAC` then
        (let (macdec_0 , result_list , prev, lst) = macdec lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push macdec_0 result_list in
         let (more_macdecs_1 , result_list , prev, lst) = more_macdecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_macdecs_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`declaration`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `declaration` prev lst `nil`)
    else
         fail
  ? fail;;

more_typedecs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_typedecs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typedec_1 , result_list , prev, lst) =  typedec  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,typedec_1) in
         let result_list = push tmp_2 result_list in
         let (more_typedecs_2 , result_list , prev, lst) = more_typedecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_typedecs_2 result_list in
         do_return result_list whitespace `more_typedecs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`typedecs`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_typedecs` WORD lst expected);;

more_fndecs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_fndecs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (fndec_1 , result_list , prev, lst) =  fndec  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,fndec_1) in
         let result_list = push tmp_2 result_list in
         let (more_fndecs_2 , result_list , prev, lst) = more_fndecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_fndecs_2 result_list in
         do_return result_list whitespace `more_fndecs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`fndecs`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_fndecs` WORD lst expected);;

more_intdecs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_intdecs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (intdec_1 , result_list , prev, lst) =  intdec  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,intdec_1) in
         let result_list = push tmp_2 result_list in
         let (more_intdecs_2 , result_list , prev, lst) = more_intdecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_intdecs_2 result_list in
         do_return result_list whitespace `more_intdecs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`intdecs`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_intdecs` WORD lst expected);;

more_constdecs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_constdecs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (constdec_1 , result_list , prev, lst) =  constdec  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,constdec_1) in
         let result_list = push tmp_2 result_list in
         let (more_constdecs_2 , result_list , prev, lst) = more_constdecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_constdecs_2 result_list in
         do_return result_list whitespace `more_constdecs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`constdecs`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_constdecs` WORD lst expected);;

more_macdecs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_macdecs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (macdec_1 , result_list , prev, lst) =  macdec  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,macdec_1) in
         let result_list = push tmp_2 result_list in
         let (more_macdecs_2 , result_list , prev, lst) = more_macdecs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_macdecs_2 result_list in
         do_return result_list whitespace `more_macdecs` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`macdecs`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_macdecs` WORD lst expected);;

