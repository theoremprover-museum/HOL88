
% A1.6 CONSTANTS %
constdec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`constdec`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
     let result_list = push name_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `=` WORD lst `constdec` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (const_2 , result_list , prev, lst) =  const  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`constdec`,POP_1,const_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `constdec` prev lst `nil`);;

const:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`const`,expected,WORD);
   
    (let (const1_0 , result_list , prev, lst) = const1 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push const1_0 result_list in
     let (more_consts_1 , result_list , prev, lst) = more_consts lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_consts_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`const`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `const` prev lst `nil`);;

more_consts:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_consts`,expected,WORD);
   
    if WORD = `|` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (const1_1 , result_list , prev, lst) =  const1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,const1_1) in
         let result_list = push tmp_2 result_list in
         let (more_consts_2 , result_list , prev, lst) = more_consts lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_consts_2 result_list in
         do_return result_list whitespace `more_consts` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_consts` WORD lst expected);;

const1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`const1`,expected,WORD);
   
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `const1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (const1_2 , result_list , prev, lst) =  const1  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`const1`,POP_1,const1_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `const1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `STRING` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\[` WORD lst `const1` in
         let TOKENS = explode WORD in
         let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `const1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (const2_2 , result_list , prev, lst) =  const2  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`const1_STRING`,POP_1,const2_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`const1`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `const1` prev lst `nil`)
    else
         fail
  ?
    (let (const2_0 , result_list , prev, lst) =  const2  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`const1`,const2_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `const1` prev lst `nil`);;

const2:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`const2`,expected,WORD);
   
    if WORD = `?` then
        (let (const2_0 , result_list , prev, lst) =  const2  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_one(`const2_uninit`,const2_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`const2`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `const2` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (const_0 , result_list , prev, lst) = const lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push const_0 result_list in
         let (more_consts_1 , result_list , prev, lst) = more_consts lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_consts_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `const2` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`const2_tuple`,POP_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`const2`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `const2` WORD lst expected)
    else
         fail
  ?
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (const2_name_stuff_1 , result_list , prev, lst) = const2_name_stuff lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push const2_name_stuff_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`const2`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `const2` prev lst `nil`);;

const2_name_stuff:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`const2_name_stuff`,expected,WORD);
   
    if WORD = `/` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `(` WORD lst `const2_name_stuff` in
         let TOKENS = explode WORD in
         let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `const2_name_stuff` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (int_3 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_4 = MK_three(`const2_int_range`,POP_1,POP_2,int_3) in
         let result_list = push tmp_4 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `const2_name_stuff` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `const2_name_stuff` WORD lst expected)
    else
         fail
  ?
    if WORD = `/` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula2_1 , result_list , prev, lst) =  formula2  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`const2_formula2`,POP_0,formula2_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `const2_name_stuff` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (char_1 , result_list , prev, lst) =  char  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = MK_two(`const2_char`,POP_0,char_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `const2_name_stuff` prev lst `nil`)
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (string_1 , result_list , prev, lst) =  string  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = MK_two(`const2_string`,POP_0,string_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `const2_name_stuff` prev lst `nil`)
  ?
    if WORD = `&` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (const2_1 , result_list , prev, lst) =  const2  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`const2_const2`,POP_0,const2_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `const2_name_stuff` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (char_0 , result_list , prev, lst) = char lst whitespace whitespace result_list FIRST_CHARS CHARS `..` in
         let result_list = push char_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `const2_name_stuff` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (char_3 , result_list , prev, lst) =  char  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_4 = MK_three(`const2_char_range`,POP_1,POP_2,char_3) in
         let result_list = push tmp_4 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `const2_name_stuff` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `const2_name_stuff` WORD lst expected)
    else
         fail
  ?
    (do_return result_list whitespace `const2_name_stuff` WORD lst expected);;

more_consts:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_consts`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (const_1 , result_list , prev, lst) =  const  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,const_1) in
         let result_list = push tmp_2 result_list in
         let (more_consts_2 , result_list , prev, lst) = more_consts lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_consts_2 result_list in
         do_return result_list whitespace `more_consts` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_consts` WORD lst expected);;

