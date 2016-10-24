
% A1.4 TYPES %
typedec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`typedec`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
     let result_list = push name_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `=` WORD lst `typedec` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (enum_or_type_2 , result_list , prev, lst) =  enum_or_type  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`typedec`,POP_1,enum_or_type_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `typedec` prev lst `nil`);;

enum_or_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`enum_or_type`,expected,WORD);
   
    if WORD = `NEW` then
        (let (finish_enum_0 , result_list , prev, lst) = finish_enum lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
         let result_list = push finish_enum_0 result_list in
         do_return result_list whitespace `enum_or_type` prev lst `nil`)
    else
         fail
  ?
    (let (typ_0 , result_list , prev, lst) = typ lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push typ_0 result_list in
     do_return result_list whitespace `enum_or_type` prev lst `nil`);;

finish_enum:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`finish_enum`,expected,WORD);
   
    if WORD = `(` then
        (let (name_with_typ_0 , result_list , prev, lst) = name_with_typ lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push name_with_typ_0 result_list in
         let (more_enum_typ_1 , result_list , prev, lst) = more_enum_typ lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_enum_typ_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `finish_enum` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `finish_enum` WORD lst expected)
    else
         fail
  ?
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (char_or_int_1 , result_list , prev, lst) = char_or_int lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push char_or_int_1 result_list in
     do_return result_list whitespace `finish_enum` prev lst `nil`);;

char_or_int:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`char_or_int`,expected,WORD);
   
    if WORD = `/` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `(` WORD lst `char_or_int` in
         let TOKENS = explode WORD in
         let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `..` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `..` WORD lst `char_or_int` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (int_3 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS `)` in
         let tmp_4 = MK_three(`enum_int`,POP_1,POP_2,int_3) in
         let result_list = push tmp_4 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `char_or_int` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `char_or_int` WORD lst expected)
    else
         fail
  ?
    if WORD = `(` then
        (let (poss_char_range_0 , result_list , prev, lst) = poss_char_range lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push poss_char_range_0 result_list in
         let (more_char_ranges_1 , result_list , prev, lst) = more_char_ranges lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_char_ranges_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `char_or_int` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `char_or_int` WORD lst expected)
    else
         fail
  ? fail;;

poss_char_range:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_char_range`,expected,WORD);
   
    (let (char_0 , result_list , prev, lst) = char lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push char_0 result_list in
     let (is_c_range_1 , result_list , prev, lst) = is_c_range lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push is_c_range_1 result_list in
     do_return result_list whitespace `poss_char_range` prev lst `nil`);;

is_c_range:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`is_c_range`,expected,WORD);
   
    if WORD = `..` then
        (let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (char_2 , result_list , prev, lst) =  char  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_three(`enum_char`,POP_0,POP_1,char_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `is_c_range` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_two(`enum_char`,POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `is_c_range` WORD lst expected);;

more_char_ranges:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_char_ranges`,expected,WORD);
   
    if WORD = `|` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (poss_char_range_1 , result_list , prev, lst) =  poss_char_range  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,poss_char_range_1) in
         let result_list = push tmp_2 result_list in
         let (more_char_ranges_2 , result_list , prev, lst) = more_char_ranges lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_char_ranges_2 result_list in
         do_return result_list whitespace `more_char_ranges` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`enum_chars`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_char_ranges` WORD lst expected);;

more_enum_typ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_enum_typ`,expected,WORD);
   
    if WORD = `|` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (name_with_typ_1 , result_list , prev, lst) =  name_with_typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,name_with_typ_1) in
         let result_list = push tmp_2 result_list in
         let (more_enum_typ_2 , result_list , prev, lst) = more_enum_typ lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_enum_typ_2 result_list in
         do_return result_list whitespace `more_enum_typ` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`enum_types`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_enum_typ` WORD lst expected);;

name_with_typ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`name_with_typ`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push name_0 result_list in
     let (poss_typ_1 , result_list , prev, lst) = poss_typ lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_typ_1 result_list in
     do_return result_list whitespace `name_with_typ` prev lst `nil`);;

poss_typ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_typ`,expected,WORD);
   
    if WORD = `&` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`enum_type`,POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_typ` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`enum_type`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `poss_typ` WORD lst expected);;

typ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`typ`,expected,WORD);
   
    (let (typ1_0 , result_list , prev, lst) = typ1 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push typ1_0 result_list in
     let (imp_typ1_1 , result_list , prev, lst) = imp_typ1 lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push imp_typ1_1 result_list in
     do_return result_list whitespace `typ` prev lst `nil`);;

imp_typ1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`imp_typ1`,expected,WORD);
   
    if WORD = `->` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ1_1 , result_list , prev, lst) =  typ1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_two(`type`,POP_0,typ1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `imp_typ1` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_one(`type`,POP_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `imp_typ1` WORD lst expected);;

typ1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`typ1`,expected,WORD);
   
    if WORD = `(` then
        (let (typ_0 , result_list , prev, lst) = typ lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push typ_0 result_list in
         let (more_typs_1 , result_list , prev, lst) = more_typs lst whitespace prev result_list FIRST_CHARS CHARS `)` in
         let result_list = push more_typs_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `typ1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`type_tuple`,POP_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`type1`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `typ1` WORD lst expected)
    else
         fail
  ?
    if WORD = `[` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `typ1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (typ_2 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`type_int`,POP_1,typ_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`type1`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `typ1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `STRING` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\[` WORD lst `typ1` in
         let TOKENS = explode WORD in
         let (int_0 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `typ1` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (typename_2 , result_list , prev, lst) =  typename  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`type_STRING`,POP_1,typename_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`type1`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `typ1` prev lst `nil`)
    else
         fail
  ?
    (let (typename_0 , result_list , prev, lst) =  typename  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`type1`,typename_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `typ1` prev lst `nil`)
  ?
    (let (typ2_0 , result_list , prev, lst) =  typ2  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`type1`,typ2_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `typ1` prev lst `nil`);;

more_typs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_typs`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         let (more_typs_2 , result_list , prev, lst) = more_typs lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_typs_2 result_list in
         do_return result_list whitespace `more_typs` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_typs` WORD lst expected);;

typ2:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`typ2`,expected,WORD);
   
    if WORD = `STRING` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\[` WORD lst `typ2` in
         let TOKENS = explode WORD in
         let (WORD,lst) = eat_terminal `INT` WORD lst `typ2` in
         let TOKENS = explode WORD in
         let (typename_0 , result_list , prev, lst) = typename lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push typename_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `typ2` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (name_2 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`type_STRING_INT`,POP_1,name_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`type2`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `typ2` prev lst `nil`)
    else
         fail
  ?
    if WORD = `TYPE` then
        (let (typename_0 , result_list , prev, lst) =  typename  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_one(`type_TYPE`,typename_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`type2`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `typ2` prev lst `nil`)
    else
         fail
  ?
    if WORD = `[` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `INT` WORD lst `typ2` in
         let TOKENS = explode WORD in
         let (typename_0 , result_list , prev, lst) = typename lst whitespace WORD result_list FIRST_CHARS CHARS `\]` in
         let result_list = push typename_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `typ2` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (typ_2 , result_list , prev, lst) =  typ  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
         let tmp_3 = MK_two(`type_INT`,POP_1,typ_2) in
         let result_list = push tmp_3 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = MK_one(`type2`,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `typ2` prev lst `nil`)
    else
         fail
  ? fail;;

