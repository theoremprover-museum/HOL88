tyname:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`tyname`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = mk_type_name(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `tyname` whitespace lst `nil`);;

tyvar:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`tyvar`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = mk_type_var(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `tyvar` whitespace lst `nil`);;

MAIN_LOOP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MAIN_LOOP`,expected,WORD);
   
    (let (typ_0 , result_list , prev, lst) = typ lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push typ_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `nil` WORD lst `MAIN_LOOP` in
     let TOKENS = explode WORD in
     do_return result_list whitespace `MAIN_LOOP` WORD lst expected);;

let PARSE_file (in_file,whitespace,separators) =
   let white = if null whitespace then
                  [` `;`\T`;`\L`]
               else
                  whitespace and
       inf = open_file `in` in_file in
   let WORD = e_w_s inf (hd white) white in
   let lst = read_input inf [] white separators WORD IGNORE USEFUL in
   let (WORD,lst) = (hd lst,tl lst) in
   let result = fst (MAIN_LOOP lst (hd white) WORD []
                               FIRST_CHARS CHARS `nil`) in
       result
   ? fail;;

let PARSE_text (text,whitespace,separators) =
    let outf = open_file `out` `/tmp/.000HOL` in
    write_string text outf;
    close_file outf;
    let result = PARSE_file (`/tmp/.000HOL`,whitespace,separators) in
        unlink `/tmp/.000HOL`; result;;

typ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`typ`,expected,WORD);
   
    (let (type1_0 , result_list , prev, lst) = type1 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push type1_0 result_list in
     let (more_type_1 , result_list , prev, lst) = more_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_type_1 result_list in
     do_return result_list whitespace `typ` prev lst `nil`);;

more_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_type`,expected,WORD);
   
    if WORD = `#` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (type1_0 , result_list , prev, lst) =  type1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(type1_0,POP_1) in
         let result_list = push tmp_2 result_list in
         let (more_prod_type_2 , result_list , prev, lst) = more_prod_type lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push more_prod_type_2 result_list in
         let (sum_or_fun_type_3 , result_list , prev, lst) = sum_or_fun_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push sum_or_fun_type_3 result_list in
         do_return result_list whitespace `more_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `->` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_bin_type(`fun`,POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `more_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `+` then
        (let (type1_0 , result_list , prev, lst) = type1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push type1_0 result_list in
         let (more_sum_type_1 , result_list , prev, lst) = more_sum_type lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push more_sum_type_1 result_list in
         let (fun_type_2 , result_list , prev, lst) = fun_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push fun_type_2 result_list in
         do_return result_list whitespace `more_type` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_type` WORD lst expected);;

more_prod_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_prod_type`,expected,WORD);
   
    if WORD = `#` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (type1_0 , result_list , prev, lst) =  type1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(type1_0,POP_1) in
         let result_list = push tmp_2 result_list in
         let (more_prod_type_2 , result_list , prev, lst) = more_prod_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_prod_type_2 result_list in
         do_return result_list whitespace `more_prod_type` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let tmp_1 = MK_defd_type(POP_0,`prod`) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `more_prod_type` WORD lst expected);;

sum_or_fun_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`sum_or_fun_type`,expected,WORD);
   
    if WORD = `+` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_bin_type(`sum`,POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `sum_or_fun_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `->` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_bin_type(`fun`,POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `sum_or_fun_type` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `sum_or_fun_type` WORD lst expected);;

more_sum_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_sum_type`,expected,WORD);
   
    if WORD = `+` then
        (let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = add_to_list_rev(POP_0,POP_1) in
         let result_list = push tmp_2 result_list in
         let (type1_2 , result_list , prev, lst) = type1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push type1_2 result_list in
         let (more_sum_type_3 , result_list , prev, lst) = more_sum_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_sum_type_3 result_list in
         do_return result_list whitespace `more_sum_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `#` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (type1_0 , result_list , prev, lst) =  type1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(type1_0,POP_1) in
         let result_list = push tmp_2 result_list in
         let (more_prod_type_2 , result_list , prev, lst) = more_prod_type lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push more_prod_type_2 result_list in
         let (more_sum_type_3 , result_list , prev, lst) = more_sum_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_sum_type_3 result_list in
         do_return result_list whitespace `more_sum_type` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = add_to_list_rev(POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_defd_type(POP_2,`sum`) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `more_sum_type` WORD lst expected);;

fun_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`fun_type`,expected,WORD);
   
    if WORD = `->` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_bin_type(`fun`,POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `fun_type` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `fun_type` WORD lst expected);;

type1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`type1`,expected,WORD);
   
    if WORD = `(` then
        (let (typ_0 , result_list , prev, lst) = typ lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push typ_0 result_list in
         let (poss_cmpnd_type_1 , result_list , prev, lst) = poss_cmpnd_type lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push poss_cmpnd_type_1 result_list in
         do_return result_list whitespace `type1` prev lst `nil`)
    else
         fail
  ?
    (let (tyname_0 , result_list , prev, lst) = tyname lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push tyname_0 result_list in
     let (more_type1_1 , result_list , prev, lst) = more_type1 lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_type1_1 result_list in
     do_return result_list whitespace `type1` prev lst `nil`)
  ?
    (let (tyvar_0 , result_list , prev, lst) = tyvar lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push tyvar_0 result_list in
     let (more_type1_1 , result_list , prev, lst) = more_type1 lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_type1_1 result_list in
     do_return result_list whitespace `type1` prev lst `nil`);;

poss_cmpnd_type:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_cmpnd_type`,expected,WORD);
   
    if WORD = `)` then
        (let (more_type1_0 , result_list , prev, lst) = more_type1 lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
         let result_list = push more_type1_0 result_list in
         do_return result_list whitespace `poss_cmpnd_type` prev lst `nil`)
    else
         fail
  ?
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         let (rest_of_cmpnd_2 , result_list , prev, lst) = rest_of_cmpnd lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_cmpnd_2 result_list in
         do_return result_list whitespace `poss_cmpnd_type` prev lst `nil`)
    else
         fail
  ? fail;;

rest_of_cmpnd:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_cmpnd`,expected,WORD);
   
    if WORD = `,` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = add_to_list(POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         let (rest_of_cmpnd_2 , result_list , prev, lst) = rest_of_cmpnd lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_cmpnd_2 result_list in
         do_return result_list whitespace `rest_of_cmpnd` prev lst `nil`)
    else
         fail
  ?
    if WORD = `)` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (WORD,lst) = gnt lst whitespace whitespace in
         let TOKENS = explode WORD in
         let TOKEN_1 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
         let tmp_2 = MK_cmpnd_type(POP_0,TOKEN_1) in
         let result_list = push tmp_2 result_list in
         let (more_type1_2 , result_list , prev, lst) = more_type1 lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
         let result_list = push more_type1_2 result_list in
         do_return result_list whitespace `rest_of_cmpnd` prev lst `nil`)
    else
         fail
  ? fail;;

more_type1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_type1`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let TOKEN_1 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
     let tmp_2 = MK_type(POP_0,TOKEN_1) in
     let result_list = push tmp_2 result_list in
     let (more_type1_2 , result_list , prev, lst) = more_type1 lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
     let result_list = push more_type1_2 result_list in
     do_return result_list whitespace `more_type1` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_type1` WORD lst expected);;

