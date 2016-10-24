MAIN_LOOP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MAIN_LOOP`,expected,WORD);
   
    (let (foo_0 , result_list , prev, lst) = foo lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push foo_0 result_list in
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

foo:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`foo`,expected,WORD);
   
    if WORD = `'` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let TOKENS = explode WORD in
         let WORD_0 = WORD in
         let tmp_1 = print_string(WORD_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `'` WORD lst `foo` in
         let TOKENS = explode WORD in
         let (foo_1 , result_list , prev, lst) = foo lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push foo_1 result_list in
         do_return result_list whitespace `foo` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `foo` WORD lst expected);;

