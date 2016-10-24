
% A1.2 TEXT (MAIN_LOOP is the text non-terminal) %
MAIN_LOOP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MAIN_LOOP`,expected,WORD);
   
    (let (declaration_0 , result_list , prev, lst) = declaration lst whitespace WORD result_list FIRST_CHARS CHARS `.` in
     let result_list = push declaration_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `.` WORD lst `MAIN_LOOP` in
     let TOKENS = explode WORD in
     let (more_decs_1 , result_list , prev, lst) = more_decs lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_decs_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let tmp_3 = MK_one(`text`,POP_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `MAIN_LOOP` prev lst `nil`);;

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

more_decs:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_decs`,expected,WORD);
   
    (let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (declaration_1 , result_list , prev, lst) =  declaration  lst whitespace  WORD  result_list FIRST_CHARS CHARS `.` in
     let tmp_2 = add_to_list(POP_0,declaration_1) in
     let result_list = push tmp_2 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `.` WORD lst `more_decs` in
     let TOKENS = explode WORD in
     let (more_decs_2 , result_list , prev, lst) = more_decs lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push more_decs_2 result_list in
     do_return result_list whitespace `more_decs` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_decs` WORD lst expected);;

