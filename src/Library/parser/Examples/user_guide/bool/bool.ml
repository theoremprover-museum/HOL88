term:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`term`,expected,WORD);
   
    if WORD = `CONJ` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (term_1 , result_list , prev, lst) =  term  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_conj(term_0,term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `DISJ` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (term_1 , result_list , prev, lst) =  term  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_disj(term_0,term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `NOT` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = mk_neg(term_0) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IMP` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (term_1 , result_list , prev, lst) =  term  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_imp(term_0,term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `term` prev lst `nil`)
    else
         fail
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = mk_var(TOKEN_0,":bool") in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `term` whitespace lst `nil`);;

eof:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`eof`,expected,WORD);
   
    if WORD = `nil` then
        (do_return result_list whitespace `eof` `nil` lst expected)
    else
         fail
  ? fail;;

conj:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`conj`,expected,WORD);
   
    if WORD = `CONJ` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (term_1 , result_list , prev, lst) =  term  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_conj(term_0,term_1) in
         let result_list = push tmp_2 result_list in
         let (eof_2 , result_list , prev, lst) = eof lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push eof_2 result_list in
         do_return result_list whitespace `conj` prev lst `nil`)
    else
         fail
  ? fail;;

disj:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`disj`,expected,WORD);
   
    if WORD = `DISJ` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (term_1 , result_list , prev, lst) =  term  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_disj(term_0,term_1) in
         let result_list = push tmp_2 result_list in
         let (eof_2 , result_list , prev, lst) = eof lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push eof_2 result_list in
         do_return result_list whitespace `disj` prev lst `nil`)
    else
         fail
  ? fail;;

neg:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`neg`,expected,WORD);
   
    if WORD = `NEG` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = mk_neg(term_0) in
         let result_list = push tmp_1 result_list in
         let (eof_1 , result_list , prev, lst) = eof lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push eof_1 result_list in
         do_return result_list whitespace `neg` prev lst `nil`)
    else
         fail
  ? fail;;

imp:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`imp`,expected,WORD);
   
    if WORD = `IMP` then
        (let (term_0 , result_list , prev, lst) =  term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (term_1 , result_list , prev, lst) =  term  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_imp(term_0,term_1) in
         let result_list = push tmp_2 result_list in
         let (eof_2 , result_list , prev, lst) = eof lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push eof_2 result_list in
         do_return result_list whitespace `imp` prev lst `nil`)
    else
         fail
  ? fail;;

MAIN_LOOP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MAIN_LOOP`,expected,WORD);
   
    (let (conj_0 , result_list , prev, lst) = conj lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push conj_0 result_list in
     do_return result_list whitespace `MAIN_LOOP` prev lst `nil`)
  ?
    (let (disj_0 , result_list , prev, lst) = disj lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push disj_0 result_list in
     do_return result_list whitespace `MAIN_LOOP` prev lst `nil`)
  ?
    (let (neg_0 , result_list , prev, lst) = neg lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push neg_0 result_list in
     do_return result_list whitespace `MAIN_LOOP` prev lst `nil`)
  ?
    (let (imp_0 , result_list , prev, lst) = imp lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push imp_0 result_list in
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

