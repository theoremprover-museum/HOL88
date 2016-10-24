MAIN_LOOP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MAIN_LOOP`,expected,WORD);
   
    (let (Term_0 , result_list , prev, lst) = Term lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push Term_0 result_list in
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

Term:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`Term`,expected,WORD);
   
    if WORD = `\\` then
        (let (Var_or_const_0 , result_list , prev, lst) =  Var_or_const  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (Abstraction_1 , result_list , prev, lst) =  Abstraction  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = preterm_abs(Var_or_const_0,Abstraction_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `Term` prev lst `nil`)
    else
         fail
  ?
    (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push Term1_0 result_list in
     let (more_Term_1 , result_list , prev, lst) = more_Term lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_Term_1 result_list in
     do_return result_list whitespace `Term` prev lst `nil`);;

Abstraction:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`Abstraction`,expected,WORD);
   
    if WORD = `.` then
        (let (Term_0 , result_list , prev, lst) = Term lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
         let result_list = push Term_0 result_list in
         do_return result_list whitespace `Abstraction` prev lst `nil`)
    else
         fail
  ?
    if WORD = `\\` then
        (let (Var_or_const_0 , result_list , prev, lst) =  Var_or_const  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (Abstraction_1 , result_list , prev, lst) =  Abstraction  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = preterm_abs(Var_or_const_0,Abstraction_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `Abstraction` prev lst `nil`)
    else
         fail
  ?
    (let (Var_or_const_0 , result_list , prev, lst) =  Var_or_const  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let (Abstraction_1 , result_list , prev, lst) =  Abstraction  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = preterm_abs(Var_or_const_0,Abstraction_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `Abstraction` prev lst `nil`);;

Term1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`Term1`,expected,WORD);
   
    if WORD = `~` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = mk_unop_typed(`~`,Term1_0,`bool`,`bool`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `Term1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (Term_0 , result_list , prev, lst) = Term lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push Term_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `Term1` in
         let TOKENS = explode WORD in
         let (is_typed_1 , result_list , prev, lst) = is_typed lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push is_typed_1 result_list in
         do_return result_list whitespace `Term1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `[` then
        (let (Term_list_0 , result_list , prev, lst) = Term_list lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term_list_0 result_list in
         let (is_typed_1 , result_list , prev, lst) = is_typed lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push is_typed_1 result_list in
         do_return result_list whitespace `Term1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `CONS` then
        (let (Term_0 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`CONS`,Term_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `Term1` prev lst `nil`)
    else
         fail
  ?
    (let (Var_or_const_0 , result_list , prev, lst) = Var_or_const lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push Var_or_const_0 result_list in
     do_return result_list whitespace `Term1` prev lst `nil`);;

Term_list:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`Term_list`,expected,WORD);
   
    if WORD = `]` then
        (let tmp_0 = preterm_const(`NIL`) in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `Term_list` whitespace lst expected)
    else
         fail
  ?
    (let (Term_0 , result_list , prev, lst) =  Term  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let (rest_of_list_1 , result_list , prev, lst) =  rest_of_list  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
     let tmp_2 = mk_cons(Term_0,rest_of_list_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `Term_list` prev lst `nil`);;

rest_of_list:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_list`,expected,WORD);
   
    if WORD = `;` then
        (let (Term_0 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (rest_of_list_1 , result_list , prev, lst) =  rest_of_list  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_cons(Term_0,rest_of_list_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_list` prev lst `nil`)
    else
         fail
  ?
    if WORD = `]` then
        (let tmp_0 = preterm_const(`NIL`) in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `rest_of_list` whitespace lst expected)
    else
         fail
  ? fail;;

Var_or_const:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`Var_or_const`,expected,WORD);
   
    if WORD = `\`` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let TOKENS = explode WORD in
         let WORD_0 = WORD in
         let tmp_1 = string_const(WORD_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\`` WORD lst `Var_or_const` in
         let TOKENS = explode WORD in
         let (is_typed_1 , result_list , prev, lst) = is_typed lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push is_typed_1 result_list in
         do_return result_list whitespace `Var_or_const` prev lst `nil`)
    else
         fail
  ?
    if WORD = `NIL` then
        (let tmp_0 = preterm_const(`NIL`) in
         let result_list = push tmp_0 result_list in
         let (is_typed_0 , result_list , prev, lst) = is_typed lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
         let result_list = push is_typed_0 result_list in
         do_return result_list whitespace `Var_or_const` prev lst `nil`)
    else
         fail
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
     let tmp_1 = num_const(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     let (is_typed_1 , result_list , prev, lst) = is_typed lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
     let result_list = push is_typed_1 result_list in
     do_return result_list whitespace `Var_or_const` prev lst `nil`)
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
     let tmp_1 = bool_const(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     let (is_typed_1 , result_list , prev, lst) = is_typed lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
     let result_list = push is_typed_1 result_list in
     do_return result_list whitespace `Var_or_const` prev lst `nil`)
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
     let tmp_1 = preterm_var(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     let (is_typed_1 , result_list , prev, lst) = is_typed lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
     let result_list = push is_typed_1 result_list in
     do_return result_list whitespace `Var_or_const` prev lst `nil`);;

is_typed:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`is_typed`,expected,WORD);
   
    if WORD = `:` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (typ_1 , result_list , prev, lst) =  typ  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = change_to_typed(POP_0,typ_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `is_typed` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `is_typed` WORD lst expected);;

more_Term:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_Term`,expected,WORD);
   
    if WORD = `o` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`o`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `Sum` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`Sum`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IS_ASSUMPTION_OF` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`IS_ASSUMPTION_OF`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `=` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (EQ_lower_1 , result_list , prev, lst) = EQ_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push EQ_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_EQ_3 , result_list , prev, lst) =  more_EQ  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_untyped(`=`,POP_2,more_EQ_3) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_untyped(`=`,POP_4,POP_5) in
         let result_list = push tmp_6 result_list in
         let (EQ_higher_6 , result_list , prev, lst) = EQ_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push EQ_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=>` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (IFF_lower_1 , result_list , prev, lst) = IFF_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push IFF_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_IFF_3 , result_list , prev, lst) =  more_IFF  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`<=>`,POP_2,more_IFF_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`<=>`,POP_4,POP_5,`bool`,`bool`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (IFF_higher_6 , result_list , prev, lst) = IFF_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push IFF_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `==>` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (IMP_lower_1 , result_list , prev, lst) = IMP_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push IMP_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_IMP_3 , result_list , prev, lst) =  more_IMP  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`==>`,POP_2,more_IMP_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`==>`,POP_4,POP_5,`bool`,`bool`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (IMP_higher_6 , result_list , prev, lst) = IMP_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push IMP_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `\\/` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (DISJ_lower_1 , result_list , prev, lst) = DISJ_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push DISJ_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_DISJ_3 , result_list , prev, lst) =  more_DISJ  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`\\/`,POP_2,more_DISJ_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`\\/`,POP_4,POP_5,`bool`,`bool`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (DISJ_higher_6 , result_list , prev, lst) = DISJ_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push DISJ_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `/\\` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (CONJ_lower_1 , result_list , prev, lst) = CONJ_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push CONJ_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_CONJ_3 , result_list , prev, lst) =  more_CONJ  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`/\\`,POP_2,more_CONJ_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`/\\`,POP_4,POP_5,`bool`,`bool`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (CONJ_higher_6 , result_list , prev, lst) = CONJ_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push CONJ_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`>`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`>`,POP_4,POP_5,`num`,`num`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (BOOL_higher_6 , result_list , prev, lst) = BOOL_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push BOOL_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`<`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`<`,POP_4,POP_5,`num`,`num`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (BOOL_higher_6 , result_list , prev, lst) = BOOL_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push BOOL_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>=` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`>=`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`>=`,POP_4,POP_5,`num`,`num`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (BOOL_higher_6 , result_list , prev, lst) = BOOL_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push BOOL_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`<=`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`<=`,POP_4,POP_5,`num`,`num`,`bool`) in
         let result_list = push tmp_6 result_list in
         let (BOOL_higher_6 , result_list , prev, lst) = BOOL_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push BOOL_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `+` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (P_M_lower_1 , result_list , prev, lst) = P_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push P_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_P_M_3 , result_list , prev, lst) =  more_P_M  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`+`,POP_2,more_P_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`+`,POP_4,POP_5,`num`,`num`,`num`) in
         let result_list = push tmp_6 result_list in
         let (P_M_higher_6 , result_list , prev, lst) = P_M_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push P_M_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (P_M_lower_1 , result_list , prev, lst) = P_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push P_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_P_M_3 , result_list , prev, lst) =  more_P_M  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`-`,POP_2,more_P_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`-`,POP_4,POP_5,`num`,`num`,`num`) in
         let result_list = push tmp_6 result_list in
         let (P_M_higher_6 , result_list , prev, lst) = P_M_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push P_M_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `*` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (MLT_lower_1 , result_list , prev, lst) = MLT_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push MLT_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_MLT_3 , result_list , prev, lst) =  more_MLT  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`*`,POP_2,more_MLT_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`*`,POP_4,POP_5,`num`,`num`,`num`) in
         let result_list = push tmp_6 result_list in
         let (MLT_higher_6 , result_list , prev, lst) = MLT_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push MLT_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `DIV` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (D_M_lower_1 , result_list , prev, lst) = D_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push D_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_D_M_3 , result_list , prev, lst) =  more_D_M  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`DIV`,POP_2,more_D_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`DIV`,POP_4,POP_5,`num`,`num`,`num`) in
         let result_list = push tmp_6 result_list in
         let (D_M_higher_6 , result_list , prev, lst) = D_M_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push D_M_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `MOD` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (D_M_lower_1 , result_list , prev, lst) = D_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push D_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_D_M_3 , result_list , prev, lst) =  more_D_M  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_4 = mk_binop_typed(`MOD`,POP_2,more_D_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_binop_typed(`MOD`,POP_4,POP_5,`num`,`num`,`num`) in
         let result_list = push tmp_6 result_list in
         let (D_M_higher_6 , result_list , prev, lst) = D_M_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push D_M_higher_6 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    if WORD = `EXP` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_EXP_1 , result_list , prev, lst) =  more_EXP  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_binop_typed(`EXP`,Term1_0,more_EXP_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`EXP`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         let (EXP_higher_4 , result_list , prev, lst) = EXP_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push EXP_higher_4 result_list in
         do_return result_list whitespace `more_Term` prev lst `nil`)
    else
         fail
  ?
    (let WORD_0 = WORD in
     let tmp_1 = IS_infix(WORD_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let (Term1_3 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
     let (more_arbit_4 , result_list , prev, lst) =  more_arbit  lst whitespace  prev  result_list FIRST_CHARS CHARS `nil` in
     let tmp_5 = arbit_binop3(POP_1,POP_2,Term1_3,more_arbit_4) in
     let result_list = push tmp_5 result_list in
     let (arbit_higher_5 , result_list , prev, lst) = arbit_higher lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push arbit_higher_5 result_list in
     do_return result_list whitespace `more_Term` prev lst `nil`)
  ?
    (do_return result_list whitespace `more_Term` WORD lst expected);;

more_arbit:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_arbit`,expected,WORD);
   
    (let WORD_0 = WORD in
     let tmp_1 = IS_infix(WORD_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (Term1_2 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
     let (more_arbit_3 , result_list , prev, lst) =  more_arbit  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
     let tmp_4 = arbit_binop2(POP_1,Term1_2,more_arbit_3) in
     let result_list = push tmp_4 result_list in
     do_return result_list whitespace `more_arbit` prev lst `nil`)
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_arbit` WORD lst expected);;

more_EXP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_EXP`,expected,WORD);
   
    if WORD = `EXP` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (EXP_lower_1 , result_list , prev, lst) = EXP_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push EXP_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_EXP_3 , result_list , prev, lst) =  more_EXP  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`EXP`,POP_2,more_EXP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_EXP` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_EXP` WORD lst expected);;

EXP_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`EXP_lower`,expected,WORD);
   
    (let WORD_0 = WORD in
     let tmp_1 = IS_infix(WORD_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let (Term1_3 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
     let (more_arbit_4 , result_list , prev, lst) =  more_arbit  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
     let tmp_5 = arbit_binop3(POP_1,POP_2,Term1_3,more_arbit_4) in
     let result_list = push tmp_5 result_list in
     do_return result_list whitespace `EXP_lower` prev lst `nil`)
  ?
    (do_return result_list whitespace `EXP_lower` WORD lst expected);;

more_D_M:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_D_M`,expected,WORD);
   
    if WORD = `DIV` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (D_M_lower_1 , result_list , prev, lst) = D_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push D_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_D_M_3 , result_list , prev, lst) =  more_D_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`DIV`,POP_2,more_D_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_D_M` prev lst `nil`)
    else
         fail
  ?
    if WORD = `MOD` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (D_M_lower_1 , result_list , prev, lst) = D_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push D_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_D_M_3 , result_list , prev, lst) =  more_D_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`MOD`,POP_2,more_D_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_D_M` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_D_M` WORD lst expected);;

D_M_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`D_M_lower`,expected,WORD);
   
    if WORD = `EXP` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_EXP_1 , result_list , prev, lst) =  more_EXP  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`EXP`,Term1_0,more_EXP_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`EXP`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `D_M_lower` prev lst `nil`)
    else
         fail
  ?
    (let (EXP_lower_0 , result_list , prev, lst) = EXP_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push EXP_lower_0 result_list in
     do_return result_list whitespace `D_M_lower` prev lst `nil`);;

more_MLT:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_MLT`,expected,WORD);
   
    if WORD = `*` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (MLT_lower_1 , result_list , prev, lst) = MLT_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push MLT_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_MLT_3 , result_list , prev, lst) =  more_MLT  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`*`,POP_2,more_MLT_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_MLT` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_MLT` WORD lst expected);;

MLT_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MLT_lower`,expected,WORD);
   
    if WORD = `DIV` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_D_M_1 , result_list , prev, lst) =  more_D_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`DIV`,Term1_0,more_D_M_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`DIV`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `MLT_lower` prev lst `nil`)
    else
         fail
  ?
    if WORD = `MOD` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_D_M_1 , result_list , prev, lst) =  more_D_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`MOD`,Term1_0,more_D_M_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`MOD`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `MLT_lower` prev lst `nil`)
    else
         fail
  ?
    (let (D_M_lower_0 , result_list , prev, lst) = D_M_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push D_M_lower_0 result_list in
     do_return result_list whitespace `MLT_lower` prev lst `nil`);;

more_P_M:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_P_M`,expected,WORD);
   
    if WORD = `+` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (P_M_lower_1 , result_list , prev, lst) = P_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push P_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_P_M_3 , result_list , prev, lst) =  more_P_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`+`,POP_2,more_P_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_P_M` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (P_M_lower_1 , result_list , prev, lst) = P_M_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push P_M_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_P_M_3 , result_list , prev, lst) =  more_P_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`-`,POP_2,more_P_M_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_P_M` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_P_M` WORD lst expected);;

P_M_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`P_M_lower`,expected,WORD);
   
    if WORD = `*` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_MLT_1 , result_list , prev, lst) =  more_MLT  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`*`,Term1_0,more_MLT_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`*`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `P_M_lower` prev lst `nil`)
    else
         fail
  ?
    (let (MLT_lower_0 , result_list , prev, lst) = MLT_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push MLT_lower_0 result_list in
     do_return result_list whitespace `P_M_lower` prev lst `nil`);;

more_BOOL:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_BOOL`,expected,WORD);
   
    if WORD = `<` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`<`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_BOOL` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`>`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_BOOL` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`<=`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_BOOL` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>=` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (BOOL_lower_1 , result_list , prev, lst) = BOOL_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push BOOL_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_BOOL_3 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`>=`,POP_2,more_BOOL_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_BOOL` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_BOOL` WORD lst expected);;

BOOL_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`BOOL_lower`,expected,WORD);
   
    if WORD = `+` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_P_M_1 , result_list , prev, lst) =  more_P_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`+`,Term1_0,more_P_M_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`+`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `BOOL_lower` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_P_M_1 , result_list , prev, lst) =  more_P_M  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`-`,Term1_0,more_P_M_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`-`,POP_2,POP_3,`num`,`num`,`num`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `BOOL_lower` prev lst `nil`)
    else
         fail
  ?
    (let (P_M_lower_0 , result_list , prev, lst) = P_M_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push P_M_lower_0 result_list in
     do_return result_list whitespace `BOOL_lower` prev lst `nil`);;

more_CONJ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_CONJ`,expected,WORD);
   
    if WORD = `/\\` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (CONJ_lower_1 , result_list , prev, lst) = CONJ_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push CONJ_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_CONJ_3 , result_list , prev, lst) =  more_CONJ  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`/\\`,POP_2,more_CONJ_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_CONJ` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_CONJ` WORD lst expected);;

CONJ_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`CONJ_lower`,expected,WORD);
   
    if WORD = `<` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_BOOL_1 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`<`,Term1_0,more_BOOL_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`<`,POP_2,POP_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `CONJ_lower` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_BOOL_1 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`>`,Term1_0,more_BOOL_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`>`,POP_2,POP_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `CONJ_lower` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_BOOL_1 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`<=`,Term1_0,more_BOOL_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`<=`,POP_2,POP_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `CONJ_lower` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>=` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_BOOL_1 , result_list , prev, lst) =  more_BOOL  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`>=`,Term1_0,more_BOOL_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`>=`,POP_2,POP_3,`num`,`num`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `CONJ_lower` prev lst `nil`)
    else
         fail
  ?
    (let (BOOL_lower_0 , result_list , prev, lst) = BOOL_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push BOOL_lower_0 result_list in
     do_return result_list whitespace `CONJ_lower` prev lst `nil`);;

more_DISJ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_DISJ`,expected,WORD);
   
    if WORD = `\\/` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (DISJ_lower_1 , result_list , prev, lst) = DISJ_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push DISJ_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_DISJ_3 , result_list , prev, lst) =  more_DISJ  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`\\/`,POP_2,more_DISJ_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_DISJ` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_DISJ` WORD lst expected);;

DISJ_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`DISJ_lower`,expected,WORD);
   
    if WORD = `/\\` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_CONJ_1 , result_list , prev, lst) =  more_CONJ  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`/\\`,Term1_0,more_CONJ_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`/\\`,POP_2,POP_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `DISJ_lower` prev lst `nil`)
    else
         fail
  ?
    (let (CONJ_lower_0 , result_list , prev, lst) = CONJ_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push CONJ_lower_0 result_list in
     do_return result_list whitespace `DISJ_lower` prev lst `nil`);;

more_IMP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_IMP`,expected,WORD);
   
    if WORD = `==>` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (IMP_lower_1 , result_list , prev, lst) = IMP_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push IMP_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_IMP_3 , result_list , prev, lst) =  more_IMP  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`==>`,POP_2,more_IMP_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_IMP` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_IMP` WORD lst expected);;

IMP_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`IMP_lower`,expected,WORD);
   
    if WORD = `\\/` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_DISJ_1 , result_list , prev, lst) =  more_DISJ  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`\\/`,Term1_0,more_DISJ_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`\\/`,POP_2,POP_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `IMP_lower` prev lst `nil`)
    else
         fail
  ?
    (let (DISJ_lower_0 , result_list , prev, lst) = DISJ_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push DISJ_lower_0 result_list in
     do_return result_list whitespace `IMP_lower` prev lst `nil`);;

more_IFF:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_IFF`,expected,WORD);
   
    if WORD = `<=>` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (IFF_lower_1 , result_list , prev, lst) = IFF_lower lst whitespace prev result_list FIRST_CHARS CHARS `nil` in
         let result_list = push IFF_lower_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (more_IFF_3 , result_list , prev, lst) =  more_IFF  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_4 = mk_binop_typed(`<=>`,POP_2,more_IFF_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_IFF` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_IFF` WORD lst expected);;

IFF_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`IFF_lower`,expected,WORD);
   
    if WORD = `==>` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_IMP_1 , result_list , prev, lst) =  more_IMP  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`==>`,Term1_0,more_IMP_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`==>`,POP_2,POP_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `IFF_lower` prev lst `nil`)
    else
         fail
  ?
    (let (IMP_lower_0 , result_list , prev, lst) = IMP_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push IMP_lower_0 result_list in
     do_return result_list whitespace `IFF_lower` prev lst `nil`);;

more_EQ:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_EQ`,expected,WORD);
   
    if WORD = `=` then
        (let (Term1_0 , result_list , prev, lst) = Term1 lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push Term1_0 result_list in
         let (EQ_lower_1 , result_list , prev, lst) = EQ_lower lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push EQ_lower_1 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_untyped(`=`,POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_EQ` prev lst `nil`)
    else
         fail
  ?
    (let tmp_0 = dummy() in
     let result_list = push tmp_0 result_list in
     do_return result_list whitespace `more_EQ` WORD lst expected);;

EQ_lower:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`EQ_lower`,expected,WORD);
   
    if WORD = `<=>` then
        (let (Term1_0 , result_list , prev, lst) =  Term1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let (more_IFF_1 , result_list , prev, lst) =  more_IFF  lst whitespace  prev  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`<=>`,Term1_0,more_IFF_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_binop_typed(`<=>`,POP_2,POP_3,`bool`,`bool`,`bool`) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `EQ_lower` prev lst `nil`)
    else
         fail
  ?
    (let (IFF_lower_0 , result_list , prev, lst) = IFF_lower lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push IFF_lower_0 result_list in
     do_return result_list whitespace `EQ_lower` prev lst `nil`);;

arbit_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`arbit_higher`,expected,WORD);
   
    if WORD = `EXP` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`EXP`,POP_0,Term_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `arbit_higher` prev lst `nil`)
    else
         fail
  ?
    (let (EXP_higher_0 , result_list , prev, lst) = EXP_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push EXP_higher_0 result_list in
     do_return result_list whitespace `arbit_higher` prev lst `nil`);;

EXP_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`EXP_higher`,expected,WORD);
   
    if WORD = `MOD` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`MOD`,POP_0,Term_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `EXP_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `DIV` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`DIV`,POP_0,Term_1,`bool`,`bool`,`num`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `EXP_higher` prev lst `nil`)
    else
         fail
  ?
    (let (D_M_higher_0 , result_list , prev, lst) = D_M_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push D_M_higher_0 result_list in
     do_return result_list whitespace `EXP_higher` prev lst `nil`);;

D_M_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`D_M_higher`,expected,WORD);
   
    if WORD = `*` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`*`,POP_0,Term_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `D_M_higher` prev lst `nil`)
    else
         fail
  ?
    (let (MLT_higher_0 , result_list , prev, lst) = MLT_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push MLT_higher_0 result_list in
     do_return result_list whitespace `D_M_higher` prev lst `nil`);;

MLT_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MLT_higher`,expected,WORD);
   
    if WORD = `+` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`+`,POP_0,Term_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `MLT_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`-`,POP_0,Term_1,`num`,`num`,`num`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `MLT_higher` prev lst `nil`)
    else
         fail
  ?
    (let (P_M_higher_0 , result_list , prev, lst) = P_M_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push P_M_higher_0 result_list in
     do_return result_list whitespace `MLT_higher` prev lst `nil`);;

P_M_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`P_M_higher`,expected,WORD);
   
    if WORD = `<` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`<`,POP_0,Term_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `P_M_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`<=`,POP_0,Term_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `P_M_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`>`,POP_0,Term_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `P_M_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`>=`,POP_0,Term_1,`num`,`num`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `P_M_higher` prev lst `nil`)
    else
         fail
  ?
    (let (BOOL_higher_0 , result_list , prev, lst) = BOOL_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push BOOL_higher_0 result_list in
     do_return result_list whitespace `P_M_higher` prev lst `nil`);;

BOOL_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`BOOL_higher`,expected,WORD);
   
    if WORD = `/\\` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`/\\`,POP_0,Term_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `BOOL_higher` prev lst `nil`)
    else
         fail
  ?
    (let (CONJ_higher_0 , result_list , prev, lst) = CONJ_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push CONJ_higher_0 result_list in
     do_return result_list whitespace `BOOL_higher` prev lst `nil`);;

CONJ_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`CONJ_higher`,expected,WORD);
   
    if WORD = `\\/` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`\\/`,POP_0,Term_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `CONJ_higher` prev lst `nil`)
    else
         fail
  ?
    (let (DISJ_higher_0 , result_list , prev, lst) = DISJ_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push DISJ_higher_0 result_list in
     do_return result_list whitespace `CONJ_higher` prev lst `nil`);;

DISJ_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`DISJ_higher`,expected,WORD);
   
    if WORD = `==>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`==>`,POP_0,Term_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `DISJ_higher` prev lst `nil`)
    else
         fail
  ?
    (let (IMP_higher_0 , result_list , prev, lst) = IMP_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push IMP_higher_0 result_list in
     do_return result_list whitespace `DISJ_higher` prev lst `nil`);;

IMP_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`IMP_higher`,expected,WORD);
   
    if WORD = `<=>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_typed(`<=>`,POP_0,Term_1,`bool`,`bool`,`bool`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `IMP_higher` prev lst `nil`)
    else
         fail
  ?
    (let (IFF_higher_0 , result_list , prev, lst) = IFF_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push IFF_higher_0 result_list in
     do_return result_list whitespace `IMP_higher` prev lst `nil`);;

IFF_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`IFF_higher`,expected,WORD);
   
    if WORD = `=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`=`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `IFF_higher` prev lst `nil`)
    else
         fail
  ?
    (let (EQ_higher_0 , result_list , prev, lst) = EQ_higher lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push EQ_higher_0 result_list in
     do_return result_list whitespace `IFF_higher` prev lst `nil`);;

EQ_higher:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`EQ_higher`,expected,WORD);
   
    if WORD = `o` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`o`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `EQ_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `Sum` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`Sum`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `EQ_higher` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IS_ASSUMPTION_OF` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (Term_1 , result_list , prev, lst) =  Term  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_binop_untyped(`IS_ASSUMPTION_OF`,POP_0,Term_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `EQ_higher` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `EQ_higher` WORD lst expected);;

