
%
Tokens
%

% Logical expressions (for use with assert and invariant) %
logical_1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`logical_1`,expected,WORD);
   
    if WORD = `/\\` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (logical_expr_1 , result_list , prev, lst) =  logical_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_conj(POP_0,logical_expr_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `logical_1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `\\/` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (logical_expr_1 , result_list , prev, lst) =  logical_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_disj(POP_0,logical_expr_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `logical_1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `==>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (logical_expr_1 , result_list , prev, lst) =  logical_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_imp(POP_0,logical_expr_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `logical_1` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `logical_1` WORD lst expected);;

logical_expr:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`logical_expr`,expected,WORD);
   
    if WORD = `(` then
        (let (logical_expr_0 , result_list , prev, lst) = logical_expr lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push logical_expr_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `logical_expr` in
         let TOKENS = explode WORD in
         let (logical_1_1 , result_list , prev, lst) = logical_1 lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push logical_1_1 result_list in
         do_return result_list whitespace `logical_expr` prev lst `nil`)
    else
         fail
  ?
    (let (bool_expr_0 , result_list , prev, lst) = bool_expr lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push bool_expr_0 result_list in
     let (logical_1_1 , result_list , prev, lst) = logical_1 lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push logical_1_1 result_list in
     do_return result_list whitespace `logical_expr` prev lst `nil`);;


%
Expressions:
%
possible_paren:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`possible_paren`,expected,WORD);
   
    if WORD = `(` then
        (let (expression_0 , result_list , prev, lst) = expression lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push expression_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `possible_paren` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `possible_paren` WORD lst expected)
    else
         fail
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = mk_variable(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `possible_paren` whitespace lst `nil`);;

rest_of_expression:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_expression`,expected,WORD);
   
    if WORD = `+` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (possible_paren_1 , result_list , prev, lst) =  possible_paren  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_plus(POP_0,possible_paren_1) in
         let result_list = push tmp_2 result_list in
         let (rest_of_expression_2 , result_list , prev, lst) = rest_of_expression lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_expression_2 result_list in
         do_return result_list whitespace `rest_of_expression` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (possible_paren_1 , result_list , prev, lst) =  possible_paren  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_minus(POP_0,possible_paren_1) in
         let result_list = push tmp_2 result_list in
         let (rest_of_expression_2 , result_list , prev, lst) = rest_of_expression lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_expression_2 result_list in
         do_return result_list whitespace `rest_of_expression` prev lst `nil`)
    else
         fail
  ?
    if WORD = `*` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (possible_paren_1 , result_list , prev, lst) =  possible_paren  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_2 = mk_mult(POP_0,possible_paren_1) in
         let result_list = push tmp_2 result_list in
         let (rest_of_expression_2 , result_list , prev, lst) = rest_of_expression lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_expression_2 result_list in
         do_return result_list whitespace `rest_of_expression` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `rest_of_expression` WORD lst expected);;

expression:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`expression`,expected,WORD);
   
    if WORD = `(` then
        (let (expression_0 , result_list , prev, lst) = expression lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push expression_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `expression` in
         let TOKENS = explode WORD in
         let (rest_of_expression_1 , result_list , prev, lst) = rest_of_expression lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_expression_1 result_list in
         do_return result_list whitespace `expression` prev lst `nil`)
    else
         fail
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
     let tmp_1 = mk_variable(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     let (rest_of_expression_1 , result_list , prev, lst) = rest_of_expression lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
     let result_list = push rest_of_expression_1 result_list in
     do_return result_list whitespace `expression` prev lst `nil`);;

rest_of_bool:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_bool`,expected,WORD);
   
    if WORD = `=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (bool_1_1 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_eq(POP_0,bool_1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_bool` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (bool_1_1 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_gt(POP_0,bool_1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_bool` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (bool_1_1 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_lt(POP_0,bool_1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_bool` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (bool_1_1 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_lte(POP_0,bool_1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_bool` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (bool_1_1 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_gte(POP_0,bool_1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_bool` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (bool_1_1 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_neq(POP_0,bool_1_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_bool` prev lst `nil`)
    else
         fail
  ? fail;;

bool_1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`bool_1`,expected,WORD);
   
    if WORD = `~` then
        (let (bool_1_0 , result_list , prev, lst) =  bool_1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = mk_neg(bool_1_0) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `bool_1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (bool_1_0 , result_list , prev, lst) = bool_1 lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push bool_1_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `bool_1` in
         let TOKENS = explode WORD in
         let (poss_rest_of_bool_1 , result_list , prev, lst) = poss_rest_of_bool lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push poss_rest_of_bool_1 result_list in
         do_return result_list whitespace `bool_1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `T` then
        (let tmp_0 = mk_const(`T`,":bool") in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `bool_1` whitespace lst expected)
    else
         fail
  ?
    if WORD = `F` then
        (let tmp_0 = mk_const(`F`,":bool") in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `bool_1` whitespace lst expected)
    else
         fail
  ?
    (let (expression_0 , result_list , prev, lst) = expression lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push expression_0 result_list in
     let (poss_rest_of_bool_1 , result_list , prev, lst) = poss_rest_of_bool lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_rest_of_bool_1 result_list in
     do_return result_list whitespace `bool_1` prev lst `nil`);;

poss_rest_of_bool:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_rest_of_bool`,expected,WORD);
   
    (let (rest_of_bool_0 , result_list , prev, lst) = rest_of_bool lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push rest_of_bool_0 result_list in
     do_return result_list whitespace `poss_rest_of_bool` prev lst `nil`)
  ?
    (do_return result_list whitespace `poss_rest_of_bool` WORD lst expected);;

bool_expr:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`bool_expr`,expected,WORD);
   
    if WORD = `~` then
        (let (bool_expr_0 , result_list , prev, lst) =  bool_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = mk_neg(bool_expr_0) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `bool_expr` prev lst `nil`)
    else
         fail
  ?
    if WORD = `(` then
        (let (bool_expr_0 , result_list , prev, lst) = bool_expr lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push bool_expr_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `bool_expr` in
         let TOKENS = explode WORD in
         let (poss_rest_of_bool_1 , result_list , prev, lst) = poss_rest_of_bool lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push poss_rest_of_bool_1 result_list in
         do_return result_list whitespace `bool_expr` prev lst `nil`)
    else
         fail
  ?
    if WORD = `T` then
        (let tmp_0 = mk_const(`T`,":bool") in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `bool_expr` whitespace lst expected)
    else
         fail
  ?
    if WORD = `F` then
        (let tmp_0 = mk_const(`F`,":bool") in
         let result_list = push tmp_0 result_list in
         do_return result_list whitespace `bool_expr` whitespace lst expected)
    else
         fail
  ?
    (let (expression_0 , result_list , prev, lst) = expression lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push expression_0 result_list in
     let (rest_of_bool_1 , result_list , prev, lst) = rest_of_bool lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push rest_of_bool_1 result_list in
     do_return result_list whitespace `bool_expr` prev lst `nil`);;


%
Assignment Statement:
%
assignment_stmnt:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`assignment_stmnt`,expected,WORD);
   
    if WORD = `:=` then
        (let (expression_0 , result_list , prev, lst) =  expression  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = mk_semantic(expression_0) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = mk_assign(POP_1,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `assignment_stmnt` prev lst `nil`)
    else
         fail
  ? fail;;


%
If Statement:
%
more_if_stmnts:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_if_stmnts`,expected,WORD);
   
    if WORD = `else` then
        (let (a_stmnt_0 , result_list , prev, lst) = a_stmnt lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push a_stmnt_0 result_list in
         let (more_stmnts_1 , result_list , prev, lst) = more_stmnts lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_stmnts_1 result_list in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let tmp_5 = mk_if2(POP_2,POP_3,POP_4) in
         let result_list = push tmp_5 result_list in
         do_return result_list whitespace `more_if_stmnts` prev lst `nil`)
    else
         fail
  ?
    (let (result_list,pop_list) = chop_off 2 [] result_list in
     let (POP_0 , pop_list ) = (pop pop_list) in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = mk_if1(POP_0,POP_1) in
     let result_list = push tmp_2 result_list in
     do_return result_list whitespace `more_if_stmnts` WORD lst expected);;

rest_of_if:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_if`,expected,WORD);
   
    if WORD = `then` then
        (let (many_stmnts_0 , result_list , prev, lst) = many_stmnts lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push many_stmnts_0 result_list in
         let (more_if_stmnts_1 , result_list , prev, lst) = more_if_stmnts lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_if_stmnts_1 result_list in
         do_return result_list whitespace `rest_of_if` prev lst `nil`)
    else
         fail
  ? fail;;


%
While Statement:
%
rest_of_while:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`rest_of_while`,expected,WORD);
   
    if WORD = `do` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (many_stmnts_1 , result_list , prev, lst) =  many_stmnts  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = mk_while(POP_0,many_stmnts_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `rest_of_while` prev lst `nil`)
    else
         fail
  ? fail;;


%
General Statements:
%
MAIN_LOOP:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`MAIN_LOOP`,expected,WORD);
   
    if WORD = `{` then
        (let (logical_expr_0 , result_list , prev, lst) =  logical_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `\}` in
         let tmp_1 = mk_semantic(logical_expr_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         let (is_spec_1 , result_list , prev, lst) = is_spec lst whitespace WORD result_list FIRST_CHARS CHARS expected in
         let result_list = push is_spec_1 result_list in
         do_return result_list whitespace `MAIN_LOOP` prev lst `nil`)
    else
         fail
  ?
    if WORD = `[` then
        (let (logical_expr_0 , result_list , prev, lst) =  logical_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `\]` in
         let tmp_1 = mk_semantic(logical_expr_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         let (many_stmnts_1 , result_list , prev, lst) = many_stmnts lst whitespace WORD result_list FIRST_CHARS CHARS `\[` in
         let result_list = push many_stmnts_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\[` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         let (logical_expr_2 , result_list , prev, lst) =  logical_expr  lst whitespace  WORD  result_list FIRST_CHARS CHARS `\]` in
         let tmp_3 = mk_semantic(logical_expr_2) in
         let result_list = push tmp_3 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\]` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = mk_t_spec(POP_3,POP_4,POP_5) in
         let result_list = push tmp_6 result_list in
         let (WORD,lst) = eat_terminal `nil` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `MAIN_LOOP` WORD lst expected)
    else
         fail
  ?
    if WORD = `(` then
        (let (many_expr_logical_0 , result_list , prev, lst) = many_expr_logical lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push many_expr_logical_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         let (WORD,lst) = eat_terminal `nil` WORD lst `MAIN_LOOP` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `MAIN_LOOP` WORD lst expected)
    else
         fail
  ?
    (let (many_expr_logical_0 , result_list , prev, lst) = many_expr_logical lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push many_expr_logical_0 result_list in
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

is_spec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`is_spec`,expected,WORD);
   
    if WORD = `nil` then
        (do_return result_list whitespace `is_spec` `nil` lst expected)
    else
         fail
  ?
    (let (many_stmnts_0 , result_list , prev, lst) = many_stmnts lst whitespace WORD result_list FIRST_CHARS CHARS `\{` in
     let result_list = push many_stmnts_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `\{` WORD lst `is_spec` in
     let TOKENS = explode WORD in
     let (logical_expr_1 , result_list , prev, lst) =  logical_expr  lst whitespace  WORD  result_list FIRST_CHARS CHARS `\}` in
     let tmp_2 = mk_semantic(logical_expr_1) in
     let result_list = push tmp_2 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `\}` WORD lst `is_spec` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 3 [] result_list in
     let (POP_2 , pop_list ) = (pop pop_list) in
     let (POP_3 , pop_list ) = (pop pop_list) in
     let (POP_4 , pop_list ) = (pop pop_list) in
     let tmp_5 = mk_spec(POP_2,POP_3,POP_4) in
     let result_list = push tmp_5 result_list in
     let (WORD,lst) = eat_terminal `nil` WORD lst `is_spec` in
     let TOKENS = explode WORD in
     do_return result_list whitespace `is_spec` WORD lst expected);;

many_expr_logical:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`many_expr_logical`,expected,WORD);
   
    (let (many_stmnts_0 , result_list , prev, lst) = many_stmnts lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push many_stmnts_0 result_list in
     do_return result_list whitespace `many_expr_logical` prev lst `nil`)
  ?
    (let (expression_0 , result_list , prev, lst) = expression lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push expression_0 result_list in
     do_return result_list whitespace `many_expr_logical` prev lst `nil`)
  ?
    (let (bool_expr_0 , result_list , prev, lst) = bool_expr lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push bool_expr_0 result_list in
     do_return result_list whitespace `many_expr_logical` prev lst `nil`)
  ?
    (let (logical_expr_0 , result_list , prev, lst) = logical_expr lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push logical_expr_0 result_list in
     do_return result_list whitespace `many_expr_logical` prev lst `nil`);;

more_stmnts:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`more_stmnts`,expected,WORD);
   
    if WORD = `;` then
        (let (a_stmnt_0 , result_list , prev, lst) = a_stmnt lst whitespace whitespace result_list FIRST_CHARS CHARS `nil` in
         let result_list = push a_stmnt_0 result_list in
         let (more_stmnts_1 , result_list , prev, lst) = more_stmnts lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push more_stmnts_1 result_list in
         let (result_list,pop_list) = chop_off 2 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let tmp_4 = mk_seq(POP_2,POP_3) in
         let result_list = push tmp_4 result_list in
         do_return result_list whitespace `more_stmnts` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `more_stmnts` WORD lst expected);;

many_stmnts:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`many_stmnts`,expected,WORD);
   
    (let (a_stmnt_0 , result_list , prev, lst) = a_stmnt lst whitespace WORD result_list FIRST_CHARS CHARS `nil` in
     let result_list = push a_stmnt_0 result_list in
     let (more_stmnts_1 , result_list , prev, lst) = more_stmnts lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push more_stmnts_1 result_list in
     do_return result_list whitespace `many_stmnts` prev lst `nil`);;

meta_logical_stmnt:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`meta_logical_stmnt`,expected,WORD);
   
    if WORD = `assert` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\{` WORD lst `meta_logical_stmnt` in
         let TOKENS = explode WORD in
         let (logical_expr_0 , result_list , prev, lst) =  logical_expr  lst whitespace  WORD  result_list FIRST_CHARS CHARS `\}` in
         let tmp_1 = mk_semantic(logical_expr_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `meta_logical_stmnt` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = mk_assert(POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `meta_logical_stmnt` WORD lst expected)
    else
         fail
  ?
    if WORD = `invariant` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\{` WORD lst `meta_logical_stmnt` in
         let TOKENS = explode WORD in
         let (logical_expr_0 , result_list , prev, lst) =  logical_expr  lst whitespace  WORD  result_list FIRST_CHARS CHARS `\}` in
         let tmp_1 = mk_semantic(logical_expr_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `\}` WORD lst `meta_logical_stmnt` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = mk_invariant(POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `meta_logical_stmnt` WORD lst expected)
    else
         fail
  ?
    if WORD = `variant` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\{` WORD lst `meta_logical_stmnt` in
         let TOKENS = explode WORD in
         let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `\}` in
         let tmp_1 = mk_variable(TOKEN_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `\}` WORD lst `meta_logical_stmnt` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = mk_semantic(POP_1) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = mk_variant(POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `meta_logical_stmnt` WORD lst expected)
    else
         fail
  ? fail;;

a_stmnt:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`a_stmnt`,expected,WORD);
   
    if WORD = `(` then
        (let (many_stmnts_0 , result_list , prev, lst) = many_stmnts lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push many_stmnts_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `a_stmnt` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `a_stmnt` WORD lst expected)
    else
         fail
  ?
    if WORD = `if` then
        (let (bool_expr_0 , result_list , prev, lst) =  bool_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = mk_semantic(bool_expr_0) in
         let result_list = push tmp_1 result_list in
         let (rest_of_if_1 , result_list , prev, lst) = rest_of_if lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_if_1 result_list in
         do_return result_list whitespace `a_stmnt` prev lst `nil`)
    else
         fail
  ?
    if WORD = `while` then
        (let (bool_expr_0 , result_list , prev, lst) =  bool_expr  lst whitespace  whitespace  result_list FIRST_CHARS CHARS `nil` in
         let tmp_1 = mk_semantic(bool_expr_0) in
         let result_list = push tmp_1 result_list in
         let (rest_of_while_1 , result_list , prev, lst) = rest_of_while lst whitespace prev result_list FIRST_CHARS CHARS expected in
         let result_list = push rest_of_while_1 result_list in
         do_return result_list whitespace `a_stmnt` prev lst `nil`)
    else
         fail
  ?
    (let (meta_logical_stmnt_0 , result_list , prev, lst) = meta_logical_stmnt lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push meta_logical_stmnt_0 result_list in
     do_return result_list whitespace `a_stmnt` prev lst `nil`)
  ?
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) `nil` in
     let tmp_1 = mk_variable_name(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     let (assignment_stmnt_1 , result_list , prev, lst) = assignment_stmnt lst whitespace whitespace result_list FIRST_CHARS CHARS expected in
     let result_list = push assignment_stmnt_1 result_list in
     do_return result_list whitespace `a_stmnt` prev lst `nil`);;

