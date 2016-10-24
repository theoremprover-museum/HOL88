
%-------------------------------------------------------------------------%

% A1.5 INTEGERS                                                           %

%                                                                         %

% NOTE: The formula1 production has been optimised away.                  %

%-------------------------------------------------------------------------%
intdec:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`intdec`,expected,WORD);
   
    (let (name_0 , result_list , prev, lst) = name lst whitespace WORD result_list FIRST_CHARS CHARS `=` in
     let result_list = push name_0 result_list in
     let (WORD,lst) = gnt lst whitespace prev in
     let (WORD,lst) = eat_terminal `=` WORD lst `intdec` in
     let TOKENS = explode WORD in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let (int_2 , result_list , prev, lst) =  int  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_3 = MK_two(`intdec`,POP_1,int_2) in
     let result_list = push tmp_3 result_list in
     do_return result_list whitespace `intdec` prev lst `nil`);;

int:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`int`,expected,WORD);
   
    (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`int`,formula_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `int` prev lst `nil`);;

formula:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`formula`,expected,WORD);
   
    if WORD = `+` then
        (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula_0,`+`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula_0,`-`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula` prev lst `nil`)
    else
         fail
  ?
    if WORD = `INOT` then
        (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula_0,`INOT`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula` prev lst `nil`)
    else
         fail
  ?
    if WORD = `ABS` then
        (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula_0,`ABS`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula` prev lst `nil`)
    else
         fail
  ?
    if WORD = `SQRT` then
        (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula_0,`SQRT`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula` prev lst `nil`)
    else
         fail
  ?
    if WORD = `NOT` then
        (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula_0,`NOT`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula` prev lst `nil`)
    else
         fail
  ?
    (let (formula2_0 , result_list , prev, lst) =  formula2  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_1 = MK_one(`formula1`,formula2_0) in
     let result_list = push tmp_1 result_list in
     let (result_list,pop_list) = chop_off 1 [] result_list in
     let (POP_1 , pop_list ) = (pop pop_list) in
     let tmp_2 = MK_one(`formula`,POP_1) in
     let result_list = push tmp_2 result_list in
     let (poss_ibinop_2 , result_list , prev, lst) = poss_ibinop lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_ibinop_2 result_list in
     do_return result_list whitespace `formula` prev lst `nil`);;

formula1:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`formula1`,expected,WORD);
   
    if WORD = `+` then
        (let (formula1_0 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula1_0,`+`) in
         let result_list = push tmp_1 result_list in
         do_return result_list whitespace `formula1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (formula1_0 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula1_0,`-`) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`formula`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `formula1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `INOT` then
        (let (formula1_0 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula1_0,`INOT`) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`formula`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `formula1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `ABS` then
        (let (formula1_0 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula1_0,`ABS`) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`formula`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `formula1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `SQRT` then
        (let (formula1_0 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula1_0,`SQRT`) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`formula`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `formula1` prev lst `nil`)
    else
         fail
  ?
    if WORD = `NOT` then
        (let (formula1_0 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_1 = MK_unary(formula1_0,`NOT`) in
         let result_list = push tmp_1 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`formula`,POP_1) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `formula1` prev lst `nil`)
    else
         fail
  ?
    (let (formula2_0 , result_list , prev, lst) =  formula2  lst whitespace  WORD  result_list FIRST_CHARS CHARS `nil` in
     let tmp_1 = MK_one(`formula1`,formula2_0) in
     let result_list = push tmp_1 result_list in
     let (poss_ibinop_1 , result_list , prev, lst) = poss_ibinop lst whitespace prev result_list FIRST_CHARS CHARS expected in
     let result_list = push poss_ibinop_1 result_list in
     do_return result_list whitespace `formula1` prev lst `nil`);;

poss_ibinop:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`poss_ibinop`,expected,WORD);
   
    if WORD = `+` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`+`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `-` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`-`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IDIV` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`IDIV`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `%` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`%`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `*` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`*`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `MOD` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`MOD`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `SL` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`SL`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `SR` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`SR`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IAND` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`IAND`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `IOR` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`IOR`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`=`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `/=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`/=`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`>`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`<`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `>=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`>=`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `<=` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`<=`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `AND` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`AND`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    if WORD = `OR` then
        (let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_0 , pop_list ) = (pop pop_list) in
         let (formula1_1 , result_list , prev, lst) =  formula1  lst whitespace  whitespace  result_list FIRST_CHARS CHARS expected in
         let tmp_2 = MK_binary(POP_0,formula1_1,`OR`) in
         let result_list = push tmp_2 result_list in
         do_return result_list whitespace `poss_ibinop` prev lst `nil`)
    else
         fail
  ?
    (do_return result_list whitespace `poss_ibinop` WORD lst expected);;

formula2:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`formula2`,expected,WORD);
   
    if WORD = `IF` then
        (let (boolean_0 , result_list , prev, lst) = boolean lst whitespace whitespace result_list FIRST_CHARS CHARS `THEN` in
         let result_list = push boolean_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `THEN` WORD lst `formula2` in
         let TOKENS = explode WORD in
         let (int_1 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `ELSE` in
         let result_list = push int_1 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `ELSE` WORD lst `formula2` in
         let TOKENS = explode WORD in
         let (int_2 , result_list , prev, lst) = int lst whitespace WORD result_list FIRST_CHARS CHARS `FI` in
         let result_list = push int_2 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `FI` WORD lst `formula2` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 3 [] result_list in
         let (POP_3 , pop_list ) = (pop pop_list) in
         let (POP_4 , pop_list ) = (pop pop_list) in
         let (POP_5 , pop_list ) = (pop pop_list) in
         let tmp_6 = MK_three(`formula2_cond`,POP_3,POP_4,POP_5) in
         let result_list = push tmp_6 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_6 , pop_list ) = (pop pop_list) in
         let tmp_7 = MK_one(`formula2`,POP_6) in
         let result_list = push tmp_7 result_list in
         do_return result_list whitespace `formula2` WORD lst expected)
    else
         fail
  ?
    if WORD = `(` then
        (let (int_0 , result_list , prev, lst) = int lst whitespace whitespace result_list FIRST_CHARS CHARS `)` in
         let result_list = push int_0 result_list in
         let (WORD,lst) = gnt lst whitespace prev in
         let (WORD,lst) = eat_terminal `)` WORD lst `formula2` in
         let TOKENS = explode WORD in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_1 , pop_list ) = (pop pop_list) in
         let tmp_2 = MK_one(`formula2_int`,POP_1) in
         let result_list = push tmp_2 result_list in
         let (result_list,pop_list) = chop_off 1 [] result_list in
         let (POP_2 , pop_list ) = (pop pop_list) in
         let tmp_3 = MK_one(`formula2`,POP_2) in
         let result_list = push tmp_3 result_list in
         do_return result_list whitespace `formula2` WORD lst expected)
    else
         fail
  ?
    (let (name_0 , result_list , prev, lst) =  name  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`formula2`,name_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `formula2` prev lst `nil`)
  ?
    (let (integer_0 , result_list , prev, lst) =  integer  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`formula2`,integer_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `formula2` prev lst `nil`);;

boolean:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`boolean`,expected,WORD);
   
    (let (formula_0 , result_list , prev, lst) =  formula  lst whitespace  WORD  result_list FIRST_CHARS CHARS expected in
     let tmp_1 = MK_one(`boolean`,formula_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `boolean` prev lst `nil`);;

