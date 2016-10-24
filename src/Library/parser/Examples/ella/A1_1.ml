
% A1.1 BASICS %
integer:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`integer`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = MK_digit(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `integer` whitespace lst `nil`);;

char:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`char`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = MK_char(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `char` whitespace lst `nil`);;

name:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`name`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = MK_name(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `name` whitespace lst `nil`);;

fnname:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`fnname`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = MK_fnname(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `fnname` whitespace lst `nil`);;

typename:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`typename`,expected,WORD);
   
    (let TOKEN_0 = TOKEN TOKENS FIRST_CHARS CHARS (hd lst) expected in
     let tmp_1 = MK_typename(TOKEN_0) in
     let result_list = push tmp_1 result_list in
     do_return result_list whitespace `typename` whitespace lst `nil`);;

macname:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`macname`,expected,WORD);
   
    (let (fnname_0 , result_list , prev, lst) = fnname lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push fnname_0 result_list in
     do_return result_list whitespace `macname` prev lst `nil`);;

biopname:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`biopname`,expected,WORD);
   
    (let (fnname_0 , result_list , prev, lst) = fnname lst whitespace WORD result_list FIRST_CHARS CHARS expected in
     let result_list = push fnname_0 result_list in
     do_return result_list whitespace `biopname` prev lst `nil`);;

string:=
   \lst whitespace prev result_list FIRST_CHARS CHARS expected.
    let (WORD,lst) = gnt lst whitespace prev in
    let TOKENS = explode WORD in
    debug_enter(`string`,expected,WORD);
   
    if WORD = `"` then
        (let (WORD,lst) = gnt lst whitespace whitespace in
         let TOKENS = explode WORD in
         let WORD_0 = WORD in
         let tmp_1 = MK_string(WORD_0) in
         let result_list = push tmp_1 result_list in
         let (WORD,lst) = gnt lst whitespace whitespace in
         let (WORD,lst) = eat_terminal `"` WORD lst `string` in
         let TOKENS = explode WORD in
         do_return result_list whitespace `string` WORD lst expected)
    else
         fail
  ? fail;;

