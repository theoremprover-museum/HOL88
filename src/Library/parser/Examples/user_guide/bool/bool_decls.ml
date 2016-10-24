FIRST_CHARS := words `a b`;;

CHARS := words `a b c d`;;

letref term
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref eof
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref conj
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref disj
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref neg
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref imp
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref MAIN_LOOP
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letrec TOKEN_1 TOKENS CHARS =
   if null TOKENS then ()
   else if mem (hd TOKENS) CHARS then
      TOKEN_1 (tl TOKENS) CHARS
   else
      fail;;

let TOKEN TOKENS FIRST_CHARS CHARS next expected =
   if mem (hd TOKENS) FIRST_CHARS then
      (TOKEN_1 (tl TOKENS) CHARS;
       let wrd = implode TOKENS in
         if expected = `nil` then
             wrd
         else if expected = next then
             wrd
         else fail)
   else
      fail
   ? fail;;

