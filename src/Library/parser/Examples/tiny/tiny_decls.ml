FIRST_CHARS := words `a b c d e f g h i j k l m n o p q r s t u v w x y z               A B C D E F G H I J K L M N O P Q R S T U V W X Y Z               1 2 3 4 5 6 7 8 9 0`;;

CHARS := words `a b c d e f g h i j k l m n o p q r s t u v w x y z         A B C D E F G H I J K L M N O P Q R S T U V W X Y Z         1 2 3 4 5 6 7 8 9 0 _`;;

letref logical_1
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref logical_expr
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref possible_paren
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref rest_of_expression
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref expression
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref rest_of_bool
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref bool_1
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref poss_rest_of_bool
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref bool_expr
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref assignment_stmnt
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref more_if_stmnts
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref rest_of_if
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref rest_of_while
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref MAIN_LOOP
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref is_spec
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref many_expr_logical
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref more_stmnts
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref many_stmnts
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref meta_logical_stmnt
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:term list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:term,fail:term list,fail:string,fail:string list);;

letref a_stmnt
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

