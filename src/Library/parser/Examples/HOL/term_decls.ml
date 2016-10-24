FIRST_CHARS := words `a b c d e f g h i j k l m n o p q r s t u v w x y z               A B C D E F G H I J K L M N O P Q R S T U V W X Y Z               1 2 3 4 5 6 7 8 9 0 *`;;

CHARS := words `a b c d e f g h i j k l m n o p q r s t u v w x y z         A B C D E F G H I J K L M N O P Q R S T U V W X Y Z         1 2 3 4 5 6 7 8 9 0 ' *`;;

USEFUL := [(`\``,`\``)];;

letref MAIN_LOOP
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref Term
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref Abstraction
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref Term1
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref Term_list
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref rest_of_list
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref Var_or_const
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref is_typed
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_Term
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_arbit
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_EXP
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref EXP_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_D_M
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref D_M_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_MLT
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref MLT_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_P_M
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref P_M_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_BOOL
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref BOOL_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_CONJ
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref CONJ_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_DISJ
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref DISJ_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_IMP
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref IMP_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_IFF
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref IFF_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref more_EQ
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref EQ_lower
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref arbit_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref EXP_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref D_M_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref MLT_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref P_M_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref BOOL_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref CONJ_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref DISJ_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref IMP_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref IFF_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

letref EQ_higher
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:preterm list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:preterm,fail:preterm list,fail:string,fail:string list);;

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

