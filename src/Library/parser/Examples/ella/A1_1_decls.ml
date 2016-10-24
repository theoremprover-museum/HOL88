FIRST_CHARS := words `a b c d e f g h i j k l m n o p q r s t u v w x y z               A B C D E F G H I J K L M N O P Q R S T U V W X Y Z               1 2 3 4 5 6 7 8 9 0`;;

CHARS := words `a b c d e f g h i j k l m n o p q r s t u v w x y z         A B C D E F G H I J K L M N O P Q R S T U V W X Y Z         1 2 3 4 5 6 7 8 9 0 _`;;

USEFUL := [(`"`,`"`)];;

IGNORE := [(`#`,`\L`)];;

letref integer
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref char
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref name
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref fnname
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref typename
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref macname
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref biopname
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

letref string
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:ella list list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:ella list,fail:ella list list,fail:string,fail:string list);;

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

