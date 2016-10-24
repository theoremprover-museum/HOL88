USEFUL := [(`'`,`'`)];;

IGNORE := [(`"`,`"`)];;

letref MAIN_LOOP
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:void list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:void,fail:void list,fail:string,fail:string list);;

letref foo
   (lst:string list) (whitespace:string)(prev:string)
   (result_list:void list)
   (FIRST_CHARS:string list) (CHARS:string list) (expected:string) =
   (fail:void,fail:void list,fail:string,fail:string list);;

