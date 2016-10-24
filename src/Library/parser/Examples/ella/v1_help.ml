let lower thing flag = if thing = `_` then true
                       else if ascii_code thing > 96 then
                          if ascii_code thing < 123 then true
                          else false
                       else if not flag then 
                          if mem thing (words `1 2 3 4 5 6 7 8 9 0`) then true
                          else false
                       else false;;

let upper thing flag = if thing = `_` then true
                       else if ascii_code thing > 64 then
                          if ascii_code thing < 91 then true
                          else false
                       else if not flag then 
                          if mem thing (words `1 2 3 4 5 6 7 8 9 0`) then true
                          else false
                       else false;;

letrec is_lower lst flag = if null lst then true 
                           else if lower (hd lst) flag then 
                              is_lower (tl lst) false
                           else false;;

letrec is_upper lst flag = if null lst then true
                           else if upper (hd lst) flag then 
                              is_upper (tl lst) false
                           else false;;

let reserved thing =
    mem thing [`ARITH`;`BEGIN`;`BIOP`;`CASE`;`COM`;`CONC`;`CONST`;`DELAY`;
               `ELSE`;`ELSEOF`;`END`;`ESAC`;`FAULT`;`FI`;`FINISH`;`FN`;
               `FNSET`;`FOR`;`IDELAY`;`IF`;`IMPORT`;`IMPORTS`;`INIT`;
               `INT`;`IO`;`JOIN`;`LET`;`MAC`;`MAKE`;`MOC`;`MODULE`;
               `NEW`;`OF`;`OUTPUT`;`PRINT`;`PVAR`;`RAM`;`REFORM`;`RENAMED`;
               `SEQ`;`STATE`;`STRING`;`THEN`;`TYPE`;`VAR`];;

let add_to_list (lst,thing) = (append lst thing):ella list;;

let MK_zero node = [Print_node (node,[])];;

let MK_one (node,a) = [Print_node (node,a)];;

let MK_two (node,a,b) = [Print_node (node,(hd a).b)];;

let MK_three (node,a,b,c) = [Print_node (node,(hd a).(hd b).c)];;

let MK_four (node,a,b,c,d) = [Print_node (node,(hd a).(hd b).(hd c).d)];;

let MK_five (node,a,b,c,d,e) = 
    [Print_node (node,(hd a).(hd b).(hd c).(hd d).e)];;

let MK_string thing = MK_one(`string`,(MK_zero thing));;

let MK_fnname thing = if is_upper (explode thing) true then 
                         if not (reserved thing) then 
                            MK_one(`fnname`,(MK_one (`uppercasename`,
                                                     MK_zero thing)))
                         else failwith `FNNAME`
                      else failwith `FNNAME`;;

let MK_typename thing = if is_lower (explode thing) true then 
                           MK_one(`name`,MK_zero thing)
                        else failwith `TYPENAME`;;

let MK_digit thing = if can int_of_string thing then 
                        MK_one(`integervalue`,MK_zero thing)
                     else failwith `DIGIT`;;

let MK_char thing = if length (explode thing) = 1 then
                       MK_one(`name`,MK_zero thing)
                    else failwith `CHAR`;;

let MK_name thing = if is_lower (explode thing) true then
                       MK_one(`name`,MK_zero thing)
                    else failwith `NAME`;;


let MK_text thing = [Print_node (`text`,thing)];;



% A1.5 Integers %

let MK_op thing = Print_node (`operator`,(MK_zero thing));;

let MK_unary(expr,op) = MK_one (`formula1`, (MK_op op) . expr);;

let MK_binary(lhs,rhs,op) = MK_one (`formula`,(hd lhs).(MK_op op).rhs);;

