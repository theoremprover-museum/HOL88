% group.ml. Some examples from the original paper by 
  Knuth and Bendix. The standard group theory example
  is test1.
%
new_theory `group`;;

let ftype = ":*";;
curry new_infix    `op`   ":^ftype -> ^ftype -> ^ftype" ;;
curry new_constant `inv`  ":^ftype -> ^ftype";;
curry new_constant `flip` ":^ftype -> ^ftype";;
curry new_constant `un`   ":^ftype -> ^ftype";;
curry new_constant `two`  ":^ftype -> ^ftype";;
curry new_constant `i`    ftype;;
curry new_constant `Id`   ftype;;


let op = curry mk_const `op` ":^ftype -> ^ftype -> ^ftype" ;;
let inv = curry mk_const `inv` ":^ftype -> ^ftype";;
let flip = curry mk_const `flip` ":^ftype -> ^ftype";;
let un = curry mk_const `un` ":^ftype -> ^ftype";;
let two = curry mk_const `two` ":^ftype -> ^ftype";;
let i = curry mk_const `i` ":^ftype";;
let Id = curry mk_const `Id` ftype;;

let e1 = curry new_axiom `e1` "($= : ^ftype -> ^ftype -> bool) (i op x) x";;
let e2 = curry new_axiom `e2` "($= : ^ftype -> ^ftype -> bool) ((inv x) op x) i";;
let e3 = curry new_axiom `e3` "($= : ^ftype -> ^ftype -> bool) ((x op y) op z) (x op (y op z))";;
let e4 = curry new_axiom `e4` "($= : ^ftype -> ^ftype -> bool) (x op i) x";;
let e5 = curry new_axiom `e5` "($= : ^ftype -> ^ftype -> bool) (x op (inv x)) i";;
let e6 = curry new_axiom `e6` "($= : ^ftype -> ^ftype -> bool) ((inv x) op (x op y)) y";;
let e7 = curry new_axiom `e7` "($= : ^ftype -> ^ftype -> bool) (Id op x) x";;
let e8 = curry new_axiom `e8` "($= : ^ftype -> ^ftype -> bool) ((flip x) op x) Id";;
let e9 = curry new_axiom `e9` "($= : ^ftype -> ^ftype -> bool) ((x op y) op (y op z)) y";;
let e10 = curry new_axiom `e10` "($= : ^ftype -> ^ftype -> bool) ((x op x) op x) (un x)";;
let e11 = curry new_axiom `e11` "($= : ^ftype -> ^ftype -> bool) (x op (x op x)) (two x)";;
let e12 = curry new_axiom `e12` "($= : ^ftype -> ^ftype -> bool) ((two x) op y) (x op y)";;

close_theory();;

% Orderings %
let status tm = (tm = op);;

% inv > op > i %
let inv_op_i x y = 
   if (x = y)
   then false 
   else (x = inv) or
        ((x = op) & (y = i));;


% flip > inv > op > Id > i %
let flip_inv_op_Id_i x y =
   if (x = y)
   then false
   else ((x = op) & ((y = i) or (y = Id)))
        or
        ((x = Id) & (y = i))
        or
        (x = flip) 
        or
        ((x = inv) & (not (y = flip)));;


% Ordering for example sixteen and seventeen
 op > un & op > two
%
let o16 x y =
   if (x = y)
   then false 
   else ((x = op) & ((y = un) or (y = two)));;


% Example 1 %
let ex1 = [e1;e2;e3];;

% Example 3 %
let ex3 = [e4;e5;e3];;

% Example 4 %
let ex4 = [e6];;

% Example 5  tests generation of critical pairs %
let ex5a = [ e3; e1; e7; e2; e8 ];;

% Example 5  %
let ex5b = [e1;e7;e2;e8;e3];;

% Example 6, central groupoids 1 %
let ex6 = [e9];;

% Example 12, (l,r) systems %
let ex12 = [ e1;e5;e3];;

% Example 16, central groupoids 2 %
let ex16 = [ e9; e10; e11; e12 ];;

% Example 17, central groupoids 3 %
let ex17 = [ e9; e10; e11 ];;

let (test1, test3, test4, test5a, test5b, test6, test12, test16, test17) =
   let test order eset () = 
      (print_string `Equations:`;
       print_newline();
       show_list (\th. print_thm th; print_newline()) eset; 
       print_newline();
       print_string `Rules:`;
       print_newline();
       show_list (\th. print_thm th; print_newline())
                 (kb (rpos status order) eset); ())
   in
   (test inv_op_i ex1,
    test inv_op_i ex3,
    test inv_op_i ex4,
    test flip_inv_op_Id_i ex5a,
    test flip_inv_op_Id_i ex5b,
    test inv_op_i ex6,
    test inv_op_i ex12,
    test o16 ex16,
    test o16 ex17);;

% These (old) timings are from the conversion-based rewriting
  implementation. When you run kb now, there should be speedup 
  corresponding to the table at the top of rewrite.ml
##
  timer true;;
  test1();;
  test3();;
  test4();;
  test5a();;
  test5b();;
  test6();;
  test12();;
  test16();;
  test17();;

false : bool
Run time: 0.0s

#Equations:

|- !x. i op x = x
|- !x. (inv x) op x = i
|- !x y z. (x op y) op z = x op (y op z)


Rules:

|- i op x1 = x1
|- (inv x1) op x1 = i
|- (x1 op x2) op x3 = x1 op (x2 op x3)
|- (inv x1) op (x1 op x2) = x2
|- x1 op i = x1
|- inv i = i
                                    |- inv(inv x1) = x1
 
                                    |- x1 op (inv x1) = i
|- x1 op ((inv x1) op x2) = x2
|- inv(x1 op x2) = (inv x2) op (inv x1)

() : void
Run time: 180.8s
Garbage collection time: 140.2s
Intermediate theorems generated: 17436

#Equations:

|- !x. x op i = x
|- !x. x op (inv x) = i
|- !x y z. (x op y) op z = x op (y op z)


Rules:

|- x1 op i = x1
|- x1 op (inv x1) = i
|- (x1 op x2) op x3 = x1 op (x2 op x3)
|- x1 op ((inv x1) op x2) = x2
|- i op x1 = x1
|- inv i = i
|- inv(inv x1) = x1
|- (inv x1) op x1 = i
|- (inv x1) op (x1 op x2) = x2
|- inv(x1 op x2) = (inv x2) op (inv x1)

() : void
Run time: 437.1s
Garbage collection time: 690.6s
Intermediate theorems generated: 44517

#Equations:

|- !x y. (inv x) op (x op y) = y


Rules:

|- (inv x1) op (x1 op x2) = x2
|- (inv(inv x1)) op x2 = x1 op x2
|- x1 op ((inv x1) op x2) = x2

() : void
Run time: 12.5s
Garbage collection time: 20.6s
Intermediate theorems generated: 1070

#Equations:

|- !x y z. (x op y) op z = x op (y op z)
|- !x. i op x = x
|- !x. Id op x = x
|- !x. (inv x) op x = i
|- !x. (flip x) op x = Id


Rules:

|- (x1 op x2) op x3 = x1 op (x2 op x3)
|- i op x1 = x1
|- (inv x1) op x1 = i
|- (inv x1) op (x1 op x2) = x2
|- x1 op i = x1
|- Id = i
|- inv(inv x1) = x1
|- inv i = i
|- flip x1 = inv x1
|- x1 op (inv x1) = i
|- x1 op ((inv x1) op x2) = x2
|- inv(x1 op x2) = (inv x2) op (inv x1)

() : void
Run time: 309.1s
Garbage collection time: 632.9s
Intermediate theorems generated: 28591

#Equations:

|- !x. i op x = x
|- !x. Id op x = x
|- !x. (inv x) op x = i
|- !x. (flip x) op x = Id
|- !x y z. (x op y) op z = x op (y op z)


Rules:

|- i op x1 = x1
|- (inv x1) op x1 = i
|- (x1 op x2) op x3 = x1 op (x2 op x3)
|- (inv x1) op (x1 op x2) = x2
|- x1 op i = x1
|- Id = i
|- inv i = i
|- inv(inv x1) = x1
|- flip x1 = inv x1
|- x1 op (inv x1) = i
|- x1 op ((inv x1) op x2) = x2
|- inv(x1 op x2) = (inv x2) op (inv x1)

() : void
Run time: 314.1s
Garbage collection time: 807.4s
Intermediate theorems generated: 28779

#Equations:

|- !x y z. (x op y) op (y op z) = y


Rules:
|- (x1 op x2) op (x2 op x3) = x2
|- x1 op ((x1 op x2) op x3) = x1 op x2
|- (x1 op (x2 op x3)) op x3 = x2 op x3

() : void
Run time: 24.5s
Garbage collection time: 64.9s
Intermediate theorems generated: 2297

#Equations:

|- !x. i op x = x
|- !x. x op (inv x) = i
|- !x y z. (x op y) op z = x op (y op z)


Rules:

|- i op x1 = x1
|- x1 op (inv x1) = i
|- (x1 op x2) op x3 = x1 op (x2 op x3)
|- inv i = i
|- x1 op ((inv x1) op x2) = x2
|- inv(inv x1) = x1 op i
|- (inv x1) op (x1 op x2) = x2
|- inv(x1 op x2) = (inv x2) op (inv x1)
|- (inv x1) op i = inv x1

() : void
Run time: 227.3s
Garbage collection time: 666.7s
Intermediate theorems generated: 22972

#Equations:

|- !x y z. (x op y) op (y op z) = y
|- !x. (x op x) op x = un x
|- !x. x op (x op x) = two x
|- !x y. (two x) op y = x op y


Rules:
Space request would exceed maximum memory allocation  
[Storage space totally exhausted]
Space exhausted when allocating  symbol   
evaluation failed     lisp error

%


