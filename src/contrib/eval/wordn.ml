
let word_el i l = el (i+1) (rev l);;

letrec truncate i l =
 if i=0 then [] else hd l.truncate(i-1)(tl l);;

letrec seg (m,n) l =
 (if m<0 or n<m then fail
  if m=0 then truncate ((n-m)+1) l
         else seg (m-1,n-1) (tl l)
 ) ? failwith `seg`;;

let word_seg (m,n) l = rev(seg(m,n)(rev l));;

%
 mk_CONS_ty ty = ":^ty -> ^ty list -> ^ty list"
%

let mk_CONS_ty ty = 
 let listty = mk_type(`list`,[ty])
 in mk_type(`fun`,[ty; mk_type(`fun`,[listty;listty])]);;

%
 mk_NIL ty = "NIL:(^ty list)"
%

let mk_NIL ty = mk_const(`NIL`, mk_type(`list`,[ty]));;

%
 ol_cons tm1 tm2 = "CONS ^tm1 ^tm2"
%

let ol_cons tm1 tm2 = 
 mk_comb(mk_comb(mk_const(`CONS`, mk_CONS_ty(type_of tm1)),tm1), tm2);;

%
 mk_list ty [tm1; ... tmn] = "[^tm1; ... ;^tmn]:(^ty list)"
%

let mk_list ty l = itlist ol_cons l (mk_NIL ty);;


let int_to_term n = mk_const(string_of_int n, ":num");;

%
 num_to_word w "n" = "#b...b" (w gives the number of b's)
%

let num_to_word w t =
 (let n = int_of_string(fst(dest_const t))
  in
  mk_const
   (implode(`#`.(mk_bin_rep(w,n))), 
    mk_type(concat `word` (string_of_int w), []))
 ) ? failwith `num_to_word`;;

%
 bits_to_int [b1;...;bw] = n (where n is the number denoted by b1...bw)
%

letrec bits_to_int l =
 letrec f e acc l' =
  if null l'   then acc
  if hd l'=`1` then f (2*e) (acc+e) (tl l')
  if hd l'=`0` then f (2*e) acc     (tl l')
               else failwith `bits_to_int`
 in
 f 1 0 (rev l);;

%
 word_to_num "#b...b" = "n" (where n is the number denoted by b...b)
%

let word_to_num t =
 (let tok,ty = dest_const t
  in
  if seg(0,3)(explode(fst(dest_type ty))) = [`w`;`o`;`r`;`d`]
  then int_to_term(bits_to_int(tl(explode tok)))
  else fail
 ) ? failwith `word_to_num`;;

%
 word_or w1 w2 = w3 (where w3 is got by bitwise ORing words w1 and w2)
%

let word_or w1 w2 =
 let tok1,ty1 = dest_const w1
 and tok2,ty2 = dest_const w2
 in
 mk_const
  (implode
    (`#`.
     (map2 
      (\(t1,t2). if t1=`0` & t2=`0` then `0` else `1`)
      (tl(explode tok1), tl(explode tok2)))),
   ty1);;

%
 word_and w1 w2 = w3 (where w3 is got by bitwise ANDing words w1 and w2)
%

let word_and w1 w2 =
 let tok1,ty1 = dest_const w1
 and tok2,ty2 = dest_const w2
 in
 mk_const
  (implode
    (`#`.
     (map2 
      (\(t1,t2). if t1=`1` & t2=`1` then `1` else `0`)
      (tl(explode tok1), tl(explode tok2)))),
   ty1);;

%
 word_not w = w' (where w' is got by bitwise NOTing word w)
%

let word_not w =
 let tok,ty = dest_const w
 in
 mk_const
  (implode
    (`#`.
     (map
      (\t. if t=`1` then `0` else `1`)
      (tl(explode tok)))),
   ty);;

let declare_word_widths numl =
 let tokl = map string_of_int numl
 in
 (map (\tok. new_type 0 (concat `word`      tok)) tokl;
  map (\tok. new_type 0 (concat `tri_word`  tok)) tokl;
  map (\tok.
        let ty  = mk_type(concat `word`     tok, [])
        and ty' = mk_type(concat `tri_word` tok, [])
        in
        new_constant(concat `VAL`      tok, ":^ty -> num");
        new_constant(concat `WORD`     tok, ":num -> ^ty");
        new_constant(concat `BITS`     tok, ":^ty -> bool list");
        new_constant(concat `NOT`      tok, ":^ty -> ^ty");
        new_constant(concat `FLOAT`    tok, ":^ty'");
        new_constant(concat `MK_TRI`   tok, ":^ty  -> ^ty'");
        new_constant(concat `DEST_TRI` tok, ":^ty' -> ^ty ");
        new_infix(concat `U`   tok, ":^ty' -> ^ty' -> ^ty'");
        new_infix(concat `OR`  tok, ":^ty  -> ^ty  -> ^ty");
        new_infix(concat `AND` tok, ":^ty  -> ^ty  -> ^ty"))
      tokl;
  () );;

let declare_memories addr_val_list =
 let tok_pair_l = map (string_of_int # string_of_int) addr_val_list
 in
 (map (\(t1,t2). new_type 0 (concat `mem` (concat t1 (concat `_` t2))))
      tok_pair_l;
  map (\(t1,t2).
        let mty  = mk_type(concat `mem` (concat t1 (concat `_` t2)),[])
        and wty1 = mk_type(concat `word` t1, [])
        and wty2 = mk_type(concat `word` t2, [])
        in
        new_constant(concat `STORE` t1, ":^wty1 -> ^wty2 -> ^mty -> ^mty");
        new_constant(concat `FETCH` t1, ":^mty -> ^wty1 -> ^wty2"))
      tok_pair_l;
  () );;
