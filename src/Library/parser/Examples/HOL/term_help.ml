% 
  Dest_ functions for pre_terms that do the same as their counterparts
  in HOL.
%

let Dest_var (preterm_var x) = x
and Dest_const(preterm_const x) = x
and Dest_comb(preterm_comb(x,y)) = x,y
and left_comb (preterm_comb(x,y)) = x
and right_comb (preterm_comb(x,y)) = y
and Dest_abs (preterm_abs x) = x 
and Dest_type (preterm_typed(x,y)) = x,y
and Dest_antiquot(preterm_antiquot x) = x;;

%
  Create various types of constants.
%

let string_const WORD = preterm_const (`\``^WORD^`\``)
and bool_const WORD = if mem WORD [`T`;`F`] then
                         preterm_typed (preterm_const WORD,mk_type(`bool`,[]))
                      else preterm_var WORD
and num_const WORD = if can int_of_string WORD then 
                        preterm_typed (preterm_const WORD,mk_type(`num`,[]))
                     else failwith `non-num`;;

%
  Sometimes we need a dummy variable as a placeholder when the
  parser is unwinding.
%

let dummy() = preterm_var `$$FOO$$`
and inner(op,T,ty1,ty2,ty3) =
   preterm_comb(preterm_typed(preterm_const op,mk_type(`fun`,[mk_type(ty1,[]);
                                       mk_type(`fun`,[mk_type(ty2,[]);
                                                      mk_type(ty3,[])])])),
        T);;

%
  Make the operators, and check to see that we aren't dealing with
  a placeholder.
%

let mk_binop_untyped(op,T1,T2) =
    if can Dest_var T2 then
       if (Dest_var T2) = `$$FOO$$` then
          T1
       else preterm_comb (preterm_comb(preterm_const op,T1),T2)
    else preterm_comb (preterm_comb(preterm_const op,T1),T2)
and mk_binop_typed (op,T1,T2,ty1,ty2,ty3) =
    if can Dest_var T2 then
       if (Dest_var T2) = `$$FOO$$` then
          T1
       else
          preterm_comb(inner (op,T1,ty1,ty2,ty3),T2)
    else
       preterm_comb(inner (op,T1,ty1,ty2,ty3),T2)
and mk_unop_untyped(op,thing) =
    preterm_comb(preterm_const op,thing)
and mk_unop_typed(op,thing,typ1,typ2) =
    preterm_comb(preterm_typed(preterm_const op,mk_type(`fun`,[mk_type(typ1,[]);mk_type(typ2,[])])),
         thing);;

%
  Functions to make "generic" pre-terms.
%

let IS_infix thing = if is_infix thing then preterm_const thing else fail
and arbit_binop3(prev,op,T1,T2) =
    let c = Dest_const op in
        preterm_comb(preterm_comb (preterm_const c,prev),mk_binop_untyped(c,T1,T2))
and arbit_binop2(op,T1,T2) =
    let c = Dest_const op in
        mk_binop_untyped(c,T1,T2);;

let mk_uncurry thing = preterm_comb(preterm_const `UNCURRY`,thing);;

%
  Modified functions from the type parser.
%

let mk_type_name thing = preterm_typed (preterm_var`foo`,mk_type(thing,[]))
and mk_type_var thing = preterm_typed (preterm_var`foo`,mk_vartype thing)
and add_to_list (lst,thing) = 
    let _,ty1 = Dest_type lst 
    and _,ty2 = Dest_type thing in
        preterm_typed (preterm_var `foo`,mk_type(`prod`,[ty1; ty2]))
and add_to_list_rev (lst,thing) = 
    let _,ty1 = Dest_type lst
    and _,ty2 = Dest_type thing in
        preterm_typed (preterm_var `foo`,mk_type(`prod`,[ty2; ty1]))
and MK_type(lst,op) = 
    let _,ty = Dest_type lst in
        preterm_typed (preterm_var `foo`,mk_type(op,[ty]))
and MK_bin_type(op,type1,typ) =
    let _,ty1 = Dest_type type1 
    and _,ty2 = Dest_type typ in
        preterm_typed (preterm_var `foo`,mk_type(op,[ty1;ty2]));;

letrec convert_to_list ty = 
   let name,lst = dest_type ty in
   if null lst then [mk_type(name,[])]
   else (hd lst) . (convert_to_list (hd (tl lst)));;

letrec fix_defd(lst,op,result) =
    if null lst then result
    else fix_defd(tl lst,op,mk_type(op,[hd lst;result]));;

let MK_defd_type(thing,op) =
    let _,foo = Dest_type thing in
    let ty = convert_to_list foo in
        preterm_typed (preterm_var `foo`,
               fix_defd(tl (tl ty),op,mk_type(op,[hd (tl ty);hd ty])));;

let change_to_typed(prev,typ) =
    let _,ty = Dest_type typ in
        if can Dest_var prev then
           preterm_typed (preterm_var (Dest_var prev),ty)
        else
           preterm_typed (preterm_const (Dest_const prev),ty);;

let mk_cons(car,cdr) =
    preterm_comb(preterm_comb (preterm_const `CONS`,car),cdr);;
