let mk_type_name thing = [mk_type(thing,[])]
and mk_type_var thing = [mk_vartype thing]
and add_to_list (lst,thing) = append lst thing
and add_to_list_rev (lst,thing) = append thing lst
and MK_type(lst,op) = [mk_type(op,lst)]
and MK_bin_type(op,type1,typ) = [mk_type(op,(append type1 typ))];;

letrec fix_defd(lst,op,result) =
    if null lst then result
    else fix_defd(tl lst,op,mk_type(op,[hd lst;result]));;

let MK_defd_type(lst,op) =
    [fix_defd(tl (tl lst),op,mk_type(op,[hd (tl lst);hd lst]))];;
